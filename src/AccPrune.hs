{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module AccPrune where

import Data.Word
import qualified Prelude                        as P

import Data.Array.Accelerate                    as A
import Data.Array.Accelerate.Data.Bits
import Data.Array.Accelerate.Control.Lens


-- bitmap: bits 0 to 8 are numbers and bit 9 represents that there is only
-- one option left.
--
type Cell = Word16

-- Returns the pruned list of sudokus, together with a list of bools
-- representing whether the sudoku is inconsistent (contains a field that
-- can't be filled anymore)
--
pruneAndCheck
    :: Acc (Array DIM3 Cell)
    -> Acc (Array DIM3 Cell, Array DIM1 Bool) --n*9*9 -> (n*9*9,n)
pruneAndCheck = finish . pruneGrids
  where
    finish xs = T2 xs (zipWith3 (\x y z -> x && y && z) (check1 xs) (check2 xs) (check3 xs))

    check1 xs =
      let sz ::. h ::. w = shape xs
          xs'            = reshape (sz ::. h*w) xs
       in fold1 (&&) $ map (/=0) xs'

    check2  = fold1 (&&)
            . map (\x -> 511 == x .&. 511)
            . fold1 (.|.)

    check3  = check2 . transposeOn _1 _2

-- gets a list of sudokus (2+1=3dim) (n*9*9)
--
-- replicate this 3 times (4dim) (3*n*9*9)
-- permute the second one to make it columns instead of rows
-- permute the third one to make it blocks instead of rows
--
-- replicate this twice, applying 'weirdtransform' to one of them. (2*3*n*9*9)
-- weirdtransform applies a bijection between the numbers 1..9 and the 9 fields in each `row`.
-- So for example if the bit for digit 5 was set in only the first three fields, the new fifth field will have binary value 111.
-- (I haven't seen this transformation anywhere before)
-- This allows us to only search for fields that have only 1 or 2 bits set, automatically also finding the bits that are only set in 1 or 2 fields.
--
-- fold over the innermost dimension to get a single bitmap of all numbers that are already found in this row/column/block
-- use the this version to imap over the original and remove all disallowed bits
--
-- permute to make all 3 versions align again
-- transposeOn and fold to fuse all the changes within each sudoku
--
-- map over everything to set all relevant bit9s
--
-- use awhile to loop this
--
-- pruneGrids is `safe` on sudokus that are still possible, but as soon as
-- a bad guess is done outside of pruneGrid it will ofcourse result in
-- questionable sudoku solutions. This needs to be checked seperately.
--
pruneGrids :: Acc (Array DIM3 Cell) -> Acc (Array DIM3 Cell)
pruneGrids xs = asnd $ awhile p f (T2 xs (pruneGrids' xs))
  where
    f (T2 _ y) = T2 y (pruneGrids' y)
    p (T2 x y) = map not
               . and
               . flatten
               $ zipWith (==) x y

pruneGrids' :: Acc (Array DIM3 Cell) -> Acc (Array DIM3 Cell)
pruneGrids'
  = mapSingles
  . fuseSudokus
  . pruneDoubles
  . pruneSingles
  . mapSingles
  . splitSudokus

splitSudokus :: Acc (Array DIM3 Cell) -> Acc (Array DIM5 Cell)
splitSudokus
  = weirdtransform
  . (\xs -> backpermute (shape xs) permutation xs)
  . replicate (constant (Z :. (3::Int) :. All :. All :. All))
  . map (`clearBit` 9)


-- this permutation is a bijection, and its own inverse.
--
permutation :: Exp DIM4 -> Exp DIM4
permutation (I4 m n i j) =
       if m == 0 then Z_ ::. 0 ::. n ::. i ::. j    -- rows
  else if m == 1 then Z_ ::. 1 ::. n ::. j ::. i    -- columns
  else {- m == 2 -} let c  = 3*i+(j`div`3)          -- blocks
                        d  = j`rem`3
                        c' = 9*(c`div`9) + 3*(c`rem`3) + (c`rem`9)`div`3
                     in Z_ ::. 2 ::. n ::. (c'`div`3) ::. (3*(c'`rem`3)+d)

-- adds another layer, bijecting between numbers and fields.
--
weirdtransform :: Acc (Array DIM4 Cell) -> Acc (Array DIM5 Cell)
weirdtransform xs = concatOn _3 (split3 xs) (split3 (weirdtransform' xs))
  where
    split3 = replicate (constant (Z :. All :. All :. (1::Int) :. All :. All))

unweirdtransform :: Acc (Array DIM5 Cell) -> Acc (Array DIM4 Cell)
unweirdtransform xs =
  let ys = slice xs (constant (Z :. All :. All :. (0::Int) :. All :. All))
      zs = slice xs (constant (Z :. All :. All :. (1::Int) :. All :. All))
   in
   zipWith (.&.) ys (weirdtransform' zs)

--weirdtransform' is also its own inverse, except for bit9
--
weirdtransform' :: Acc (Array DIM4 Cell) -> Acc (Array DIM4 Cell)
weirdtransform' xs =
  let f b = replicate (constant (Z :. All :. All :. All :. (1::Int)))
          . fold1 (.|.)
          . A.imap (\(I4 _ _ _ i) y -> shiftL 1 b .&. y == 0 ? (0, setBit 0 i))
          $ xs
   in
   P.foldr1 (++) (P.map (f . constant) [0..8])

pruneSingles :: Acc (Array DIM5 Cell) -> Acc (Array DIM5 Cell)
pruneSingles xs
  = zipWith (\x y -> if testBit x 9 then x else x .&. complement y) xs
  $ replicate (constant (Z :. All :. All :. All :. All :. (9::Int)))
  $ findSingles xs

-- bit 9 represents a field having only 1 option left, here we .|. all those bits.
--
findSingles :: Acc (Array DIM5 Cell) -> Acc (Array DIM4 Cell)
findSingles
  = fold1 (.|.)
  . map (\x -> if testBit x 9 then x `clearBit` 9 else 0)

fuseSudokus :: Acc (Array DIM5 Cell) -> Acc (Array DIM3 Cell)
fuseSudokus
  = fold1 (.&.)
  . transposeOn _1 _4
  . transposeOn _1 _3
  . transposeOn _1 _2
  . (\xs -> backpermute (shape xs) permutation xs)
  . unweirdtransform

mapSingles :: Shape sh => Acc (Array sh Cell) -> Acc (Array sh Cell)
mapSingles
  = map (\x -> if popCount x == 1 then setBit x 9 else x)
  . map (`clearBit` 9)

pruneDoubles :: Acc (Array DIM5 Cell) -> Acc (Array DIM5 Cell)
pruneDoubles
  = pruneDoubles'
  . map (`clearBit` 9)

pruneDoubles' :: Acc (Array DIM5 Cell) -> Acc (Array DIM5 Cell)
pruneDoubles' xs
  = zipWith f xs
  . replicate (constant (Z :. All :. All :. All :. All :. (9::Int)))
  $ findDoubles xs
  where
    f x y = if popCount x <= 2 && x == x .&. y
               then x
               else x .&. complement y

findDoubles :: Acc (Array DIM5 Cell) -> Acc (Array DIM4 Cell)
findDoubles
  = map unDoubleIndexes
  . map (\(T3 _ z2 z3) -> z2 - z3)
  . fold1 f
  . map (\x -> T3 x 0 0)
  . map doubleIndexes
  where
    f (T3 x1 x2 x3) (T3 y1 y2 y3) =
      T3 (x1 .|. y1)                                  -- seen at least once
         (x2 .|. y2 .|. (x1 .&. y1))                  -- seen at least twice
         (x3 .|. y3 .|. (x1 .&. y2) .|. (x2 .&. y1))  -- seen more than twice


-- inverse of below, for a map containing an arbitrary number of bits that
-- each refer to two numbers, recover which numbers are all relevant
--
unDoubleIndexes :: Exp Word64 -> Exp Word16
unDoubleIndexes = fst . while p f . T2 0
  where
    p (T2 _ b) = b /= 0
    f (T2 a b) = T2 (a .|. fromIntegral (unDoubleIndex b))
                    (clearBit b (countTrailingZeros b))

    -- unDoubleIndex could also be written with the floor of a square root for
    -- less conditionals
    unDoubleIndex :: Exp Word64 -> Exp Word64
    unDoubleIndex x =
      let i = countTrailingZeros x
       in if i <  8 then setBit (shift x    1 ) 0 else
          if i < 15 then setBit (shift x (- 6)) 1 else
          if i < 21 then setBit (shift x (-12)) 2 else
          if i < 26 then setBit (shift x (-17)) 3 else
          if i < 30 then setBit (shift x (-21)) 4 else
          if i < 33 then setBit (shift x (-24)) 5 else
          if i < 35 then setBit (shift x (-26)) 6 else
                           setBit (setBit 0 8)  7

-- Given a word, if it has exactly two bits set, compute a bitmask that
-- signifies which two bits are set. Barely doesn't fit in 32 bits :(
--
doubleIndexes :: Exp Word16 -> Exp Word64
doubleIndexes i =
  let firstBit  = countTrailingZeros i
      secondBit = countTrailingZeros (shift i (-firstBit-1))
   in
   if popCount i /= 2
      then 0
      else setBit 0 (secondBit + (36 - shift ((9-firstBit)*(8-firstBit)) (-1)))

