{-# LANGUAGE BinaryLiterals #-}

module Main where

import Utils
import Prune

import Control.Monad
import Data.Bits
import Data.List
import Data.Maybe
import Data.Word
import Prelude                                            as P

import qualified Data.Array.Accelerate                    as A
import qualified Data.Array.Accelerate.LLVM.Native        as CPU
import qualified Data.Array.Accelerate.Interpreter        as Interpreter
-- import qualified Data.Array.Accelerate.LLVM.PTX           as PTX

newtype Sudoku = Sudoku (A.Array A.DIM2 Word16)

main =
  interact
    -- $ show . (\x -> (length x, map length x, sum $ map length x))
    $ pretty . head
    . solve
    . readSudoku

pretty :: [[Word16]] -> String
pretty []  = "mwep"
pretty grs = concatMap (foldl f "\n" . sud) grs where
  sud [] = []
  sud xs = take 9 xs : sud (drop 9 xs)
  f s xs = s ++ unwords (map (show . unBitmap) xs) ++ "\n"

-- currently returns a list of possible solutions, in practice this list
-- usually contains only the actual solution. It should not be hard to
-- filter the bad solutions out.
--
solve :: [[Word16]] -> [[[Word16]]]
solve grs = solve' (accelerateStep grs, [])
 where
  solve' :: ([[Word16]], [[[Word16]]]) -> [[[Word16]]]
  solve' ([], xs) = xs
  solve' (todos, xs) =
    let (finished, newtodos) = partition solved todos
    in  let ys = accelerateStep . concatMap doGuess $ newtodos
        in  solve' (ys, finished : xs)

  doGuess :: [Word16] -> [[Word16]]
  doGuess xs =
    let i = splitIndex xs
    in  map (\j -> take i xs ++ j : drop (i + 1) xs) (splitBits (xs !! i))

  splitIndex :: [Word16] -> Int
  splitIndex xs =
    let ys = map (\x -> if testBit x 9 then 100 else popCount x) xs
    in  fromJust $ elemIndex (minimum ys) ys

  accelerateStep :: [[Word16]] -> [[Word16]]
  accelerateStep xs =
    let (ys, bools) = accelerateStep' xs
    in  (map snd . filter fst . zip (A.toList bools) . chunkList 81 . A.toList)
          ys

  accelerateStep' :: [[Word16]] -> (A.Array A.DIM3 Word16, A.Array A.DIM1 Bool)
  accelerateStep' xs
      = step
      $ A.fromList (A.Z A.:. length xs A.:. 9 A.:. 9)
      $ concat xs

  step :: A.Array A.DIM3 Word16 -> (A.Array A.DIM3 Word16, A.Array A.DIM1 Bool)
  step = CPU.runN pruneAndCheck

solved :: [Word16] -> Bool
solved = all (`testBit` 9)

help :: [[Word16]] -> String
help = show . map (map (map help') . chunkList 9)
help' x = map (\i -> testBit x (i - 1)) [1 .. 9]

readSudoku :: String -> [[Word16]]
readSudoku = go . map f . filter valid where
  f '.' = 511 --decimal for the binary value of 9 ones
  f '1' = (512 +) $ setBit 0 0
  f '2' = (512 +) $ setBit 0 1
  f '3' = (512 +) $ setBit 0 2
  f '4' = (512 +) $ setBit 0 3
  f '5' = (512 +) $ setBit 0 4
  f '6' = (512 +) $ setBit 0 5
  f '7' = (512 +) $ setBit 0 6
  f '8' = (512 +) $ setBit 0 7
  f '9' = (512 +) $ setBit 0 8
  valid x = x `elem` ".123456789"
  go [] = []
  go xs = take 81 xs : go (drop 81 xs)

splitBits :: Word16 -> [Word16]
splitBits w = mapMaybe f [0 .. 8]
 where
  f i | testBit w i = Just $ bit i
      | otherwise   = Nothing


unBitmap 513 = 1
unBitmap 514 = 2
unBitmap 516 = 3
unBitmap 520 = 4
unBitmap 528 = 5
unBitmap 544 = 6
unBitmap 576 = 7
unBitmap 640 = 8
unBitmap 768 = 9
unBitmap i   = 0

readSudoku' :: String -> Sudoku
readSudoku'
  = Sudoku
  . A.fromList (A.Z A.:. 9 A.:. 9)
  . P.map f
  where
    f '.' = 0b0111111111
    f '1' = 0b1000000001
    f '2' = 0b1000000010
    f '3' = 0b1000000100
    f '4' = 0b1000001000
    f '5' = 0b1000010000
    f '6' = 0b1000100000
    f '7' = 0b1001000000
    f '8' = 0b1010000000
    f '9' = 0b1100000000
    f _   = error "readSudoku: elements must be one of \".123456789\""

showSudoku' :: Sudoku -> String
showSudoku' (Sudoku s) = undefined
  where
    f 0b0111111111 = '.'
    f 0b1000000001 = '1'
    f 0b1000000010 = '2'
    f 0b1000000100 = '3'
    f 0b1000001000 = '4'
    f 0b1000010000 = '5'
    f 0b1000100000 = '6'
    f 0b1001000000 = '7'
    f 0b1010000000 = '8'
    f 0b1100000000 = '9'
    f _            = error "showSudoku: unexpected value"

-- instance Show Sudoku where
--   show (Sudoku s) =
--     flip P.map [0..2] $ \by ->
--       flip P.map [0..2] $ \bx ->
--         flip P.map [0..2] $ \cy ->
--           flip P.map [0..2] $ \cx ->
--             unBitmap $ A.indexArray s (A.Z A.:. by*3+cy A.:. bx*3+cx)

