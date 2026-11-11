-- Prove2me | Definitions.Def_ARGFContract_Hardness_BinaryCodes
-- name    : ARGFContract_Hardness_BinaryCodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:23.083259+00:00
-- url     : https://prove2.me/theorems/0788225b-7898-41e8-9195-44b3c550e49d
-- title:
--   Binary numbers, exact rational values, and subset bitmaps
-- statement:
--   Natural numbers use least-significant-first binary digits, each prefixed by a $1$, terminated by a $0$. A rational is its sign followed by the self-delimiting codes of the absolute reduced numerator and positive denominator. A subset of $\{0,\ldots,n-1\}$ is an $n$-bit bitmap.
--
--   $$S(b)=\{i<n:b_i=1\}.$$
--
--   Missing bits are zero and excess bits are ignored, so every output word is feasible. The parser rejects unfinished digit blocks. These explicit conventions implement the paper's input-size and exact-value interpretation without tabulating a set function.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), §2.1, p. 5, Definition 2.1 (3), p. 6, and Definition 3.3, p. 10; computational encoding reading; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Mathlib

namespace ARGFContract.Hardness

/-- Self-delimiting least-significant-first binary digits, terminated by 0.
Each digit b is represented by 1b. -/
def encodeNat (n : ℕ) : List Bool := (n.bits.flatMap fun b => [true, b]) ++ [false]

/-- Parse a self-delimiting digit block; malformed or unterminated input fails. -/
def parseDigits : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (digits, tail) ← parseDigits rest
      pure (b :: digits, tail)
  | _ => none

/-- Exact signed reduced rational representation: sign, binary |numerator|, denominator. -/
def encodeRat (q : ℚ) : List Bool :=
  decide (q.num < 0) :: (encodeNat q.num.natAbs ++ encodeNat q.den)

/-- Every word denotes a subset. Missing bits are false, excess bits are ignored. -/
def decodeBitmap (n : ℕ) (bits : List Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => bits.getD i.val false = true

/-- The canonical n-bit output for a subset. -/
def encodeBitmap {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn fun i => decide (i ∈ S)

end ARGFContract.Hardness


