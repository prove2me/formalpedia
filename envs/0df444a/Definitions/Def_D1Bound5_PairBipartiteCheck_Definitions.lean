-- Prove2me | Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
-- name    : D1Bound5_PairBipartiteCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:28:07.456992+00:00
-- url     : https://prove2.me/theorems/9a151d73-f169-40ac-94bf-829a9d6d602a
-- title:
--   Pair Bipartite Check
-- statement:
--   An arbitrary bit mask partitions every input occurrence. No correctness condition on the mask, disjointness, or absence of duplicates is needed. The named objects in this bundle include `pairSplitByMask`, `pairIndependentBool`.
-- source:
--   D1Bound5/PairBipartiteCheck.lean, lines 6-12, SHA-256 d1497b46c9dcbae577d7172e6c4401388a1797e68d33ba795d4e6a6a05dd4c0c; D1Bound5/PairBipartiteCheck.lean, lines 28-35, SHA-256 d1497b46c9dcbae577d7172e6c4401388a1797e68d33ba795d4e6a6a05dd4c0c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions

section
namespace D1Bound5
open QuadInt

/-- An arbitrary bit mask partitions every input occurrence. No correctness
condition on the mask, disjointness, or absence of duplicates is needed. -/
def pairSplitByMask {α : Type*} : List α → ℕ → List α × List α
  | [], _ => ([], [])
  | x::xs, colors =>
      let tail := pairSplitByMask xs (colors / 2)
      if colors.testBit 0 then (tail.1, x::tail.2) else (x::tail.1, tail.2)



/-- Each unordered pair of distinct values is tested once. Repetitions are
allowed; a square root of zero is treated exactly as every other root. -/
def pairIndependentBool {tau nu : ℤ} (sieve : List (ℕ × ℕ)) :
    List (QuadInt tau nu) → Bool
  | [] => true
  | x::xs =>
      (xs.all fun y => if decide (x = y) then true
        else !(hasSquareRootFast sieve (x*y+1))) && pairIndependentBool sieve xs







end D1Bound5
end


