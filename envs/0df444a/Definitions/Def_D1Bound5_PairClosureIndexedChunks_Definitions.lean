-- Prove2me | Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
-- name    : D1Bound5_PairClosureIndexedChunks_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:39:04.740295+00:00
-- url     : https://prove2.me/theorems/7cdc5175-6e81-4d7c-97f7-4cdeac77327c
-- title:
--   Pair Closure Indexed Chunks
-- statement:
--   Check a prefix of witness/destination rows. Destination indices always refer to the complete original vertex list, never to a truncated list. The named objects in this bundle include `pairIndexedWitnessesPrefixBool`.
-- source:
--   D1Bound5/PairClosureIndexedChunks.lean, lines 6-16, SHA-256 29488713ab2248b4e724873977d8278f8e302994a76dfd2d1c47bf8aa3e6e226. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions

section
namespace D1Bound5
open QuadInt

/-- Check a prefix of witness/destination rows. Destination indices always
refer to the complete original vertex list, never to a truncated list. -/
def pairIndexedWitnessesPrefixBool {tau nu : ℤ} (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu)) :
    ℕ → List (PairRootWitness tau nu) → List (Option Nat × Option Nat) → Bool
  | 0, _, _ => true
  | _ + 1, [], [] => true
  | n + 1, w :: ws, d :: ds =>
      pairIndexedRootWitnessCheckedBool a b r0 bound vertices w d &&
        pairIndexedWitnessesPrefixBool a b r0 bound vertices n ws ds
  | _ + 1, _, _ => false









end D1Bound5
end


