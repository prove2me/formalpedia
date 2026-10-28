-- Prove2me | Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
-- name    : D1Bound5_PairClosureIndexedWitness_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:57:24.134838+00:00
-- url     : https://prove2.me/theorems/2b5e3db5-68fc-4b25-8c1b-8aadec50f85b
-- title:
--   Pair Closure Indexed Witness
-- statement:
--   A supplied destination is checked by exact indexed lookup. `none` is accepted only when the computed candidate lies strictly outside the bound. No membership search or square-root search occurs in this checker. The named objects in this bundle include `pairIndexedCandidateCoveredBool`, `pairIndexedRootWitnessCheckedBool`, `pairIndexedWitnessesCheckedBool`, `pairClosureIndexedWitnessBool`.
-- source:
--   D1Bound5/PairClosureIndexedWitness.lean, lines 6-14, SHA-256 396e39b992bc9611aabcfcda13356692e98676409381a756555e84104fe22420; D1Bound5/PairClosureIndexedWitness.lean, lines 16-26, SHA-256 396e39b992bc9611aabcfcda13356692e98676409381a756555e84104fe22420; D1Bound5/PairClosureIndexedWitness.lean, lines 28-37, SHA-256 396e39b992bc9611aabcfcda13356692e98676409381a756555e84104fe22420; D1Bound5/PairClosureIndexedWitness.lean, lines 39-46, SHA-256 396e39b992bc9611aabcfcda13356692e98676409381a756555e84104fe22420. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions

section
namespace D1Bound5
open QuadInt

/-- A supplied destination is checked by exact indexed lookup. `none` is
accepted only when the computed candidate lies strictly outside the bound.
No membership search or square-root search occurs in this checker. -/
def pairIndexedCandidateCoveredBool {tau nu : ℤ} (bound : ℤ)
    (vertices : List (QuadInt tau nu)) (w : QuadInt tau nu)
    (destination : Option Nat) : Bool :=
  match destination with
  | none => decide (bound < w.norm)
  | some i => decide (vertices[i]? = some w)

/-- Check the same supplied roots and both signed mutations as the accepted
witness checker, using the two supplied destination indices. -/
def pairIndexedRootWitnessCheckedBool {tau nu : ℤ} (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (w : PairRootWitness tau nu) (destinations : Option Nat × Option Nat) : Bool :=
  decide (w.leftRoot * w.leftRoot = a * w.vertex + 1 ∧
    w.rightRoot * w.rightRoot = b * w.vertex + 1) &&
    (pairIndexedCandidateCoveredBool bound vertices
        (mutate a b w.vertex r0 w.leftRoot w.rightRoot) destinations.1 &&
      pairIndexedCandidateCoveredBool bound vertices
        (mutate a b w.vertex r0 w.leftRoot (-w.rightRoot)) destinations.2)

/-- Consume the roots and destination pairs together. Either unmatched tail
rejects the certificate, so no vertex or mutation sign can be omitted. -/
def pairIndexedWitnessesCheckedBool {tau nu : ℤ} (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu)) :
    List (PairRootWitness tau nu) → List (Option Nat × Option Nat) → Bool
  | [], [] => true
  | w :: ws, d :: ds =>
      pairIndexedRootWitnessCheckedBool a b r0 bound vertices w d &&
        pairIndexedWitnessesCheckedBool a b r0 bound vertices ws ds
  | _, _ => false

/-- The original anchor root and ordered vertex coverage are checked exactly.
Only the method of certifying each mutation's membership is different. -/
def pairClosureIndexedWitnessBool {tau nu : ℤ} (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat)) : Bool :=
  decide (r0 * r0 = a * b + 1 ∧ witnesses.map PairRootWitness.vertex = vertices) &&
    pairIndexedWitnessesCheckedBool a b r0 bound vertices witnesses destinations











end D1Bound5
end


