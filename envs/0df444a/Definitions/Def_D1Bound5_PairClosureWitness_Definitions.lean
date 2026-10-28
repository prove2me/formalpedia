-- Prove2me | Definitions.Def_D1Bound5_PairClosureWitness_Definitions
-- name    : D1Bound5_PairClosureWitness_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:53:35.260343+00:00
-- url     : https://prove2.me/theorems/94ebe7af-7621-4ec5-a679-05b5c670efd4
-- title:
--   Pair Closure Witness
-- statement:
--   An explicit pair-extension vertex and square roots of both anchor products. The checker verifies these equalities; the record itself asserts nothing. The named objects in this bundle include `PairRootWitness`, `PairRootWitness.leftRoot`, `PairRootWitness.rightRoot`, `PairRootWitness.vertex`, `pairWitnessCandidateCoveredBool`, `pairRootWitnessCheckedBool`, `pairClosureWitnessBool`.
-- source:
--   D1Bound5/PairClosureWitness.lean, lines 6-11, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62; D1Bound5/PairClosureWitness.lean, lines 13-16, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62; D1Bound5/PairClosureWitness.lean, lines 18-29, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62; D1Bound5/PairClosureWitness.lean, lines 31-38, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5
open QuadInt

/-- An explicit pair-extension vertex and square roots of both anchor products.
The checker verifies these equalities; the record itself asserts nothing. -/
structure PairRootWitness (tau nu : ℤ) where
  vertex : QuadInt tau nu
  leftRoot : QuadInt tau nu
  rightRoot : QuadInt tau nu

/-- A candidate outside the bound needs no list membership certificate. -/
def pairWitnessCandidateCoveredBool {tau nu : ℤ} (bound : ℤ)
    (vertices : List (QuadInt tau nu)) (w : QuadInt tau nu) : Bool :=
  if decide (w.norm ≤ bound) then decide (w ∈ vertices) else true

/-- Verify supplied roots and the two distinct mutation values. The four
choices of signs for the two supplied roots yield precisely these two values.
This computation contains no square-root search. -/
def pairRootWitnessCheckedBool {tau nu : ℤ} (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (w : PairRootWitness tau nu) : Bool :=
  decide (w.leftRoot * w.leftRoot = a * w.vertex + 1 ∧
    w.rightRoot * w.rightRoot = b * w.vertex + 1) &&
    (pairWitnessCandidateCoveredBool bound vertices
        (mutate a b w.vertex r0 w.leftRoot w.rightRoot) &&
      pairWitnessCandidateCoveredBool bound vertices
        (mutate a b w.vertex r0 w.leftRoot (-w.rightRoot)))

/-- A replacement closure certificate. It verifies the anchor root, exact
coverage in the original vertex order, all vertex roots, and both mutations.
The original vertex list and final mathematical closure claim are unchanged. -/
def pairClosureWitnessBool {tau nu : ℤ} (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu)) : Bool :=
  decide (r0 * r0 = a * b + 1 ∧ witnesses.map PairRootWitness.vertex = vertices) &&
    witnesses.all (pairRootWitnessCheckedBool a b r0 bound vertices)













end D1Bound5
end


