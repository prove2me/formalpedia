-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionCoordinateEquation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionCoordinateEquation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:40.896866+00:00
-- url     : https://prove2.me/theorems/26e2732a-ee2a-4bbc-ae40-377fc3acac4e
-- title:
--   St Projection Coordinate Equation
-- statement:
--   Definitions and structural lemmas for St Projection Coordinate Equation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StProjectionCoordinateEquation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Matrix
noncomputable section
def ProjectionCoordinateEquation.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ) (O : Set (Fin k → ℂ)),
    IsAffVariety J k → IsOpen O → O.Nonempty → (∀ y ∈ O, ∃ x ∈ zeroLocus J, A *ᵥ x = y) →
    ∀ j : Fin n, ∃ (Q : MvPolynomial (Fin (k + 1)) ℂ) (D : MvPolynomial (Fin k) ℂ), D ≠ 0 ∧
      (∀ x ∈ zeroLocus J, eval (Fin.cons (x j) (A *ᵥ x) : Fin (k + 1) → ℂ) Q = 0) ∧
      ∀ x ∈ zeroLocus J, eval (A *ᵥ x) D ≠ 0 →
        eval (Fin.cons (x j) (A *ᵥ x) : Fin (k + 1) → ℂ) (pderiv 0 Q) ≠ 0
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


