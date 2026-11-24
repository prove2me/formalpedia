-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFormsThroughPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFormsThroughPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:27.845078+00:00
-- url     : https://prove2.me/theorems/3e88d5da-f199-4a0b-b5f8-6dd551be0972
-- title:
--   Statements Forms Through Point
-- statement:
--   Definitions and structural lemmas for Statements Forms Through Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsFormsThroughPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def FormsThroughPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((k : ℕ) : WithBot ℕ∞) →
    ∀ x : Fin n → AlgebraicClosure F, x ≠ 0 → (∃ q ∈ Q, aeval x q ≠ 0) →
      ∃ u : Fin k × Fin n → AlgebraicClosure F, (∀ i, ∑ j, u (i, j) * x j = 0) ∧ u ∉ incidence Q k
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


