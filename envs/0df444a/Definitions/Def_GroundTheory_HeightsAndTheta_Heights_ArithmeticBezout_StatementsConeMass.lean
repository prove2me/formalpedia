-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:18.686261+00:00
-- url     : https://prove2.me/theorems/1b57c579-d5e6-4622-903c-403fa2bae4fe
-- title:
--   Statements Cone Mass
-- statement:
--   Definitions and structural lemmas for Statements Cone Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
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
open MvPolynomial MeasureTheory
noncomputable section
def ConeMassOfFibre.Statement : Prop :=
  ∀ (n m δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsProjPrime J →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = δ) →
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
        (δ : ENNReal) * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}
end
end GroundTheory.Heights₂.Heights


