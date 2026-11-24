-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:12.404289+00:00
-- url     : https://prove2.me/theorems/404b8c70-cca5-4a5d-be0b-7c7e0eefb01f
-- title:
--   St Cone Sheet Gram
-- statement:
--   Definitions and structural lemmas for St Cone Sheet Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StConeSheetGram.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeChartGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
def ConeSheetGram.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℝ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
    IntegrableOn f {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}
      (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) →
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
          ∫ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, f z
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0}).toReal *
          ∫ y, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
            (fun _ s => ∫ t : ℂ, f (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y)) *
              (‖t‖ ^ (2 * e) * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y)) y
end
end GroundTheory.Heights₂.Heights


