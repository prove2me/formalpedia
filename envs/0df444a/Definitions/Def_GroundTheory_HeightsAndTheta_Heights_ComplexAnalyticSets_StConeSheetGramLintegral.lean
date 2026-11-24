-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:29.140568+00:00
-- url     : https://prove2.me/theorems/4fb82653-ece9-42ad-9956-84fe912bcef8
-- title:
--   St Cone Sheet Gram Lintegral
-- statement:
--   Definitions and structural lemmas for St Cone Sheet Gram Lintegral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StConeSheetGramLintegral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
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
open scoped ENNReal
noncomputable section
open Classical in

def sheetThrough {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (x : Fin n → ℂ) : (Fin d → ℂ) → Fin n → ℂ :=
  if hs : ∃ s, IsSheetAt J A x s then hs.choose else 0
def ConeSheetGramLintegral.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A → Measurable F →
      AEMeasurable (fun y : Fin e → ℂ =>
          ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
            F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
              ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
                (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) ∧
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, F z
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0} *
          ∫⁻ y : Fin e → ℂ,
            ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
              F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
                ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
                  (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)
end
end GroundTheory.Heights₂.Heights


