-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:50.645206+00:00
-- url     : https://prove2.me/theorems/3189bd98-7b6a-4382-afbb-02eb336e7d13
-- title:
--   St Lelong Mass Near Small
-- statement:
--   Definitions and structural lemmas for St Lelong Mass Near Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLelongMassNearSmall.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def LelongMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (J I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → J ⊔ Ideal.span {linForm u} ≤ I →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ δ > 0, ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧
        (∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          |varInt J (d + 1) (fun x => χ x * f x) (vecCons (logReg u ε) φ)| ≤ δ) ∧
        |∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (fun x => χ x * f x) φ| ≤ δ
end
end GroundTheory.Heights₂.Heights


