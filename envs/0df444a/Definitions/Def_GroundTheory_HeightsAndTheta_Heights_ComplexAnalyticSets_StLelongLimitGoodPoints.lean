-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitGoodPoints
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitGoodPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:26.745966+00:00
-- url     : https://prove2.me/theorems/24f4d705-3354-4aaa-836d-7696dab66dbd
-- title:
--   St Lelong Limit Good Points
-- statement:
--   Definitions and structural lemmas for St Lelong Limit Good Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLelongLimitGoodPoints.lean

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
def LelongLimitGoodPoints.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
            Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
              (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
                  (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
                (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))
end
end GroundTheory.Heights₂.Heights


