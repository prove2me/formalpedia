-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongPolyLimit
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongPolyLimit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:10.150621+00:00
-- url     : https://prove2.me/theorems/decfb730-aaaf-40a7-8766-732f900811c6
-- title:
--   St Lelong Poly Limit
-- statement:
--   Definitions and structural lemmas for St Lelong Poly Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StLelongPolyLimit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology Matrix
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult)
def LelongPolyLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (f k : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → p ∉ J →
    SmoothNear (ComplexSets.zeroSet J) f → HasCompactSupport f →
    (∀ j, SmoothNear (ComplexSets.zeroSet J) (φ j)) →
    SmoothNear (ComplexSets.zeroSet J) k → (∀ x ∈ ComplexSets.zeroSet J, 0 < k x) →
      Tendsto (fun ε : ℝ =>
          varInt J (d + 1) f (vecCons (fun x => Real.log (‖eval x p‖ ^ 2 + ε * k x ^ 2) / 2) φ))
        (𝓝[>] 0)
        (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {p}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {p}) W : ℝ) * varInt W d f φ))
end GroundTheory.Heights₂.Heights.Targets


