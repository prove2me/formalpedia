-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:16.180698+00:00
-- url     : https://prove2.me/theorems/62441e2d-8a1a-46ea-86b2-648383d39aba
-- title:
--   St Slice Cut Off Limit
-- statement:
--   Definitions and structural lemmas for St Slice Cut Off Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
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
variable {n : ℕ}
def SliceCutOffLimit.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
        ∀ F G : (Fin n → ℂ) → ℝ,
          (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → F (t • x) = F x) →
          (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → G (t • x) = G x) →
          ContDiffOn ℝ ∞ F {x | x ≠ 0} → ContDiffOn ℝ ∞ G {x | x ≠ 0} →
            Tendsto (fun k =>
                varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => χ k x * F x)
                  (vecCons G fun _ x => Real.log (h.dualNorm x))) atTop
              (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) F
                (vecCons G fun _ x => Real.log (h.dualNorm x)))) ∧
            Tendsto (fun k =>
                varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) G
                  (vecCons (fun x => χ k x * F x) fun _ x => Real.log (h.dualNorm x))) atTop
              (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) G
                (vecCons F fun _ x => Real.log (h.dualNorm x))))
end
end GroundTheory.Heights₂.Heights


