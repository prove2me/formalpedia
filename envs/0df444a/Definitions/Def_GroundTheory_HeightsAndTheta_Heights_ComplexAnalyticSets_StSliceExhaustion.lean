-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:06.821845+00:00
-- url     : https://prove2.me/theorems/4970409a-f1ff-43b4-9b4f-9e642726d560
-- title:
--   St Slice Exhaustion
-- statement:
--   Definitions and structural lemmas for St Slice Exhaustion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceExhaustion.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
def SliceExhaustion.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      ∃ f : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (f k)) ∧ (∀ k, HasCompactSupport (f k)) ∧
        (∀ k x, f k x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x, Tendsto (fun k => f k x) atTop (𝓝 1)) ∧
        Tendsto (fun k => varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (f k)
            (fun _ x => Real.log (h.dualNorm x))) atTop
          (𝓝 (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
            (fun _ x => Real.log (h.dualNorm x)))) ∧
        (∀ W ∈ (divCycle J u).support,
          Tendsto (fun k => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k)
              (fun _ x => Real.log (h.dualNorm x))) atTop
            (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (fun _ => 1)
              (fun _ x => Real.log (h.dualNorm x))))) ∧
        Tendsto (fun k =>
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
                (vecCons (f k) fun _ x => Real.log (h.dualNorm x)) -
              varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
                (vecCons (f k) fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)
end
end GroundTheory.Heights₂.Heights


