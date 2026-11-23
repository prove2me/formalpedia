-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:01.021421+00:00
-- url     : https://prove2.me/theorems/f75b50d5-dc3c-4aef-b1a0-c28eca8802ce
-- title:
--   Trace Comp Left Fun Left
-- statement:
--   Definitions and structural lemmas for Trace Comp Left Fun Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TraceCompLeftFunLeft.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
noncomputable section
namespace GlobalTheory.BadShare
section
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)
def coindSum : (G → W) →ₗ[ℂ] Representation.coindV r σ :=
  LinearMap.codRestrict _
    (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) (by
      intro φ δ x
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.compLeft_apply,
        Function.comp_apply, LinearMap.funLeft_apply, map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_
      simp only [Equiv.coe_mulRight, map_mul r, mul_assoc, mul_inv_rev]
      rw [← Module.End.mul_apply, ← map_mul σ, mul_inv_cancel_left])
end
end GlobalTheory.BadShare


