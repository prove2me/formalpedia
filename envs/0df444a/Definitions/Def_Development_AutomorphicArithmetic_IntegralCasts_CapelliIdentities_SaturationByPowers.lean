-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SaturationByPowers
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SaturationByPowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:16.013248+00:00
-- url     : https://prove2.me/theorems/4c16dfa4-57b1-43b5-9a3c-390fa4748ed6
-- title:
--   Saturation By Powers
-- statement:
--   Definitions and structural lemmas for Saturation By Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SaturationByPowers.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers.{u_1} :
    {A : Type u_1} → [inst : CommRing A] → Ideal A → A → Ideal A :=
  fun {A} _ J a =>
    { carrier := {x : A | ∃ n : ℕ, a ^ n * x ∈ J}
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : a ^ (m + n) * (x + y) = a ^ n * (a ^ m * x) + a ^ m * (a ^ n * y) := by ring
        rw [h]
        exact J.add_mem (J.mul_mem_left _ hm) (J.mul_mem_left _ hn)
      zero_mem' := ⟨0, by rw [mul_zero]; exact J.zero_mem⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : a ^ n * (c • x) = c * (a ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact J.mul_mem_left _ hn }


