-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Saturation
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Saturation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:23.537492+00:00
-- url     : https://prove2.me/theorems/30680e04-030c-424f-823d-914dd3bad8ee
-- title:
--   Saturation
-- statement:
--   Definitions and structural lemmas for Saturation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/Saturation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.IdealSaturationByElement.sat :
    {R : Type} → [inst : CommRing R] → Ideal R → R → Ideal R :=
  fun {R} _ Q f =>
    { carrier := {g : R | ∃ n : ℕ, f ^ n * g ∈ Q}
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : f ^ (m + n) * (a + b) = f ^ n * (f ^ m * a) + f ^ m * (f ^ n * b) := by ring
        rw [h]
        exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : f ^ n * (c • a) = c * (f ^ n * a) := by
          rw [smul_eq_mul]; ring
        rw [h]
        exact Q.mul_mem_left _ hn }


