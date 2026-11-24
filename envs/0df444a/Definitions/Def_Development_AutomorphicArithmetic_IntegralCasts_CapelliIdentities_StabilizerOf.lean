-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:03.535817+00:00
-- url     : https://prove2.me/theorems/f8618d48-7199-4316-8186-b3fa4823230f
-- title:
--   Stabilizer Of
-- statement:
--   Definitions and structural lemmas for Stabilizer Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/StabilizerOf.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.StabilizerOf.stabilizerOf.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] →
        {V : Type u_2} → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G} _ {_V} _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      one_mem' := by
        show ρ 1 v = v
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by rw [inv_mul_cancel, map_one]; rfl }


