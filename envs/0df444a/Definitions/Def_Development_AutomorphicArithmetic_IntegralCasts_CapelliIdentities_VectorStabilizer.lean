-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VectorStabilizer
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VectorStabilizer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:19.281796+00:00
-- url     : https://prove2.me/theorems/612de7d7-dee8-44fb-9324-df91676586f9
-- title:
--   Vector Stabilizer
-- statement:
--   Definitions and structural lemmas for Vector Stabilizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/VectorStabilizer.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.VectorStabilizer.vecStab :
    {M : Type} →
      [inst : Group M] →
        {X : Type} → [inst_1 : AddCommGroup X] → [inst_2 : _root_.Module ℂ X] → Representation ℂ M X → X → Subgroup M :=
  fun {M} _ {_} _ _ ρ x =>
    { carrier := {g : M | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one, Module.End.one_apply]
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by rw [inv_mul_cancel, map_one, Module.End.one_apply] }


