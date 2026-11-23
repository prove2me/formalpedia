-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisLast
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisLast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:11.716809+00:00
-- url     : https://prove2.me/theorems/4a338786-c959-4203-b702-982d10eaebc1
-- title:
--   Imports Bis Last
-- statement:
--   Definitions and structural lemmas for Imports Bis Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsBisLast.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
def UpperTheory.Reformulated.B.RepresentationStabilizer.stab {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U) (u : U) : Subgroup G where
  carrier := {g | ρ g u = u}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [ha]
      _ = u := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]


