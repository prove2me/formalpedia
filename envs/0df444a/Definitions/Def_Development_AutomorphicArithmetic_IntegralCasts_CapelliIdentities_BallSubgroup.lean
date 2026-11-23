-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:08.316792+00:00
-- url     : https://prove2.me/theorems/4e0ca189-005f-42ca-a339-a97341cbf68e
-- title:
--   Ball Subgroup
-- statement:
--   Definitions and structural lemmas for Ball Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BallSubgroup.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.BallSubgroup.ball :
    (L : Type) → [inst : NontriviallyNormedField L] → [IsUltrametricDist L] → ValuationSubring L :=
  fun L _ _ =>
    { carrier := {x : L | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rwa [norm_neg]
      mem_or_inv_mem' := fun x => by
        simp only [Set.mem_setOf_eq]
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · right
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ h }


