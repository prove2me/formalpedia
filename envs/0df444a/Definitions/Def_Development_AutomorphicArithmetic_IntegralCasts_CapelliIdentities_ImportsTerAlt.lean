-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerAlt
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:53.163787+00:00
-- url     : https://prove2.me/theorems/7cd7ca4e-0af1-47c5-be81-968f1c07a2a7
-- title:
--   Imports Ter Alt
-- statement:
--   Definitions and structural lemmas for Imports Ter Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTerAlt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.PadicComplexIntegerSubring.intSub :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] := fun p _ =>
  { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
    mul_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      rw [norm_mul]
      exact mul_le_one₀ ha (norm_nonneg b) hb
    one_mem' := by
      simp only [Set.mem_setOf_eq, norm_one, le_refl]
    add_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
    zero_mem' := by
      simp only [Set.mem_setOf_eq, norm_zero, zero_le_one]
    neg_mem' := fun {a} ha => by
      simp only [Set.mem_setOf_eq] at ha ⊢
      rwa [norm_neg] }


