-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:03.857801+00:00
-- url     : https://prove2.me/theorems/39df3e0d-06d2-47db-a940-8a52a6b842c4
-- title:
--   Imports Ter Ter
-- statement:
--   Definitions and structural lemmas for Imports Ter Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTerTer.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.PadicComplexValuationRing.intS (p : ℕ) [inst : Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  mul_mem' := fun {a b} ha hb =>
    (norm_mul_le a b).trans (mul_le_one₀ ha (norm_nonneg b) hb)
  neg_mem' := fun {a} ha => by
    simpa only [Set.mem_setOf_eq, norm_neg] using ha


