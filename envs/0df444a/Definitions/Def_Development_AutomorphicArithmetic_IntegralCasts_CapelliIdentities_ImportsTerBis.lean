-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:20.435537+00:00
-- url     : https://prove2.me/theorems/9973780d-0132-45cd-87c8-2b8a79c5d78b
-- title:
--   Imports Ter Bis
-- statement:
--   Definitions and structural lemmas for Imports Ter Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTerBis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rwa [norm_neg] }


