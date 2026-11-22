-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaM
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:31.964367+00:00
-- url     : https://prove2.me/theorems/588f40fe-4cda-4340-a49d-c2834994183a
-- title:
--   First Lemma M
-- statement:
--   Definitions and structural lemmas for First Lemma M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaM.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Bl.FirstLemmaM
noncomputable def goal1 (K : Type*) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
end Bl.FirstLemmaM


