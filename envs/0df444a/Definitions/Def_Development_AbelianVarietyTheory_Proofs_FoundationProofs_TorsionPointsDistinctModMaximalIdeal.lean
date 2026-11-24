-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TorsionPointsDistinctModMaximalIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_TorsionPointsDistinctModMaximalIdeal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:27.077107+00:00
-- url     : https://prove2.me/theorems/6b51f921-3f90-4af8-84e7-67c5beea951a
-- title:
--   Torsion Points Distinct Mod Maximal Ideal
-- statement:
--   Definitions and structural lemmas for Torsion Points Distinct Mod Maximal Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TorsionPointsDistinctModMaximalIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine
namespace TorsionUnit
variable {K : Type} [NormedField K] [IsUltrametricDist K]
def unitBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha
end TorsionUnit
end GlobalTheory


