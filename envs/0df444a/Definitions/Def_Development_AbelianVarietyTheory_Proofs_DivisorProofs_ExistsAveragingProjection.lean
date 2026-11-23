-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:26.535294+00:00
-- url     : https://prove2.me/theorems/165c5480-88b8-42c1-ada1-b78db6e49732
-- title:
--   Exists Averaging Projection
-- statement:
--   Definitions and structural lemmas for Exists Averaging Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
def stab (x : V) : Subgroup L where
  carrier := {l | π (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
noncomputable def cv (H : Subgroup L) (x : V) (q : L ⧸ H) : V := π ((q.out : L) : G) x
noncomputable def avgH (H : Subgroup L) (x : V) : V :=
  ((H.index : ℂ))⁻¹ • ∑ᶠ q : L ⧸ H, cv π L H x q
noncomputable def avg (x : V) : V := avgH π L (stab π L x) x
end GlobalTheory.OrbitAvg


