-- Prove2me | Definitions.Def_Sensitivity213981Formal_Packed5591Rotation
-- name    : Sensitivity213981Formal_Packed5591Rotation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:11:49.907197+00:00
-- url     : https://prove2.me/theorems/6c57da2f-335d-4f6c-b470-a8f7fd023f0c
-- title:
--   Packed5591 Rotation — sensitivity certificate definitions
-- statement:
--   The definitions for Packed5591 Rotation in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Packed.intersection_mask`, `Sensitivity5591Packed.out_bit`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Packed5591Rotation.lean, lines 1–46.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Packed5591Data
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section
/- Semantics of the sparse-word cyclic shifts. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Sensitivity5591Packed
open ThreeBoundPackedBits

theorem out_bit(v y:ℕ)(hv:v< 5591)(hy:y< 5591):
    (out v).testBit (16*y)=base.testBit (16*((y+5591-v)%5591)) := by
  unfold out
  rw [Nat.testBit_or,Nat.testBit_mod_two_pow,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  have hy':16*y< 16*5591:=by omega
  simp only [hy',decide_true,Bool.true_and]
  by_cases h:v≤ y
  · have hvy:16*v≤ 16*y:=by omega
    have hm:(y+5591-v)%5591=y-v:=by omega
    have hd:16*y-16*v=16*(y-v):=by omega
    have hi:16*5591≤ 16*(5591-v)+16*y:=by omega
    have hb:base.testBit (16*(5591-v)+16*y)=false:=
      Nat.testBit_lt_two_pow (base_lt.trans_le (Nat.pow_le_pow_right (by decide) hi))
    simp only [hvy,decide_true,Bool.true_and,hm,hd,hb,Bool.or_false]
  · have hvy:¬16*v≤ 16*y:=by omega
    have hi:16*(5591-v)+16*y=16*((y+5591-v)%5591):=by omega
    simp only [hvy,decide_false,Bool.false_and,Bool.false_or,hi]

theorem intersection_mask(v:ℕ):intersection v &&& mask 5591=intersection v := by
  rw [lanes_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  have hb:=congrArg (fun z:ℕ=>z.testBit i) base_mask
  simp only [Nat.testBit_and] at hb
  unfold intersection
  simp only [Nat.testBit_and]
  calc
    _=(((base.testBit i && lanes.testBit i) && (out 1).testBit i) && (out v).testBit i) := by ac_rfl
    _=_ := by rw [hb]



end Sensitivity5591Packed



end
end Sensitivity213981Formal


