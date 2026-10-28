-- Prove2me | Definitions.Def_Sensitivity213981Formal_Packed5591Checks
-- name    : Sensitivity213981Formal_Packed5591Checks
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:16:28.617686+00:00
-- url     : https://prove2.me/theorems/160ec08a-51b4-4fc6-aee4-2863e9b3f2f7
-- title:
--   Packed5591 Checks — sensitivity certificate definitions
-- statement:
--   The definitions for Packed5591 Checks in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Packed.checked_blocks`, `Sensitivity5591Packed.checked_all`, `Sensitivity5591Packed.euler_correct`, `Sensitivity5591Packed.intersection_bound`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Packed5591Checks.lean, lines 1–114.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Packed5591Check00
import Definitions.Def_Sensitivity213981Formal_Packed5591Check01
import Definitions.Def_Sensitivity213981Formal_Packed5591Check02
import Definitions.Def_Sensitivity213981Formal_Packed5591Check03
import Definitions.Def_Sensitivity213981Formal_Packed5591Check04
import Definitions.Def_Sensitivity213981Formal_Packed5591Check05
import Definitions.Def_Sensitivity213981Formal_Packed5591Check06
import Definitions.Def_Sensitivity213981Formal_Packed5591Check07
import Definitions.Def_Sensitivity213981Formal_Packed5591Check08
import Definitions.Def_Sensitivity213981Formal_Packed5591Check09
import Definitions.Def_Sensitivity213981Formal_Packed5591Check10
import Definitions.Def_Sensitivity213981Formal_Packed5591Check11
import Definitions.Def_Sensitivity213981Formal_Packed5591Check12
import Definitions.Def_Sensitivity213981Formal_Packed5591Check13
import Definitions.Def_Sensitivity213981Formal_Packed5591Check14
import Definitions.Def_Sensitivity213981Formal_Packed5591Check15
import Definitions.Def_Sensitivity213981Formal_Packed5591Check16
import Definitions.Def_Sensitivity213981Formal_Packed5591Check17
import Definitions.Def_Sensitivity213981Formal_Packed5591Check18
import Definitions.Def_Sensitivity213981Formal_Packed5591Check19
import Definitions.Def_Sensitivity213981Formal_Packed5591Check20
import Definitions.Def_Sensitivity213981Formal_Packed5591Check21
import Definitions.Def_Sensitivity213981Formal_Packed5591Check22
import Definitions.Def_Sensitivity213981Formal_Packed5591Check23
import Definitions.Def_Sensitivity213981Formal_Packed5591Check24
import Definitions.Def_Sensitivity213981Formal_Packed5591Check25
import Definitions.Def_Sensitivity213981Formal_Packed5591Check26
import Definitions.Def_Sensitivity213981Formal_Packed5591Check27
import Definitions.Def_Sensitivity213981Formal_Packed5591Check28
import Definitions.Def_Sensitivity213981Formal_Packed5591Check29
import Definitions.Def_Sensitivity213981Formal_Packed5591Check30
import Definitions.Def_Sensitivity213981Formal_Packed5591Check31
import Definitions.Def_Sensitivity213981Formal_Packed5591Check32
import Definitions.Def_Sensitivity213981Formal_Packed5591Check33
import Definitions.Def_Sensitivity213981Formal_Packed5591Check34
import Definitions.Def_Sensitivity213981Formal_Packed5591Check35
import Definitions.Def_Sensitivity213981Formal_Packed5591Check36
import Definitions.Def_Sensitivity213981Formal_Packed5591Check37
import Definitions.Def_Sensitivity213981Formal_Packed5591Check38
import Definitions.Def_Sensitivity213981Formal_Packed5591Check39
import Definitions.Def_Sensitivity213981Formal_Packed5591Check40
import Definitions.Def_Sensitivity213981Formal_Packed5591Check41
import Definitions.Def_Sensitivity213981Formal_Packed5591Check42
import Definitions.Def_Sensitivity213981Formal_Packed5591Check43
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Sensitivity5591Packed

theorem checked_blocks:∀b:Fin 44,checkRange (128*b.val) (min 128 (5591-128*b.val))=true:=by
  intro b
  fin_cases b
  · exact checked_0
  · exact checked_1
  · exact checked_2
  · exact checked_3
  · exact checked_4
  · exact checked_5
  · exact checked_6
  · exact checked_7
  · exact checked_8
  · exact checked_9
  · exact checked_10
  · exact checked_11
  · exact checked_12
  · exact checked_13
  · exact checked_14
  · exact checked_15
  · exact checked_16
  · exact checked_17
  · exact checked_18
  · exact checked_19
  · exact checked_20
  · exact checked_21
  · exact checked_22
  · exact checked_23
  · exact checked_24
  · exact checked_25
  · exact checked_26
  · exact checked_27
  · exact checked_28
  · exact checked_29
  · exact checked_30
  · exact checked_31
  · exact checked_32
  · exact checked_33
  · exact checked_34
  · exact checked_35
  · exact checked_36
  · exact checked_37
  · exact checked_38
  · exact checked_39
  · exact checked_40
  · exact checked_41
  · exact checked_42
  · exact checked_43

theorem checked_all(v:Fin 5591):checkAt v.val=true:=by
  have hb:v.val/128< 44:=by omega
  have h:=checked_blocks ⟨v.val/128,hb⟩
  change checkRange (128*(v.val/128)) (min 128 (5591-128*(v.val/128)))=true at h
  apply checkRange_sound _ _ h v.val <;> omega

theorem euler_correct(v:Fin 5591):decide (euler v.val=1)=base.testBit (16*v.val):=by
  have h:=(Bool.and_eq_true_iff.mp (checked_all v)).1
  exact beq_iff_eq.mp h

theorem intersection_bound(v:Fin 5591)(hv:2≤ v.val):intersection v.val%65535≤ 800:=by
  have h:=(Bool.and_eq_true_iff.mp (checked_all v)).2
  simpa only [checkAt,if_neg (by omega : ¬ v.val< 2),decide_eq_true_eq] using h

end Sensitivity5591Packed



end
end Sensitivity213981Formal


