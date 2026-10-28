-- Prove2me | Definitions.Def_Sensitivity213981Formal_PackedBitCard
-- name    : Sensitivity213981Formal_PackedBitCard
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:07:32.53397+00:00
-- url     : https://prove2.me/theorems/f6489d7c-e6ea-4873-82d0-d47a3b9474dd
-- title:
--   Packed Bit Card — sensitivity certificate definitions
-- statement:
--   The definitions for Packed Bit Card in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundPackedBits.filter_card_bits`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; PackedBitCard.lean, lines 1–50.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_PackedBits
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section

set_option autoImplicit false
namespace ThreeBoundPackedBits
open scoped Classical BigOperators
noncomputable section






theorem filter_card_bits {n:ℕ}{V:Type*}[Fintype V]
    (e:Fin n≃V)(P:V→Prop)[DecidablePred P](x:ℕ)
    (h:∀y:Fin n,x.testBit (16*y.val)=decide (P (e y))):
    (Finset.univ.filter P).card=bitSum n x := by
  calc
    _=∑y:V,if P y then 1 else 0 := by simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    _=∑y:Fin n,(x.testBit (16*y.val)).toNat := by
      symm
      apply Fintype.sum_equiv e
      intro y
      rw [h y]
      by_cases hp:P (e y) <;> simp [hp]
    _=bitSum n x := Fin.sum_univ_eq_sum_range (fun i=> (x.testBit (16*i)).toNat) n

end
end ThreeBoundPackedBits


end
end Sensitivity213981Formal


