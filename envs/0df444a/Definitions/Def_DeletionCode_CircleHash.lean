-- Prove2me | Definitions.Def_DeletionCode_CircleHash
-- name    : DeletionCode_CircleHash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:03:02.777123+00:00
-- url     : https://prove2.me/theorems/e987cc9f-1cc8-4f1c-a061-c4176f948afa
-- title:
--   Circle Hash
-- statement:
--   Definitions and structural lemmas for Circle Hash, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
set_option autoImplicit true
namespace DeletionCode.CircleHash
open scoped BigOperators
noncomputable def representative (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 z).val
@[simp] theorem coe_representative (z : UnitAddCircle) :
    (representative z : UnitAddCircle) = z :=
  AddCircle.coe_equivIco
noncomputable def label (Q : ℕ) (z : UnitAddCircle) : ℤ :=
  ⌊(Q : ℝ) * representative z⌋
noncomputable def weightedHash {I : Type*} [Fintype I]
    (weights : I → UnitAddCircle) : (I → ℤ) →+ UnitAddCircle where
  toFun p := ∑ g, p g • weights g
  map_zero' := by simp
  map_add' p q := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]
noncomputable def realWeightedHash {I : Type*} [Fintype I]
    (weights : I → ℝ) : (I → ℤ) →+ UnitAddCircle :=
  weightedHash (fun g => (weights g : UnitAddCircle))
def surviving {V : Type*} [AddCommGroup V] (H : V →+ UnitAddCircle)
    (Q : ℕ) (K₀ : Set V) : Set V :=
  {w | w ∈ K₀ ∧ ‖H w‖ < 1 / (Q : ℝ)}
end DeletionCode.CircleHash


