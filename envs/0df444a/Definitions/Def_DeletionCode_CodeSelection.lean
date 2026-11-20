-- Prove2me | Definitions.Def_DeletionCode_CodeSelection
-- name    : DeletionCode_CodeSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:37:53.127683+00:00
-- url     : https://prove2.me/theorems/52d60c8b-f90b-453d-b622-88e9f7263e45
-- title:
--   Code Selection
-- statement:
--   Definitions and structural lemmas for Code Selection, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeSelection.lean

import Definitions.Def_DeletionCode_BipartiteSelection
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Theorems.Thm_DeletionCode_CircleHash_label_range

set_option autoImplicit true
namespace DeletionCode.CodeSelection
open HeaderRecovery ConflictGraphWitness BipartiteSelection
variable {n k : ℕ}
noncomputable instance vertexFintype {A : Type*} (t k : ℕ) (label : Bits n → A) :
    Fintype (FiniteConflictGraph.Vertex t k label) := Fintype.ofFinite _
def Corrects (t : ℕ) (C : Finset (Bits n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬ FiniteConflictGraph.Confusable t x y
noncomputable def wordLabelFin (Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (x : Bits n) : Fin Q :=
  ⟨(wordLabel Q H x).toNat, by
    have hr := CircleHash.label_range Q hQ (H (spectrum k x))
    change 0 ≤ wordLabel Q H x ∧ wordLabel Q H x < (Q : ℤ) at hr
    omega⟩
end DeletionCode.CodeSelection


