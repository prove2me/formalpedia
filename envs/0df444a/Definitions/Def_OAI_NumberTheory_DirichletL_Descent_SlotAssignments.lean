-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments
-- name    : OAI_NumberTheory_DirichletL_Descent_SlotAssignments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:09.348873+00:00
-- url     : https://prove2.me/theorems/cba95aca-9f4e-4550-ba25-52cfbec08ce9
-- title:
--   Slot Assignments
-- statement:
--   Definitions and structural lemmas for Slot Assignments, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SlotAssignments.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
set_option autoImplicit false
namespace OAI
namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
def slotAssignmentWeight (I : Finset σ) (a : σ → ι → ℂ)
    (q : ∀ i ∈ I, ι) : ℂ := ∏ i ∈ I.attach, a i.val (q i.val i.property)
def indexedSlotAssignment (I : Finset σ) (q : ∀ i ∈ I, ι) : Fin I.card → ι :=
  fun j => q ((I.equivFin).symm j).val ((I.equivFin).symm j).property
end
end SevenEighths.InverseMoment
end OAI


