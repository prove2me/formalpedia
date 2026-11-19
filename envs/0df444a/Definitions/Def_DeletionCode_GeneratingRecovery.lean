-- Prove2me | Definitions.Def_DeletionCode_GeneratingRecovery
-- name    : DeletionCode_GeneratingRecovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:15:17.217504+00:00
-- url     : https://prove2.me/theorems/2e84ab56-3ca0-4264-957d-4c0e824e285b
-- title:
--   Generating Recovery
-- statement:
--   Definitions and structural lemmas for Generating Recovery, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingRecovery.lean

import Definitions.Def_DeletionCode_GeneratingModel
import Definitions.Def_DeletionCode_ConcreteRecovery
import Definitions.Def_DeletionCode_SupportComponents
import Theorems.Thm_DeletionCode_PathMemory_pathInitialAgreement

set_option autoImplicit true
namespace DeletionCode.GeneratingRecovery
open Windows HeaderRecovery GeneratingModel ConcreteDecoder
variable {B : Type*} {k : ℕ}
theorem initial_vertices_agree (E : EditedFamily B k) (b : B) :
    SupportComponents.vertex E.family (windowLength k) b false 0 =
      SupportComponents.vertex E.family (windowLength k) b true 0 := by
  apply (SupportComponents.vertex_eq_iff_agree E.family (windowLength k)
    b b false true 0 0).mpr
  exact PathMemory.pathInitialAgreement k (E.header b) (E.long b)
noncomputable def componentGraphEquiv (E : EditedFamily B k) :
    GeneratingModel.Components E ≃ SupportComponents.GraphComponents E.family (windowLength k) :=
  SupportComponents.componentEquiv E.family (windowLength k)
    (by unfold windowLength; omega) (initial_vertices_agree E)
noncomputable instance componentsFintype [Fintype B] (E : EditedFamily B k) :
    Fintype (GeneratingModel.Components E) := Fintype.ofFinite _
noncomputable instance graphComponentsFintype [Fintype B] (E : EditedFamily B k) :
    Fintype (SupportComponents.GraphComponents E.family (windowLength k)) :=
  Fintype.ofEquiv (GeneratingModel.Components E) (componentGraphEquiv E)
noncomputable def rootEquiv (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    GeneratingModel.Components E ≃ {b // (model E x n hx hg).schedule.root b} where
  toFun C := ⟨selectedRoot E x n hx hg C, C, rfl⟩
  invFun b := Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k)) b.val
  left_inv C := (selectedRoot_spec E x n hx hg C).1
  right_inv b := by
    apply Subtype.ext
    obtain ⟨C, hC⟩ := b.property
    change selectedRoot E x n hx hg
      (Quotient.mk (GeneratingModel.componentSetoid E.family (windowLength k)) b.val) = b.val
    rw [← hC, (selectedRoot_spec E x n hx hg C).1]
end DeletionCode.GeneratingRecovery


