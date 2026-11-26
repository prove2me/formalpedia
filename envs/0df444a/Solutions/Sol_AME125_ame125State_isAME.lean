-- Prove2me | solution 1 for AME125.ame125State_isAME
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:22:29.64508+00:00
-- url     : https://prove2.me/submissions/ef1c175d-b58a-46f7-8d33-02de2e301de1

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_FormalTarget
public import Theorems.Thm_AME125_cutInj_all
public import Theorems.Thm_AME125_graphState_isAME
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.diagonalState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply



set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
namespace AME125
theorem _root_.solution : IsAME ame125State :=
  graphState_isAME ⟨6, rfl⟩ U fun A hA ↦ cutInj_all A (by simpa using hA)
end AME125
