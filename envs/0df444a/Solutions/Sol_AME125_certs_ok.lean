-- Prove2me | solution 1 for AME125.certs_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:19:19.412797+00:00
-- url     : https://prove2.me/submissions/7d6b4d4d-4adb-47d3-a04f-97dc59a108f2

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
public import Theorems.Thm_AME125_certs0_ok
public import Theorems.Thm_AME125_certs1_ok
public import Theorems.Thm_AME125_certs2_ok
public import Theorems.Thm_AME125_certs3_ok
public import Theorems.Thm_AME125_certs4_ok
public import Theorems.Thm_AME125_certs5_ok
public import Theorems.Thm_AME125_certs6_ok
public import Theorems.Thm_AME125_certs7_ok
public import Theorems.Thm_AME125_certs8_ok
public import Theorems.Thm_AME125_certs9_ok
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
open scoped Matrix
namespace AME125
theorem _root_.solution : certs.all certOK = true := by
  simp only [certs, List.all_append, certs0_ok, certs1_ok, certs2_ok, certs3_ok, certs4_ok,
    certs5_ok, certs6_ok, certs7_ok, certs8_ok, certs9_ok, Bool.and_self]
end AME125
