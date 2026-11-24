-- Prove2me | solution 1 for AddUN.Coding.mu_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:30:00.888958+00:00
-- url     : https://prove2.me/submissions/884b4c3e-c43f-472f-bda9-1d7c5b6cb103

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n : ℕ) : mu (n + 1) = 4 * mu n := by
  simp only [mu, pow_succ]
  ring
end AddUN.Coding
