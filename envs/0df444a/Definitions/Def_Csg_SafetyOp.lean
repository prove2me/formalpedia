-- Prove2me | Definitions.Def_Csg_SafetyOp
-- name    : Csg_SafetyOp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:46:48.987869+00:00
-- url     : https://prove2.me/theorems/803c563c-25ba-4265-8149-29054f8022ae
-- title:
--   Safety Op
-- statement:
--   Definitions and structural lemmas for Safety Op, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SafetyOp.lean

import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_stageValue_le_one
import Theorems.Thm_Csg_CSG_stageValue_mono
import Theorems.Thm_Csg_CSG_stageValue_nonneg

set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def safetyOpFun (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) : Set.Icc (0 : ℝ) 1 :=
  if safe s then
    ⟨C.stageValue s (fun s' => (v s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (v s').2.1), C.stageValue_le_one hr (fun s' => (v s').2.2)⟩
  else ⟨0, by norm_num, by norm_num⟩
theorem safetyOpFun_mono (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    Monotone (C.safetyOpFun safe hr) := by
  intro v w hvw s
  by_cases h : safe s
  · simp only [safetyOpFun, if_pos h]
    exact C.stageValue_mono fun s' => hvw s'
  · have heq : C.safetyOpFun safe hr v s = C.safetyOpFun safe hr w s := by
      simp only [safetyOpFun, if_neg h]
    exact heq.le
noncomputable def safetyOp (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.safetyOpFun safe hr
  monotone' := C.safetyOpFun_mono safe hr
end CSG
end Csg


