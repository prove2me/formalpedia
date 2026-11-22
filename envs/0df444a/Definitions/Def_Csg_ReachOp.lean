-- Prove2me | Definitions.Def_Csg_ReachOp
-- name    : Csg_ReachOp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:46:41.850848+00:00
-- url     : https://prove2.me/theorems/5d680090-cd36-4ed8-97cf-609e8b120320
-- title:
--   Reach Op
-- statement:
--   Definitions and structural lemmas for Reach Op, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachOp.lean

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
noncomputable def reachOpFun (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) : Set.Icc (0 : ℝ) 1 :=
  if goal s then ⟨1, by norm_num, by norm_num⟩
  else ⟨C.stageValue s (fun s' => (v s' : ℝ)),
    C.stageValue_nonneg hr (fun s' => (v s').2.1), C.stageValue_le_one hr (fun s' => (v s').2.2)⟩
theorem reachOpFun_mono (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    Monotone (C.reachOpFun goal hr) := by
  intro v w hvw s
  by_cases h : goal s
  · have heq : C.reachOpFun goal hr v s = C.reachOpFun goal hr w s := by
      simp only [reachOpFun, if_pos h]
    exact heq.le
  · simp only [reachOpFun, if_neg h]
    exact C.stageValue_mono fun s' => hvw s'
noncomputable def reachOp (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.reachOpFun goal hr
  monotone' := C.reachOpFun_mono goal hr
end CSG
end Csg


