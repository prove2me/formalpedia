-- Prove2me | Definitions.Def_Csg_UntilOp
-- name    : Csg_UntilOp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:49:41.561427+00:00
-- url     : https://prove2.me/theorems/85f283a9-3ea6-4a2a-adbb-eed127fb9469
-- title:
--   Until Op
-- statement:
--   Definitions and structural lemmas for Until Op, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/UntilOp.lean

import Definitions.Def_Csg_CsgMonotone
import Definitions.Def_Csg_ReachOp
import Theorems.Thm_Csg_CSG_stageValue_le_one
import Theorems.Thm_Csg_CSG_stageValue_mono
import Theorems.Thm_Csg_CSG_stageValue_nonneg

set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def untilOpFun (safe goal : S → Prop) [DecidablePred safe] [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) : Set.Icc (0 : ℝ) 1 :=
  if goal s then ⟨1, by norm_num, by norm_num⟩
  else if safe s then ⟨C.stageValue s (fun s' => (v s' : ℝ)),
    C.stageValue_nonneg hr (fun s' => (v s').2.1), C.stageValue_le_one hr (fun s' => (v s').2.2)⟩
  else ⟨0, by norm_num, by norm_num⟩
theorem untilOpFun_mono (safe goal : S → Prop) [DecidablePred safe] [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    Monotone (C.untilOpFun safe goal hr) := by
  intro v w hvw s
  by_cases hg : goal s
  · have heq : C.untilOpFun safe goal hr v s = C.untilOpFun safe goal hr w s := by
      simp only [untilOpFun, if_pos hg]
    exact heq.le
  · by_cases hs : safe s
    · simp only [untilOpFun, if_neg hg, if_pos hs]
      exact C.stageValue_mono fun s' => hvw s'
    · have heq : C.untilOpFun safe goal hr v s = C.untilOpFun safe goal hr w s := by
        simp only [untilOpFun, if_neg hg, if_neg hs]
      exact heq.le
noncomputable def untilOp (safe goal : S → Prop) [DecidablePred safe] [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.untilOpFun safe goal hr
  monotone' := C.untilOpFun_mono safe goal hr
end CSG
end Csg


