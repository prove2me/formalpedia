-- Prove2me | Definitions.Def_Csg_BuchiOp
-- name    : Csg_BuchiOp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:46:49.466115+00:00
-- url     : https://prove2.me/theorems/7608f1b4-94bd-4664-b5aa-07ea9c5bc1ba
-- title:
--   Buchi Op
-- statement:
--   Definitions and structural lemmas for Buchi Op, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BuchiOp.lean

import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_stageValue_le_one
import Theorems.Thm_Csg_CSG_stageValue_mono
import Theorems.Thm_Csg_CSG_stageValue_nonneg

set_option autoImplicit true
theorem OrderHom.lfp_mono_of_le {α : Type*} [CompleteLattice α] {f g : α →o α}
    (h : ∀ a, f a ≤ g a) : f.lfp ≤ g.lfp :=
  f.lfp_le ((h g.lfp).trans (le_of_eq g.map_lfp))
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def buchiInnerOpFun (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (y x : S → Set.Icc (0 : ℝ) 1) (s : S) :
    Set.Icc (0 : ℝ) 1 :=
  if U s then
    ⟨C.stageValue s (fun s' => (y s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (y s').2.1), C.stageValue_le_one hr (fun s' => (y s').2.2)⟩
  else
    ⟨C.stageValue s (fun s' => (x s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (x s').2.1), C.stageValue_le_one hr (fun s' => (x s').2.2)⟩
theorem buchiInnerOpFun_mono (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (y : S → Set.Icc (0 : ℝ) 1) :
    Monotone (C.buchiInnerOpFun U hr y) := by
  intro x1 x2 hx s
  by_cases h : U s
  · have heq : C.buchiInnerOpFun U hr y x1 s = C.buchiInnerOpFun U hr y x2 s := by
      simp only [buchiInnerOpFun, if_pos h]
    exact heq.le
  · simp only [buchiInnerOpFun, if_neg h]
    exact C.stageValue_mono fun s' => hx s'
noncomputable def buchiInnerOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (y : S → Set.Icc (0 : ℝ) 1) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.buchiInnerOpFun U hr y
  monotone' := C.buchiInnerOpFun_mono U hr y
theorem buchiInnerOpFun_mono_y (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {y1 y2 : S → Set.Icc (0 : ℝ) 1} (hy : y1 ≤ y2)
    (x : S → Set.Icc (0 : ℝ) 1) :
    C.buchiInnerOpFun U hr y1 x ≤ C.buchiInnerOpFun U hr y2 x := by
  intro s
  by_cases h : U s
  · simp only [buchiInnerOpFun, if_pos h]
    exact C.stageValue_mono fun s' => hy s'
  · have heq : C.buchiInnerOpFun U hr y1 x s = C.buchiInnerOpFun U hr y2 x s := by
      simp only [buchiInnerOpFun, if_neg h]
    exact heq.le
noncomputable def buchiOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun y := (C.buchiInnerOp U hr y).lfp
  monotone' := fun _y1 _y2 hy =>
    OrderHom.lfp_mono_of_le (fun x => C.buchiInnerOpFun_mono_y U hr hy x)
end CSG
end Csg


