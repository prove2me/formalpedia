-- Prove2me | Definitions.Def_Csg_CoBuchiOp
-- name    : Csg_CoBuchiOp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:53:43.951748+00:00
-- url     : https://prove2.me/theorems/12fcb346-8b53-4fb2-ae77-66daf8515d9e
-- title:
--   Co Buchi Op
-- statement:
--   Definitions and structural lemmas for Co Buchi Op, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoBuchiOp.lean

import Definitions.Def_Csg_BuchiOp
import Theorems.Thm_Csg_CSG_stageValue_le_one
import Theorems.Thm_Csg_CSG_stageValue_mono
import Theorems.Thm_Csg_CSG_stageValue_nonneg
import Theorems.Thm_OrderHom_gfp_mono_of_le

set_option autoImplicit true
namespace Csg
namespace CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
noncomputable def coBuchiInnerOpFun (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x y : S → Set.Icc (0 : ℝ) 1) (s : S) :
    Set.Icc (0 : ℝ) 1 :=
  if U s then
    ⟨C.stageValue s (fun s' => (y s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (y s').2.1), C.stageValue_le_one hr (fun s' => (y s').2.2)⟩
  else
    ⟨C.stageValue s (fun s' => (x s' : ℝ)),
      C.stageValue_nonneg hr (fun s' => (x s').2.1), C.stageValue_le_one hr (fun s' => (x s').2.2)⟩
theorem coBuchiInnerOpFun_mono (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x : S → Set.Icc (0 : ℝ) 1) :
    Monotone (C.coBuchiInnerOpFun U hr x) := by
  intro y1 y2 hy s
  by_cases h : U s
  · simp only [coBuchiInnerOpFun, if_pos h]
    exact C.stageValue_mono fun s' => hy s'
  · have heq : C.coBuchiInnerOpFun U hr x y1 s = C.coBuchiInnerOpFun U hr x y2 s := by
      simp only [coBuchiInnerOpFun, if_neg h]
    exact heq.le
noncomputable def coBuchiInnerOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x : S → Set.Icc (0 : ℝ) 1) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun := C.coBuchiInnerOpFun U hr x
  monotone' := C.coBuchiInnerOpFun_mono U hr x
theorem coBuchiInnerOpFun_mono_x (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {x1 x2 : S → Set.Icc (0 : ℝ) 1} (hx : x1 ≤ x2)
    (y : S → Set.Icc (0 : ℝ) 1) :
    C.coBuchiInnerOpFun U hr x1 y ≤ C.coBuchiInnerOpFun U hr x2 y := by
  intro s
  by_cases h : U s
  · have heq : C.coBuchiInnerOpFun U hr x1 y s = C.coBuchiInnerOpFun U hr x2 y s := by
      simp only [coBuchiInnerOpFun, if_pos h]
    exact heq.le
  · simp only [coBuchiInnerOpFun, if_neg h]
    exact C.stageValue_mono fun s' => hx s'
noncomputable def coBuchiOp (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (S → Set.Icc (0 : ℝ) 1) →o (S → Set.Icc (0 : ℝ) 1) where
  toFun x := (C.coBuchiInnerOp U hr x).gfp
  monotone' := fun _x1 _x2 hx =>
    OrderHom.gfp_mono_of_le (fun y => C.coBuchiInnerOpFun_mono_x U hr hx y)
end CSG
end Csg


