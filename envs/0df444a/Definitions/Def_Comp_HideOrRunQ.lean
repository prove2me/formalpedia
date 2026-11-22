-- Prove2me | Definitions.Def_Comp_HideOrRunQ
-- name    : Comp_HideOrRunQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:47:21.423799+00:00
-- url     : https://prove2.me/theorems/6b4f5244-da58-479a-a139-2d9134ca7233
-- title:
--   Hide Or Run Q
-- statement:
--   Definitions and structural lemmas for Hide Or Run Q, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_mem_aF
import Theorems.Thm_Comp_CsgQ_mem_apre1F
import Theorems.Thm_Comp_CsgQ_mem_bF
import Theorems.Thm_Comp_CsgQ_mem_gStepF
import Theorems.Thm_Comp_CsgQ_mem_lpre1F
import Theorems.Thm_Comp_CsgQ_mem_pre1F
import Theorems.Thm_Comp_CsgQ_mem_supportF
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
import Theorems.Thm_Comp_ModelData_mem_enabled1
import Theorems.Thm_Comp_ModelData_mem_enabled2
import Theorems.Thm_Comp_ModelData_padFin1_mem
import Theorems.Thm_Comp_ModelData_padFin2_mem
import Theorems.Thm_Comp_ModelData_toCsgQ_K
attribute [local simp] Comp.CsgQ.castIcc_coe
attribute [local simp] Comp.CsgQ.coe_supportF
attribute [local simp] Comp.CsgQ.mem_aF
attribute [local simp] Comp.CsgQ.mem_apre1F
attribute [local simp] Comp.CsgQ.mem_bF
attribute [local simp] Comp.CsgQ.mem_gStepF
attribute [local simp] Comp.CsgQ.mem_lpre1F
attribute [local simp] Comp.CsgQ.mem_pre1F
attribute [local simp] Comp.CsgQ.mem_supportF
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A
attribute [local simp] Comp.ModelData.mem_enabled1
attribute [local simp] Comp.ModelData.mem_enabled2
attribute [local simp] Comp.ModelData.padFin1_mem
attribute [local simp] Comp.ModelData.padFin2_mem
attribute [local simp] Comp.ModelData.toCsgQ_K


set_option autoImplicit true
set_option linter.hashCommand false
namespace Comp
open Csg
namespace HideOrRun
inductive HR
  | live
  | goal
  | dead
  deriving DecidableEq, Inhabited, Repr
instance : Fintype HR where
  elems := {HR.live, HR.goal, HR.dead}
  complete := by intro x; cases x <;> decide
def dirac (t : HR) : HR → ℚ := fun s' => if s' = t then 1 else 0
theorem dirac_nonneg (t s' : HR) : 0 ≤ dirac t s' := by
  unfold dirac
  split_ifs <;> norm_num
theorem sum_dirac (t : HR) : ∑ s' : HR, dirac t s' = 1 := by
  unfold dirac
  simp
def kernel : HR → Bool → Bool → (HR → ℚ)
  | .live, true, true => dirac .dead
  | .live, true, false => dirac .goal
  | .live, false, true => dirac .goal
  | .live, false, false => dirac .live
  | .goal, _, _ => dirac .goal
  | .dead, _, _ => dirac .dead
def game : CsgQ HR Bool Bool where
  K := kernel
  r := fun _ _ _ => 0
theorem kernel_dirac (s : HR) (a1 a2 : Bool) : ∃ t, game.K s a1 a2 = dirac t := by
  cases s <;> cases a1 <;> cases a2 <;> exact ⟨_, rfl⟩
theorem game_wf : game.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · obtain ⟨t, ht⟩ := kernel_dirac s a1 a2
    rw [ht]
    exact dirac_nonneg t s'
  · obtain ⟨t, ht⟩ := kernel_dirac s a1 a2
    rw [ht]
    exact sum_dirac t
def supp : HR → Bool → Bool → Finset HR
  | .live, true, true => {.dead}
  | .live, true, false => {.goal}
  | .live, false, true => {.goal}
  | .live, false, false => {.live}
  | .goal, _, _ => {.goal}
  | .dead, _, _ => {.dead}
def aC (v2 : Finset Bool) (y : Finset HR) (s : HR) : Finset Bool :=
  Finset.univ.filter fun a1 => ∀ a2, a2 ∈ v2 ∨ supp s a1 a2 ⊆ y
def bC (v1 : Finset Bool) (x : Finset HR) (s : HR) : Finset Bool :=
  Finset.univ.filter fun a2 => ∃ a1 ∈ v1, (supp s a1 a2 ∩ x).Nonempty
def lStepC (x y : Finset HR) (s : HR) (w : Finset Bool) : Finset Bool := aC (bC w x s) y s
def lwC (x y : Finset HR) (s : HR) : Finset Bool := (lStepC x y s)^[2] ∅
def lpre1C (w : HR → Finset Bool) (x : Finset HR) : Finset HR :=
  Finset.univ.filter fun s => bC (w s) x s = Finset.univ
def midStep (b y x : Finset HR) : Finset HR := lpre1C (fun s => lwC x y s) x ∪ b
def target : Finset HR := {HR.goal}
def winning : Finset HR := {HR.live, HR.goal}
def apre1C (x y : Finset HR) : Finset HR :=
  Finset.univ.filter fun s => bC (aC ∅ y s) x s = Finset.univ
def afStepC (b y x : Finset HR) : Finset HR := apre1C x y ∪ b
end HideOrRun
end Comp


