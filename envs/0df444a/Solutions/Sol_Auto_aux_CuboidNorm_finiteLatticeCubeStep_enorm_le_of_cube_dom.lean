-- Prove2me | solution 1 for Auto.aux_CuboidNorm.finiteLatticeCubeStep_enorm_le_of_cube_dom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:09.326407+00:00
-- url     : https://prove2.me/submissions/7b196ccd-6146-4a84-940c-adb0ac1f7979

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_apply_of_mem
public import Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_apply_eq_zero
public import Theorems.Thm_Auto_aux_CuboidNorm_latticeCuboid_pairwise_disjoint

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ}
    {ε c : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n))
    (a : ZVector n → ℝ) (G : RVector n → ℝ)
    (hdom : ∀ k, k ∈ A → ∀ x, x ∈ latticeCuboid ε k →
      ‖c * a k‖ₑ ≤ ‖G x‖ₑ) :
    ∀ x, ‖finiteLatticeCubeStep ε A (fun k ↦ c * a k) x‖ₑ ≤ ‖G x‖ₑ := by
  intro x
  by_cases hx : ∃ k ∈ A, x ∈ latticeCuboid ε k
  · obtain ⟨k, hk, hxk⟩ := hx
    have hstep : finiteLatticeCubeStep ε A (fun k ↦ c * a k) x = c * a k := by
      unfold finiteLatticeCubeStep
      exact finiteStep_apply_of_mem A (latticeCuboid ε) (fun k ↦ c * a k)
        (fun k hk l hl hkl ↦ latticeCuboid_pairwise_disjoint hε hkl) hk hxk
    rw [hstep]
    exact hdom k hk x hxk
  · have hstep : finiteLatticeCubeStep ε A (fun k ↦ c * a k) x = 0 := by
      unfold finiteLatticeCubeStep
      apply finiteStep_apply_eq_zero
      intro k hk hxk
      exact hx ⟨k, hk, hxk⟩
    rw [hstep, enorm_zero]
    exact bot_le
end Auto.aux_CuboidNorm
