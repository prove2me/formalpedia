-- Prove2me | solution 1 for Autoconvolutions.ratio_ge_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:31.825143+00:00
-- url     : https://prove2.me/submissions/17265e0d-c961-41ea-ab70-6559fe9fd475

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_auto_step_L1
public import Theorems.Thm_Autoconvolutions_auto_step_Linf_le
public import Theorems.Thm_Autoconvolutions_auto_step_Linf_pos
public import Theorems.Thm_Autoconvolutions_blocks_energy_le
public import Theorems.Thm_Autoconvolutions_sum_pos_of_positive_cell


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution {ι : Type*} (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hne : ∃ i, 0 < p i) (M : ℝ) (hM : 0 < M) (hb : ∀ k : ℤ, convCoeff d p k ≤ M)
    (D : ℕ) (T : Finset ι) (code width : ι → ℕ) (height : ι → ℝ)
    (hinj : Set.InjOn code (↑T)) (hw : ∀ i ∈ T, width i ≤ D)
    (heq : ∀ i ∈ T, ∀ h ≤ width i, convCoeff d p ((D*code i+h : ℕ) : ℤ) = height i) :
    (∑ i ∈ T, (width i : ℝ)*(height i)^2) / ((∑ j, p j)^2*M) ≤ ratio (step d p) := by
  unfold ratio
  rw [auto_step_L1 d p hp]
  have hmass := pow_pos (sum_pos_of_positive_cell hp hne) 2
  exact div_le_div₀ (sq_nonneg _) (blocks_energy_le d p D T code width height hinj hw heq)
    (mul_pos hmass (auto_step_Linf_pos hp hne))
    (mul_le_mul_of_nonneg_left (auto_step_Linf_le d p hp M hM.le hb) hmass.le)
end Autoconvolutions
