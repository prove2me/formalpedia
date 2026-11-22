-- Prove2me | solution 1 for Autoconvolutions.auto_step_tents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:24.9758+00:00
-- url     : https://prove2.me/submissions/b51935a3-f3c3-4b6a-9159-82e86315ac4c

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Definitions.Def_Autoconvolutions_Interpolation
public import Theorems.Thm_Autoconvolutions_integral_cell_mul_cell
section
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace Autoconvolutions
private theorem cellProduct_ae (a b v w x : ℝ) :
    (fun t => cell a v t * cell b w (x-t)) =ᵐ[volume]
      (Icc (max a (x-b-1)) (min (a+1) (x-b))).indicator (fun _ => v*w) := by
  filter_upwards [volume.ae_ne (a+1), volume.ae_ne (x-b-1)] with t ht₁ ht₂
  have hiff : t ∈ Icc (max a (x-b-1)) (min (a+1) (x-b)) ↔
      t ∈ Ico a (a+1) ∧ x-t ∈ Ico b (b+1) := by
    simp only [mem_Icc, max_le_iff, le_min_iff, mem_Ico]
    constructor
    · rintro ⟨⟨h₁,h₂⟩, h₃,h₄⟩
      exact ⟨⟨h₁, lt_of_le_of_ne h₃ ht₁⟩, by linarith, by
        have := lt_of_le_of_ne h₂ (Ne.symm ht₂)
        linarith⟩
    · rintro ⟨⟨h₁,h₂⟩, h₃,h₄⟩
      exact ⟨⟨h₁, by linarith⟩, h₂.le, by linarith⟩
  classical
  by_cases ha : t ∈ Ico a (a+1) <;> by_cases hb : x-t ∈ Ico b (b+1) <;>
    simp [cell, Set.indicator, ha, hb, hiff]
private theorem integrable_cellProduct (a b v w x : ℝ) :
    Integrable (fun t => cell a v t * cell b w (x-t)) := by
  apply Integrable.congr _ (cellProduct_ae a b v w x).symm
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (by simp)
end Autoconvolutions
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (x : ℝ) :
    auto (step d p) x = ∑ i, ∑ j, p i*p j*tent (x-i.val-j.val) := by
  classical
  have hs (t : ℝ) : step d p t = ∑ i, cell i.val (p i) t := by
    rfl
  simp only [auto, hs, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_cellProduct i.val j.val (p i) (p j) x))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_cellProduct i.val j.val (p i) (p j) x)]
  exact Finset.sum_congr rfl (fun j _ => integral_cell_mul_cell _ _ _ _ _)
end Autoconvolutions
