-- Prove2me | solution 1 for Autoconvolutions.integral_cell_mul_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:38.809811+00:00
-- url     : https://prove2.me/submissions/246f2620-1ff5-4b61-b411-018a10bc3a0a

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Definitions.Def_Autoconvolutions_Interpolation
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
theorem _root_.solution (a b v w x : ℝ) :
    (∫ t, cell a v t * cell b w (x-t)) = v*w*tent (x-a-b) := by
  rw [integral_congr_ae (cellProduct_ae a b v w x), integral_indicator measurableSet_Icc,
    setIntegral_const, Real.volume_real_Icc, smul_eq_mul]
  have hlength : max (min (a+1) (x-b) - max a (x-b-1)) 0 = tent (x-a-b) := by
    simp only [tent, max_def, min_def]
    split_ifs <;> linarith
  rw [hlength]
  ring
end Autoconvolutions
