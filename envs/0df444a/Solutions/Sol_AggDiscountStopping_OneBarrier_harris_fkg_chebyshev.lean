-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.harris_fkg_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:02:56.589782+00:00
-- url     : https://prove2.me/submissions/66d94eab-49ee-4628-a5f1-238c9d695678

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : Set ℝ)
    (hS : μ Sᶜ = 0) (f h : ℝ → ℝ) (hf : AntitoneOn f S) (hh : MonotoneOn h S)
    (hfi : Integrable f μ) (hhi : Integrable h μ) (hfhi : Integrable (fun r => f r * h r) μ) :
    ∫ r, f r * h r ∂μ ≤ (∫ r, f r ∂μ) * (∫ r, h r ∂μ) := by
  set A := ∫ r, f r ∂μ
  set B := ∫ r, h r ∂μ
  set C := ∫ r, f r * h r ∂μ
  have haeS : ∀ᵐ r ∂μ, r ∈ S := by
    rw [ae_iff]
    exact hS
  -- pointwise sign of the symmetrized product
  have hsign : ∀ r s, r ∈ S → s ∈ S → (f r - f s) * (h r - h s) ≤ 0 := by
    intro r s hr hs
    rcases le_total r s with hrs | hsr
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hf hr hs hrs))
        (sub_nonpos.mpr (hh hr hs hrs))
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hf hs hr hsr))
        (sub_nonneg.mpr (hh hs hr hsr))
  -- the inner integral
  have hinner : ∀ s, ∫ r, (f r - f s) * (h r - h s) ∂μ = C - h s * A - f s * B + f s * h s := by
    intro s
    have hexp : (fun r => (f r - f s) * (h r - h s)) =
        fun r => ((f r * h r - h s * f r) - f s * h r) + f s * h s := by
      funext r; ring
    rw [hexp]
    have i1 : Integrable (fun r => h s * f r) μ := hfi.const_mul _
    have i2 : Integrable (fun r => f s * h r) μ := hhi.const_mul _
    have e1 : ∫ r, (f r * h r - h s * f r - f s * h r + f s * h s) ∂μ =
        ∫ r, (f r * h r - h s * f r - f s * h r) ∂μ + ∫ _r, f s * h s ∂μ :=
      integral_add ((hfhi.sub i1).sub i2) (integrable_const _)
    have e2 : ∫ r, (f r * h r - h s * f r - f s * h r) ∂μ =
        ∫ r, (f r * h r - h s * f r) ∂μ - ∫ r, f s * h r ∂μ :=
      integral_sub (hfhi.sub i1) i2
    have e3 : ∫ r, (f r * h r - h s * f r) ∂μ = ∫ r, f r * h r ∂μ - ∫ r, h s * f r ∂μ :=
      integral_sub hfhi i1
    rw [e1, e2, e3, integral_const_mul, integral_const_mul, integral_const]
    simp [A, B, C]
  have hinner_nonpos : ∀ᵐ s ∂μ, ∫ r, (f r - f s) * (h r - h s) ∂μ ≤ 0 := by
    filter_upwards [haeS] with s hs
    apply integral_nonpos_of_ae
    filter_upwards [haeS] with r hr
    exact hsign r s hr hs
  have hout : ∫ s, (C - h s * A - f s * B + f s * h s) ∂μ = 2 * (C - A * B) := by
    have i1 : Integrable (fun s => h s * A) μ := hhi.mul_const _
    have i2 : Integrable (fun s => f s * B) μ := hfi.mul_const _
    have e1 : ∫ s, (C - h s * A - f s * B + f s * h s) ∂μ =
        ∫ s, (C - h s * A - f s * B) ∂μ + ∫ s, f s * h s ∂μ :=
      integral_add (((integrable_const C).sub i1).sub i2) hfhi
    have e2 : ∫ s, (C - h s * A - f s * B) ∂μ = ∫ s, (C - h s * A) ∂μ - ∫ s, f s * B ∂μ :=
      integral_sub ((integrable_const C).sub i1) i2
    have e3 : ∫ s, (C - h s * A) ∂μ = ∫ _s, C ∂μ - ∫ s, h s * A ∂μ :=
      integral_sub (integrable_const C) i1
    rw [e1, e2, e3, integral_mul_const, integral_mul_const, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have hle : ∫ s, (C - h s * A - f s * B + f s * h s) ∂μ ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hinner_nonpos] with s hs
    rw [hinner s] at hs
    exact hs
  rw [hout] at hle
  linarith
