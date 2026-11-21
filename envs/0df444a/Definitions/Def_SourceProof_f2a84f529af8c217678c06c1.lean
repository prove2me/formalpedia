-- Prove2me | Definitions.Def_SourceProof_f2a84f529af8c217678c06c1
-- name    : SourceProof_f2a84f529af8c217678c06c1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:36:15.1399+00:00
-- url     : https://prove2.me/theorems/a688b837-7057-453c-8da8-45da9483004a
-- title:
--   LevyStochCalc source module: SourceProof_f2a84f529af8c217678c06c1
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_sub_bieleckiLimit_rpow_le` comes from the `LevyStochCalc.Ito.PicardLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of Bielecki-Cauchy sequences of path maps

A sequence of path maps whose consecutive Bielecki differences are summable converges: at every
time of the window the increments are summable in `L²`, hence almost surely absolutely summable,
so the pointwise `limsup` is the almost-sure limit. The `limsup` inherits joint measurability and
progressive measurability from the sequence, and the Bielecki distance to the sequence tends to
zero.

The Bielecki norm is the weighted supremum over `t` of the `L²` norms, so it controls the paths
at each fixed time only: a càdlàg property of the terms is not inherited by the limit. The limit
constructed here is therefore a jointly measurable, progressively measurable path map, not an
`SBoundedProcess`; the càdlàg property of a Picard fixed point comes from the Picard step's own
output, not from the limit.

## Main statements

* `bieleckiLimit` — the pointwise `limsup` of a sequence of path maps.
* `measurable_bieleckiLimit`, `progressivelyMeasurable_bieleckiLimit` — its measurability.
* `bieleckiNorm_le_of_perTime_rpow`, `lintegral_sq_rpow_le_of_bieleckiNorm` — the two directions
  between the Bielecki norm and the weighted `L²` norms at a fixed time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The Bielecki norm and the weighted `L²` norms at a fixed time -/

/-! ### The limit path map -/

/-! ### Telescoping -/

/-! ### Almost sure convergence at a fixed time -/

/-! ### Convergence to the limit path map -/


theorem _root_.Prove2MeSourceProof.h_f2a84f529af8c217678c06c1 (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (hc : ∑' k, c k ≠ ⊤) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (β * t)) * ∑' j, c (k + j) := by
  set B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (β * t)) * ∑' j, c (k + j) with hB
  have hFm : ∀ m, Measurable fun ω => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2 := fun m =>
    LevyStochCalc.Ito.Picard.measurable_sq_slice (LevyStochCalc.Ito.Picard.measurable_uncurry_sub (hmeas k) (hmeas m)) t
  -- Fatou against the almost sure limit.
  have hae : ∀ᵐ ω ∂P, Filter.liminf
      (fun m => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2) Filter.atTop
      = ∑ i, (‖X k t ω i - LevyStochCalc.Ito.Picard.bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [LevyStochCalc.Ito.Picard.ae_tendsto_bieleckiLimit (P := P) β T hmeas hstep hc ht] with ω hω
    refine Filter.Tendsto.liminf_eq ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    have hnn : Filter.Tendsto (fun m => (‖X k t ω i - X m t ω i‖₊ : ℝ≥0) ^ 2) Filter.atTop
        (nhds ((‖X k t ω i - LevyStochCalc.Ito.Picard.bieleckiLimit X t ω i‖₊ : ℝ≥0) ^ 2)) :=
      (Filter.Tendsto.const_sub (X k t ω i) (hω i)).nnnorm.pow 2
    simpa only [Function.comp_def, ENNReal.coe_pow] using
      (ENNReal.continuous_coe.tendsto _).comp hnn
  have hfatou : ∫⁻ ω, ∑ i, (‖X k t ω i - LevyStochCalc.Ito.Picard.bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ Filter.liminf
        (fun m => ∫⁻ ω, ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop := by
    calc ∫⁻ ω, ∑ i, (‖X k t ω i - LevyStochCalc.Ito.Picard.bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, Filter.liminf
            (fun m => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2) Filter.atTop ∂P :=
          (lintegral_congr_ae (hae.mono fun _ h => h)).symm
      _ ≤ _ := lintegral_liminf_le hFm
  -- Each term of the sequence is bounded by `B ^ 2`, eventually.
  have hev : ∀ᶠ m in Filter.atTop,
      ∫⁻ ω, ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ B ^ (2 : ℕ) := by
    filter_upwards [Filter.eventually_ge_atTop k] with m hm
    have hrev : (fun ω => ∑ i, (‖X k t ω i - X m t ω i‖₊ : ℝ≥0∞) ^ 2)
        = fun ω => ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 := by
      funext ω
      exact Finset.sum_congr rfl fun i _ => by
        rw [show X k t ω i - X m t ω i = -(X m t ω i - X k t ω i) by ring, nnnorm_neg]
    have hb : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X m t ω i - X k t ω i)
        ≤ ∑' j, c (k + j) :=
      (LevyStochCalc.Ito.Picard.bieleckiNorm_sub_le_sum_Ico (P := P) β T hmeas hstep k m hm).trans
        (LevyStochCalc.Ito.Picard.sum_Ico_le_tsum_shift k m)
    have hhalf : (∫⁻ ω, ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) ≤ B :=
      (LevyStochCalc.Ito.Picard.lintegral_sq_rpow_le_of_bieleckiNorm (P := P) β T
        (fun t ω i => X m t ω i - X k t ω i) ht).trans (mul_le_mul' le_rfl hb)
    rw [hrev]
    calc ∫⁻ ω, ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ((∫⁻ ω, ∑ i, (‖X m t ω i - X k t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
          rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
          norm_num
      _ ≤ B ^ (2 : ℕ) := pow_le_pow_left' hhalf 2
  have hsq : ∫⁻ ω, ∑ i, (‖X k t ω i - LevyStochCalc.Ito.Picard.bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ B ^ (2 : ℕ) :=
    hfatou.trans (Filter.liminf_le_of_frequently_le hev.frequently)
  calc (∫⁻ ω, ∑ i, (‖X k t ω i - LevyStochCalc.Ito.Picard.bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ (B ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = B := by
        rw [← ENNReal.rpow_natCast B 2, ← ENNReal.rpow_mul]
        norm_num
/-! ### The geometric case -/

end LevyStochCalc.Ito.Picard


