-- Prove2me | Definitions.Def_SourceProof_65aff826a3bca159fc89f9df
-- name    : SourceProof_65aff826a3bca159fc89f9df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:35:05.172309+00:00
-- url     : https://prove2.me/theorems/543994fa-3ca2-4693-aa6d-d8561f619ffe
-- title:
--   LevyStochCalc source module: SourceProof_65aff826a3bca159fc89f9df
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.PathRegularity.lintegral_sq_sub_cellTimeAverage_U_le_of_lipschitz` comes from the `LevyStochCalc.BSDEJ.CellAverageRateMarked` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRateMarked_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for a separated Lipschitz marked integrand

For a marked integrand `U s ω e = h s * φ e` whose time factor obeys `|h s - h t| ≤ K * |s - t|`
and a strictly monotone partition `0 = t_0 < ⋯ < t_M = T` of mesh at most `δ`, the pathwise
average of `U` over the cell `(t_n, t_{n+1}]` containing `s` differs from `U s ω e` by at most
`K * δ * |φ e|`, so the marked energy of `U - cellTimeAverage_U π U` over the horizon
`[0, T]` is at most `(K * δ) ^ 2 * T` times the mark integral `∫⁻ e, ‖φ e‖₊ ^ 2 ∂ν`.

The integrand treated here is deterministic in the sample point and its mark dependence is a
single separated factor. The cell-average rate for a marked integrand of general form is a
different statement and is not covered by anything below.
-/

open MeasureTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u v

section Separated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ} {φ : E → ℝ}

omit [MeasurableSpace Ω] in

theorem _root_.Prove2MeSourceProof.h_65aff826a3bca159fc89f9df (ν : Measure E)
    (hmono : StrictMono π) (h0 : π 0 = 0) (hT : π (Fin.last M) = T)
    (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖h s * φ e
        - cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal ((K * δ) ^ 2 * T) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  classical
  have hinner : ∀ {s : ℝ}, s ∈ Set.Ioc (0 : ℝ) T →
      ∫⁻ e, (‖h s * φ e
          - LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ENNReal.ofReal ((K * δ) ^ 2) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    intro s hs
    have hpt : ∀ e : E, (‖h s * φ e
        - LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal ((K * δ) ^ 2) * (‖φ e‖₊ : ℝ≥0∞) ^ 2 := by
      intro e
      have hb := LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U_sub_le_of_lipschitz (φ := φ) hmono h0 hT hδ hlip hs ω e
      set x := h s * φ e
        - LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e with hxdef
      clear_value x
      have hsq : |x| * |x| ≤ K * δ * |φ e| * (K * δ * |φ e|) :=
        mul_self_le_mul_self (abs_nonneg x) hb
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
        ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
        show (‖φ e‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖φ e‖ from (ofReal_norm (φ e)).symm,
        ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
        ← ENNReal.ofReal_mul (sq_nonneg (K * δ))]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [hsq])
    calc ∫⁻ e, (‖h s * φ e
          - LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ∫⁻ e, ENNReal.ofReal ((K * δ) ^ 2) * (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := lintegral_mono hpt
      _ = ENNReal.ofReal ((K * δ) ^ 2) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ e, (‖h s * φ e
          - LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ENNReal.ofReal ((K * δ) ^ 2) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with
      s hs0 hsIcc
    exact hinner ⟨lt_of_le_of_ne hsIcc.1 (Ne.symm (by simpa using hs0)), hsIcc.2⟩
  calc ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖h s * φ e
          - LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal ((K * δ) ^ 2) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := lintegral_mono_ae hae
    _ = ENNReal.ofReal ((K * δ) ^ 2) * (∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) *
        volume (Set.Icc (0 : ℝ) T) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((K * δ) ^ 2 * T) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
        rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_mul (sq_nonneg (K * δ))]
        ring
end Separated

end LevyStochCalc.BSDEJ.PathRegularity


