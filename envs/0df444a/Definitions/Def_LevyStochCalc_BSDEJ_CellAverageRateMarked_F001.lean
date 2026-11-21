-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRateMarked_F001
-- name    : LevyStochCalc_BSDEJ_CellAverageRateMarked_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:39:13.495734+00:00
-- url     : https://prove2.me/theorems/be7cb509-fcbb-4576-96cf-d7a412f95d66
-- title:
--   LevyStochCalc source module: LevyStochCalc.BSDEJ.CellAverageRateMarked
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.BSDEJ.CellAverageRateMarked in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRate_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001
import Definitions.Def_SourceProof_65aff826a3bca159fc89f9df

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

/-- For the marked integrand `U s ω e = h s * φ e` with `|h s - h t| ≤ K * |s - t|`, the marked
energy of the cell-average error over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T` times the
mark integral of `‖φ‖ ^ 2`, where `δ` bounds the mesh of the strictly monotone partition `π` of
`[0, T]`. -/
theorem markedEnergy_sub_cellTimeAverage_U_le_of_lipschitz (P : Measure Ω)
    (ν : Measure E) [IsProbabilityMeasure P] (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = T) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) :
    Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => h s * φ e
          - cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e)
      ≤ ENNReal.ofReal ((K * δ) ^ 2 * T) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  rw [Poisson.Compensated.markedEnergy]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖h s * φ e
          - cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e‖₊ : ℝ≥0∞) ^ 2
            ∂ν ∂volume ∂P
      ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((K * δ) ^ 2 * T) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P :=
        lintegral_mono fun ω =>
          _root_.Prove2MeSourceProof.h_65aff826a3bca159fc89f9df ν hmono h0 hT hδ hlip ω
    _ = ENNReal.ofReal ((K * δ) ^ 2 * T) * ∫⁻ e, (‖φ e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
        rw [lintegral_const, measure_univ, mul_one]
end Separated

end LevyStochCalc.BSDEJ.PathRegularity


