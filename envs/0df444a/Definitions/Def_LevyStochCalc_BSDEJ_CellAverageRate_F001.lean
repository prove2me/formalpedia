-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRate_F001
-- name    : LevyStochCalc_BSDEJ_CellAverageRate_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:30:26.250339+00:00
-- url     : https://prove2.me/theorems/545dbef7-6d47-4227-a680-a3843a51f54a
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.CellAverageRate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.CellAverageRate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRate_F000
import Definitions.Def_SourceProof_aa940cfe8f26de935fbb8849

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for a deterministic Lipschitz integrand

For a function `h : ℝ → ℝ` with `|h s - h t| ≤ K * |s - t|` and a strictly monotone partition
`0 = t_0 < ⋯ < t_M = T` of mesh at most `δ`, the pathwise average of `h` over the cell
`(t_n, t_{n+1}]` containing `s` differs from `h s` by at most `K * δ`, so the energy of
`h - cellTimeAverage_Z π h` over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T`.

The integrand treated here is deterministic: it is the process `Z s ω i = h s`, constant in the
sample point and in the coordinate. The cell-average rate for a random integrand is a different,
genuinely stochastic statement and is not covered by anything below.
-/

open MeasureTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u

section Lipschitz

variable {K : ℝ} {h : ℝ → ℝ}

end Lipschitz

section Cells

variable {M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

/-- On the cell `(π n.castSucc, π n.succ]` of a strictly monotone partition of mesh at most `δ`,
the average of a function obeying `|h s - h t| ≤ K * |s - t|` over that cell differs from its
value at any point of the cell by at most `K * δ`. -/
theorem cell_sub_average_le_of_lipschitz (hmono : StrictMono π)
    (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (n : Fin M) {s : ℝ}
    (hs : s ∈ Set.Ioc (π n.castSucc) (π n.succ)) :
    |h s - (1 / (π n.succ - π n.castSucc)) *
      ∫ u in Set.Icc (π n.castSucc) (π n.succ), h u| ≤ K * δ := by
  have hab : π n.castSucc < π n.succ := hmono (Fin.castSucc_lt_succ)
  exact (abs_sub_intervalAverage_le hlip hab hs).trans
    (mul_le_mul_of_nonneg_left (hδ n) (nonneg_of_lipschitz_bound hlip))
end Cells

section Deterministic

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

omit [MeasurableSpace Ω] in
/-- For the deterministic process `Z s ω i = h s` with `|h s - h t| ≤ K * |s - t|`, the pathwise
cell average over a strictly monotone partition of `[0, T]` of mesh at most `δ` stays within
`K * δ` of `h s` at every time of `(0, T]`. -/
theorem cellTimeAverage_sub_le_of_lipschitz (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = T) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T)
    (ω : Ω) (i : Fin d) :
    |h s - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i| ≤ K * δ := by
  classical
  obtain ⟨n₀, hn₀, huniq⟩ := _root_.Prove2MeSourceProof.h_aa940cfe8f26de935fbb8849 hmono h0 hT hs
  have hsum : cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i
      = (1 / (π n₀.succ - π n₀.castSucc)) *
        ∫ u in Set.Icc (π n₀.castSucc) (π n₀.succ), h u := by
    simp only [cellTimeAverage_Z]
    rw [Finset.sum_eq_single n₀]
    · rw [if_pos hn₀]
    · intro b _ hb
      exact if_neg fun hcon => hb (huniq b hcon)
    · intro hcon
      exact absurd (Finset.mem_univ n₀) hcon
  rw [hsum]
  exact cell_sub_average_le_of_lipschitz hmono hδ hlip n₀ (Set.mem_Ioc.mpr hn₀)
omit [MeasurableSpace Ω] in
/-- For the deterministic process `Z s ω i = h s` with `|h s - h t| ≤ K * |s - t|`, the squared
`L²(dt)` error of the pathwise cell average over a strictly monotone partition of `[0, T]` of
mesh at most `δ` is at most `(K * δ) ^ 2 * T`. -/
theorem lintegral_sq_sub_cellTimeAverage_le_of_lipschitz (hmono : StrictMono π)
    (h0 : π 0 = 0) (hT : π (Fin.last M) = T) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (ω : Ω) (i : Fin d) :
    ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖h s - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i‖₊ :
          ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal ((K * δ) ^ 2 * T) := by
  classical
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (‖h s - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i‖₊ :
        ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal ((K * δ) ^ 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with
      s hs0 hsIcc
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) T :=
      ⟨lt_of_le_of_ne hsIcc.1 (Ne.symm (by simpa using hs0)), hsIcc.2⟩
    have hbound := cellTimeAverage_sub_le_of_lipschitz hmono h0 hT hδ hlip hsIoc ω i
    set x := h s - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i with hx
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg x])
  calc ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖h s - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i‖₊ :
          ℝ≥0∞) ^ 2
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((K * δ) ^ 2) := lintegral_mono_ae hae
    _ = ENNReal.ofReal ((K * δ) ^ 2) * volume (Set.Icc (0 : ℝ) T) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((K * δ) ^ 2 * T) := by
        rw [Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (sq_nonneg _)]
/-- For the deterministic process `Z s ω i = h s` with `|h s - h t| ≤ K * |s - t|`, the energy of
the cell-average error over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T`, where `δ` bounds
the mesh of the strictly monotone partition `π` of `[0, T]`. -/
theorem energy_sub_cellTimeAverage_le_of_lipschitz (P : Measure Ω)
    [IsProbabilityMeasure P] (hmono : StrictMono π) (h0 : π 0 = 0) (hT : π (Fin.last M) = T)
    (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (i : Fin d) :
    Brownian.Ito.energy P T
        (fun ω s => h s - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i)
      ≤ ENNReal.ofReal ((K * δ) ^ 2 * T) := by
  calc Brownian.Ito.energy P T
        (fun ω s => h s - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i)
      ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((K * δ) ^ 2 * T) ∂P :=
        lintegral_mono fun ω =>
          lintegral_sq_sub_cellTimeAverage_le_of_lipschitz hmono h0 hT hδ hlip ω i
    _ = ENNReal.ofReal ((K * δ) ^ 2 * T) := by rw [lintegral_const, measure_univ, mul_one]
end Deterministic

end LevyStochCalc.BSDEJ.PathRegularity


