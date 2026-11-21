-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRateMarked_F000
-- name    : LevyStochCalc_BSDEJ_CellAverageRateMarked_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:52.190167+00:00
-- url     : https://prove2.me/theorems/482efe9a-eefc-4ca6-a537-3ce1050fd7d0
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.CellAverageRateMarked
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.CellAverageRateMarked. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRate_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001

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

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- For the marked integrand `U s ω e = h s * φ e` with `|h s - h t| ≤ K * |s - t|`, the pathwise
cell average over a strictly monotone partition of `[0, T]` of mesh at most `δ` stays within
`K * δ * |φ e|` of `h s * φ e` at every time of `(0, T]`. -/
theorem cellTimeAverage_U_sub_le_of_lipschitz (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = T) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T)
    (ω : Ω) (e : E) :
    |h s * φ e - cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e|
      ≤ K * δ * |φ e| := by
  classical
  obtain ⟨n₀, hn₀, huniq⟩ := _root_.Prove2MeSourceProof.h_aa940cfe8f26de935fbb8849 hmono h0 hT hs
  have hsum : cellTimeAverage_U π (fun u (_ : Ω) (e : E) => h u * φ e) s ω e
      = ((1 / (π n₀.succ - π n₀.castSucc)) *
        ∫ u in Set.Icc (π n₀.castSucc) (π n₀.succ), h u) * φ e := by
    simp only [cellTimeAverage_U]
    rw [Finset.sum_eq_single n₀]
    · rw [if_pos hn₀, integral_mul_const]
      ring
    · intro b _ hb
      exact if_neg fun hcon => hb (huniq b hcon)
    · intro hcon
      exact absurd (Finset.mem_univ n₀) hcon
  rw [hsum, ← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (cell_sub_average_le_of_lipschitz hmono hδ hlip n₀ (Set.mem_Ioc.mpr hn₀)) (abs_nonneg _)
end Separated

end LevyStochCalc.BSDEJ.PathRegularity


