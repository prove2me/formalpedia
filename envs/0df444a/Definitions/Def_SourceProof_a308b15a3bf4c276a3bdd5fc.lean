-- Prove2me | Definitions.Def_SourceProof_a308b15a3bf4c276a3bdd5fc
-- name    : SourceProof_a308b15a3bf4c276a3bdd5fc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:26:07.527474+00:00
-- url     : https://prove2.me/theorems/dca77400-dff3-48d7-93e6-81df845954c3
-- title:
--   LevyStochCalc source module: SourceProof_a308b15a3bf4c276a3bdd5fc
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_bounded` comes from the `LevyStochCalc.Brownian.ItoDensityShiftedAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable.


theorem _root_.Prove2MeSourceProof.h_a308b15a3bf4c276a3bdd5fc
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) :
    |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω|
      ≤ max M 0 := by
  set H := LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
  by_cases h_any : ∃ i : Fin H.N,
      H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
  · obtain ⟨i₀, hi₀⟩ := h_any
    have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
        ¬(H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) := by
      intro j hj hj_active
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have h_le : H.partition j.succ ≤ H.partition i₀.castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hj_active.2, hi₀.1]
      · have h_le : H.partition i₀.succ ≤ H.partition j.castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.2, hj_active.1]
    have h_sum_eq : (∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0)
        = H.ξ i₀ ω := by
      rw [Finset.sum_eq_single i₀]
      · simp [hi₀]
      · intro j _ hj
        simp [h_unique j hj]
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq]
    exact LevyStochCalc.Brownian.Ito.dyadicAvg_shifted_brownian_bounded T hT g M h_bound n i₀ ω
  · have h_sum_zero : (∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0)
        = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
      · exact absurd ⟨i, hi⟩ h_any
      · simp [hi]
    rw [h_sum_zero, abs_zero]
    exact le_max_right _ _
-- `omit` the unused `[MeasurableSpace Ω]` section variable.

end LevyStochCalc.Brownian.Ito


