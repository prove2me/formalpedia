-- Prove2me | Definitions.Def_SourceProof_d85ab88de821d59dc1b96591
-- name    : SourceProof_d85ab88de821d59dc1b96591
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:08:52.647026+00:00
-- url     : https://prove2.me/theorems/73120650-3cdd-498e-a1c9-82bed6301073
-- title:
--   LevyStochCalc source module: SourceProof_d85ab88de821d59dc1b96591
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian_eval_bounded` comes from the `LevyStochCalc.Brownian.ItoDensityShiftedAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F002

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


theorem _root_.Prove2MeSourceProof.h_d85ab88de821d59dc1b96591
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (ω : Ω) :
    |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω| ≤ M := by
  set φ := LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n with hφ
  have h_M_nn : (0 : ℝ) ≤ M := le_trans (abs_nonneg (g ω 0)) (h_bound ω 0)
  -- ξ bound for each i: dyadicAvg bounded by M.
  have h_each_bound : ∀ i : Fin φ.N, |φ.ξ i ω| ≤ M := fun i => by
    change |dyadicAvg_brownian (T := T) g n i ω| ≤ M
    exact _root_.Prove2MeSourceProof.h_59dc14df6f6315a597b2c358 T hT g M h_bound n i ω
  -- At most one index i has `partition i.castSucc < s ∧ s ≤ partition i.succ`.
  have h_at_most_one : ∀ i j : Fin φ.N, i ≠ j →
      ¬((φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ) ∧
        (φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ)) := by
    intro i j hij ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · -- i < j, so i.succ ≤ j.castSucc. Then s ≤ partition i.succ ≤ partition j.castSucc < s.
      have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      linarith
    · exact hij heq
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      linarith
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
  -- The sum `∑ i, (if cond_i then ξ_i ω else 0)` has at most one nonzero term.
  -- Case 1: some i fires. Sum = ξ i ω, |·| ≤ M.
  -- Case 2: no i fires. Sum = 0, |·| = 0 ≤ M.
  by_cases h_exists : ∃ i : Fin φ.N,
      φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ
  · obtain ⟨i, hi⟩ := h_exists
    have h_sum_eq : (∑ j : Fin φ.N,
        if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
        then φ.ξ j ω else 0) = φ.ξ i ω := by
      rw [Finset.sum_eq_single i]
      · exact if_pos hi
      · intro j _ hji
        refine if_neg ?_
        intro hj
        exact h_at_most_one i j (Ne.symm hji) ⟨hi, hj⟩
      · intro h_not_mem
        exact absurd (Finset.mem_univ i) h_not_mem
    rw [h_sum_eq]
    exact h_each_bound i
  · have h_sum_eq : (∑ j : Fin φ.N,
        if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
        then φ.ξ j ω else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      refine if_neg ?_
      intro hj
      exact h_exists ⟨j, hj⟩
    rw [h_sum_eq, abs_zero]
    exact h_M_nn
-- `omit` the unused `[MeasurableSpace Ω]` section variable.

end LevyStochCalc.Brownian.Ito


