-- Prove2me | Definitions.Def_SourceProof_9261f2942c4ea65092c46566
-- name    : SourceProof_9261f2942c4ea65092c46566
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:57:49.846149+00:00
-- url     : https://prove2.me/theorems/78f07b44-5be3-408b-af8b-259b3753bf6c
-- title:
--   LevyStochCalc source module: SourceProof_9261f2942c4ea65092c46566
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian_eval_eq_dyadicAvg` comes from the `LevyStochCalc.Brownian.ItoDensityShiftedAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_d2dcdd70ae2c689ce98c5bad

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

-- `omit` the unused `[MeasurableSpace Ω]` section variable.


theorem _root_.Prove2MeSourceProof.h_9261f2942c4ea65092c46566
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T) (ω : Ω) :
    (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω =
      dyadicAvg_brownian (T := T) g n (dyadicIndex n T hT s hs) ω := by
  let φ := LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian hT g h_meas M h_bound n
  let i := LevyStochCalc.Brownian.Ito.dyadicIndex n T hT s hs
  -- s ∈ (t_i, t_{i+1}], so the i-th indicator fires.
  have hi_mem := _root_.Prove2MeSourceProof.h_d2dcdd70ae2c689ce98c5bad n T hT s hs
  have h_partition_castSucc : φ.partition i.castSucc =
      ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    change LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i.castSucc = _
    unfold LevyStochCalc.Brownian.Ito.dyadicPartition_brownian
    push_cast
    simp [Fin.val_castSucc]
  have h_partition_succ : φ.partition i.succ =
      (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    change LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i.succ = _
    unfold LevyStochCalc.Brownian.Ito.dyadicPartition_brownian
    push_cast
    simp [Fin.val_succ]
  -- The i-th indicator fires: t_i < s ≤ t_{i+1}.
  have h_i_fires : φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ := by
    rw [h_partition_castSucc, h_partition_succ]
    exact hi_mem
  -- For j ≠ i, the j-th indicator does NOT fire (partition strictly monotone).
  have h_j_not_fires : ∀ j : Fin (2 ^ n), j ≠ i →
      ¬(φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ) := by
    intro j hji ⟨hj1, hj2⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_le : s ≤ φ.partition i.succ := h_i_fires.2
      linarith
    · exact hji heq.symm
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_lt : φ.partition i.castSucc < s := h_i_fires.1
      linarith
  -- Now collapse the sum.
  change (∑ j : Fin φ.N, if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                       then φ.ξ j ω else 0) = LevyStochCalc.Brownian.Ito.dyadicAvg_brownian g n i ω
  change (∑ j : Fin (2 ^ n), if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                            then φ.ξ j ω else 0) = LevyStochCalc.Brownian.Ito.dyadicAvg_brownian g n i ω
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
    change LevyStochCalc.Brownian.Ito.dyadicAvg_brownian (T := T) g n i ω = LevyStochCalc.Brownian.Ito.dyadicAvg_brownian g n i ω
    rfl
  · intro j _ hji
    refine if_neg ?_
    intro hj
    exact h_j_not_fires j hji hj
  · intro h_not_mem
    exact absurd (Finset.mem_univ i) h_not_mem
end LevyStochCalc.Brownian.Ito


