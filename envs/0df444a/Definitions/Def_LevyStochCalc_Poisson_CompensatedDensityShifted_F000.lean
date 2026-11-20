-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityShifted_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:01:00.514738+00:00
-- url     : https://prove2.me/theorems/ac540198-9a90-480e-95b2-62ae0d240aa7
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityShifted
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityShifted. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The adapted (left-shifted) dyadic eval

The variant of the dyadic evaluation whose coefficient on the `i`-th dyadic interval is the
average of `φ` over the *previous* interval, hence `ℱ_{tᵢ}`-measurable for progressively
measurable `φ`. Its almost-everywhere and `L²(P ⊗ ds ⊗ ν)` convergence to `φ` follow from the
same Lebesgue-density and dominated-convergence arguments, the left shift contributing a
vanishing displacement.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Adapted (left-shifted) eval

The coefficient on the `i`-th dyadic interval is the average over the *previous*
interval (`dyadicAvg_shifted`), making it `ℱ_{tᵢ}`-measurable for progressively
measurable `φ` — the predictable/adapted version of `dyadicEval`. -/

/-- The left-shifted dyadic eval (adapted coefficients). -/
noncomputable def dyadicEvalShifted
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) : ℝ :=
  ∑ i : Fin (2 ^ n),
    if dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
    then dyadicAvg_shifted T φ n i ω e else 0
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- For `s ∈ (0, T]`, the shifted eval collapses to the shifted average at the index of `s`. -/
lemma dyadicEvalShifted_eq_at_index
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T)
    (ω : Ω) (e : E) :
    dyadicEvalShifted T φ n s ω e = dyadicAvg_shifted T φ n (dyadicIndex n T hT s hs) ω e := by
  set i := dyadicIndex n T hT s hs with hi
  have hi_mem := _root_.Prove2MeSourceProof.h_e15e3b0d44b9d0242ba7b234 n T hT s hs
  have h_pcast : dyadicPartition T n i.castSucc = ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_castSucc]
  have h_psucc : dyadicPartition T n i.succ = (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_succ]; push_cast; ring
  have h_i_fires : dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ := by
    rw [h_pcast, h_psucc]; exact hi_mem
  unfold dyadicEvalShifted
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
  · intro j _ hji
    refine if_neg (fun ⟨hj1, hj2⟩ => ?_)
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      linarith [h_i_fires.2]
    · exact hji heq.symm
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
      linarith [h_i_fires.1]
  · intro h_not; exact absurd (Finset.mem_univ i) h_not
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The shifted eval is bounded by `max M 0` (at most one indicator fires; each shifted
average is bounded by `max M 0`). -/
lemma dyadicEvalShifted_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) :
    |dyadicEvalShifted T φ n s ω e| ≤ max M 0 := by
  unfold dyadicEvalShifted
  by_cases h : ∃ i : Fin (2 ^ n),
      dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
  · obtain ⟨i₀, hi₀⟩ := h
    have huniq : ∀ j : Fin (2 ^ n), j ≠ i₀ →
        ¬(dyadicPartition T n j.castSucc < s ∧ s ≤ dyadicPartition T n j.succ) := by
      intro j hj ⟨hj1, hj2⟩
      rcases lt_trichotomy i₀ j with hlt | heq | hgt
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hi₀.2]
      · exact hj heq.symm
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.1]
    rw [Finset.sum_eq_single i₀ (fun j _ hj => if_neg (huniq j hj))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hi₀]
    exact dyadicAvg_shifted_bounded hT φ hM n i₀ ω e
  · rw [not_exists] at h
    rw [Finset.sum_eq_zero (fun i _ => if_neg (h i)), abs_zero]; exact le_max_right _ _
/-- Joint `(ω, s, e)`-measurability of the shifted eval. -/
lemma dyadicEvalShifted_measurable_triple
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (fun p : Ω × ℝ × E => dyadicEvalShifted T φ n p.2.1 p.1 p.2.2) := by
  unfold dyadicEvalShifted
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ((measurable_fst.comp measurable_snd) measurableSet_Ioc) ?_
    measurable_const
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_measurable T φ h_meas n _).comp
      (by fun_prop : Measurable fun p : Ω × ℝ × E => ((p.1, p.2.2) : Ω × E))
/-- `dyadicPartition` depends only on the index's value. -/
lemma dyadicPartition_val_congr {T : ℝ} {n : ℕ} {k k' : Fin (2 ^ n + 1)}
    (h : (k : ℕ) = (k' : ℕ)) : dyadicPartition T n k = dyadicPartition T n k' := by
  unfold dyadicPartition
  rw [show (k : ℝ) = (k' : ℝ) from by exact_mod_cast h]
end LevyStochCalc.Poisson.Compensated


