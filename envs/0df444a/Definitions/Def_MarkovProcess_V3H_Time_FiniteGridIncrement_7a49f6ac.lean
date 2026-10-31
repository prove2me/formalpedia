-- Prove2me | Definitions.Def_MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
-- name    : MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:16:35.61697+00:00
-- url     : https://prove2.me/theorems/2a03fce7-e0b4-44de-9acf-81a65bbab1f7
-- title:
--   MarkovProcess: MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-grid increment bounds

This file supplies the finite union-bound step in a Kolmogorov--Chentsov argument. It is
independent of a particular dyadic-grid encoding: a later specialization only has to bound the
distance between adjacent grid times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The event that at least one adjacent increment of a finite time grid has `p`-th power at
least `ε ^ p`. -/
def finiteGridBadIncrement {T : Type*} {N : ℕ} (X : T → Ω → E)
    (grid : Fin (N + 1) → T) (p : ℝ) (ε : ℝ≥0∞) : Set Ω :=
  ⋃ i : Fin N,
    {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p}

/-- A finite-grid union bound obtained directly from the Kolmogorov moment condition. -/
theorem IsKolmogorovProcess.p2m_embedded_f2e9b915d032a86f
    {T : Type*} [PseudoEMetricSpace T] {N : ℕ} {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M)
    (grid : Fin (N + 1) → T) (δ ε : ℝ≥0∞)
    (hgrid : ∀ i : Fin N, edist (grid i.castSucc) (grid i.succ) ≤ δ)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X grid p ε) ≤ N * (M * δ ^ q / ε ^ p) := by
  unfold finiteGridBadIncrement
  calc
    P (⋃ i : Fin N,
        {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p}) ≤
        ∑ i : Fin N,
          P {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p} :=
      measure_iUnion_fintype_le P _
    _ ≤ ∑ _i : Fin N, (M * δ ^ q / ε ^ p) := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        P {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p} ≤
            (∫⁻ ω, edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p ∂P) /
              ε ^ p := by
          apply meas_ge_le_lintegral_div
          · exact (hX.measurable_edist.pow_const p).aemeasurable
          · exact (ENNReal.rpow_eq_zero_iff_of_pos hX.p_pos).not.mpr hε0
          · exact (ENNReal.rpow_eq_top_iff_of_pos hX.p_pos).not.mpr hεtop
        _ ≤ (M * δ ^ q) / ε ^ p := by
          gcongr
          exact (hX.kolmogorovCondition _ _).trans
            (mul_le_mul_right (ENNReal.rpow_le_rpow (hgrid i) hX.q_pos.le) M)
    _ = N * (M * δ ^ q / ε ^ p) := by simp

/-- The dyadic grid of mesh `2⁻ⁿ` on the unit time interval. -/
def unitDyadicGrid (n : ℕ) : Fin (2 ^ n + 1) → NNRat :=
  fun i ↦ (i : ℕ) / (2 ^ n : NNRat)

/-- Adjacent points of the level-`n` unit dyadic grid are at most `2⁻ⁿ` apart. -/
theorem unitDyadicGrid_edist_adjacent_le (n : ℕ) (i : Fin (2 ^ n)) :
    edist (unitDyadicGrid n i.castSucc) (unitDyadicGrid n i.succ) ≤
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [edist_dist, ENNReal.ofReal_le_iff_le_toReal]
  · rw [NNRat.dist_eq, Rat.dist_eq]
    simp only [unitDyadicGrid]
    push_cast
    rw [div_sub_div_same]
    simp only [Fin.val_castSucc, Fin.val_succ]
    push_cast
    norm_num [abs_div, abs_of_nonneg]
  · simp

/-- The Kolmogorov finite-grid bound on the level-`n` unit dyadic grid. -/
theorem IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (n : ℕ) (ε : ℝ≥0∞)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p ε) ≤
      2 ^ n * (M * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q / ε ^ p) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    _root_.MarkovProcess.IsKolmogorovProcess.p2m_embedded_f2e9b915d032a86f hX (unitDyadicGrid n) _ ε
      (unitDyadicGrid_edist_adjacent_le n) hε0 hεtop

end MarkovProcess


