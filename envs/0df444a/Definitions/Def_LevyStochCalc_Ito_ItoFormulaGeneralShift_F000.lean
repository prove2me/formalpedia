-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F000
-- name    : LevyStochCalc_Ito_ItoFormulaGeneralShift_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:58:39.108506+00:00
-- url     : https://prove2.me/theorems/82bfa335-2022-4a8a-af98-d3852c330673
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaGeneralShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaGeneralShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftIntegral_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a general random vector

A random vector approached pointwise by random vectors for which Itô's formula between two
stopping times already holds carries the formula itself: the boundary term converges by
continuity of the function, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of
two increments is at most four times the energy of the difference of the integrands, hence
almost surely along a subsequence common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_stopped_sub_diff_le` — the energy of the difference of
  the increments of two integrands is at most four times the energy of their difference.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_of_energy` — a path of finite energy is almost
  surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_sum_mul` — the pointwise inner product of two
  families of paths of finite energy is almost surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift` — Itô's formula for the increment
  of a path between two stopping times, for a function translated by a general random vector.
* `LevyStochCalc.Brownian.Ito.dyadicShift` — the dyadic lattice point of a given resolution below
  a vector, coordinate by coordinate.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx` — a bounded random vector known at a
  stopping time is a pointwise limit of finitely valued random vectors known at that time.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- The energy of the difference between the increments of two integrands between two stopping
times is at most four times the energy of the difference of the integrands. -/
theorem lintegral_sq_stopped_sub_diff_le (σ τ : Ω → WithTop ℝ) (A B : Ω → ℝ → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
            - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P
      ≤ 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h4 : ENNReal.ofReal ((2 : ℝ) ^ 2) = 4 := by
    rw [show ((2 : ℝ) ^ 2) = (4 : ℝ) by norm_num]
    simp
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
          - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)‖₊ : ℝ≥0∞) ^ 2
        ≤ 4 * (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    have habs : |(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
        - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)|
          ≤ 2 * |A ω s - B ω s| := by
      rw [stopped_sub_stopped_sub]
      exact abs_stopped_sub_stopped_le σ τ (fun ω s => A ω s - B ω s) ω s
    have hsq := sq_enorm_le_of_abs_le (by norm_num : (0 : ℝ) ≤ 2) habs
    rwa [h4] at hsq
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
              - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          4 * (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hpt ω s
    _ = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤)]
        exact MeasureTheory.lintegral_congr fun ω =>
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤)
end IncrementEnergy

section WindowIntegrability

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- A path of finite energy on a bounded window is almost surely integrable on the corresponding
half-open window. -/
theorem ae_integrableOn_Ioc_of_energy {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) {T : ℝ}
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b ω) (Set.Ioc (0 : ℝ) T) volume := by
  filter_upwards [ae_integrableOn_of_energy_lt_top hbm hbq] with ω hω
  exact hω.mono_set Set.Ioc_subset_Icc_self
end WindowIntegrability

section GeneralShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GeneralShift

section DyadicApproximation

variable {Ω : Type u} [MeasurableSpace Ω]

end DyadicApproximation

end LevyStochCalc.Brownian.Ito


