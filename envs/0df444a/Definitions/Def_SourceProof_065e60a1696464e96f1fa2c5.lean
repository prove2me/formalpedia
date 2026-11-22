-- Prove2me | Definitions.Def_SourceProof_065e60a1696464e96f1fa2c5
-- name    : SourceProof_065e60a1696464e96f1fa2c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:58:43.669934+00:00
-- url     : https://prove2.me/theorems/a00f1556-1e66-44ba-b64c-8af2b577ff53
-- title:
--   LevyStochCalc source module: SourceProof_065e60a1696464e96f1fa2c5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_sum_mul` comes from the `LevyStochCalc.Ito.ItoFormulaGeneralShift` module. The staged Lean declaration includes its source proof and dependency references.
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

end IncrementEnergy

section WindowIntegrability

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_065e60a1696464e96f1fa2c5 {n d : ℕ} {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k))) {T : ℝ}
    (hHs : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume := by
  have hprod : ∀ {μ : Measure ℝ} (u v : ℝ → ℝ), MeasureTheory.MemLp u 2 μ →
      MeasureTheory.MemLp v 2 μ → MeasureTheory.Integrable (fun s => u s * v s) μ := by
    intro μ u v hu hv
    refine MeasureTheory.Integrable.mono'
      ((hu.integrable_sq.const_mul (1 / 2 : ℝ)).add (hv.integrable_sq.const_mul (1 / 2 : ℝ)))
      (hu.1.mul hv.1) ?_
    filter_upwards with s
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (u s), sq_abs (v s), sq_nonneg (|u s| - |v s|)]
  have hfin : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    MeasureTheory.ae_all_iff.mpr fun p => MeasureTheory.ae_all_iff.mpr fun k =>
      MeasureTheory.ae_lt_top (LevyStochCalc.Brownian.Ito.measurable_energyDensity (hHm p k) T) (hHs p k).ne
  filter_upwards [hfin] with ω hω p q
  have hmem : ∀ (r : Fin n) (k : Fin d), MeasureTheory.MemLp (H r k ω) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := fun r k =>
    LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
      (Measurable.of_uncurry_left (hHm r k)) (hω r k)
  have hIcc : MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Icc (0 : ℝ) T) volume :=
    MeasureTheory.integrable_finsetSum _ fun k _ => hprod _ _ (hmem p k) (hmem q k)
  exact hIcc.mono_set Set.Ioc_subset_Icc_self
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


