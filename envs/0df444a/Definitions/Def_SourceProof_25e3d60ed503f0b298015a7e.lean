-- Prove2me | Definitions.Def_SourceProof_25e3d60ed503f0b298015a7e
-- name    : SourceProof_25e3d60ed503f0b298015a7e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:46:23.096053+00:00
-- url     : https://prove2.me/theorems/be79a044-559e-44cb-aa78-cd24a81e39da
-- title:
--   LevyStochCalc source module: SourceProof_25e3d60ed503f0b298015a7e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift_of_mul` comes from the `LevyStochCalc.Ito.ItoFormulaRandomShift` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Passing to the limit in a shifted Itô formula

A shift of the argument of a `C²` function by a random vector is approximated by shifts along a
sequence of random vectors converging to it pointwise. Each term of the resulting identity
converges: the boundary term by continuity of the function, the two Lebesgue terms by dominated
convergence along the path, and the stochastic term in `L²` by the difference isometry, hence
almost surely along a subsequence. An identity holding for every member of the sequence therefore
holds in the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.stopped_sub` — cutting off at a stopping time is linear.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_comp_shift` — the energy of the difference of
  two shifted integrands vanishes along a pointwise-convergent sequence of shifts.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_of_forall_ae_eq` — an almost-everywhere identity
  survives an almost-everywhere limit on both sides.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy` — a vanishing
  energy distance between integrands gives a vanishing `L²` distance between their Itô integrals.
* `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_of_tendsto_energy` — the same over
  finitely many Brownian channels, almost surely along a common subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {α : Type*}

section StoppedAlgebra

variable {Ω : Type*}

end StoppedAlgebra

section LimitTransfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end LimitTransfer

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

section PathIntegral

variable {Ω : Type u}


theorem _root_.Prove2MeSourceProof.h_25e3d60ed503f0b298015a7e {n : ℕ} {X : ℝ → Ω → Fin n → ℝ}
    {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g) {D : Ω → ℝ → ℝ} {ω : Ω} {K : ℝ}
    (hK : ∀ (z : Fin n → ℝ) (s : ℝ), |g z| * |D ω s| ≤ K * |D ω s|)
    {σ τ : Ω → WithTop ℝ} {T : ℝ}
    {c : Ω → Fin n → ℝ} {cm : ℕ → Ω → Fin n → ℝ}
    (hlim : Filter.Tendsto (fun m => cm m ω) Filter.atTop (nhds (c ω)))
    (hint : IntegrableOn (fun s => D ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hmeas : ∀ m : ℕ, AEStronglyMeasurable (fun s =>
        Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s)
      (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s) ∂volume)
      Filter.atTop (nhds (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + c ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + c ω) * D ω s) ω s) ∂volume)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => 2 * (K * |D ω s|)) hmeas ((hint.abs.const_mul K).const_mul 2) ?_ ?_
  · intro m
    refine Filter.Eventually.of_forall fun s => ?_
    refine le_trans (LevyStochCalc.Brownian.Ito.abs_stopped_sub_stopped_le σ τ
      (fun ω s => g (X s ω + cm m ω) * D ω s) ω s) ?_
    have : |g (X s ω + cm m ω) * D ω s| ≤ K * |D ω s| := by
      rw [abs_mul]
      exact hK _ s
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  · refine Filter.Eventually.of_forall fun s => ?_
    have hg : Filter.Tendsto (fun m => g (X s ω + cm m ω) * D ω s) Filter.atTop
        (nhds (g (X s ω + c ω) * D ω s)) :=
      Filter.Tendsto.mul_const _ ((hgc.tendsto _).comp (Filter.Tendsto.const_add _ hlim))
    have hstop : ∀ (υ : Ω → WithTop ℝ), Filter.Tendsto
        (fun m => LevyStochCalc.Probability.stopped υ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s)
        Filter.atTop
        (nhds (LevyStochCalc.Probability.stopped υ (fun ω s => g (X s ω + c ω) * D ω s) ω s)) := by
      intro υ
      unfold LevyStochCalc.Probability.stopped
      by_cases hs : ((s : ℝ) : WithTop ℝ) ≤ υ ω
      · simpa [hs] using hg
      · simp [hs]
    exact (hstop τ).sub (hstop σ)
end PathIntegral

section StochasticTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end StochasticTerm

section MultiChannel

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end MultiChannel

end LevyStochCalc.Brownian.Ito


