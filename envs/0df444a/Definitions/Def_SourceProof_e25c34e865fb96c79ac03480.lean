-- Prove2me | Definitions.Def_SourceProof_e25c34e865fb96c79ac03480
-- name    : SourceProof_e25c34e865fb96c79ac03480
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:45:57.277947+00:00
-- url     : https://prove2.me/theorems/a0ea6881-0d76-4eb1-93b0-70a46c778e0e
-- title:
--   LevyStochCalc source module: SourceProof_e25c34e865fb96c79ac03480
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_comp_shift` comes from the `LevyStochCalc.Ito.ItoFormulaRandomShift` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_e25c34e865fb96c79ac03480 {n : ℕ} {X : ℝ → Ω → Fin n → ℝ}
    {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g) {K : ℝ} (hK : ∀ z, |g z| ≤ K)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    {c : Ω → Fin n → ℝ} {cm : ℕ → Ω → Fin n → ℝ}
    (hcm : ∀ m, Measurable (cm m)) (hc : Measurable c)
    (hlim : ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (nhds (c ω)))
    {T : ℝ} (hHq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  have h2K0 : (0 : ℝ) ≤ 2 * K := by linarith
  set C : ℝ≥0∞ := ENNReal.ofReal ((2 * K) ^ 2) with hC
  -- the integrand is dominated by a constant multiple of the energy density
  have hdom : ∀ (m : ℕ) (ω : Ω) (s : ℝ),
      (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro m ω s
    refine LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le h2K0 ?_
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (LevyStochCalc.Brownian.Ito.abs_sub_le_two_mul_of_abs_le hK _ _) (abs_nonneg _)
  -- measurability of each stage and of the dominating density
  have hXcm : ∀ m : ℕ, Measurable (Function.uncurry fun ω s => X s ω + cm m ω) := by
    intro m
    exact hXm.add ((hcm m).comp measurable_fst)
  have hXc : Measurable (Function.uncurry fun ω s => X s ω + c ω) :=
    hXm.add (hc.comp measurable_fst)
  have hFm : ∀ m : ℕ, Measurable (Function.uncurry fun ω s =>
      (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2) := by
    intro m
    exact ((((hgc.measurable.comp (hXcm m)).mul hHm).sub
      ((hgc.measurable.comp hXc).mul hHm)).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hBm : Measurable (Function.uncurry fun ω s => C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_const.mul (hHm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  -- the dominating density has finite total mass
  have hBfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := by
    have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = C * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp [hC] : C ≠ ⊤)]
      exact MeasureTheory.lintegral_congr fun ω => by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp [hC] : C ≠ ⊤)]
    rw [hswap]
    exact ENNReal.mul_ne_top (by simp [hC]) hHq
  -- pointwise convergence of the integrand
  have hptw : ∀ (ω : Ω) (s : ℝ), Filter.Tendsto
      (fun m => (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
    intro ω s
    have h1 : Filter.Tendsto (fun m => g (X s ω + cm m ω) * H ω s
        - g (X s ω + c ω) * H ω s) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun m => g (X s ω + cm m ω)) Filter.atTop
          (nhds (g (X s ω + c ω))) :=
        (hgc.tendsto _).comp (Filter.Tendsto.const_add _ (hlim ω))
      simpa using (h2.mul_const (H ω s)).sub_const (g (X s ω + c ω) * H ω s)
    have h3 : Filter.Tendsto (fun m => (‖g (X s ω + cm m ω) * H ω s
        - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0)) Filter.atTop (nhds 0) := by
      simpa using h1.nnnorm
    have h5 : Filter.Tendsto (fun m => (‖g (X s ω + cm m ω) * H ω s
        - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0) ^ 2) Filter.atTop (nhds 0) := by
      simpa using h3.pow 2
    have h6 := ENNReal.tendsto_coe.2 h5
    simpa [ENNReal.coe_pow] using h6
  -- dominated convergence, first in the time variable and then in the sample point
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto
      (fun m => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
    have hfin : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T,
        C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
      MeasureTheory.ae_lt_top hBm.lintegral_prod_right' hBfin
    filter_upwards [hfin] with ω hω
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞)
      ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2) ?_ ?_ hω.ne ?_
    · exact fun m => (Measurable.of_uncurry_left (hFm m)).aemeasurable
    · exact fun m => Filter.Eventually.of_forall fun s => hdom m ω s
    · exact Filter.Eventually.of_forall fun s => hptw ω s
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ?_ ?_ hBfin hinner
  · exact fun m => (hFm m).lintegral_prod_right'.aemeasurable
  · exact fun m => Filter.Eventually.of_forall fun ω =>
      MeasureTheory.lintegral_mono fun s => hdom m ω s
end Energy

section PathIntegral

variable {Ω : Type u}

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


