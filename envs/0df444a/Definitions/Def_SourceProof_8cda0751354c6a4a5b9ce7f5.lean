-- Prove2me | Definitions.Def_SourceProof_8cda0751354c6a4a5b9ce7f5
-- name    : SourceProof_8cda0751354c6a4a5b9ce7f5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:51:09.923155+00:00
-- url     : https://prove2.me/theorems/f14311ac-ffd7-4803-9b1a-f0a2fc23a39b
-- title:
--   LevyStochCalc source module: SourceProof_8cda0751354c6a4a5b9ce7f5
-- statement:
--   The original source theorem `LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_sub_of_dominated` comes from the `LevyStochCalc.Ito.StochasticIntegralLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_8cda0751354c6a4a5b9ce7f5 {H : ℕ → Ω → ℝ → ℝ} {H₀ : Ω → ℝ → ℝ}
    {g : Ω → ℝ → ℝ} {T : ℝ}
    (hHm : ∀ m, Measurable (Function.uncurry (H m)))
    (hH₀m : Measurable (Function.uncurry H₀)) (hgm : Measurable (Function.uncurry g))
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ‖H m ω s‖ ≤ g ω s)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) atTop (𝓝 0) := by
  set bound : Ω → ℝ≥0∞ :=
    fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume with hbound
  have hgsq : Measurable (Function.uncurry fun ω s => 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_const.mul (hgm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hFm : ∀ m, Measurable
      (Function.uncurry fun ω s => (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    fun m => (((hHm m).sub hH₀m).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hboundm : Measurable bound := hgsq.lintegral_prod_right'
  have hboundfin : ∫⁻ ω, bound ω ∂P ≠ ⊤ := by
    have hswap : ∫⁻ ω, bound ω ∂P
        = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
      exact MeasureTheory.lintegral_congr fun ω =>
        MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
    rw [hswap]
    exact ENNReal.mul_ne_top (by norm_num) hg.ne
  -- the pointwise data, gathered on one set of full measure
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)) ∧ ∀ m, ‖H m ω s‖ ≤ g ω s := by
    filter_upwards [hpt, (MeasureTheory.ae_all_iff).2 hdom] with ω hptω hdomω
    filter_upwards [hptω, (MeasureTheory.ae_all_iff).2 hdomω] with s h1 h2
    exact ⟨h1, h2⟩
  -- the limit function inherits the bound, so the difference is dominated by `4 g²`
  have hstep : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ m,
      (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hae] with ω hω
    filter_upwards [hω] with s hs m
    have hlim : ‖H₀ ω s‖ ≤ g ω s :=
      le_of_tendsto hs.1.norm (Filter.Eventually.of_forall fun k => hs.2 k)
    exact LevyStochCalc.Ito.IntegralLimit.sq_enorm_sub_le_of_norm_le (hs.2 m) hlim
  -- the inner limit, for almost every sample point
  have hinner : ∀ᵐ ω ∂P, Tendsto (fun m => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) atTop (𝓝 0) := by
    filter_upwards [hae, hstep, MeasureTheory.ae_lt_top hboundm hboundfin] with ω hω hstepω hfinω
    refine LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_of_dominated_tendsto_zero
      (fun s => 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun m => (Measurable.of_uncurry_left (hFm m)).aemeasurable) ?_ hfinω.ne ?_
    · exact fun m => by filter_upwards [hstepω] with s hs using hs m
    · filter_upwards [hω] with s hs using LevyStochCalc.Ito.IntegralLimit.tendsto_sq_enorm_sub hs.1
  refine LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_of_dominated_tendsto_zero bound
    (fun m => (hFm m).lintegral_prod_right'.aemeasurable) ?_ hboundfin hinner
  intro m
  filter_upwards [hstep] with ω hω
  exact MeasureTheory.lintegral_mono_ae (by filter_upwards [hω] with s hs using hs m)
end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Subsequence

section Brownian

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Brownian.IsBrownianFiltration W ℱ)
  (H : ℕ → Ω → ℝ → ℝ) (H₀ : Ω → ℝ → ℝ) (g : Ω → ℝ → ℝ)
  (hHm : ∀ m, Measurable (Function.uncurry (H m)))
  (hHp : ∀ m, Probability.ProgressivelyMeasurable ℱ (H m))
  (hHq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hH₀m : Measurable (Function.uncurry H₀))
  (hH₀p : Probability.ProgressivelyMeasurable ℱ H₀)
  (hH₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Brownian

section Compensated

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : ℕ → Ω → ℝ → E → ℝ) (φ₀ : Ω → ℝ → E → ℝ) (g : Ω → ℝ → E → ℝ)
  (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
  (hφp : ∀ m, Probability.MarkedProgressivelyMeasurable ℱ (φ m))
  (hφq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ m ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
  (hφ₀p : Probability.MarkedProgressivelyMeasurable ℱ φ₀)
  (hφ₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Compensated

section MarkCut

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m))

end MarkCut

end LevyStochCalc.Ito.IntegralLimit


