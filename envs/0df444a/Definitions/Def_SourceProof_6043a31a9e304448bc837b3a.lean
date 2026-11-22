-- Prove2me | Definitions.Def_SourceProof_6043a31a9e304448bc837b3a
-- name    : SourceProof_6043a31a9e304448bc837b3a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:51:41.352541+00:00
-- url     : https://prove2.me/theorems/3645843b-4f77-4859-8be4-55901ee7691d
-- title:
--   LevyStochCalc source module: SourceProof_6043a31a9e304448bc837b3a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_sub_mark_of_dominated` comes from the `LevyStochCalc.Ito.StochasticIntegralLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F001

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

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_6043a31a9e304448bc837b3a {φ : ℕ → Ω → ℝ → E → ℝ}
    {φ₀ : Ω → ℝ → E → ℝ} {g : Ω → ℝ → E → ℝ} {T : ℝ}
    (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
    (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
    (hgm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖φ m ω s e‖ ≤ g ω s e)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) atTop (𝓝 0) := by
  have h4 : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hgsq : Measurable fun p : Ω × ℝ × E => 4 * (‖g p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    measurable_const.mul (hgm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hFm : ∀ m, Measurable fun p : Ω × ℝ × E =>
      (‖φ m p.1 p.2.1 p.2.2 - φ₀ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    fun m => (((hφm m).sub hφ₀m).nnnorm.coe_nnreal_ennreal).pow_const 2
  set bound : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume with hbounddef
  have hboundm : Measurable bound :=
    LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2) hgsq T
  have hboundval : ∀ ω, bound ω
      = 4 * ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
    intro ω
    rw [hbounddef, ← MeasureTheory.lintegral_const_mul' _ _ h4]
    exact MeasureTheory.lintegral_congr fun s => MeasureTheory.lintegral_const_mul' _ _ h4
  have hboundfin : ∫⁻ ω, bound ω ∂P ≠ ⊤ := by
    have hswap : ∫⁻ ω, bound ω ∂P = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
      simp_rw [hboundval]
      exact MeasureTheory.lintegral_const_mul' _ _ h4
    rw [hswap]
    exact ENNReal.mul_ne_top h4 hg.ne
  -- the pointwise data, gathered on one set of full measure
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)) ∧ ∀ m, ‖φ m ω s e‖ ≤ g ω s e := by
    filter_upwards [hpt, (MeasureTheory.ae_all_iff).2 hdom] with ω hptω hdomω
    filter_upwards [hptω, (MeasureTheory.ae_all_iff).2 hdomω] with s hpts hdoms
    filter_upwards [hpts, (MeasureTheory.ae_all_iff).2 hdoms] with e h1 h2
    exact ⟨h1, h2⟩
  -- the limit integrand inherits the bound, so the difference is dominated by `4 g²`
  have hstep : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν, ∀ m,
      (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hae] with ω hω
    filter_upwards [hω] with s hs
    filter_upwards [hs] with e he m
    have hlim : ‖φ₀ ω s e‖ ≤ g ω s e :=
      le_of_tendsto he.1.norm (Filter.Eventually.of_forall fun k => he.2 k)
    exact LevyStochCalc.Ito.IntegralLimit.sq_enorm_sub_le_of_norm_le (he.2 m) hlim
  -- the mark integral vanishes at almost every sample point and time
  have hmark : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => ∫⁻ e, (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) atTop (𝓝 0) := by
    filter_upwards [hae, hstep, MeasureTheory.ae_lt_top hboundm hboundfin] with ω hω hstepω hfinω
    have hsfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (∫⁻ e, 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) < ⊤ :=
      MeasureTheory.ae_lt_top (LevyStochCalc.Ito.IntegralLimit.measurable_section_markLIntegral
        (f := fun ω s e => 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2) hgsq ω) hfinω.ne
    filter_upwards [hω, hstepω, hsfin] with s hs hsteps hfins
    refine LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_of_dominated_tendsto_zero
      (fun e => 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2) (fun m => ?_) ?_ hfins.ne ?_
    · have hcurry : Measurable fun e => (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
        (hFm m).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      exact hcurry.aemeasurable
    · exact fun m => by filter_upwards [hsteps] with e he using he m
    · filter_upwards [hs] with e he using LevyStochCalc.Ito.IntegralLimit.tendsto_sq_enorm_sub he.1
  -- the time integral vanishes at almost every sample point
  have hinner : ∀ᵐ ω ∂P, Tendsto (fun m => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume) atTop (𝓝 0) := by
    filter_upwards [hmark, hstep, MeasureTheory.ae_lt_top hboundm hboundfin] with ω hω hstepω hfinω
    refine LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_of_dominated_tendsto_zero
      (fun s => ∫⁻ e, 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      (fun m => (LevyStochCalc.Ito.IntegralLimit.measurable_section_markLIntegral
        (f := fun ω s e => (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2) (hFm m) ω).aemeasurable)
      ?_ hfinω.ne hω
    intro m
    filter_upwards [hstepω] with s hs
    exact MeasureTheory.lintegral_mono_ae (by filter_upwards [hs] with e he using he m)
  refine LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_of_dominated_tendsto_zero bound (fun m => ?_) ?_ hboundfin hinner
  · exact (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2) (hFm m) T).aemeasurable
  · intro m
    filter_upwards [hstep] with ω hω
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [hω] with s hs
    exact MeasureTheory.lintegral_mono_ae (by filter_upwards [hs] with e he using he m)
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


