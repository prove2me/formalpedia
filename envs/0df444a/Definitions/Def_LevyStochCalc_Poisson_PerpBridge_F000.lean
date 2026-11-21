-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PerpBridge_F000
-- name    : LevyStochCalc_Poisson_PerpBridge_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:34.330023+00:00
-- url     : https://prove2.me/theorems/b886f4bc-dc0e-48bb-983a-7286a3ef10e3
-- title:
--   Source declarations: LevyStochCalc.Poisson.PerpBridge
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PerpBridge. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The perp bridge for the compensated integral

A weight measurable before a horizon does not see the compensated integral beyond it: the
increment is a martingale increment, and conditioning on the horizon kills it. So orthogonality
to every admissible integrand over `[0, T]` extends to every admissible integrand over any
larger horizon. This is the marked counterpart of the Brownian perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Congr

/-- **Two admissible integrands agreeing over the horizon integrate to the same thing there.** -/
theorem stochasticIntegral_ae_congr (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (φ ψ : Ω → ℝ → E → ℝ)
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hψp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) (h : ∀ ω s e, s ∈ Set.Icc (0 : ℝ) T → φ ω s e = ψ ω s e) :
    stochasticIntegral N ℱ hℱ φ hφm hφp hφq T
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T := by
  have hiso := itoIsometry_diff_compensated N ℱ hℱ φ ψ hφm hψm hφp hψp hφq hψq T hT
  have hzero : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) = 0 := by
    have hin : ∀ ω : Ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume) = 0 := by
      intro ω
      have heq : ∀ s ∈ Set.Icc (0 : ℝ) T,
          (∫⁻ e, (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) = 0 := by
        intro s hs
        have hpt : ∀ e : E, (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 = 0 := by
          intro e
          rw [h ω s e hs, sub_self]
          simp
        simp [hpt]
      rw [setLIntegral_congr_fun measurableSet_Icc heq]
      simp
    simp [hin]
  rw [hzero] at hiso
  have hφL : MemLp (stochasticIntegral N ℱ hℱ φ hφm hφp hφq T) 2 P :=
    stochasticIntegral_memLp N ℱ hℱ φ hφm hφp hφq T
  have hψL : MemLp (stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T) 2 P :=
    stochasticIntegral_memLp N ℱ hℱ ψ hψm hψp hψq T
  have hae : AEMeasurable (fun ω => (‖stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hφL.sub hψL).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω = 0 := by simpa using h2
  linarith
end Congr

section Clip

namespace MarkedHorizonIntegrand

/-- An admissible integrand over a larger horizon, clipped to `[0, T]`. -/
noncomputable def clip {R : ℝ} (G : MarkedHorizonIntegrand P ν ℱ R) {T : ℝ} (hTR : T ≤ R) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun ω s e) s
  measurable_uncurry := by
    have hrw : (fun p : Ω × ℝ × E =>
          (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun p.1 p.2.1 p.2.2) p.2.1)
        = {p : Ω × ℝ × E | p.2.1 ∈ Set.Icc (0 : ℝ) T}.indicator
          (fun p => G.toFun p.1 p.2.1 p.2.2) := by
      funext p
      by_cases hp : p.2.1 ∈ Set.Icc (0 : ℝ) T
      · have hp' : p ∈ {q : Ω × ℝ × E | q.2.1 ∈ Set.Icc (0 : ℝ) T} := hp
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      · have hp' : p ∉ {q : Ω × ℝ × E | q.2.1 ∈ Set.Icc (0 : ℝ) T} := hp
        rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
    rw [hrw]
    exact G.measurable_uncurry.indicator (measurable_snd.fst measurableSet_Icc)
  progressive :=
    Probability.MarkedProgressivelyMeasurable.indicator_time G.progressive measurableSet_Icc
  vanishing := fun _ _ _ hs => Set.indicator_of_notMem hs _
  energy_ne_top := by
    have heq : markedEnergy P ν T (fun ω s e =>
        (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun ω s e) s)
        = markedEnergy P ν T G.toFun := by
      simp only [markedEnergy]
      refine lintegral_congr fun ω => ?_
      refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      refine lintegral_congr fun e => ?_
      rw [Set.indicator_of_mem hs]
    rw [heq]
    refine ne_top_of_le_ne_top G.energy_ne_top ?_
    simp only [markedEnergy]
    refine lintegral_mono fun ω => ?_
    exact lintegral_mono_set (Set.Icc_subset_Icc le_rfl hTR)
/-- The clipped integrand's integral is the integral of the original over the shorter horizon. -/
theorem integral_clip (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {R : ℝ}
    (G : MarkedHorizonIntegrand P ν ℱ R) {T : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    (G.clip hTR).integral N hℱ
      =ᵐ[P] stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
        G.sq_int_global T :=
  stochasticIntegral_ae_congr N hℱ (G.clip hTR).toFun G.toFun (G.clip hTR).measurable_uncurry
    G.measurable_uncurry (G.clip hTR).progressive G.progressive (G.clip hTR).sq_int_global
    G.sq_int_global hT (by
      intro ω s e hs
      change (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun ω s e) s = G.toFun ω s e
      exact Set.indicator_of_mem hs _)
end MarkedHorizonIntegrand

end Clip

section Bridge

end Bridge

end LevyStochCalc.Poisson.Compensated


