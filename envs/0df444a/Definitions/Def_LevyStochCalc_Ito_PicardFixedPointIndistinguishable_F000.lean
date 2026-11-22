-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardFixedPointIndistinguishable_F000
-- name    : LevyStochCalc_Ito_PicardFixedPointIndistinguishable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:12:05.201789+00:00
-- url     : https://prove2.me/theorems/cfdf477c-d4cf-4e41-8492-01e1e6fe5def
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardFixedPointIndistinguishable
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardFixedPointIndistinguishable. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F000
import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F001
import Definitions.Def_SourceProof_d86b93a1720501bd3dee4555

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Indistinguishability of jump-diffusion solutions

`JumpDiffusion.exists_unique` compares two solutions time by time, so the exceptional set depends
on the time. Almost every path of a `JumpDiffusion` is right-continuous on `[0, ∞)`, so one set of
full measure serves all times at once: the clamped rationals `max 0 q`, `q : ℚ`, form a countable
subfamily of `[0, ∞)` whose exceptional sets have null union and which approaches every `t ≥ 0`
from the right.

## Main statements

* `LevyStochCalc.Ito.Setting.JumpDiffusion.indistinguishable_of_ae_eq` — two jump diffusions that
  agree almost surely at each time of `[0, ∞)` agree at every time of `[0, ∞)` on a single set of
  full measure.
* `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique_indistinguishable` — existence together
  with uniqueness in the indistinguishability form.

## Source

* Applebaum, "Lévy Processes and Stochastic Calculus", 2nd ed., Cambridge University Press, 2009,
  Theorem 6.2.9.
* Ikeda & Watanabe, "Stochastic Differential Equations and Diffusion Processes", North-Holland,
  1989, Chapter IV.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Setting
namespace JumpDiffusion

/-- Two jump diffusions agreeing almost surely at each time of `[0, ∞)` are indistinguishable on
`[0, ∞)`: on a single set of full measure they agree at every `t ≥ 0`. -/
theorem indistinguishable_of_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
    {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
    (jd jd' : JumpDiffusion W N coeffs x₀)
    (h : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → jd.X t ω = jd'.X t ω := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ,
      jd.X (max (0 : ℝ) (q : ℝ)) ω = jd'.X (max (0 : ℝ) (q : ℝ)) ω :=
    ae_all_iff.mpr fun q => h _ (le_max_left _ _)
  filter_upwards [hrat, jd.cadlag_paths, jd'.cadlag_paths] with ω hω hc hc'
  intro t ht
  have hex : ∀ k : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < t + 1 / ((k : ℝ) + 1) := by
    intro k
    refine exists_rat_btwn ?_
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  choose q hq1 hq2 using hex
  have hq0 : ∀ k, (0 : ℝ) ≤ (q k : ℝ) := fun k => le_of_lt (lt_of_le_of_lt ht (hq1 k))
  have hclamp : ∀ k, max (0 : ℝ) (q k : ℝ) = (q k : ℝ) := fun k => max_eq_right (hq0 k)
  have htend : Tendsto (fun k : ℕ => (q k : ℝ)) atTop (𝓝 t) := by
    have hcst : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    have hz : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using hcst.add hz
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => (hq1 k).le) (fun k => (hq2 k).le)
  have hsw : Tendsto (fun k : ℕ => (q k : ℝ)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
      (Eventually.of_forall fun k => hq1 k)
  have hl : Tendsto (fun k : ℕ => jd.X (q k : ℝ) ω) atTop (𝓝 (jd.X t ω)) :=
    (hc t ht).1.comp hsw
  have hl' : Tendsto (fun k : ℕ => jd'.X (q k : ℝ) ω) atTop (𝓝 (jd'.X t ω)) :=
    (hc' t ht).1.comp hsw
  refine tendsto_nhds_unique (hl.congr fun k => ?_) hl'
  have hk := hω (q k)
  rwa [hclamp k] at hk
/-- **Existence and uniqueness of the jump-diffusion SDE, with indistinguishable solutions.**
Under Lipschitz and regularity hypotheses on `(μ, σ, γ)`, and relative to a filtration `ℱ`
satisfying the usual conditions for which every coordinate of `W` is a Brownian motion and `N` a
Poisson random measure, the jump-diffusion SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`,  `X_0 = x_0`

has a solution, and any solution of the equation relative to the same `ℱ` agrees with it at every
`t ≥ 0` on a single set of full measure. -/
theorem exists_unique_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    {L : ℝ} (hL : JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs ν) :
    ∃ jd : JumpDiffusion W N coeffs x₀,
      (∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd.X T)
        ∧ ∀ jd' : JumpDiffusion W N coeffs x₀,
            (∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd'.X T) →
              ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → jd.X t ω = jd'.X t ω := by
  obtain ⟨jd, hjd, huniq⟩ :=
    _root_.Prove2MeSourceProof.h_d86b93a1720501bd3dee4555 W N ℱ hℱW hℱN hℱ0 hnull coeffs x₀ hL hReg
  exact ⟨jd, hjd, fun jd' hjd' => indistinguishable_of_ae_eq jd jd' (huniq jd' hjd')⟩
end JumpDiffusion
end LevyStochCalc.Ito.Setting


