-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
-- name    : LevyStochCalc_Ito_ItoLevyProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:40.55517+00:00
-- url     : https://prove2.me/theorems/e6aa873b-611c-47f7-aae6-7fd68b1f93f4
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_Setting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô–Lévy processes with an explicit decomposition

An Itô–Lévy process is a path with a named drift, a named diffusion vector and a named jump
integrand over one filtration, none of them required to be a function of the path:
`X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ`. A jump-diffusion solution is one
coordinatewise, with the integrands the coefficients evaluated along the path.

The decomposition is asserted almost surely at each fixed time, not outside a single null set for
all times: the two stochastic integrals are `L²` limits, defined up to modification, so a
statement for all times simultaneously is a statement about a chosen càdlàg modification and
belongs with that modification.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Ito.Setting

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-- A path with an explicit Itô–Lévy decomposition over one filtration: a drift `b`, a diffusion
vector `σ` and a jump integrand `γ`, each progressive for that filtration and admissible for the
corresponding integral, with

`X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ`

almost surely at every `t ≥ 0`. -/
structure IsItoLevyProcess {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E}
    [SigmaFinite ν] {d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (X : ℝ → Ω → ℝ) (X₀ : Ω → ℝ) (b : ℝ → Ω → ℝ) (σ : ℝ → Ω → (Fin d → ℝ))
    (γ : Ω → ℝ → E → ℝ) : Prop where
  /-- The path is jointly measurable. -/
  measurable_path : Measurable (Function.uncurry X)
  /-- The diffusion vector is jointly measurable in each coordinate. -/
  σ_meas : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j)
  /-- The diffusion vector is progressively measurable in each coordinate. -/
  σ_prog : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j
  /-- The diffusion vector has finite energy on every horizon, in each coordinate. -/
  σ_sq : ∀ j : Fin d, ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
  /-- The jump integrand is jointly measurable. -/
  γ_meas : Measurable fun p : Ω × ℝ × E => γ p.1 p.2.1 p.2.2
  /-- The jump integrand is marked progressively measurable. -/
  γ_prog : Probability.MarkedProgressivelyMeasurable ℱ γ
  /-- The jump integrand has finite energy on every horizon. -/
  γ_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
  /-- The decomposition, almost surely at each fixed nonnegative time. -/
  decomposition : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P,
    X t ω = X₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b s ω)
      + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW σ
          σ_meas σ_prog σ_sq t ω
      + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN γ γ_meas γ_prog γ_sq t ω
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

/-- **Every coordinate of a jump-diffusion solution is an Itô–Lévy process**, with the integrands
the coefficients evaluated along the path. -/
theorem JumpDiffusion.exists_isItoLevyProcess
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν} {coeffs : JumpDiffusionCoeffs n d E}
    {x₀ : Fin n → ℝ} (Xs : JumpDiffusion W N coeffs x₀) (i : Fin n) :
    ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
      (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ),
      IsItoLevyProcess W N ℱ hℱW hℱN (fun t ω => Xs.X t ω i) (fun _ => x₀ i)
        (fun s ω => coeffs.μ s (Xs.X s ω) i) (fun s ω => coeffs.σ s (Xs.X s ω) i)
        (fun ω s e => coeffs.γ s (Xs.X s ω) e i) := by
  obtain ⟨ℱ, hℱW, hℱN, hσm, hσp, hσq, hγm, hγp, hγq, heq⟩ := Xs.is_solution
  refine ⟨ℱ, hℱW, hℱN, ?_, fun j => hσm i j, fun j => hσp i j, fun j => hσq i j, hγm i, hγp i,
    hγq i, ?_⟩
  · exact Xs.measurable_path.eval
  · intro t ht
    filter_upwards [heq t ht] with ω hω
    exact hω i
end LevyStochCalc.Ito.Setting


