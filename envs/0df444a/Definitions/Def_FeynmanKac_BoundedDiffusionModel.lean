-- Prove2me | Definitions.Def_FeynmanKac_BoundedDiffusionModel
-- name    : FeynmanKac_BoundedDiffusionModel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T21:13:38.071648+00:00
-- url     : https://prove2.me/theorems/49991672-2540-46aa-831f-d86b4061f7fb
-- title:
--   Clock-augmented Brownian diffusion model for Feynman–Kac
-- statement:
--   A genuine real Brownian diffusion is represented by the first coordinate of a two-dimensional time-homogeneous Itô diffusion, whose second coordinate is the deterministic clock. The augmented drift is (μ(x,t),1) and diffusion coefficient is (σ(x,t),0). The structure carries a canonical IsDiffusion witness, starting state and horizon, a nonnegative potential, running source and terminal payoff. It deliberately assumes no Itô conclusion, martingale, PDE solution or Feynman–Kac representation. The dependent space-time Itô theorem must still be proved using the upstream vector Itô theory. This source is a compilation candidate pending remote elaboration. The canonical variant explicitly bounds and assumes continuity of both augmented coefficients, potential, running source, and terminal payoff, with nonnegative potential. These are independent hypotheses needed for integrability and verification.
-- source:
--   Accepted Prove2Me diffusion-existence theorem 7af98979-05ab-4014-86ce-c2315b88e573; Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
import Definitions.Def_FeynmanKac_PathDiscount

open MeasureTheory
open LevyStochCalc.Brownian
open LevyStochCalc.Brownian.Multidim
open FunctionalInequalities.Probability.Diffusion

/-!
A non-circular diffusion-data model. The space-time process has two coordinates:
the first is the diffusion state, the second is the deterministic clock.
The Brownian SDE property is witnessed by an upstream IsDiffusion structure.
No Itô formula, martingale, PDE solution or expectation identity is assumed.
-/
structure FeynmanKac.BoundedDiffusionModel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  initialTime : ℝ
  terminalTime : ℝ
  initialState : ℝ
  initialTime_nonneg : 0 ≤ initialTime
  horizon_nonneg : initialTime ≤ terminalTime
  drift : ℝ → ℝ → ℝ
  volatility : ℝ → ℝ → ℝ
  potential : ℝ → ℝ → ℝ
  runningSource : ℝ → ℝ → ℝ
  terminalPayoff : ℝ → ℝ
  potential_nonneg : ∀ x t, 0 ≤ potential x t
  potential_continuous : Continuous (fun z : ℝ × ℝ => potential z.1 z.2)
  potential_bounded : ∃ B : ℝ, ∀ x t, |potential x t| ≤ B
  source_continuous : Continuous (fun z : ℝ × ℝ => runningSource z.1 z.2)
  source_bounded : ∃ B : ℝ, ∀ x t, |runningSource x t| ≤ B
  terminalPayoff_continuous : Continuous terminalPayoff
  terminalPayoff_bounded : ∃ B : ℝ, ∀ x, |terminalPayoff x| ≤ B
  brownian : MultidimBrownianMotion P 1
  filtration : Filtration ℝ ‹MeasurableSpace Ω›
  brownianFiltration : ∀ k, IsBrownianFiltration (brownian.W k) filtration
  augmentedDrift : (Fin 2 → ℝ) → Fin 2 → ℝ
  augmentedVolatility : (Fin 2 → ℝ) → Fin 1 → Fin 2 → ℝ
  initialCoordinates : Fin 2 → ℝ
  initialCoordinates_space : initialCoordinates 0 = initialState
  initialCoordinates_clock : initialCoordinates 1 = initialTime
  augmentedDrift_space : ∀ z, augmentedDrift z 0 = drift (z 0) (z 1)
  augmentedDrift_clock : ∀ z, augmentedDrift z 1 = 1
  augmentedVolatility_space :
    ∀ z, augmentedVolatility z 0 0 = volatility (z 0) (z 1)
  augmentedVolatility_clock : ∀ z, augmentedVolatility z 0 1 = 0
  augmentedDrift_continuous : Continuous augmentedDrift
  augmentedDrift_bounded : ∃ B : ℝ, ∀ z, ‖augmentedDrift z‖ ≤ B
  augmentedVolatility_continuous : Continuous (fun z => augmentedVolatility z 0)
  augmentedVolatility_bounded : ∃ B : ℝ, ∀ z, ‖augmentedVolatility z 0‖ ≤ B
  augmentedPath : ℝ → Ω → Fin 2 → ℝ
  isDiffusion :
    IsDiffusion brownian filtration brownianFiltration
      augmentedDrift augmentedVolatility initialCoordinates augmentedPath

namespace FeynmanKac.BoundedDiffusionModel

/-- The real state of a clock-augmented SDE at absolute time s. -/
def path {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : BoundedDiffusionModel P)
    (s : ℝ) (ω : Ω) : ℝ :=
  m.augmentedPath (s - m.initialTime) ω 0

/-- Cumulative potential discount along the actual SDE state trajectory. -/
noncomputable def pathDiscount {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BoundedDiffusionModel P) (s : ℝ) (ω : Ω) : ℝ :=
  FeynmanKac.pathDiscount m.path m.potential m.initialTime s ω

end FeynmanKac.BoundedDiffusionModel


