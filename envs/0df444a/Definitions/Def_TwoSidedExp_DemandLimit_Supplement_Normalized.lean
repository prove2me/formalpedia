-- Prove2me | Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Normalized
-- name    : TwoSidedExp_DemandLimit_Supplement_Normalized
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:19:08.131895+00:00
-- url     : https://prove2.me/theorems/6da6560b-0f9e-4311-ae99-ef3e4f2c6e3f
-- title:
--   Normalized finite-market process and its CTMC law
-- statement:
--   The normalized process is
--
--   $$Y_t^{(N)}(\theta)=\sigma_t^{(N)}(\theta)/N.$$
--
--   The count process has the published general finite-dimensional CTMC law with the marketplace generator (3)–(5) and a point-mass initial law at the specified deterministic state σ₀^(N). Its coordinates are measurable, and its normalized paths are right-continuous on nonnegative times. These are the processes compared with the ODE in Theorem 2; the law imposes no approximation estimate.
--
--   **Formalization Note** Every finite-market size may use its own probability space. Requiring right-continuity is the usual path convention for the source's continuous-time jump chain; finite-dimensional distributions alone would allow exceptional-time modifications that change a time supremum. The outer probability in Theorem 2 agrees with the ordinary measurable probability for these paths.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, pp. 9–10, 12–13, §3, §4.3

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_FiniteMarket
import Definitions.Def_MissionAbort_HasRateChainLaw

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

/-- §4.3, p. 12: Y^(N) = σ^(N)/N. -/
noncomputable def normalized {N : ℕ} (F : FiniteMarket Γ Θ N) (σ : MarketState F) : Θ → ℝ :=
  fun θ => (σ θ : ℕ) / (N : ℝ)

/-- The published general CTMC law with point-mass initial distribution, plus measurable
coordinates and right-continuous paths. The latter excludes changes on random exceptional times
invisible to finite-dimensional laws. It imposes no bound on the approximation error. -/
def MarketChain {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Model Γ Θ) (hM : M.Standing) {N : ℕ} (F : FiniteMarket Γ Θ N)
    (tau : ℝ) (σ₀ : MarketState F) (X : ℝ → Ω → MarketState F) : Prop := by
  classical
  exact MissionAbort.HasRateChainLaw (fun σ => if σ = σ₀ then 1 else 0)
      (generator M hM F tau) (Set.Ici 0) X μ ∧
    (∀ t, 0 ≤ t → Measurable (X t)) ∧
    (∀ ω t, 0 ≤ t → ContinuousWithinAt (fun r => normalized F (X r ω)) (Set.Ici t) t)

end TwoSidedExp.DemandLimit.Supplement


