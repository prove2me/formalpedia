-- Prove2me | Definitions.Def_BetaCoskew_ThreeMoment_Supplement_PayoffProblem
-- name    : BetaCoskew_ThreeMoment_Supplement_PayoffProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:38:25.372638+00:00
-- url     : https://prove2.me/theorems/20025577-107e-4182-af7f-2fbb79fd3ca2
-- title:
--   §2.2, pp. 9–10 — full payoff problem, inverse marginal and constructed candidate
-- statement:
--   Let $P$ be the probability measure, $\tilde m$ the positive integrable pricing kernel, $u$ the outcome utility and $w$ the probability weighting. Feasible payoffs are exactly the published measurable, almost surely nonnegative payoffs with integrable cost and budget $\mathbb E[\tilde mX]=1$.
--
--   The inverse marginal utility $I(y)=(u')^{-1}(y)$ is the inverse on positive wealth, for $y>0$. The hypothesis and constructed payoff of Theorem 1 are
--
--   $$
--   \forall\mu>0:\quad\int_0^{1-} I\bigl(\mu\widehat N'_+(\bar w(p))\bigr)Q^-_{\tilde m}(1-p)\,dp<\infty,
--   \qquad
--   X_\lambda=I\bigl(\lambda\widehat N'_+(1-w(F_{\tilde m}(\tilde m)))\bigr).
--   $$
--   Optimality means feasibility and existence of a genuine extended RDU value dominating the genuine value of every feasible payoff, using the separately disclosed Stieltjes correction at atoms. It includes every competitor of (P′), including zero payoffs on events and atomic payoff laws. Existence of values for all those competitors is part of the optimality conclusion, not an additional premise.
--
--   **Formalization Note** The all-multiplier integral is expressed as Lebesgue integrability on $(0,1)$; its integrand is nonnegative under the source assumptions. No selected multiplier is assumed to exist. The restricted inverse uses positive marginal values and wealth; its unused value at nonpositive arguments is assigned zero. The model assumptions imply that marginal utility is a continuous strictly decreasing bijection on $(0,\infty)$. This problem does not use the base equilibrium definition or a finite portfolio-replication condition.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), pp. 9–10, (2) and Theorem 1, with the explicit atomic objective correction

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model
import Definitions.Def_BetaCoskew_ThreeMoment_Supplement_QuantileData
import Definitions.Def_BetaCoskew_ThreeMoment_Supplement_ConcaveEnvelope
import Definitions.Def_BetaCoskew_ThreeMoment_Supplement_Objective

namespace BetaCoskew.ThreeMoment.Supplement

open MeasureTheory ProbabilityTheory Set

/-- The inverse of marginal utility on positive wealth, used at positive
marginal values. Under UtilityAssumption, u′ is a bijection (0,∞) → (0,∞).
The value at nonpositive arguments is irrelevant and assigned 0. -/
noncomputable def inverseMarginal (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  if 0 < y then Function.invFunOn (deriv u) (Ioi 0) y else 0

/-- The paper's all-µ finiteness condition, as genuine Lebesgue integrability
on the open unit interval, including the exact Q⁻(1-p) weight. -/
def AllMuFinite (μ : Measure ℝ) (u w : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → IntegrableOn (fun p : ℝ =>
    inverseMarginal u (a * rightSlope (tailN μ w) (dualWeight w p)) *
      lowerQuantile μ (1 - p)) (Ioo 0 1)

/-- The constructed payoff in Theorem 1. In particular, neither an optimizer
nor an envelope nor a multiplier is supplied as free data here. -/
noncomputable def candidate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (mt : Ω → ℝ) (u w : ℝ → ℝ) (lam : ℝ) (ω : Ω) : ℝ :=
  inverseMarginal u (lam * rightSlope (tailN (P.map mt) w)
    (1 - w (cdf (P.map mt) (mt ω))))

/-- Full problem (P′), with the disclosed atomic correction to its objective.
Every feasible payoff has a genuine extended value and is compared; no
continuous-law, strictly positive-payoff or integrable-objective restriction. -/
def IsOptimal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (mt : Ω → ℝ) (u w : ℝ → ℝ) (hw : WeightingAssumption w) (X : Ω → ℝ) : Prop :=
  Feasible P mt X ∧ ∃ v : EReal,
    HasRduValue (P.map X) u w hw v ∧
    ∀ Y : Ω → ℝ, Feasible P mt Y → ∃ z : EReal,
      HasRduValue (P.map Y) u w hw z ∧ z ≤ v

end BetaCoskew.ThreeMoment.Supplement


