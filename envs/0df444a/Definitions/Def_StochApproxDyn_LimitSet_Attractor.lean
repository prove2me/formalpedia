-- Prove2me | Definitions.Def_StochApproxDyn_LimitSet_Attractor
-- name    : StochApproxDyn_LimitSet_Attractor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:02:39.083294+00:00
-- url     : https://prove2.me/theorems/81655a33-96ab-4955-bb40-1856bf86ccff
-- title:
--   Attractors and their basins
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(X,d)$ and write $\operatorname{dist}(x,A)=\inf_{a\in A}d(x,a)$. A subset $A\subset X$ is an **attractor** for $\Phi$ provided
--
--   1. $A$ is nonempty, compact and invariant ($\Phi_tA=A$ for all $t\ge0$); and
--   2. $A$ has a neighbourhood $W\subset X$ such that
--   $$\sup_{x\in W}\operatorname{dist}(\Phi_tx,A)\xrightarrow[t\to\infty]{}0,$$
--   that is, $\operatorname{dist}(\Phi_tx,A)\to0$ uniformly in $x\in W$.
--
--   The **basin** of $A$ is the set of all points $x$ such that $\operatorname{dist}(\Phi_tx,A)\to0$ as $t\to\infty$. An attractor $A\ne X$ is called proper.
--
--   Attractors are the sets toward which stochastic approximation algorithms converge with positive probability; their relation to chain recurrence (Proposition 5.3) is the key tool for locating limit sets.
--
--   **Formalization Note** "Neighbourhood of $A$" is `W ∈ 𝓝ˢ A` (W contains an open set containing $A$). The uniform convergence is written with $\varepsilon$: for every $\varepsilon>0$ there is $t_0$ with $\operatorname{dist}(\Phi_tx,A)<\varepsilon$ for all $t\ge t_0$ and all $x\in W$. Since $A$ is nonempty, `Metric.infDist` is the genuine distance to $A$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 22, Section 5.1 (definition of attractor, fundamental neighborhood, basin)

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Invariance

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- An *attractor* (Benaïm 1999, p. 22): `A` is nonempty, compact and invariant (`Φ_t A = A`),
and has a neighbourhood `W` such that `dist(Φ_t x, A) → 0` as `t → ∞` uniformly in `x ∈ W`. -/
def IsAttractor {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (A : Set X) : Prop :=
  A.Nonempty ∧ IsCompact A ∧ IsInvariantSet Φ A ∧
    ∃ W ∈ nhdsSet A, ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t → ∀ x ∈ W,
      Metric.infDist (Φ t x) A < ε

/-- The basin of `A`: all points `x` with `dist(Φ_t x, A) → 0` as `t → ∞`. -/
def basin {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (A : Set X) : Set X :=
  {x | Filter.Tendsto (fun t : ℝ≥0 => Metric.infDist (Φ t x) A) Filter.atTop (nhds 0)}

end StochApproxDyn.LimitSet


