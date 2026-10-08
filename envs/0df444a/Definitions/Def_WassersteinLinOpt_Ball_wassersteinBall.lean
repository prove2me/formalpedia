-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
-- name    : WassersteinLinOpt_Ball_wassersteinBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T15:00:19.589027+00:00
-- url     : https://prove2.me/theorems/100aecc1-8aa7-4c05-b930-d6fbfed28e55
-- title:
--   Wasserstein ball $\mathcal B_r(\nu)$ (Eq. (2))
-- statement:
--   For a Borel probability measure $\nu$ on a metric space $(X,d)$, $p\ge 1$ and a radius $r$, the **Wasserstein ball** is
--
--   $$\mathcal B_r(\nu)=\{\mu\in\mathcal P(X): W_p(\mu,\nu)\le r\},$$
--
--   where $\mathcal P(X)$ is the set of Borel probability measures on $X$ and $W_p$ is the Wasserstein distance of Eq. (1). The paper takes $r>0$; every theorem using the ball carries $0<r$ as a hypothesis.
--
--   **Formalization Note.** The ball is a subset of Mathlib's `ProbabilityMeasure X` (whose topology is the weak topology of convergence against bounded continuous functions), and the constraint is `wassersteinDist p μ ν ≤ ENNReal.ofReal r` in `ℝ≥0∞`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1108, Eq. (2)

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- The Wasserstein ball of radius `r` centred at `ν`, Eq. (2), p. 1108:
`𝓑_r(ν) = {μ ∈ 𝒫(X) : W_p(μ, ν) ≤ r}`. -/
def wassersteinBall {X : Type*} [MetricSpace X] [MeasurableSpace X] (p r : ℝ)
    (ν : ProbabilityMeasure X) : Set (ProbabilityMeasure X) :=
  {μ | wassersteinDist p μ ν ≤ ENNReal.ofReal r}

end WassersteinLinOpt.Ball


