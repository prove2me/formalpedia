-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonDivergence
-- name    : LinearHashingPoissonesque_ExpectedLoads_PoissonDivergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:01:19.254745+00:00
-- url     : https://prove2.me/theorems/b4b3cb0d-e480-4c08-bfeb-29a191a33207
-- title:
--   Scalar divergence between two Poisson means
-- statement:
--   For $\mu>0$ and $t\ge0$, define the scalar Poisson divergence by
--
--   $$D(t,\mu)=t\log(t/\mu)-t+\mu,\qquad D(0,\mu)=\mu.$$
--
--   The first argument is the candidate load level, and the second is the mean. This deterministic analytic function specifies the comparison thresholds; it does not require constructing Poisson random variables or a Poisson process.
--
--   **Formalization Note** Multiplication by $t=0$ implements the source convention $0\log0=0$. Outside the stated domain Lean's real logarithm and division are total, but no source claim uses those extra values.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.8, Section 2, Poisson Random Variables; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Mathlib

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Section 2, p.8: scalar Poisson divergence. Real.log 0 = 0 implements 0 log 0 = 0.
Its source domain is t ≥ 0 and μ > 0. -/
noncomputable def poissonDivergence (t mu : ℝ) : ℝ :=
  t * Real.log (t / mu) - t + mu

end LinearHashingPoissonesque.ExpectedLoads


