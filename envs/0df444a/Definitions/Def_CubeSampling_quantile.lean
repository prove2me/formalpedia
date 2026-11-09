-- Prove2me | Definitions.Def_CubeSampling_quantile
-- name    : CubeSampling_quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:23.141559+00:00
-- url     : https://prove2.me/theorems/a4481c16-8d5a-482e-bcfa-6a84109f964f
-- title:
--   Quantile $Q_{1-\delta}(Z) = \inf\{r \ge 0 : P(Z \le r) \ge 1-\delta\}$
-- statement:
--   For a nonnegative, possibly infinite random variable $Z$ and $\delta \in (0,1)$,
--   $$
--   Q_{1-\delta}(Z) = \inf\{r \ge 0 : P(Z \le r) \ge 1-\delta\}, \qquad \inf\emptyset = +\infty .
--   $$
--
--   **Formalization Note** $Z$ takes values in $[0,\infty]$ and $r$ ranges over the finite values only, as in the paper ($r$ is a real number); the infimum is taken in $[0,\infty]$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- The quantile `Q_{1−δ}(Z) = inf{r ≥ 0 : P(Z ≤ r) ≥ 1 − δ}`, `inf ∅ = +∞`, of a nonnegative,
possibly infinite random variable `Z` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3).

**Formalization Note** `r` ranges over the finite values of `[0, ∞]` only (the paper's `r` is a
real number); the infimum is taken in `[0, ∞]`, so it is `⊤` when no finite `r` qualifies. -/
noncomputable def quantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ≥0∞) (δ : ℝ) :
    ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | r ≠ ⊤ ∧ ENNReal.ofReal (1 - δ) ≤ μ {ω | Z ω ≤ r}}

end CubeSampling


