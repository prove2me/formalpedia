-- Prove2me | Definitions.Def_NestedCRP_gemLaw
-- name    : NestedCRP_gemLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:33.062486+00:00
-- url     : https://prove2.me/theorems/06ae9523-cf0a-4b25-8151-deefb69bd48c
-- title:
--   Stick-breaking law $\mathrm{GEM}(m,\pi)$ and the weights $\theta_i$
-- statement:
--   The law of the stick variables of $\mathrm{GEM}(m,\pi)$: an i.i.d. sequence $V_0,V_1,\dots$ with each $V_i\sim\mathrm{Beta}(m\pi,(1-m)\pi)$. The stick-breaking weights are
--
--   $$
--   \theta_i=V_i\prod_{j<i}(1-V_j).
--   $$
--
--   These are the per-document distributions over levels in the hierarchical topic model.
--
--   **Formalization Note** Indices are 0-based: $V_i$ here is the paper's $V_{i+1}$.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §2.3, p.7:7 and p.7:8

import Mathlib
open MeasureTheory ProbabilityTheory

namespace NestedCRP

/-- The law of the stick variables of GEM(m, π): `V₀, V₁, …` independent, each
`Beta(mπ, (1 − m)π)`. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §2.3, p.7:7 and p.7:8.

**Formalization Note** Indices are 0-based: `U i` is the paper's `V_{i+1}`. -/
noncomputable def gemLaw (m pi : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => betaMeasure (m * pi) ((1 - m) * pi)

/-- The stick-breaking weight `θ_i = V_i ∏_{j<i} (1 − V_j)`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §2.3, p.7:7.

**Formalization Note** Indices are 0-based, so the product runs over `j < i`. -/
noncomputable def stick (U : ℕ → ℝ) (i : ℕ) : ℝ :=
  U i * ∏ j ∈ Finset.range i, (1 - U j)

end NestedCRP


