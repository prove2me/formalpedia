-- Prove2me | Definitions.Def_NestedCRP_dirichletMeasure
-- name    : NestedCRP_dirichletMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:30.506986+00:00
-- url     : https://prove2.me/theorems/fd2b14d9-ff84-40e9-9202-581d33cb772f
-- title:
--   Dirichlet distribution $\mathrm{Dir}(\alpha)$
-- statement:
--   For a finite index set $\iota$ and parameters $\alpha_i>0$, the Dirichlet distribution $\mathrm{Dir}(\alpha)$ is the law on the simplex of $\mathbb R^\iota$ of the normalized vector
--
--   $$
--   \Bigl(\frac{X_i}{\sum_{j} X_j}\Bigr)_{i\in\iota},\qquad X_i\sim\mathrm{Gamma}(\alpha_i,1)\ \text{independent.}
--   $$
--
--   This is the topic prior of the model, in its symmetric case $\alpha_i=\eta$, and it is reusable for any finite-dimensional Dirichlet law.
--
--   **Formalization Note** The paper names the law without a formula. The normalized-Gamma form is a standard construction and needs no case split when $\iota$ has one element. With a nonpositive parameter the Gamma measure is not a probability measure, so theorems use positive $\alpha$ only; the map is measurable.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §2.1, p.7:6

import Mathlib
open MeasureTheory ProbabilityTheory

namespace NestedCRP

/-- The Dirichlet law Dir(α) on the simplex of `ι → ℝ`, for `αi > 0`: the law of
`(X_i / ∑_j X_j)_i` for independent `X_i ∼ Gamma(α_i, 1)`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §2.1, p.7:6.

**Formalization Note** The paper names the law without a formula. This is the standard
construction and needs no case split at `card ι = 1`. For `α` positive and `ι` nonempty it is a
probability measure carried by the simplex, with the usual density; `ι` nonempty is the paper's
`K ≥ 1`. With a nonpositive parameter `gammaMeasure` is not a probability measure, so the theorems
of this development only use positive `α`. -/
noncomputable def dirichletMeasure {ι : Type*} [Fintype ι] (α : ι → ℝ) : Measure (ι → ℝ) :=
  (Measure.pi fun i => gammaMeasure (α i) 1).map fun x i => x i / ∑ j, x j

end NestedCRP


