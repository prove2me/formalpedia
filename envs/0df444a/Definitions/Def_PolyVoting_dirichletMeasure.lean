-- Prove2me | Definitions.Def_PolyVoting_dirichletMeasure
-- name    : PolyVoting_dirichletMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:26.674734+00:00
-- url     : https://prove2.me/theorems/ca12ca09-e610-483b-b45f-8f1b087ed6fd
-- title:
--   The Dirichlet distribution $\mathrm{Dir}(a_1,\dots,a_K)$
-- statement:
--   The Dirichlet distribution with parameters $(a_1,\dots,a_K)$ is the probability distribution on the standard simplex $\{x\in\mathbb R_+^K:\sum_{k=1}^K x_k=1\}$ with density
--   $$f(x_1,\dots,x_K)=\frac{\Gamma\big(\sum_{k=1}^K a_k\big)}{\prod_{k=1}^K\Gamma(a_k)}\prod_{k=1}^K x_k^{a_k-1}.$$
--   It is the limit law of the shares of a Pólya urn.
--
--   **Formalization Note** The density is taken with respect to Lebesgue measure on the first $K-1$ coordinates: the measure is the pushforward, under $y\mapsto(y,1-\sum_i y_i)$, of Lebesgue measure on $\mathbb R^{K-1}$ with density $f(y,1-\sum_i y_i)$ on $\{y\ge0,\ \sum_i y_i\le1\}$. For $K=1$ this is the point mass at $1$. The definition is meant for $a_k>0$.
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, §2.2, p.10

import Mathlib

open MeasureTheory

namespace PolyVoting

/-- The point `(y, 1 - ∑ y)` of `ℝ^(m+1)`: the first `m` coordinates determine a point of the
standard simplex. -/
noncomputable def simplexLift {m : ℕ} (y : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) y (1 - ∑ i, y i)

/-- **The Dirichlet distribution** `Dir(a₁, …, a_K)` (Tang & Yao, *Polynomial Voting Rules*,
arXiv:2206.10105v5, p.10): the probability measure on the standard simplex
`{x ∈ ℝ₊^K : ∑ x_k = 1}` with density
`f(x) = Γ(∑ a_k) / ∏ Γ(a_k) * ∏ x_k ^ (a_k - 1)`.

**Formalization Note.** The simplex is a null set of `ℝ^K`, so the density is taken, as usual,
with respect to Lebesgue measure on the first `K - 1` coordinates `y`. The measure is the
pushforward under `y ↦ (y, 1 - ∑ y)` of Lebesgue measure on `ℝ^(K-1)` with density
`f(y, 1 - ∑ y)` on `{y ≥ 0, ∑ y ≤ 1}`. For `K = 1` this is the point mass at `1`, the only point of
the simplex; for `K = 0` there is no simplex and the value is `0`. The definition is meaningful
for `a_k > 0`, the range of the paper's parameters. -/
noncomputable def dirichletMeasure : {K : ℕ} → (Fin K → ℝ) → Measure (Fin K → ℝ)
  | 0, _ => 0
  | m + 1, a =>
    ((volume : Measure (Fin m → ℝ)).withDensity fun y =>
      Set.indicator {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}
        (fun y => ENNReal.ofReal
          ((Real.Gamma (∑ k, a k) / ∏ k, Real.Gamma (a k)) *
            ∏ k, simplexLift y k ^ (a k - 1))) y).map simplexLift

end PolyVoting


