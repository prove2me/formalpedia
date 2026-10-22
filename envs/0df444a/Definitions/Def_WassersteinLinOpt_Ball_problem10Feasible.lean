-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_problem10Feasible
-- name    : WassersteinLinOpt_Ball_problem10Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T16:50:09.241472+00:00
-- url     : https://prove2.me/theorems/c4701a2f-4773-4c9d-9256-5d3cce13d3a1
-- title:
--   Feasible region of the discrete relaxation (10)
-- statement:
--   Let $(X,d)$ be a metric space, $p\ge1$, $r>0$, $y_1,\dots,y_N\in X$, $Y=\{y_1,\dots,y_N\}$ and $\alpha\in\mathbb R^N_+$. A measure $\gamma$ on $X\times X$ is feasible in problem (10) if
--
--   $$\gamma\in\mathcal D_{N+1}(X\times Y),\qquad \int_{X\times Y}\mathbb 1_{X\times\{y_i\}}\,d\gamma=\alpha_i\ \ (i=1,\dots,N),\qquad \int_{X\times Y}d^p(x_1,x_2)\,d\gamma(x_1,x_2)\le r^p,$$
--
--   that is, $\gamma=\sum_{j=1}^{N+1}w_j\delta_{(x_j,y'_j)}$ with $w_j\ge0$ and every $y'_j\in Y$, the mass $\gamma(X\times\{y_i\})$ equals $\alpha_i$, and the transport cost is at most $r^p$. Problem (10) maximizes $\int_{X\times Y} f(x_1)\,d\gamma(x_1,x_2)$ over this set.
--
--   **Formalization Note.** A measure on $X\times Y$ is represented as a measure on `X × X` that is a `Fin (N+1)`-indexed Dirac mixture whose atoms have second coordinate in `Set.range y`; the indicator constraint is `γ (Set.univ ×ˢ {y i}) = α i` and the cost is a lower Lebesgue integral in `ℝ≥0∞` compared with `ENNReal.ofReal (r ^ p)`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1117, problem (10)

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- The feasible region of problem (10), p. 1117. With `Y = {y₁, …, y_N}`, a measure `γ` on
`X × X` is feasible when
* `γ ∈ 𝒟_{N+1}(X × Y)`: `γ = ∑_{j=1}^{N+1} w_j δ_{z_j}` with `w_j ≥ 0` and every atom
  `z_j = (x_j, y')` having second coordinate `y' ∈ Y`;
* `∫_{X×Y} 1_{X×{y_i}} dγ = γ(X × {y_i}) = α_i` for all `i = 1, …, N`;
* `∫_{X×Y} d^p(x₁, x₂) dγ(x₁, x₂) ≤ r^p`. -/
def problem10Feasible {X : Type*} [MetricSpace X] [MeasurableSpace X] (p r : ℝ) {N : ℕ}
    (y : Fin N → X) (α : Fin N → ℝ≥0) : Set (Measure (X × X)) :=
  {γ | (∃ (z : Fin (N + 1) → X × X) (w : Fin (N + 1) → ℝ≥0),
          (∀ j, (z j).2 ∈ Set.range y) ∧ γ = ∑ j, (w j : ℝ≥0∞) • Measure.dirac (z j)) ∧
       (∀ i, γ (Set.univ ×ˢ {y i}) = (α i : ℝ≥0∞)) ∧
       ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ ≤ ENNReal.ofReal (r ^ p)}

end WassersteinLinOpt.Ball


