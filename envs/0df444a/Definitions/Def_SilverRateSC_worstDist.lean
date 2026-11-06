-- Prove2me | Definitions.Def_SilverRateSC_worstDist
-- name    : SilverRateSC_worstDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:16.618756+00:00
-- url     : https://prove2.me/theorems/c12a5d8a-f49c-4fe8-9368-b17dd3e16aa8
-- title:
--   Worst-case squared-distance ratio $D_{n,\kappa}(H)$, (1)
-- statement:
--   Fix $\kappa\ge1$ and let $\mathscr F_{1/\kappa,1}(\mathbb R^d)$ be the class of differentiable $\tfrac1\kappa$-strongly convex functions on $\mathbb R^d$ with $1$-Lipschitz gradient. For a stepsize schedule $H=(h_1,\dots,h_n)$, the **worst-case squared-distance ratio** is
--   $$D_{n,\kappa}(H) := \sup_{d\in\mathbb N}\ \sup_{F\in\mathscr F_{1/\kappa,1}(\mathbb R^d)}\ \sup_{x_0\neq x_*}\ \frac{\|x_n-x_*\|^2}{\|x_0-x_*\|^2},$$
--   where $x_*$ is the minimizer of $F$ and $x_n$ is the gradient-descent iterate $x_t=x_{t-1}-h_t\nabla F(x_{t-1})$ after the $n$ steps of $H$ from $x_0$. The normalization $L=1$, $\mu=1/\kappa$ loses no generality (dividing $F$ by $L$ and multiplying each stepsize by $L$ preserves the iterates).
--
--   A lower bound on $D_{n,\kappa}(H)$ valid for every schedule bounds how fast gradient descent with any predetermined stepsizes can contract the distance to the minimizer.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, so an unbounded family would give $+\infty$ rather than a junk value $0$; it is in fact finite (verification file). The class is the published `HighResODE.NAGSC.IsS1 F κ⁻¹ 1`, the minimizer is any $x_*$ with $F(x_*)\le F(y)$ for all $y$ (unique by strong convexity), and the iterate is the published `SilverRateLB.gdRun`.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §1.1, (1), p.5; footnote 3, p.4

import Mathlib
import Definitions.Def_SilverRateLB_gdRun
import Definitions.Def_HighResODE_NAGSC_FunctionClass

open scoped ENNReal

namespace SilverRateSC

/-- **Worst-case squared-distance ratio** `D_{n,κ}(H)`, (1):
`D_{n,κ}(H) := sup_{d ∈ ℕ} sup_{F ∈ F_{1/κ,1}(ℝ^d)} sup_{x_0 ≠ x_*} ‖x_n − x_*‖² / ‖x_0 − x_*‖²`,
where `F_{1/κ,1}(ℝ^d)` is the class of differentiable `1/κ`-strongly convex functions on `ℝ^d`
with `1`-Lipschitz gradient, `x_*` is the minimizer of `F`, and `x_n` is the gradient-descent
iterate after the schedule `H = (h_1, …, h_n)` started at `x_0`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §1.1, (1), p. 5 (normalization `L = 1`, `µ = 1/κ`: footnote 3, p. 4).

**Formalization Note** The supremum is taken in `ℝ≥0∞`, so an unbounded family would give `⊤`
and no junk value `0` arises. `F_{1/κ,1}(ℝ^d)` is `HighResODE.NAGSC.IsS1 F κ⁻¹ 1`
(differentiable, convex, `1`-Lipschitz gradient, `κ⁻¹`-strongly convex, `0 < κ⁻¹ ≤ 1`); for
`κ < 1` the class is empty in every dimension `d ≥ 1`, as in the paper. The minimizer is the binder
`x_*` with `∀ y, F x_* ≤ F y` (unique by strong convexity). The schedule is a `List ℝ` read left
to right and `n` is its length; `x_n` is `SilverRateLB.gdRun F H x₀`. `d = 0` contributes nothing
(there is no `x_0 ≠ x_*`). -/
noncomputable def worstDist (κ : ℝ) (H : List ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (_ : HighResODE.NAGSC.IsS1 F κ⁻¹ 1)
    (xs : EuclideanSpace ℝ (Fin d)) (_ : ∀ y, F xs ≤ F y)
    (x₀ : EuclideanSpace ℝ (Fin d)) (_ : x₀ ≠ xs),
    ENNReal.ofReal (‖SilverRateLB.gdRun F H x₀ - xs‖ ^ 2 / ‖x₀ - xs‖ ^ 2)

end SilverRateSC


