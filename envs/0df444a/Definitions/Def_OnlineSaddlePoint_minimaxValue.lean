-- Prove2me | Definitions.Def_OnlineSaddlePoint_minimaxValue
-- name    : OnlineSaddlePoint_minimaxValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:15.464978+00:00
-- url     : https://prove2.me/theorems/8a79b859-d634-4730-948d-46a7e380960b
-- title:
--   Min-max value $\min_{x\in X}\max_{y\in Y} f(x,y)$
-- statement:
--   Let $X\subseteq E$, $Y\subseteq F$ and let $f : X\times Y\to\mathbb R$ be a two-player zero-sum game in which the $x$-player minimizes and the $y$-player maximizes. Its **min-max value** is
--
--   $$
--   \min_{x\in X}\max_{y\in Y} f(x,y).
--   $$
--
--   Applied to the cumulative payoff $\sum_{t=1}^T\mathcal L_t$, it is the benchmark in the definition of the saddle-point regret.
--
--   **Formalization Note** The value is `sInf` over $x\in X$ of `sSup` over $y\in Y$ in $\mathbb R$. Lean's `sSup`/`sInf` return $0$ on empty or unbounded sets; every statement that uses this value assumes $X$, $Y$ nonempty and compact and $f$ Lipschitz on $X\times Y$, so both extrema are attained.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, display (1), p.2; Theorem 1, p.6

import Mathlib

namespace OnlineSaddlePoint

/-- **Min-max value** `min_{x∈X} max_{y∈Y} f(x, y)` of a two-player zero-sum game `f` on
`X × Y`. Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, p.2, display (1), and p.6, Theorem 1,
where it is applied to `f = ∑_{t=1}^T 𝓛_t`.

**Formalization Note.** The value is `sInf { sSup { f x y | y ∈ Y } | x ∈ X }` in `ℝ`. Lean's
`sSup`/`sInf` on `ℝ` return `0` on empty or unbounded sets. Every statement that uses this value
assumes `X`, `Y` nonempty and compact and `f` Lipschitz on `X × Y` (hence continuous), so the
inner supremum is an attained maximum, the outer infimum an attained minimum, and the value is
the paper's `min max`. -/
noncomputable def minimaxValue {E F : Type*} (X : Set E) (Y : Set F) (f : E → F → ℝ) : ℝ :=
  sInf ((fun x => sSup ((fun y => f x y) '' Y)) '' X)

end OnlineSaddlePoint


