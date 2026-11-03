-- Prove2me | Definitions.Def_OnlineSaddlePoint_maximinValue
-- name    : OnlineSaddlePoint_maximinValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:17.603448+00:00
-- url     : https://prove2.me/theorems/7d62b6d1-511f-46ba-9172-92607a156255
-- title:
--   Max-min value $\max_{y\in Y}\min_{x\in X} f(x,y)$
-- statement:
--   Let $X\subseteq E$, $Y\subseteq F$ and let $f : X\times Y\to\mathbb R$ be a two-player zero-sum game. Its **max-min value** is
--
--   $$
--   \max_{y\in Y}\min_{x\in X} f(x,y).
--   $$
--
--   The $y$-update of Saddle-Point Follow-the-Leader maximizes the inner minimum, and at a saddle point the max-min value equals the min-max value.
--
--   **Formalization Note** The value is `sSup` over $y\in Y$ of `sInf` over $x\in X$ in $\mathbb R$; Lean's conventions return $0$ on empty or unbounded sets, and every statement that uses it assumes $X$, $Y$ nonempty and compact and $f$ Lipschitz, so both extrema are attained.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, p.2; Algorithm 1, p.6

import Mathlib

namespace OnlineSaddlePoint

/-- **Max-min value** `max_{y∈Y} min_{x∈X} f(x, y)` of a two-player zero-sum game `f` on
`X × Y`. Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, p.2 ("min_{x∈X} max_{y∈Y} ∑ 𝓛_t(x, y) =
∑ 𝓛_t(x*, y*) = max_{y∈Y} min_{x∈X} ∑ 𝓛_t(x, y)") and Algorithm 1, p.6 (the update of `y_{t+1}`).

**Formalization Note.** The value is `sSup { sInf { f x y | x ∈ X } | y ∈ Y }` in `ℝ`. Lean's
`sSup`/`sInf` on `ℝ` return `0` on empty or unbounded sets; every statement that uses this value
assumes `X`, `Y` nonempty and compact and `f` Lipschitz on `X × Y`, so both extrema are attained
and the value is the paper's `max min`. -/
noncomputable def maximinValue {E F : Type*} (X : Set E) (Y : Set F) (f : E → F → ℝ) : ℝ :=
  sSup ((fun y => sInf ((fun x => f x y) '' X)) '' Y)

end OnlineSaddlePoint


