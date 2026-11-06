-- Prove2me | Definitions.Def_IntervalToDynamic_surrogate
-- name    : IntervalToDynamic_surrogate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:41.697756+00:00
-- url     : https://prove2.me/theorems/df564324-4edf-4339-ae35-ef2596c0b8b5
-- title:
--   Eqs. (10)–(12): the surrogate loss $h_t$
-- statement:
--   Given the corrected gradient $d$, the played point $x$ and the decision $y$ of the round, the surrogate is the function of $y'\in\mathbb R^d$
--   $$
--   h(y')=\begin{cases}d^\top y'&\text{convex},\\ d^\top y'+\dfrac\gamma2\,[d^\top(y'-y)]^2&\text{exp-concave},\\ d^\top y'+\dfrac\lambda2\,\|y'-x\|_2^2&\text{strongly convex.}\end{cases}
--   $$
--
--   These losses are what the wrapper feeds to the inner algorithm.
--
--   **Formalization Note** The quadratic of Eq. (11) is centred at $y_t$ and that of Eq. (12) at $x_t$, as printed.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Eqs. (10)–(12), p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_LossMode
import Definitions.Def_IntervalToDynamic_gammaParam

namespace IntervalToDynamic

/-- The surrogate loss `h_t` of Eqs. (10)–(12), as a function of the corrected gradient `dv = d_t`,
the played point `x = x_t` and the decision `y = y_t` of the inner algorithm. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423,
Eqs. (10)–(12), p.8:
`h_t(y') = d_tᵀ y'` (convex); `h_t(y') = d_tᵀ y' + (γ/2) [d_tᵀ (y' − y_t)]²` (exp-concave);
`h_t(y') = d_tᵀ y' + (λ/2) ‖y' − x_t‖₂²` (strongly convex).

**Formalization Note.** The quadratic of Eq. (11) is centred at `y_t` and that of Eq. (12) at
`x_t`, as printed. `γ` is `gammaParam DX G α` of Eq. (14). -/
noncomputable def surrogate {d : ℕ} (mode : LossMode) (DX G : ℝ) (dv x y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℝ :=
  match mode with
  | .convex => fun y' => inner ℝ dv y'
  | .expConcave α => fun y' =>
      inner ℝ dv y' + (gammaParam DX G α / 2) * (inner ℝ dv (y' - y)) ^ 2
  | .stronglyConvex lam => fun y' => inner ℝ dv y' + (lam / 2) * ‖y' - x‖ ^ 2

end IntervalToDynamic


