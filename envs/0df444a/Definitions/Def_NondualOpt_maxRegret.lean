-- Prove2me | Definitions.Def_NondualOpt_maxRegret
-- name    : NondualOpt_maxRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:40.108919+00:00
-- url     : https://prove2.me/theorems/f9696409-1ad4-4a3a-9bdb-75c8aeba6e7c
-- title:
--   The max-regret $R^{\max}_{X,n}$
-- statement:
--   For a decision set $X$, actions $x_1,\dots,x_n$ and losses $\ell_1,\dots,\ell_n$, the **max-regret** is
--   $$
--   R^{\max}_{X,n}=\sum_{t=1}^n\ell_t(x_t)-\inf_{u\in X}\,n\max_{t\le n}\ell_t(u).
--   $$
--   The comparator is $n$ times the maximum of the losses at a fixed point, rather than their sum; since $\max_t\ell_t(u)\ge\frac1n\sum_t\ell_t(u)$, the max-regret never exceeds the ordinary regret.
--
--   **Formalization Note** The value is an extended real: for arbitrary losses the infimum can be $-\infty$ (max-regret $+\infty$), and over an empty $X$ it is $+\infty$. The sum is a real number, so no $\infty-\infty$ occurs.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (1), p.3

import Mathlib

namespace NondualOpt

/-- The max-regret of actions `x_1, …, x_n` against losses `ℓ_1, …, ℓ_n` over the decision set `X`:
`R^max_{X,n} = ∑_t ℓ_t(x_t) − inf_{u ∈ X} n · max_{t ≤ n} ℓ_t(u)`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (1), p.3.

**Formalization Note.** Valued in `EReal`: for arbitrary losses the infimum over `X` can be `−∞`
(then the max-regret is `+∞`), and over an empty `X` it is `+∞`. The sum is a real number, so no
`⊤ − ⊤` occurs. Rounds are `Fin n` (0-based); the comparator multiplier is the horizon `n`. -/
noncomputable def maxRegret {E : Type*} {n : ℕ} (X : Set E) (x : Fin n → E) (ℓ : Fin n → E → ℝ) :
    EReal :=
  ((∑ t, ℓ t (x t) : ℝ) : EReal) - ⨅ u : X, ((n : ℝ) : EReal) * ⨆ t, ((ℓ t u : ℝ) : EReal)

end NondualOpt


