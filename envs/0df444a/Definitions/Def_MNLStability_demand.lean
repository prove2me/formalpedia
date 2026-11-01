-- Prove2me | Definitions.Def_MNLStability_demand
-- name    : MNLStability_demand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:51.082638+00:00
-- url     : https://prove2.me/theorems/4e6aac8c-2ea0-4544-bf83-d16e68827287
-- title:
--   The dynamic MNL demand process with $m$ customers
-- statement:
--   Start from the initial inventory vector $U\in\mathbb Z_+^n$. Customers $1,2,\dots,m$ arrive one at a time; each faces the products still in stock (initial stock minus the units bought by earlier customers) and chooses by the MNL rule. The **demand process** is the joint law of
--
--   $$\bigl(X^U(m),\,X_0^U(m)\bigr),$$
--
--   where $X_i^U(m)$ is the number of units of product $i$ consumed by customers $1,\dots,m$ and $X_0^U(m)$ is the number of customers who chose the no-purchase option.
--
--   The no-purchase count is the paper's auxiliary product $0$ "with an infinite inventory level" (§5.1). Expected demands, unit-consumption probabilities and the stochastic comparisons of §5 are all read off this law.
--
--   **Formalization Note** Defined by recursion on $m$ through `PMF.bind`, so each choice depends on the past only through the current stock, as in the paper.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §1.1, p.4; notation X_j^U(M), §5.1, p.25

import Mathlib
import Definitions.Def_MNLStability_step

namespace MNLStability

variable {n : ℕ}

/-- The dynamic MNL demand process with a fixed number `m` of customers (SSRN:3498325, §1.1, p.4,
and the notation `X_j^U(M)` of §5.1, p.25): the joint law of `(X, X₀)` after `m` arrivals, starting
from the initial inventory vector `U`, where `X i` is the number of units of product `i` consumed
and `X₀` is the number of customers who chose the no-purchase option.

Customers arrive one at a time. Customer `k + 1` faces the products still in stock under
`U − X` (the units consumed by customers `1, …, k` removed) and chooses by `step`.

**Formalization Note.** Defined by recursion on `m` through `PMF.bind`, so successive choices are
conditionally independent given the current stock, as in the paper. The second coordinate is the
no-purchase option "as an auxiliary product with an infinite inventory level" (p.25). `U - x.1` is
the pointwise truncated subtraction of `ℕ`, exact on the support since `x.1 ≤ U` there. -/
noncomputable def demand (wts : Weights n) (U : Fin n → ℕ) : ℕ → PMF ((Fin n → ℕ) × ℕ)
  | 0 => PMF.pure (0, 0)
  | m + 1 => (demand wts U m).bind fun x =>
      (step wts (U - x.1)).map fun
        | none => (x.1, x.2 + 1)
        | some i => (x.1 + Pi.single i 1, x.2)

end MNLStability


