-- Prove2me | Definitions.Def_MNLStability_IsUpSetOff
-- name    : MNLStability_IsUpSetOff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:21.453811+00:00
-- url     : https://prove2.me/theorems/aa0c4206-e6bd-4eee-a34d-791e7d37d3b3
-- title:
--   Up-sets of consumption vectors that ignore one product
-- statement:
--   Order consumption outcomes $(X,X_0)$ coordinatewise. A set $A$ of outcomes is an **up-set ignoring product $a$** when
--
--   1. $A$ is upward closed: $x\in A$ and $x\le y$ imply $y\in A$;
--   2. membership in $A$ does not depend on the coordinate $X_a$.
--
--   The events of the paper's variable $X^U_C(m)$ (p.26), "at least $C_j$ units of product $j$ are consumed for every $j\in[n]\cup\{0\}$", with $C_1=0$ and product $1$ in the role of $a$, are exactly the principal up-sets $\{x\ge C\}$ of this kind. Comparing the probabilities of all such up-sets is the usual stochastic order on consumption vectors of the products other than $a$, including the no-purchase option.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §5.1, p.26 (X_C^U(m)); §5.4, p.30

import Mathlib

namespace MNLStability

variable {n : ℕ}

/-- `A` is an up-set of consumption vectors that ignores product `a`: a set of outcomes
`(X, X₀)` (units consumed of each product, and number of no-purchases) that is upward closed for the
coordinatewise order, and whose membership does not depend on the coordinate `X a`.

The events `{X_j ≥ C_j for every j ∈ [n] ∪ {0}}` with `C_a = 0` of SSRN:3498325, p.26 (the variable
`X^U_C(m)`, with product `1` in the role of `a`) are exactly the principal up-sets of this kind. -/
def IsUpSetOff (a : Fin n) (A : Set ((Fin n → ℕ) × ℕ)) : Prop :=
  IsUpperSet A ∧
    ∀ x y : (Fin n → ℕ) × ℕ, (∀ j, j ≠ a → x.1 j = y.1 j) → x.2 = y.2 → x ∈ A → y ∈ A

end MNLStability


