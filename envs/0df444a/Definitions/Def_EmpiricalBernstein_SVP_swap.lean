-- Prove2me | Definitions.Def_EmpiricalBernstein_SVP_swap
-- name    : EmpiricalBernstein_SVP_swap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:29.376679+00:00
-- url     : https://prove2.me/theorems/4e2ea13c-d862-45dc-b7ad-9a5dfe3ae0c0
-- title:
--   Sec. 3, p. 5 — the swapped vector $(\sigma,x,x')$
-- statement:
--   Given two vectors $x, x' \in \mathcal X^n$ and a sign vector $\sigma \in \{-1,1\}^n$, the vector $(\sigma, x, x') \in \mathcal X^n$ is
--
--   $$
--   (\sigma, x, x')_i = \begin{cases} x_i & \text{if } \sigma_i = 1,\\ x'_i & \text{if } \sigma_i = -1.\end{cases}
--   $$
--
--   Thus $(\sigma,x,x')$ and $(-\sigma,x,x')$ are obtained from the pair $(x,x')$ by exchanging $x_i$ and $x'_i$ at the coordinates where $\sigma_i = -1$. When the $\sigma_i$ are independent and uniform on $\{-1,1\}$ this is the symmetrization device of the double-sample method.
--
--   **Formalization Note** A sign vector is `σ : Fin n → Bool`, with $\sigma_i = 1$ encoded as `true` and $\sigma_i = -1$ as `false`; $-\sigma$ is `fun i => !σ i`. Probabilities and expectations over independent uniform signs are uniform averages over the $2^n$ vectors `σ`.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Sec. 3, p. 5

import Mathlib

namespace EmpiricalBernstein.SVP

/-- The swapped vector `(σ, x, x′) ∈ 𝒳^n` for `x, x′ ∈ 𝒳^n` and `σ ∈ {−1, 1}^n`:
`(σ, x, x′)_i = x_i` if `σ_i = 1` and `x′_i` if `σ_i = −1` (arXiv:0907.3740v1, Sec. 3, p. 5).
The sign `σ_i = 1` is encoded as `σ i = true`, `σ_i = −1` as `σ i = false`; `−σ` is `fun i => !σ i`. -/
def swap {𝒳 : Type*} {n : ℕ} (σ : Fin n → Bool) (x x' : Fin n → 𝒳) : Fin n → 𝒳 :=
  fun i => if σ i then x i else x' i

end EmpiricalBernstein.SVP


