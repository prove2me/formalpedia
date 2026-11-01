-- Prove2me | Definitions.Def_AdditiveConvexity_transformSet
-- name    : AdditiveConvexity_transformSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:09.636999+00:00
-- url     : https://prove2.me/theorems/b40cc8ed-af16-4cb1-a079-bda9d01383c1
-- title:
--   Feasible set $\mathbb C(x)$ of the transformation problem
-- statement:
--   Let $x\in V$ and $0\le k\le n$. The feasible set of problem (1) of the paper is
--   $$
--   \mathbb C(x)=\{y\in I\times\mathbb R^k \mid y_0\le y_1\le\cdots\le y_k\le x_{k+1},\ y_0-x_0\ge y_1-x_1\ge\cdots\ge y_k-x_k\ge 0\}.
--   $$
--   The differences $y_i-x_i$ are the amounts that the coordinates are raised by, and they may only decrease along the chain.
--
--   **Formalization Note** A feasible $y$ is stored with the unchanged tail as one vector $z=(y_0,\dots,y_k,x_{k+1},\dots,x_n)$ in $V$, so that $f(y,x_{k+1},\dots,x_n)$ is $f(z)$. Membership in $V$ carries $y_0\in I$, the chain and $y_k\le x_{k+1}$. At $k=n$ there is no coordinate $x_{k+1}$ and no such bound: the paper's stage $n+1$ is then an external stage with unlimited supply (p.6).
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Theorem 1, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_AdditiveConvexity_chainDomain

namespace AdditiveConvexity

/-- The feasible set `ℂ(x)` of the optimal transformation problem (1) of Gong–Wang, Preservation
of Additive Convexity, SSRN 3217007 (accepted manuscript), Theorem 1, p.4 (PDF p.4):
`ℂ(x) = {y ∈ I × ℝᵏ | y₀ ≤ ⋯ ≤ y_k ≤ x_{k+1}, y₀ - x₀ ≥ ⋯ ≥ y_k - x_k ≥ 0}`.

**Formalization Note.** A feasible `y = (y₀, …, y_k)` is stored together with the unchanged tail as
one vector `z = (y₀, …, y_k, x_{k+1}, …, xₙ)`, so `f(y, x_{k+1}, …, xₙ)` is `f z`. Membership of `z`
in `chainDomain I n` carries `y₀ ∈ I`, the chain and `y_k ≤ x_{k+1}`; at `k = n` there is no
coordinate `x_{k+1}` and no such bound (p.6, PDF p.6: stage `n + 1` is "an external stage with
unlimited supply"). The comparison of indices is on `i.val` and uses no natural subtraction. -/
def transformSet (I : Set ℝ) {n : ℕ} (k : ℕ) (x : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {z | z ∈ chainDomain I n ∧ (∀ i : Fin (n + 1), k < i.val → z i = x i) ∧
    (∀ i : Fin (n + 1), i.val ≤ k → 0 ≤ z i - x i) ∧
    ∀ i j : Fin (n + 1), i ≤ j → j.val ≤ k → z j - x j ≤ z i - x i}

end AdditiveConvexity


