-- Prove2me | Definitions.Def_TestScoreSubmod_pad
-- name    : TestScoreSubmod_pad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:58.957348+00:00
-- url     : https://prove2.me/theorems/4c5d2f09-348b-48e0-9d13-1a52e332f977
-- title:
--   Padding a vector of dimension $r$ to $n$ coordinates
-- statement:
--   For a vector $y\in\mathbb R_+^{r}$, $\mathrm{pad}(y)\in\mathbb R_+^{n}$ writes $y$ into the first $r$ coordinates and fills the remaining $n-r$ coordinates with $\varphi=0$:
--
--   $$
--   \mathrm{pad}(y)=(y_1,\dots,y_r,0,\dots,0).
--   $$
--
--   This is the paper's convention of writing $g(y)$ for a vector of dimension $r<n$, and the argument $g(X_i^{(1)},\dots,X_i^{(k)},\varphi,\dots,\varphi)$ of a replication test score.
--
--   **Formalization Note** $\varphi=0$. If $r>n$ the extra coordinates of $y$ are dropped; every use in this mission has $r\le n$.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, §2.1, p.11 and Definition 2, eq. (7), p.17

import Mathlib

open scoped NNReal

namespace TestScoreSubmod

/-- **Padding a short vector with `φ`** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, §2.1, p.11:
"we sometimes abuse notation by writing g(x) for a vector of dimension d < n, instead of
g(x, z) where z is a vector of dimension n − d that has all elements equal to φ"; and
Definition 2, eq. (7), p.17, `g(X⁽¹⁾, …, X⁽ᵏ⁾, φ, …, φ)`).

`pad y` writes a vector `y` of dimension `r` into the first `r` of `n` coordinates and fills the
remaining coordinates with `0`.

**Formalization Note** `φ = 0`. If `r > n` the coordinates of `y` beyond `n` are dropped; every
use in this mission has `r ≤ n`. -/
def pad {n r : ℕ} (y : Fin r → ℝ≥0) : Fin n → ℝ≥0 :=
  fun i => if h : i.val < r then y ⟨i.val, h⟩ else 0

end TestScoreSubmod


