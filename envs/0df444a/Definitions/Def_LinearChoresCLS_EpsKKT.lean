-- Prove2me | Definitions.Def_LinearChoresCLS_EpsKKT
-- name    : LinearChoresCLS_EpsKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:54.595393+00:00
-- url     : https://prove2.me/theorems/b27b686f-df9b-4371-9c9b-4b37b3f9c141
-- title:
--   ε-KKT points of a box quadratic program and the ε-quadratic-KKT search problem (Definition 2.4)
-- statement:
--   Let $A\in\mathbb Q^{n\times n}$ be symmetric, $c\in\mathbb Q^n$, $n\ge1$, and consider
--   $$
--   \max\ Q(x)=\tfrac12x^\top Ax+c^\top x\quad\text{s.t. } 0\le x_i\le 1\ (i=1,\dots,n).
--   $$
--   A point $x\in[0,1]^n$ is an **$\varepsilon$-KKT point** if for all $i$: $\partial Q/\partial x_i(x)\le\varepsilon$ when $x_i=0$; $|\partial Q/\partial x_i(x)|\le\varepsilon$ when $0<x_i<1$; and $\partial Q/\partial x_i(x)\ge-\varepsilon$ when $x_i=1$.
--
--   The **$\varepsilon$-quadratic-KKT problem** takes $I=(A,c,\varepsilon)$ with rational $\varepsilon>0$, encoded in binary, and asks for a rational $\varepsilon$-KKT point. It is the CLS-complete source problem of the reduction.
--
--   **Formalization Note** The quadratic is the public `Quadratic` (rational, symmetric); $\partial Q/\partial x_i=\sum_jA_{ij}x_j+c_i$ is the public `sourceGradient`. The signs are those of maximization, as printed (the public `ApproxQuadraticKKT` uses minimization signs and is not reused). Answers carry no length bound here; the public `bounded` adds one.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Definition 2.4, Eqs. (2.5)–(2.6), p.7

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding

open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **ε-KKT point of the box quadratic program** `max Q(x) := ½xᵀAx + cᵀx` s.t. `0 ≤ xᵢ ≤ 1`
(arXiv:2611.06589, held version sha256 85d34a9e…, Definition 2.4, Eq. (2.5), p.7): `x ∈ [0,1]ⁿ`
and for every `i`: if `xᵢ = 0` then `∂Q/∂xᵢ(x) ≤ ε`; if `0 < xᵢ < 1` then `|∂Q/∂xᵢ(x)| ≤ ε`; if
`xᵢ = 1` then `∂Q/∂xᵢ(x) ≥ −ε`.

**Formalization Note.** The quadratic `(A, c)` is the public
`NetworkEquilibriumCLS.LinearNash.Quadratic` (rational, symmetric `A`); `∂Q/∂xᵢ(x) = ∑ⱼ Aᵢⱼxⱼ + cᵢ`
is its public `sourceGradient` (by symmetry of `A`). The signs are those of **maximization**, as
printed; the public `ApproxQuadraticKKT` uses the minimization signs and is not reused. -/
def IsEpsKKT {n : ℕ} (P : Quadratic n) (ε : ℝ) (x : Fin n → ℝ) : Prop :=
  InCube x ∧ ∀ i, (x i = 0 → sourceGradient P x i ≤ ε) ∧
    (0 < x i → x i < 1 → |sourceGradient P x i| ≤ ε) ∧ (x i = 1 → -ε ≤ sourceGradient P x i)

/-- **The ε-quadratic-KKT search problem** (arXiv:2611.06589, Definition 2.4, p.7): an instance is
`I = (A, c, ε)` with `A ∈ ℚ^{n×n}` symmetric, `c ∈ ℚⁿ`, `n ≥ 1`, and rational `ε > 0`, encoded as
`encQuadratic (A, c) ++ encRat ε`; an answer is the encoding `encVector z` of a rational point
`z ∈ ℚⁿ` that is an ε-KKT point of `I`.

**Formalization Note.** `n ≥ 1` follows the paper's `[k]` for positive integers `k` (p.5) and the
public `quadraticSearch`. Answers have no length bound here; `bounded epsQKKTSearch k` adds one. -/
def epsQKKTSearch : SearchProblem where
  valid x := ∃ n, 0 < n ∧ ∃ (P : Quadratic n) (ε : ℚ), 0 < ε ∧ encQuadratic P ++ encRat ε = x
  answer x y := ∃ n, 0 < n ∧ ∃ (P : Quadratic n) (ε : ℚ), 0 < ε ∧
    encQuadratic P ++ encRat ε = x ∧
    ∃ z : Fin n → ℚ, encVector z = y ∧ IsEpsKKT P (ε : ℝ) (fun i => (z i : ℝ))

end LinearChoresCLS


