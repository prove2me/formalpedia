-- Prove2me | Definitions.Def_MatrixLewis_lineDeriv
-- name    : MatrixLewis_lineDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:46.089656+00:00
-- url     : https://prove2.me/theorems/206d55ec-0c61-45cd-91aa-5e7d2f919df4
-- title:
--   Directional derivatives $D^k\varphi(S)[\dot S,\dots,\dot S]$ and $D^2\varphi(S)[X,Y]$
-- statement:
--   For a real function $\varphi$ of a matrix, the $k$-th directional derivative and the mixed second derivative are read as
--   $$
--   D^k\varphi(S)[\dot S,\dots,\dot S]=\frac{d^k}{dt^k}\varphi(S+t\dot S)\Big|_{t=0},\qquad
--   D^2\varphi(S)[X,Y]=\frac{\partial^2}{\partial s\,\partial t}\varphi(S+sX+tY)\Big|_{s=t=0}.
--   $$
--
--   **Formalization Note** For a function of class $C^k$ near $S$ these are the Fréchet derivatives evaluated at the given directions; the matrix Lewis potential is real analytic on $\mathbb S^n_{++}$ (Theorem 3.9(iv)), so this is the paper's $D^k\varphi_q$. No norm on matrices is needed.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.12(iii), p.23; Theorems 3.15, 3.17; Lemmas 3.16, 3.20, pp.24–33

import Mathlib

namespace MatrixLewis

/-- The `k`-th directional derivative `Dᵏφ(S)[Ṡ, …, Ṡ]` of a function `φ` of a matrix,
read along the line: `(d/dt)ᵏ φ(S + tṠ)` at `t = 0` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.12(iii), Theorems 3.15,
3.17, Lemmas 3.16, 3.20).

**Formalization Note** For a function that is `Cᵏ` near `S` (the potential `φ_q` is real
analytic on `Sⁿ₊₊`, Theorem 3.9(iv)) this is the `k`-th Fréchet derivative applied to `Ṡ` `k`
times; it needs no norm on matrices. -/
noncomputable def lineDeriv {ι : Type*} (k : ℕ) (φ : Matrix ι ι ℝ → ℝ)
    (S Sdot : Matrix ι ι ℝ) : ℝ :=
  iteratedDeriv k (fun t : ℝ => φ (S + t • Sdot)) 0

/-- The mixed second derivative `D²φ(S)[X, Y]`, read as `∂_s ∂_t φ(S + sX + tY)` at
`s = t = 0` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.20(a)–(b), p.33: `D²φ_q(I)[X, X²]`).

**Formalization Note** For `φ` of class `C²` near `S` this is the symmetric bilinear second
Fréchet derivative evaluated at `(X, Y)`. -/
noncomputable def mixedDeriv2 {ι : Type*} (φ : Matrix ι ι ℝ → ℝ) (S X Y : Matrix ι ι ℝ) : ℝ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => φ (S + s • X + t • Y)) 0) 0

end MatrixLewis


