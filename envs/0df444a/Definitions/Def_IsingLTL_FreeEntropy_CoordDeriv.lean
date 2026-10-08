-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_CoordDeriv
-- name    : IsingLTL_FreeEntropy_CoordDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:20.621987+00:00
-- url     : https://prove2.me/theorems/17a375fb-a044-484e-967d-2f4a32a2a5a6
-- title:
--   Coordinate partial derivatives $\partial_{x_i}F$ on $\mathbb R^\ell$ (Lemma 6.1)
-- statement:
--   For a function $F:\mathbb R^\ell\to\mathbb R$, the partial derivative in the $i$-th coordinate at $x$ is
--   $$\partial_{x_i}F(x)=\frac{d}{dt}F(x_1,\dots,x_{i-1},t,x_{i+1},\dots,x_\ell)\Big|_{t=x_i},$$
--   and the mixed derivative $\partial^2F/\partial x_1\partial x_2$ is $\partial_{x_1}$ of $\partial_{x_2}F$.
--
--   **Formalization Note** Coordinates are indexed from $0$: the paper's $x_1$ and $x_2$ are indices $0$ and $1$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, pp. 21-22, Lemma 6.1

import Mathlib

namespace IsingLTL.FreeEntropy

/-- The partial derivative `∂_{x_i} f(x)` of a function `f : ℝ^ℓ → ℝ` in its `i`-th coordinate,
`d/dt f(x₁, …, t, …, x_ℓ)` at `t = x_i` (Dembo–Montanari, *Ising Models on Locally Tree-Like
Graphs*, arXiv:0804.4726v3, Lemma 6.1, pp. 21–22). Coordinate `x₁` of the paper is index `0`,
`x₂` is index `1`. The mixed derivative `∂²f/∂x₁∂x₂` is
`coordDeriv (fun y => coordDeriv f 1 y) 0 x`. -/
noncomputable def coordDeriv {ℓ : ℕ} (f : (Fin ℓ → ℝ) → ℝ) (i : Fin ℓ) (x : Fin ℓ → ℝ) : ℝ :=
  deriv (fun t : ℝ => f (Function.update x i t)) (x i)

end IsingLTL.FreeEntropy


