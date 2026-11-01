-- Prove2me | Definitions.Def_PSDPolyApprox_qy
-- name    : PSDPolyApprox_qy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:54.782382+00:00
-- url     : https://prove2.me/theorems/249a60e2-a6d0-41e1-9a65-6541c5b5c699
-- title:
--   $q_y(x)=\frac1n(x^{\mathsf T}y)^2$ on $H_n$
-- statement:
--   For a fixed $y\in H_n$, the function $q_y:H_n\to\mathbb R$,
--   $$
--   q_y(x)=\frac1n\,(x^{\mathsf T}y)^2=\frac1n\Bigl(\sum_{i=1}^n x_iy_i\Bigr)^2 .
--   $$
--   Note $q_y(y)=n$ and $\mathbb E[q_y]=1$.
--
--   **Formalization Note** Lean's convention $1/0=0$ makes $q_y\equiv0$ when $n=0$; every statement using $q_y$ assumes $n\ge1$.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §3, p.5

import Mathlib
import Definitions.Def_PSDPolyApprox_Cube

namespace PSDPolyApprox

/-- **The function `q_y(x) = (1/n)(xᵀy)²` on the hypercube.**
Fawzi, arXiv:1811.09649v1, §3, p.5: "For each ﬁxed y, let qy(x) = 1/n(xT y)2."

`qy n y x = (1/n) (∑ᵢ xᵢ yᵢ)²` for `x, y ∈ Hₙ`. At `n = 0` Lean's `(0 : ℝ)⁻¹ = 0` makes it `0`;
every statement using it has `n ≥ 1`. -/
noncomputable def qy (n : ℕ) (y : Cube n) (x : Cube n) : ℝ :=
  (n : ℝ)⁻¹ * (∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2

end PSDPolyApprox


