-- Prove2me | Definitions.Def_SphereSOS_Rate_Sphere
-- name    : SphereSOS_Rate_Sphere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:42.071987+00:00
-- url     : https://prove2.me/theorems/4a38aaf2-48f2-46bf-b738-3bdc649e4276
-- title:
--   p. 2 — the Euclidean unit sphere $S^{d-1}\subset\mathbb R^d$
-- statement:
--   The **unit sphere** in $\mathbb R^d$ is
--
--   $$S^{d-1}=\{x\in\mathbb R^d:\ x_1^2+\cdots+x_d^2=1\}.$$
--
--   It is the feasible set of the polynomial optimization problem $p_{\max}=\max_{x\in S^{d-1}}p(x)$ and the domain on which every sum-of-squares certificate of this mission is required to hold.
--
--   **Formalization Note** Points are coordinate vectors $x:\{0,\dots,d-1\}\to\mathbb R$ (0-based, the paper writes $x_1,\dots,x_d$), and the sphere is cut out by the Euclidean equation $\sum_i x_i^2=1$, not by the sup norm of `Fin d → ℝ`. For $d=0$ the set is empty.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 2, display (1) and the definition of $S^{d-1}$ after it

import Mathlib

namespace SphereSOS.Rate

/-- The Euclidean unit sphere in `ℝ^d`. -/
def sphere (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∑ i, x i ^ 2 = 1}

end SphereSOS.Rate


