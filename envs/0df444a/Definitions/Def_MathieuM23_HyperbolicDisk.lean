-- Prove2me | Definitions.Def_MathieuM23_HyperbolicDisk
-- name    : MathieuM23_HyperbolicDisk
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T15:48:44.469214+00:00
-- url     : https://prove2.me/theorems/09b0703b-ce03-40f5-983e-203a95ee6a52
-- title:
--   Hyperbolic distance and angles in the Poincaré disk; the vertices $a,b,c$
-- statement:
--   Model the hyperbolic plane by the open unit disk $D=\{q\in\mathbb{C}:|q|<1\}$ with its metric $d$ of curvature $-1$, for which
--
--   $$\cosh d(z,w)=1+\frac{2|z-w|^2}{(1-|z|^2)(1-|w|^2)}.$$
--
--   For a hyperbolic triangle with vertices $p,q,r$, the interior angle at $p$ is the unique $\alpha\in[0,\pi]$ with
--
--   $$\cos\alpha=\frac{\cosh d(p,q)\cosh d(p,r)-\cosh d(q,r)}{\sinh d(p,q)\,\sinh d(p,r)}$$
--
--   (hyperbolic law of cosines). For $\theta\in(0,\pi/4)$ the source defines
--
--   $$a:=e^{-i\theta}\sqrt{\tan\left(\tfrac{\pi}{4}-\theta\right)},\qquad b:=0,\qquad c:=\sqrt{\cos 2\theta}.$$
--
--   **Formalization Note** The interior angle is defined through the hyperbolic law of cosines, with $\sinh d=\sqrt{\cosh^2 d-1}$. In the disk model this agrees with the Euclidean angle between the geodesic arcs.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 5, definitions of $a,b,c$ before Lemma 3.2

import Mathlib

/-!
# Hyperbolic triangles in the Poincaré disk (Lemma 3.2)

The hyperbolic plane is modelled by the open unit disk `D = {q ∈ ℂ : |q| < 1}` with the
metric of constant curvature `-1`, for which
`cosh d(z, w) = 1 + 2|z - w|² / ((1 - |z|²)(1 - |w|²))`.
The interior angle of a hyperbolic triangle at a vertex is expressed through the hyperbolic law
of cosines.
-/

namespace MathieuM23

/-- `cosh d(z, w)` for the hyperbolic metric on the unit disk. -/
noncomputable def diskCoshDist (z w : ℂ) : ℝ :=
  1 + 2 * ‖z - w‖ ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))

/-- The interior angle at the vertex `p` of the hyperbolic triangle with vertices `p, q, r` in
the unit disk, defined by the hyperbolic law of cosines
`cos ∠p = (cosh d(p,q) cosh d(p,r) - cosh d(q,r)) / (sinh d(p,q) sinh d(p,r))`,
with `sinh d = √(cosh² d - 1)`. -/
noncomputable def diskAngle (p q r : ℂ) : ℝ :=
  Real.arccos
    ((diskCoshDist p q * diskCoshDist p r - diskCoshDist q r) /
      (Real.sqrt (diskCoshDist p q ^ 2 - 1) * Real.sqrt (diskCoshDist p r ^ 2 - 1)))

/-- The vertex `a = e^{-iθ} √(tan(π/4 - θ))`. -/
noncomputable def vertexA (θ : ℝ) : ℂ :=
  Complex.exp (-(θ : ℂ) * Complex.I) * (Real.sqrt (Real.tan (Real.pi / 4 - θ)) : ℂ)

/-- The vertex `b = 0`. -/
noncomputable def vertexB : ℂ := 0

/-- The vertex `c = √(cos 2θ)`. -/
noncomputable def vertexC (θ : ℝ) : ℂ := (Real.sqrt (Real.cos (2 * θ)) : ℂ)

end MathieuM23


