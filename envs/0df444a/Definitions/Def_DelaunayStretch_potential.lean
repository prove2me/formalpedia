-- Prove2me | Definitions.Def_DelaunayStretch_potential
-- name    : DelaunayStretch_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:25.282371+00:00
-- url     : https://prove2.me/theorems/a7c8b7bc-d6b5-42b1-85e5-1487cef0fc60
-- title:
--   The potential $W_{H,U}$ and the pencil residual $\mathcal E_U[H;\nabla]$
-- statement:
--   Let $U\in\mathbb R$ and let $H$ be a real function on $\Omega\times\mathbb R$.
--
--   1. The **potential of $H$ at level $U$** is the function on gate states
--   $$
--   W_{H,U}(s)=r\Big[\frac\pi2-\theta-H(\gamma,\varphi,\theta,\psi)\Big]+U\,\big(x(c(s))-x(o)\big),
--   $$
--   where $o$, $r$ are the center and radius of the disk of $s$ and $(\gamma,\varphi,\theta,\psi)$ are its angular coordinates.
--   2. For $z=(\gamma,\varphi,\theta,\psi)\in\Omega\times\mathbb R$ and $\nabla=(\nabla_\gamma,\nabla_\varphi,\nabla_\theta,\nabla_\psi)\in\mathbb R^4$, the **pencil residual** is
--   $$
--   \mathcal E_U[H;\nabla](z)=\cos\theta\Big(\frac\pi2-\theta\Big)+\sin\theta-U\cos\varphi-\cos\theta\,H(z)+\cos\theta\,(\psi-\varphi)\,\nabla_\psi-\mathcal A\,\nabla_\gamma+\sin\theta\,\nabla_\theta,
--   $$
--   with $\mathcal A=(\sin\varphi-\sin\gamma\cos\theta)/\cos\gamma$. If $H$ is differentiable at $z$, $\mathcal E_U[H](z)=\mathcal E_U[H;\nabla H(z)](z)$.
--
--   The potential is the form in which the paper looks for a feasible potential, and the pencil residual is its rate of change along a pencil of circles (Lemma 4.4).
--
--   **Formalization Note** $H$ is a function on $\mathbb R^4$; only its values on $\Omega\times\mathbb R$ are read. $\nabla H(z)$ is the vector of the four partial derivatives (the Fréchet derivative applied to the coordinate vectors). The same module defines the dot product of $\mathbb R^4$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 4.3, p.24

import Mathlib
import Definitions.Def_DelaunayStretch_SigmaSet

namespace DelaunayStretch

/-- The dot product `∇ · w` of two vectors of `ℝ⁴`. -/
def dot4 (g w : R4) : ℝ := g.1 * w.1 + g.2.1 * w.2.1 + g.2.2.1 * w.2.2.1 + g.2.2.2 * w.2.2.2

/-- The gradient `∇F(z) = (∂_γ F, ∂_φ F, ∂_θ F, ∂_ψ F)(z)` of `F : ℝ⁴ → ℝ`, from its Fréchet
derivative. -/
noncomputable def gradient4 (F : R4 → ℝ) (z : R4) : R4 :=
  (fderiv ℝ F z (1, 0, 0, 0), fderiv ℝ F z (0, 1, 0, 0), fderiv ℝ F z (0, 0, 1, 0),
    fderiv ℝ F z (0, 0, 0, 1))

/-- **The potential of `H` at level `U`** (Definition 4.3(1), equation (4.3), p.24):
`W_{H,U}(s) = r[π/2 − θ − H(γ, φ, θ, ψ)] + U(x(c(s)) − x(o))`, where `o`, `r` are the center
and radius of the disk of `s` and `(γ, φ, θ, ψ)` are its angular coordinates.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 4.3, p.24.

**Formalization Note** `H` is a function on all of `ℝ⁴`; at gate states the angular
coordinates lie in `Σ ⊆ Ω × ℝ` (Lemma 4.2), so only the values of `H` on `Ω × ℝ` enter. -/
noncomputable def potential (H : R4 → ℝ) (U : ℝ) (s : GateState) : ℝ :=
  s.O.radius * (Real.pi / 2 - s.thetaCoord - H s.angularCoords) +
    U * (s.crossing.re - s.O.center.re)

/-- `𝓐 = (sin φ − sin γ cos θ)/cos γ` (Definition 4.3(2), p.24). -/
noncomputable def pencilA (z : R4) : ℝ :=
  (Real.sin z.2.1 - Real.sin z.1 * Real.cos z.2.2.1) / Real.cos z.1

/-- **The pencil residual** (Definition 4.3(2), equation (4.4), p.24): for
`z = (γ, φ, θ, ψ)` and `∇ = (∇γ, ∇φ, ∇θ, ∇ψ)`,
`𝓔_U[H; ∇](z) = cos θ(π/2 − θ) + sin θ − U cos φ − cos θ H(z) + cos θ (ψ − φ) ∇ψ − 𝓐 ∇γ
+ sin θ ∇θ`. -/
noncomputable def pencilResidual (U : ℝ) (H : R4 → ℝ) (g z : R4) : ℝ :=
  Real.cos z.2.2.1 * (Real.pi / 2 - z.2.2.1) + Real.sin z.2.2.1 - U * Real.cos z.2.1 -
    Real.cos z.2.2.1 * H z + Real.cos z.2.2.1 * (z.2.2.2 - z.2.1) * g.2.2.2 -
    pencilA z * g.1 + Real.sin z.2.2.1 * g.2.2.1

/-- `𝓔_U[H](z) = 𝓔_U[H; ∇H(z)](z)` for `H` differentiable at `z` (Definition 4.3(2), p.24). -/
noncomputable def pencilResidualGrad (U : ℝ) (H : R4 → ℝ) (z : R4) : ℝ :=
  pencilResidual U H (gradient4 H z) z

end DelaunayStretch


