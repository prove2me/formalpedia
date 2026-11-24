-- Prove2me | Definitions.Def_DelaunayStretch_PieceResiduals
-- name    : DelaunayStretch_PieceResiduals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T07:33:22.977858+00:00
-- url     : https://prove2.me/theorems/acd6e2d8-55fe-4c72-9a14-26d6632ab680
-- title:
--   Coordinates $(\gamma,a,b,\xi)$, accessibility (6.2) and the residuals $E^c_U$, $E^\pm_U$ of $H_\star$
-- statement:
--   Coordinates and residuals of §6.1 (pp.39) of Mo–Cheng–Ding for the explicit function $H_\star$.
--
--   1. **Coordinates.** For $\gamma\in\mathbb R$ and $a,b,\xi\in\mathbb R$, the point with coordinates $(\gamma,a,b,\xi)$ is $(\gamma,\varphi,\theta,\psi)$, where
--   $$
--   \theta=\big(\tfrac\pi2+\gamma\big)a+\big(\tfrac\pi2-\gamma\big)b,\qquad \varphi=\gamma-\big(\tfrac\pi2+\gamma\big)a+\big(\tfrac\pi2-\gamma\big)b,\qquad \psi=k(\gamma)\,\xi,
--   $$
--   with $k(\gamma)=\frac\pi2-\cos\gamma$. These are the relations (5.1).
--   2. **Accessibility** (6.2): $|k(\gamma)\xi-\varphi|\le\sin\theta$. By Lemma 6.1(1), the points of $\bar\Sigma$ with $0\le\gamma<\frac\pi2$ are those with $(a,b)\in[0,1]^2$ satisfying (6.2).
--   3. **Residuals** (6.1). The residual of the central piece is $E^c_U(\gamma,a,b,\xi)=\mathcal E_U[H^c]$ at the point with coordinates $(\gamma,a,b,\xi)$. For the outer pieces $\pm\xi\ge1$, $E^\pm_U(\gamma,a,b)=\mathcal E_U[H^\pm]$, evaluated at $\xi=\pm1$. Here $\mathcal E_U[F]$ is the pencil residual of Definition 4.3 with the gradient of $F$, and $H^c,H^\pm$ are the piece functions of Definition 5.5 for $H_\star$.
--
--   The residuals turn condition (H4) into explicit inequalities on closed boxes in $(\gamma,a,b,\xi)$. These are what the computer-assisted verification of Proposition 6.7 checks.
--
--   **Formalization Note** The residual of an outer piece does not depend on $\xi$, because $H^\pm$ does not depend on $\psi$; it is evaluated at $\xi=\pm1$.
-- source:
--   Mo, Cheng, Ding, arXiv:2609.07979v6, §6.1, (6.1)–(6.2) and Lemma 6.1 (p.39), with (5.1) (p.31)

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients
import Definitions.Def_DelaunayStretch_potential

namespace DelaunayStretch

/-- The point `(γ, φ, θ, ψ)` of `Ω × ℝ` with coordinates `(γ, a, b, ξ)` (Definition 5.2, (5.1),
p.31): `θ = (π/2 + γ) a + (π/2 − γ) b`, `φ = γ − (π/2 + γ) a + (π/2 − γ) b`, `ψ = k(γ) ξ` with
`k(γ) = π/2 − cos γ`. -/
noncomputable def coordPt (γ a b ξ : ℝ) : R4 :=
  (γ, γ - (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b,
    (Real.pi / 2 + γ) * a + (Real.pi / 2 - γ) * b, (Real.pi / 2 - Real.cos γ) * ξ)

/-- Accessibility (6.2) (Lemma 6.1(1), p.39): `|k(γ) ξ − φ| ≤ sin θ`, with `φ, θ` from (5.1). -/
def Accessible (γ a b ξ : ℝ) : Prop :=
  |(Real.pi / 2 - Real.cos γ) * ξ - (coordPt γ a b ξ).2.1| ≤ Real.sin (coordPt γ a b ξ).2.2.1

/-- The residual `E^c_U(γ, a, b, ξ)` of the central piece of `H⋆` (6.1), p.39: the pencil
residual `𝓔_U[H^c]` at the point with coordinates `(γ, a, b, ξ)`. -/
noncomputable def resC (U γ a b ξ : ℝ) : ℝ :=
  pencilResidual U (pieceHc hstarV hstarR hstarB hstarD)
    (gradient4 (pieceHc hstarV hstarR hstarB hstarD) (coordPt γ a b ξ)) (coordPt γ a b ξ)

/-- The residual `E^±_U(γ, a, b)` of the outer piece `±ξ ≥ 1` of `H⋆` (6.1), p.39 (`s = ±1`):
the pencil residual `𝓔_U[H^±]` at the point with coordinates `(γ, a, b, s)`; it does not depend
on `ξ`, since `H^±` does not depend on `ψ`. -/
noncomputable def resOut (U s γ a b : ℝ) : ℝ :=
  pencilResidual U (pieceHout hstarV hstarR hstarB hstarD s)
    (gradient4 (pieceHout hstarV hstarR hstarB hstarD s) (coordPt γ a b s)) (coordPt γ a b s)

end DelaunayStretch


