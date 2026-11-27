-- Prove2me | Definitions.Def_ALAVI_Supplement_Psi
-- name    : ALAVI_Supplement_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:27:47.881268+00:00
-- url     : https://prove2.me/theorems/152f23cb-924f-5d79-b10d-83b8ad010250
-- title:
--   The bifunction $\Psi(u,p,\zeta,\lambda)$ of the primal-dual gap function (§5.3)
-- statement:
--   Let $E=\mathbb R^n$ and $F=\mathbb R^m$ be finite-dimensional real inner product spaces, $G:E\to E$ a mapping, $J:E\to(-\infty,+\infty]$ a function and $\Theta:E\to F$ a mapping. For $u,\zeta\in E$ and $p,\lambda\in F$ define
--
--   $$
--   \Psi(u,p,\zeta,\lambda)=\langle G(\zeta),u-\zeta\rangle+J(u)-J(\zeta)+\langle\lambda,\Theta(u)\rangle-\langle p,\Theta(\zeta)\rangle .
--   $$
--
--   For a radius $r>0$, the paper's **primal-dual gap function** of (VIP) is
--
--   $$
--   \psi(u,p)=\max_{(\zeta,\lambda)\in(U\cap\mathfrak B_u(r))\times(C^*\cap\mathfrak B_p(r))}\Psi(u,p,\zeta,\lambda),
--   $$
--
--   where $\mathfrak B_u(r)$ and $\mathfrak B_p(r)$ are the balls of radius $r$ centred at the origin of $E$ and $F$. The ergodic rate of ALAVI for monotone $G$ (Theorem 3) is a bound on $\psi$ at the averaged iterates.
--
--   **Formalization Note.** $J$ enters through its real value $J(\cdot)$ on $\operatorname{dom}J$ (`EReal.toReal`), as in the published Lagrangian `ALAVI.Lag`; every statement that uses $\Psi$ evaluates it only at points where $J(u)$ and $J(\zeta)$ are finite. $\psi$ is not a separate declaration: a bound $\psi(u,p)\le c$ is stated as $\Psi(u,p,\zeta,\lambda)\le c$ for every $(\zeta,\lambda)$ in the product of balls.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, §5.3, definition of Ψ and ψ, p.21

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI.Supplement

/-- **The bifunction Ψ of §5.3**,
`Ψ(u, p, ζ, λ) = ⟨G(ζ), u - ζ⟩ + J(u) - J(ζ) + ⟨λ, Θ(u)⟩ - ⟨p, Θ(ζ)⟩`
for `u, ζ ∈ E` and `p, λ ∈ F`. The primal-dual gap function of (VIP) is
`ψ(u, p) = max_{(ζ, λ) ∈ (U ∩ B_u(r)) × (C* ∩ B_p(r))} Ψ(u, p, ζ, λ)`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, §5.3, definition of Ψ and ψ, p.21.

Formalization Note: `J : E → (-∞, +∞]` enters through `(J ·).toReal`, as in the published
`ALAVI.Lag`; every statement using `Psi` evaluates it only where `J(u)` and `J(ζ)` are finite
(`u, ζ ∈ dom J`). The dual test point `λ` is written `b` (`λ` is a Lean keyword). The gap
function `ψ` is not a separate declaration: a bound `ψ(u, p) ≤ c` is stated as
`Psi … u p ζ b ≤ c` for every `(ζ, b)` in the ball product. -/
noncomputable def Psi {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (G : E → E) (J : E → EReal) (Θ : E → F) (u : E) (p : F) (ζ : E) (b : F) : ℝ :=
  inner ℝ (G ζ) (u - ζ) + (J u).toReal - (J ζ).toReal + inner ℝ b (Θ u) - inner ℝ p (Θ ζ)

end ALAVI.Supplement


