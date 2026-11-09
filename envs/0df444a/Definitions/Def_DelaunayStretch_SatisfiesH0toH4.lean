-- Prove2me | Definitions.Def_DelaunayStretch_SatisfiesH0toH4
-- name    : DelaunayStretch_SatisfiesH0toH4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:56:19.896034+00:00
-- url     : https://prove2.me/theorems/5ecd3d95-44bb-4d37-a950-d84d36cb3448
-- title:
--   Conditions (H0)–(H4) at level $U$
-- statement:
--   Let $U\in\mathbb R$ and let $H$ be a real function on $\Omega\times\mathbb R$. $H$ **satisfies (H0)–(H4) at level $U$** if there is a piecewise $C^1$ structure for $H$ such that, with incident gradients taken with respect to it:
--
--   1. (H0) $H$ is continuous and locally Lipschitz;
--   2. (H1) $|H(\gamma,\varphi,\theta,\psi_1)-H(\gamma,\varphi,\theta,\psi_2)|\le|\psi_1-\psi_2|$ for all $(\gamma,\varphi,\theta)\in\Omega$ and all $\psi_1,\psi_2\in\mathbb R$;
--   3. (H2) $\nabla_\theta\ge|\nabla_\varphi|$ for every $z\in\Omega\times\mathbb R$ and every incident gradient $\nabla$ of $H$ at $z$;
--   4. (H3) $H(\gamma,\varphi,\theta,\gamma)\ge\frac\pi2-U\cos\gamma$ and $H(\gamma,\varphi,\theta,-\gamma)\le-\frac\pi2+U\cos\gamma$ for all $(\gamma,\varphi,\theta)\in\Omega$;
--   5. (H4) $\mathcal E_U[H;\nabla](z)\le0$ for every $z\in\Sigma$ and every incident gradient $\nabla$ of $H$ at $z$.
--
--   Theorem 4.7 shows that these five conditions make $W_{H,U}$ a feasible potential. The module also defines each condition separately, for the lemmas that assume only some of them.
--
--   **Formalization Note** (H1) and (H2) are required for all real $\psi$, (H4) only on $\Sigma$, as in the source. "Locally Lipschitz" is on $\Omega\times\mathbb R$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 4.6, pp.26–27

import Mathlib
import Definitions.Def_DelaunayStretch_PiecewiseC1

namespace DelaunayStretch

/-- (H0) `H` is continuous and locally Lipschitz on `Ω × ℝ` (Definition 4.6, p.26). -/
def CondH0 (H : R4 → ℝ) : Prop :=
  ContinuousOn H OmegaTimesR ∧ LocallyLipschitzOn OmegaTimesR H

/-- (H1) `|H(γ, φ, θ, ψ₁) − H(γ, φ, θ, ψ₂)| ≤ |ψ₁ − ψ₂|` for all `(γ, φ, θ) ∈ Ω` and **all**
`ψ₁, ψ₂ ∈ ℝ` (Definition 4.6, p.26). -/
def CondH1 (H : R4 → ℝ) : Prop :=
  ∀ γ φ θ : ℝ, (γ, φ, θ) ∈ OmegaSet → ∀ ψ₁ ψ₂ : ℝ,
    |H (γ, φ, θ, ψ₁) - H (γ, φ, θ, ψ₂)| ≤ |ψ₁ - ψ₂|

/-- (H2) `∇θ ≥ |∇φ|` for every `z ∈ Ω × ℝ` and every incident gradient `∇` of `H` at `z`
(Definition 4.6, p.26). -/
def CondH2 {H : R4 → ℝ} (P : PiecewiseC1 H) : Prop :=
  ∀ z ∈ OmegaTimesR, ∀ g : R4, P.IncidentGradient z g → |g.2.1| ≤ g.2.2.1

/-- (H3) `H(γ, φ, θ, γ) ≥ π/2 − U cos γ` and `H(γ, φ, θ, −γ) ≤ −π/2 + U cos γ` for all
`(γ, φ, θ) ∈ Ω` (Definition 4.6, p.26). -/
def CondH3 (U : ℝ) (H : R4 → ℝ) : Prop :=
  ∀ γ φ θ : ℝ, (γ, φ, θ) ∈ OmegaSet →
    Real.pi / 2 - U * Real.cos γ ≤ H (γ, φ, θ, γ) ∧
      H (γ, φ, θ, -γ) ≤ -(Real.pi / 2) + U * Real.cos γ

/-- (H4) `𝓔_U[H; ∇](z) ≤ 0` for every `z ∈ Σ` and every incident gradient `∇` of `H` at `z`
(Definition 4.6, p.27). -/
def CondH4 (U : ℝ) {H : R4 → ℝ} (P : PiecewiseC1 H) : Prop :=
  ∀ z ∈ SigmaSet, ∀ g : R4, P.IncidentGradient z g → pencilResidual U H g z ≤ 0

/-- **`H` satisfies (H0)–(H4) at level `U`** (Definition 4.6, pp.26–27): there is a piecewise
`C¹` structure for `H` such that (H0), (H1), (H2), (H3) and (H4) hold, incident gradients being
taken with respect to this structure.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 4.6, pp.26–27.

**Formalization Note** `H` is a function on `ℝ⁴ = {(γ, φ, θ, ψ)}`; every condition reads it only
on `Ω × ℝ` (on `Σ` for (H4)). (H1) and (H2) are required for all real `ψ`, as on p.27. -/
def SatisfiesH0toH4 (U : ℝ) (H : R4 → ℝ) : Prop :=
  ∃ P : PiecewiseC1 H, CondH0 H ∧ CondH1 H ∧ CondH2 P ∧ CondH3 U H ∧ CondH4 U P

end DelaunayStretch


