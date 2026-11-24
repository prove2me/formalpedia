-- Prove2me | Definitions.Def_PDSmooth_Framework_Supplement_Problem
-- name    : PDSmooth_Framework_Supplement_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:50:50.448887+00:00
-- url     : https://prove2.me/theorems/7180fed1-e1e4-4aba-b93b-33d563474b19
-- title:
--   §5, pp. 9, 19–20, 24 — problem (5.1), standing assumptions of §5, max-structure (5.2)–(5.4), dual objective (5.5), Ω (5.26)
-- statement:
--   Let $\mathbb U$ be a finite-dimensional real normed space with dual $\mathbb U^*$ (dual norm $\|\cdot\|_*$), and consider the composite problem
--
--   $$
--   (P):\qquad P^*:=\min_{u\in\mathcal U}\ \big\{P(u):=h(u)+\zeta(u)+\mu\,\omega_{\mathcal U}(u)\big\}. \tag{5.1}
--   $$
--
--   The **standing assumptions of §5** (`Sec5Setting`) are:
--
--   1. $\mathcal U\subseteq\mathbb U$ is nonempty, convex and closed;
--   2. $\omega_{\mathcal U}$ is a distance generating function on $\mathcal U$: continuous and $1$-strongly convex on $\mathcal U$, and differentiable on the interior of its domain, an open convex set written $W^o$; $\mathcal U^o:=\mathcal U\cap W^o$;
--   3. $h$ is $L_h$-smooth on $\mathcal U$: differentiable on an open set $\mathcal U'\supseteq\mathcal U$, with $\|\nabla h(u)-\nabla h(u')\|_*\le L_h\|u-u'\|$ for $u,u'\in\mathcal U$;
--   4. $h$ and $\zeta$ are convex on $\mathcal U$, $\zeta$ is closed (lower semicontinuous on $\mathcal U$), and $\mu\ge0$.
--
--   The **max-structure** of $h$ (`MaxStructure`) is: a nonempty, compact, convex set $\mathcal V$ inside an open set $\mathcal V'$ of a finite-dimensional normed space $\mathbb V$, and a function $\bar\Psi:\mathcal U'\times\mathcal V'\to\mathbb R$, jointly continuous, with
--
--   $$
--   h(u)=\max_{v\in\mathcal V}\bar\Psi(u,v)\quad(u\in\mathcal U'), \tag{5.2}
--   $$
--
--   $\bar\Psi(\cdot,v)$ convex on $\mathcal U$ and differentiable on $\mathcal U'$ for $v\in\mathcal V$,
--
--   $$
--   \|\nabla_u\bar\Psi(u,v)-\nabla_u\bar\Psi(u',v)\|_*\le L_{uu}\|u-u'\|,\qquad \|\nabla_u\bar\Psi(u,v)-\nabla_u\bar\Psi(u,v')\|_*\le L_{uv}\|v-v'\| \tag{5.3–5.4}
--   $$
--
--   for $u,u'\in\mathcal U$, $v,v'\in\mathcal V$, and $\bar\Psi(u,\cdot)$ $\rho$-strongly concave on $\mathcal V$ for $u\in\mathcal U$, with $\rho>0$.
--
--   Finally, `Pobj` is $P$; `dualInner` is the function $u\mapsto\bar\Psi(u,v)+\zeta(u)+\mu\omega_{\mathcal U}(u)$ whose infimum over $\mathcal U$ is the dual function $\Xi(v)$ of (5.5); and `OmegaU` is $\Omega_{\omega_{\mathcal U}}(u_0)=\max_{u\in\mathcal U}D_{\omega_{\mathcal U}}(u,u_0)$ of (5.26), with $D$ the Bregman divergence (2.4) of the base mission.
--
--   These objects are the setting of the non-Hilbertian inexact accelerated proximal gradient method of §5 (Algorithm 2) and of its convergence theorems.
--
--   **Formalization Note** $\omega_{\mathcal U}$ is real-valued; only its values on $\mathcal U$ enter, and the open convex set $W^o$ stands for $\operatorname{int}\operatorname{dom}\omega_{\mathcal U}$. Essential smoothness (continuity of $\nabla\omega_{\mathcal U}$ and its blow-up at the boundary) is not required. Strong convexity and strong concavity are Mathlib's `StrongConvexOn`/`StrongConcaveOn`. The overloaded $\rho$ of §5 (strong-concavity modulus) is written `ρv`. `OmegaU` is a real supremum; the theorems that use it prove its finiteness.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, pp. 9, 19–20, 24, §2.2, (5.1)–(5.6), (5.26)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Bregman

namespace PDSmooth.Framework.Supplement

/-- The standing assumptions of §5 (pp. 9, 19) for problem (5.1),
`P* = min_{u ∈ U} P(u)`, `P = h + ζ + μ ω_U`:
* `U` is a nonempty, convex and closed set in the normed space `𝕌`;
* `ω = ω_U` is a DGF on `U` (§2.2, p. 9): continuous and `1`-strongly convex on `U`, and
  differentiable on the interior of its domain, which is the open convex set `Wo`
  (so `U° = U ∩ Wo`);
* `h` is `L_h`-smooth on `U`: differentiable on an open set `U' ⊇ U`, with `∇h` `L_h`-Lipschitz on
  `U` (dual norm = operator norm);
* `h` and `ζ` are convex on `U`, `ζ` is closed (lower semicontinuous on `U`), and `μ ≥ 0`. -/
structure Sec5Setting {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU]
    (U U' Wo : Set UU) (h ζ ω : UU → ℝ) (Lh μ : ℝ) : Prop where
  U_nonempty : U.Nonempty
  U_convex : Convex ℝ U
  U_closed : IsClosed U
  ω_cont : ContinuousOn ω U
  ω_strong : StrongConvexOn U 1 ω
  Wo_open : IsOpen Wo
  Wo_convex : Convex ℝ Wo
  ω_diff : ∀ u ∈ Wo, DifferentiableAt ℝ ω u
  U'_open : IsOpen U'
  U_sub : U ⊆ U'
  h_diff : ∀ u ∈ U', DifferentiableAt ℝ h u
  h_lip : ∀ u ∈ U, ∀ u' ∈ U, ‖fderiv ℝ h u - fderiv ℝ h u'‖ ≤ Lh * ‖u - u'‖
  h_convex : ConvexOn ℝ U h
  ζ_convex : ConvexOn ℝ U ζ
  ζ_lsc : LowerSemicontinuousOn ζ U
  μ_nonneg : 0 ≤ μ

/-- The max-structure of `h` (§5, pp. 19–20): `V` is nonempty, compact and convex inside an open
set `V'`; `Ψ = Ψ̄ : U' × V' → ℝ` is jointly continuous; `h(u) = max_{v ∈ V} Ψ̄(u,v)` for `u ∈ U'`
(5.2); for `v ∈ V`, `Ψ̄(·,v)` is convex on `U` and differentiable on `U'`; (5.3) and (5.4) hold
for `u, u' ∈ U`, `v, v' ∈ V`; and `Ψ̄(u,·)` is `ρ`-strongly concave on `V` for `u ∈ U`, `ρ > 0`. -/
structure MaxStructure {UU VV : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU]
    [NormedAddCommGroup VV] [NormedSpace ℝ VV]
    (U U' : Set UU) (h : UU → ℝ) (V V' : Set VV) (Ψ : UU → VV → ℝ) (Luu Luv ρv : ℝ) : Prop where
  V_nonempty : V.Nonempty
  V_compact : IsCompact V
  V_convex : Convex ℝ V
  V'_open : IsOpen V'
  V_sub : V ⊆ V'
  Ψ_cont : ContinuousOn (fun p : UU × VV => Ψ p.1 p.2) (U' ×ˢ V')
  h_max : ∀ u ∈ U', IsGreatest ((fun v => Ψ u v) '' V) (h u)
  Ψ_convex : ∀ v ∈ V, ConvexOn ℝ U (fun u => Ψ u v)
  Ψ_diff : ∀ v ∈ V, ∀ u ∈ U', DifferentiableAt ℝ (fun y => Ψ y v) u
  lip_uu : ∀ u ∈ U, ∀ u' ∈ U, ∀ v ∈ V,
    ‖fderiv ℝ (fun y => Ψ y v) u - fderiv ℝ (fun y => Ψ y v) u'‖ ≤ Luu * ‖u - u'‖
  lip_uv : ∀ u ∈ U, ∀ v ∈ V, ∀ v' ∈ V,
    ‖fderiv ℝ (fun y => Ψ y v) u - fderiv ℝ (fun y => Ψ y v') u‖ ≤ Luv * ‖v - v'‖
  ρv_pos : 0 < ρv
  Ψ_strongConcave : ∀ u ∈ U, StrongConcaveOn V ρv (fun v => Ψ u v)

/-- (5.1), p. 19: the objective `P(u) = h(u) + ζ(u) + μ ω_U(u)`. -/
noncomputable def Pobj {UU : Type*} (h ζ ω : UU → ℝ) (μ : ℝ) (u : UU) : ℝ :=
  h u + ζ u + μ * ω u

/-- (5.5), p. 20: the function inside the infimum defining the dual function,
`Ξ(v) = inf_{u ∈ U} dualInner Ψ ζ ω μ v u`, with `dualInner Ψ ζ ω μ v u = Ψ̄(u,v) + ζ(u) + μ ω_U(u)`. -/
noncomputable def dualInner {UU VV : Type*} (Ψ : UU → VV → ℝ) (ζ ω : UU → ℝ) (μ : ℝ) (v : VV)
    (u : UU) : ℝ :=
  Ψ u v + ζ u + μ * ω u

/-- (5.26), p. 24: `Ω_{ω_U}(u₀) = max_{u ∈ U} D_{ω_U}(u, u₀)`, as a real supremum of the image. -/
noncomputable def OmegaU {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU]
    (ω : UU → ℝ) (U : Set UU) (u0 : UU) : ℝ :=
  sSup ((fun u => PDSmooth.Framework.bregman ω u u0) '' U)

end PDSmooth.Framework.Supplement


