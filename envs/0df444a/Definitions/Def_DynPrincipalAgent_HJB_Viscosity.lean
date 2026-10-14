-- Prove2me | Definitions.Def_DynPrincipalAgent_HJB_Viscosity
-- name    : DynPrincipalAgent_HJB_Viscosity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:29.274984+00:00
-- url     : https://prove2.me/theorems/fd73de1c-0c34-4cb5-973e-53cefb40233b
-- title:
--   (4.5)–(4.6), (6.6) — viscosity sub- and supersolutions of the type-θ HJB equation on D_θ and the boundary conditions (6.6)
-- statement:
--   This file defines what it means for a function $u(t,x)$ to be a continuous viscosity solution of the principal's HJB equation for an agent of type $\theta$, and the boundary conditions (6.6) for a family of such functions.
--
--   The HJB operator of (4.5) is
--   $$\mathcal L^\theta u(t,x)=\partial_t u+\sup_{\eta\le C_0,\ z\in\mathbb R}\Big[\tfrac12|z|^2\partial_{xx}u-\big[f(\theta;t,\eta)+\tilde H(\theta;t,z)\big]\partial_x u+I^h(\theta;t,z)-\eta\Big],$$
--   and the equation (4.6) is $\mathcal L^\theta u=0$ on $D_\theta$.
--
--   1. $u$ is a **viscosity subsolution** if for every $C^2$ test function $\varphi$ on $\mathbb R^2$ and every point $(t_0,x_0)$ of the interior $O_\theta$ at which $u-\varphi$ has a local maximum, $\mathcal L^\theta\varphi(t_0,x_0)\ge0$.
--   2. $u$ is a **viscosity supersolution** if at every point of $O_\theta$ where $u-\varphi$ has a local minimum, $\mathcal L^\theta\varphi(t_0,x_0)\le0$.
--   3. $u$ is a **continuous viscosity solution** of (4.6) if it is continuous on $D_\theta$ and both a sub- and a supersolution.
--
--   For a family $\{u(\theta;\cdot,\cdot)\}_{\theta\in\Theta}$ the boundary conditions (6.6) are
--   $$u(\theta;t,\overline L^\theta_t)=-C_0(T-t)\ \ (t\in[0,T)),\qquad u(\theta;T-,x)=0\ \ (x\in(\underline L^\theta_T,0)),\qquad u(\theta;t,\underline L^\theta_t+)\ge\overline u(t)\ \ (t\in[0,T)),$$
--   where $\overline u(t)=\sup_{\theta'\in\Theta}u(\theta';t,R^{\theta'}_t)-c^P_t$ is built from the family itself. The equations for different types are coupled through this last condition.
--
--   **Formalization Note.** The paper relies on Crandall–Ishii–Lions for the notion of viscosity solution; the standard notion is used, with test functions $C^2$ on $\mathbb R^2$, local extrema on a neighbourhood in $\mathbb R^2$, and the equation tested at points of the open set $O_\theta$. The supremum in (4.5) may be $+\infty$, so it is never formed: the subsolution test reads "for every $\varepsilon>0$ some $\eta\le C_0$ and $z$ make $\partial_t\varphi+[\cdots]>-\varepsilon$", and the supersolution test "every $\eta\le C_0$ and $z$ give $\partial_t\varphi+[\cdots]\le0$". The right limit $u(\theta;t,\underline L^\theta_t+)$ is required to exist as a real number $\ell$, and $\ell\ge\overline u(t)$ is written as $\ell\ge u(\theta';t,R^{\theta'}_t)-c^P_t$ for every $\theta'$, which avoids a possibly unbounded real supremum. The left limit $u(\theta;T-,x)$ is the limit of $u(\theta;s,x)$ as $s\uparrow T$.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, (4.5)–(4.6), p. 18; (6.6), p. 31; proof of Theorem 6.3, p. 32

import Mathlib
import Definitions.Def_DynPrincipalAgent_HJB_Model

open Set Filter Topology
open scoped NNReal

namespace DynPrincipalAgent.HJB

namespace Model

variable {Θ : Type} (M : Model Θ)

/-- The bracket of the HJB operator (4.5) for a payment `η` and a sensitivity `z`, evaluated on the
derivatives `p_x = ∂_x u(t, x)`, `p_xx = ∂_xx u(t, x)`:
`½ |z|² p_xx − [f(θ; t, η) + H̃(θ; t, z)] p_x + I^h(θ; t, z) − η`. -/
noncomputable def hamIn (θ : Θ) (t η z px pxx : ℝ) : ℝ :=
  (1 / 2) * z ^ 2 * pxx - (M.f θ t η + M.Htil θ t z) * px + M.Ih θ t z - η

end Model

/-- `∂_t φ(t, x)`. -/
noncomputable def dt (φ : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun s => φ s x) t

/-- `∂_x φ(t, x)`. -/
noncomputable def dx (φ : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun y => φ t y) x

/-- `∂_xx φ(t, x)`. -/
noncomputable def dxx (φ : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y => deriv (fun y' => φ t y') y) x

namespace Model

variable {Θ : Type} (M : Model Θ)

/-- `u` is a viscosity subsolution of `𝓛^θ u = 0` ((4.5)–(4.6)) on the interior `O_θ` of `D_θ`: for every
`C²` test function `φ` on `ℝ²` and every point `(t₀, x₀) ∈ O_θ` at which `u − φ` has a local maximum,
`∂_t φ + sup_{η ≤ C₀, z ∈ ℝ} [½ z² ∂_xx φ − (f(θ; t₀, η) + H̃(θ; t₀, z)) ∂_x φ + I^h(θ; t₀, z) − η] ≥ 0`,
written without forming the (possibly infinite) supremum: for every `ε > 0` some `η ≤ C₀` and `z` give
a value `> −ε`. -/
def IsViscSub (θ : Θ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ → ℝ, ContDiff ℝ 2 (fun q : ℝ × ℝ => φ q.1 q.2) →
    ∀ p ∈ M.O θ, IsLocalMax (fun q : ℝ × ℝ => u q.1 q.2 - φ q.1 q.2) p →
      ∀ ε > 0, ∃ η ≤ M.C₀, ∃ z : ℝ,
        -ε < dt φ p.1 p.2 + M.hamIn θ p.1 η z (dx φ p.1 p.2) (dxx φ p.1 p.2)

/-- `u` is a viscosity supersolution of `𝓛^θ u = 0` ((4.5)–(4.6)) on `O_θ`: for every `C²` test function
`φ` and every `(t₀, x₀) ∈ O_θ` at which `u − φ` has a local minimum, the supremum in (4.5) is `≤ 0`, i.e.
every `η ≤ C₀` and every `z` give `∂_t φ + [·] ≤ 0`. -/
def IsViscSuper (θ : Θ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ → ℝ, ContDiff ℝ 2 (fun q : ℝ × ℝ => φ q.1 q.2) →
    ∀ p ∈ M.O θ, IsLocalMin (fun q : ℝ × ℝ => u q.1 q.2 - φ q.1 q.2) p →
      ∀ η ≤ M.C₀, ∀ z : ℝ,
        dt φ p.1 p.2 + M.hamIn θ p.1 η z (dx φ p.1 p.2) (dxx φ p.1 p.2) ≤ 0

/-- `u` is a continuous viscosity solution of the HJB equation (4.6) `𝓛^θ u = 0` on `D_θ`: continuous on
`D_θ`, and a viscosity sub- and supersolution on its interior. -/
def IsContViscSol (θ : Θ) (u : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun q : ℝ × ℝ => u q.1 q.2) (M.D θ) ∧ M.IsViscSub θ u ∧ M.IsViscSuper θ u

/-- The boundary conditions (6.6) for a family `{u(θ; ·, ·)}_{θ ∈ Θ}`, with the boundary function at the
lower barrier built from the family itself, `ū(t) = sup_{θ'} u(θ'; t, R^{θ'}_t) − c^P_t`:
* `u(θ; t, L̄^θ_t) = −C₀ (T − t)` for `t ∈ [0, T)`;
* `u(θ; T−, x) = 0` for `x ∈ (L̲^θ_T, 0)`, i.e. `u(θ; s, x) → 0` as `s ↑ T`;
* `u(θ; t, L̲^θ_t +) ≥ ū(t)` for `t ∈ [0, T)`: the right limit `ℓ` of `x ↦ u(θ; t, x)` at `L̲^θ_t`
  exists and `ℓ ≥ u(θ'; t, R^{θ'}_t) − c^P_t` for every `θ'` (equivalent to `ℓ ≥ ū(t)`, without forming
  the supremum). -/
def BC6_6 (u : Θ → ℝ → ℝ → ℝ) : Prop :=
  (∀ θ, ∀ t : ℝ, 0 ≤ t → t < (M.T : ℝ) → u θ t (M.Lbar θ t) = -M.C₀ * ((M.T : ℝ) - t)) ∧
  (∀ θ, ∀ x : ℝ, M.Lund θ M.T < x → x < 0 →
    Tendsto (fun s => u θ s x) (𝓝[<] (M.T : ℝ)) (𝓝 0)) ∧
  (∀ θ, ∀ t : ℝ, 0 ≤ t → t < (M.T : ℝ) → ∃ ℓ : ℝ,
    Tendsto (u θ t) (𝓝[>] (M.Lund θ t)) (𝓝 ℓ) ∧
    ∀ θ' : Θ, u θ' t (M.R θ' t) - M.cP t ≤ ℓ)

end Model

end DynPrincipalAgent.HJB


