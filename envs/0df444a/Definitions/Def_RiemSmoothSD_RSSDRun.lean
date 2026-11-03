-- Prove2me | Definitions.Def_RiemSmoothSD_RSSDRun
-- name    : RiemSmoothSD_RSSDRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:59.378198+00:00
-- url     : https://prove2.me/theorems/3f5c5e38-f2d0-416b-91bb-1ae76cd12f97
-- title:
--   Algorithm 4.1 (RSSD): Armijo step, run, index set $K$, Assumption 4.1
-- statement:
--   Let $\mathcal M\subseteq E$, a map $R$, and $\tilde f:E\times\mathbb R_+\to\mathbb R$ be given, and write $\operatorname{grad} g(x)=\mathrm{Proj}_{T_x\mathcal M}\nabla g(x)$ for the Riemannian gradient.
--
--   1. **Armijo condition (4.1).** For a cost $g$, a point $x$ and $m\in\mathbb N$, with $\eta=-\operatorname{grad}g(x)$:
--   $$
--   g\big(R_x(\beta^m\bar\alpha\,\eta)\big)\le g(x)-\sigma\beta^m\bar\alpha\,\|\operatorname{grad}g(x)\|^2 .
--   $$
--   An **Armijo step** from $x$ is $x'=R_x(\beta^m\bar\alpha\,\eta)$ with $m$ the least natural number satisfying (4.1).
--   2. **Input.** $x_0\in\mathcal M$, $\delta_0>0$, $\mu_0>0$, $\beta\in(0,1)$, $\bar\alpha>0$, $\theta_\delta\in(0,1)$, $\theta_\mu\in(0,1)$ and $\sigma\in(0,1)$.
--   3. **Run (Algorithm 4.1 with $\delta_{opt}=\mu_{opt}=0$).** Sequences $(x_\ell,\mu_\ell,\delta_\ell)$ starting at $(x_0,\mu_0,\delta_0)$ such that, with $\eta_\ell=-\operatorname{grad}\tilde f(x_\ell,\mu_\ell)$: if $\|\eta_\ell\|\le\delta_\ell$ then $\mu_{\ell+1}=\theta_\mu\mu_\ell$, $\delta_{\ell+1}=\theta_\delta\delta_\ell$, $x_{\ell+1}=x_\ell$; otherwise $\mu_{\ell+1}=\mu_\ell$, $\delta_{\ell+1}=\delta_\ell$ and $x_{\ell+1}$ is the Armijo step from $x_\ell$ for $g=\tilde f(\cdot,\mu_\ell)$.
--   4. **Index set.** $K=\{\ell:\|\eta_\ell\|\le\delta_\ell\}$, the iterations at which $\mu$ and $\delta$ shrink.
--   5. **Assumption 4.1.** For any $\bar\mu>0$ and $\bar x\in\mathcal M$ the level set
--   $$
--   \mathcal L_{\bar x,\bar\mu}=\{x\in\mathcal M:\tilde f(x,\bar\mu)\le\tilde f(\bar x,\bar\mu)\}
--   $$
--   is compact.
--
--   These objects describe the Riemannian smoothing steepest descent method whose accumulation points the mission studies.
--
--   **Formalization Note** "The smallest integer $m$" is the least element (`IsLeast`) of the set of $m\in\mathbb N$ satisfying (4.1). The stopping test of line 4 never fires when $\delta_{opt}=\mu_{opt}=0$, because $\mu_\ell>0$, so it is omitted and every run is infinite. The Armijo constant $\sigma$ appears in (4.1) but not on the input line; it is read as $\sigma\in(0,1)$.
-- source:
--   Zhang, Chen & Ma, A Riemannian Smoothing Steepest Descent Method for Non-Lipschitz Optimization on Submanifolds, arXiv:2104.04199v1, Algorithm 4.1 and (4.1), Assumption 4.1, Proposition 4.2, p.15

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad
set_option autoImplicit false

namespace RiemSmoothSD

open ZORiem.RGD

/-- **Armijo condition (4.1)** (Zhang, Chen & Ma, arXiv:2104.04199v1, Algorithm 4.1, line 11,
p.15), for a cost `g` at `x` with the steepest-descent direction `η = −grad g(x)`:
`g(R_x(β^m ᾱ η)) ≤ g(x) − σ β^m ᾱ ‖grad g(x)‖²`. In Algorithm 4.1, `g = f̃(·, μ_ℓ)`.

**Formalization Note** `grad g(x)` is `rgrad M g x = Proj_{T_xM} ∇g(x)` (p.6); `m ∈ ℕ`. -/
def ArmijoHolds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (R : E → E → E) (g : E → ℝ) (σ β αbar : ℝ) (x : E)
    (m : ℕ) : Prop :=
  g (R x ((β ^ m * αbar) • (-rgrad M g x))) ≤ g x - σ * (β ^ m * αbar) * ‖rgrad M g x‖ ^ 2

/-- **Armijo steepest-descent step** (Zhang, Chen & Ma, arXiv:2104.04199v1, Algorithm 4.1,
lines 11–12, p.15): `x' = R_x(t η)` with `η = −grad g(x)`, `t = β^m ᾱ`, and `m` the smallest
natural number satisfying the Armijo condition (4.1).

**Formalization Note** "The smallest integer" is the least element of the set of `m ∈ ℕ`
satisfying (4.1) (`IsLeast`); the step exists only when that set is nonempty, so no junk value
of `Nat.find` enters. -/
def IsArmijoStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (R : E → E → E) (g : E → ℝ) (σ β αbar : ℝ) (x x' : E) :
    Prop :=
  ∃ m : ℕ, IsLeast {m : ℕ | ArmijoHolds M R g σ β αbar x m} m ∧
    x' = R x ((β ^ m * αbar) • (-rgrad M g x))

/-- **Input of Algorithm 4.1** (Zhang, Chen & Ma, arXiv:2104.04199v1, Algorithm 4.1, line 1,
p.15) with `δ_opt = μ_opt = 0`: `x₀ ∈ M`, `δ₀ > 0`, `μ₀ > 0`, `β ∈ (0,1)`, `ᾱ > 0`,
`θ_δ ∈ (0,1)`, `θ_μ ∈ (0,1)`, together with the Armijo constant `σ ∈ (0,1)` of (4.1).

**Formalization Note** `σ` is used in (4.1) but not listed on the input line; it is read as
`σ ∈ (0,1)`, the Armijo convention of [2] that the remark on p.15 needs. -/
def RSSDInput {E : Type*} [NormedAddCommGroup E] (M : Set E) (x₀ : E)
    (δ₀ μ₀ β αbar θδ θμ σ : ℝ) : Prop :=
  x₀ ∈ M ∧ 0 < δ₀ ∧ 0 < μ₀ ∧ 0 < β ∧ β < 1 ∧ 0 < αbar ∧ 0 < θδ ∧ θδ < 1 ∧
    0 < θμ ∧ θμ < 1 ∧ 0 < σ ∧ σ < 1

/-- **A run of the RSSD method** (Zhang, Chen & Ma, arXiv:2104.04199v1, Algorithm 4.1, p.15) with
`δ_opt = μ_opt = 0`: sequences `x_ℓ`, `μ_ℓ`, `δ_ℓ` starting at `(x₀, μ₀, δ₀)` such that, with
`η_ℓ = −grad f̃(x_ℓ, μ_ℓ)`,
* if `‖η_ℓ‖ ≤ δ_ℓ`, then `μ_{ℓ+1} = θ_μ μ_ℓ`, `δ_{ℓ+1} = θ_δ δ_ℓ` and `x_{ℓ+1} = x_ℓ` (lines 6–8);
* otherwise `μ_{ℓ+1} = μ_ℓ`, `δ_{ℓ+1} = δ_ℓ` and `x_{ℓ+1} = R_{x_ℓ}(t_ℓ η_ℓ)` with the Armijo
  step size `t_ℓ = β^m ᾱ` of (4.1) (lines 10–12).

**Formalization Note** `grad f̃(x, μ)` is `rgrad M (fun z => ftilde z μ) x`, the projection onto
`T_xM` of the Euclidean gradient of `f̃(·, μ)`. With `δ_opt = μ_opt = 0` the stopping test of
line 4 (`‖η_ℓ‖ ≤ δ_opt` and `μ_ℓ ≤ μ_opt`) never fires, because `μ_ℓ > 0` for every `ℓ` when
`μ₀ > 0`; it is therefore omitted, and a run is an infinite sequence. The parameter ranges are
in `RSSDInput`, stated separately. -/
def IsRSSDRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Set E) (R : E → E → E) (ftilde : E → ℝ → ℝ) (x₀ : E) (δ₀ μ₀ β αbar θδ θμ σ : ℝ)
    (x : ℕ → E) (μ δ : ℕ → ℝ) : Prop :=
  x 0 = x₀ ∧ μ 0 = μ₀ ∧ δ 0 = δ₀ ∧
    ∀ ℓ : ℕ,
      (‖rgrad M (fun z => ftilde z (μ ℓ)) (x ℓ)‖ ≤ δ ℓ →
          μ (ℓ + 1) = θμ * μ ℓ ∧ δ (ℓ + 1) = θδ * δ ℓ ∧ x (ℓ + 1) = x ℓ) ∧
      (¬ ‖rgrad M (fun z => ftilde z (μ ℓ)) (x ℓ)‖ ≤ δ ℓ →
          μ (ℓ + 1) = μ ℓ ∧ δ (ℓ + 1) = δ ℓ ∧
            IsArmijoStep M R (fun z => ftilde z (μ ℓ)) σ β αbar (x ℓ) (x (ℓ + 1)))

/-- **The index set `K = {ℓ | ‖η_ℓ‖ ≤ δ_ℓ}`** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Proposition 4.2 and Theorem 4.3, pp.15–16) of the iterations at which the RSSD method shrinks
`μ` and `δ`, with `η_ℓ = −grad f̃(x_ℓ, μ_ℓ)`. -/
def rssdK {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Set E) (ftilde : E → ℝ → ℝ) (x : ℕ → E) (μ δ : ℕ → ℝ) : Set ℕ :=
  {ℓ | ‖rgrad M (fun z => ftilde z (μ ℓ)) (x ℓ)‖ ≤ δ ℓ}

/-- **Assumption 4.1** (Zhang, Chen & Ma, arXiv:2104.04199v1, p.15): for any fixed `μ̄ > 0` and
any `x̄ ∈ M`, the level set `L_{x̄,μ̄} = {x ∈ M | f̃(x, μ̄) ≤ f̃(x̄, μ̄)}` is compact. -/
def Assumption41 {E : Type*} [NormedAddCommGroup E] (M : Set E) (ftilde : E → ℝ → ℝ) : Prop :=
  ∀ μbar : ℝ, 0 < μbar → ∀ xbar ∈ M, IsCompact {x | x ∈ M ∧ ftilde x μbar ≤ ftilde xbar μbar}

end RiemSmoothSD


