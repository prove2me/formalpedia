-- Prove2me | Definitions.Def_RiemProxGrad_Rate_Setting
-- name    : RiemProxGrad_Rate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:04.712212+00:00
-- url     : https://prove2.me/theorems/13ecac11-1ab0-4689-bd2b-34a2302e62ca
-- title:
--   Problem (1.1), the RPG run (Algorithm 1), retraction-smoothness and retraction-convexity, Assumptions 3.1–3.4
-- statement:
--   Let $\mathcal M$ be a finite-dimensional Riemannian manifold with inner product $\langle\cdot,\cdot\rangle_x$ and norm $\|\cdot\|_x$ on $T_x\mathcal M$, and let $R$ be a retraction ($R_x:T_x\mathcal M\to\mathcal M$ smooth, $R_x(0_x)=x$, $\mathrm DR_x(0_x)=\mathrm{id}$). Problem (1.1) is
--   $$\min_{x\in\mathcal M} F(x)=f(x)+g(x),$$
--   with $f$ differentiable with Riemannian gradient $\operatorname{grad} f$ and $g$ continuous but possibly nonsmooth.
--
--   1. **Standing assumptions.** $R$ is a retraction; $f$ is differentiable and $\langle \operatorname{grad} f(x),\eta\rangle_x=\mathrm Df(x)[\eta]$; $g$ is continuous and every pull-back $g\circ R_x:T_x\mathcal M\to\mathbb R$ is locally Lipschitz.
--   2. **Model and run (Algorithm 1).** For a constant $\tilde L$, let
--   $$\ell_x(\eta)=\langle\operatorname{grad} f(x),\eta\rangle_x+\frac{\tilde L}{2}\|\eta\|_x^2+g(R_x(\eta)),\qquad \eta\in T_x\mathcal M.$$
--   A run is a pair of sequences $x_k\in\mathcal M$, $\eta^*_{x_k}\in T_{x_k}\mathcal M$ such that, for every $k\ge0$, $0\in\partial\ell_{x_k}(\eta^*_{x_k})$ (Clarke subdifferential on $T_{x_k}\mathcal M$), $\ell_{x_k}(0)\ge\ell_{x_k}(\eta^*_{x_k})$ (3.1), and $x_{k+1}=R_{x_k}(\eta^*_{x_k})$. Also $\beta=(\tilde L-L)/2$ (3.5) and $\Omega_{x_0}=\{x\in\mathcal M\mid F(x)\le F(x_0)\}$.
--   3. **Assumption 3.1.** $F$ is bounded from below and $\Omega_{x_0}$ is compact.
--   4. **$L$-retraction-smoothness in $\mathcal N$ (Definition 3.1, used for every $\eta$).** For every $x\in\mathcal N$ and every $\eta\in T_x\mathcal M$,
--   $$h(R_x(\eta))\le h(x)+\langle\operatorname{grad} h(x),\eta\rangle_x+\frac L2\|\eta\|_x^2. \tag{3.2}$$
--   **Assumption 3.2** asks this for $f$ in $\mathcal N=\Omega_{x_0}$.
--   5. **Retraction-convexity in $\mathcal N$ (Definition 3.2).** With $q_x=h\circ R_x$: for every $x\in\mathcal N$ and all $\eta,\xi\in T_x\mathcal M$ with $R_x(\eta),R_x(\xi)\in\mathcal N$,
--   $$q_x(\eta)\ge q_x(\xi)+\langle\zeta,\eta-\xi\rangle_x, \tag{3.10}$$
--   where $\zeta=\operatorname{grad} q_x(\xi)$ for differentiable $h$ (written with the derivative $\mathrm Dq_x(\xi)[\eta-\xi]$), and, for nonsmooth $h$, for **every** Riemannian subgradient $\zeta\in\partial q_x(\xi)$.
--   6. **Assumption 3.3.** $\Omega\supseteq\Omega_{x_0}$ is open, $f$ is $L$-retraction-smooth and retraction-convex (differentiable form) in $\Omega$, and $g$ is retraction-convex (subgradient form) in $\Omega$.
--   7. **Inverse retraction and Assumption 3.4.** A map $R^{-1}$ with $R_x^{-1}(y)\in T_x\mathcal M$ and $R_x(R_x^{-1}(y))=y$ for $x,y\in\Omega$. Assumption 3.4 with a constant $\kappa_\Omega$: for all $x,y,z\in\Omega$, with $\eta_x=R_x^{-1}(y)$, $\xi_x=R_x^{-1}(z)$, $\zeta_y=R_y^{-1}(z)$,
--   $$\bigl|\|\xi_x-\eta_x\|_x^2-\|\zeta_y\|_y^2\bigr|\le\kappa_\Omega\|\eta_x\|_x^2. \tag{3.12}$$
--
--   These are the objects of the $O(1/k)$ convergence-rate analysis of the Riemannian proximal gradient method (§3.2): Lemma 3.1, Lemma 3.4, the displays (3.17)–(3.19) and Theorem 3.2 are stated with them.
--
--   **Formalization Note** Norms and inner products on $T_x\mathcal M$ are those of Mathlib's `RiemannianBundle` (the tangent space has no other norm instance); the retraction and the gradient are the published `RiemOpt.BFGS.IsRetraction` and `RiemOpt.FR.IsGradient`. Readings adopted: (a) Definition 3.1 asks (3.2) only for $\eta$ with $R_x(\eta)\in\mathcal N$; here (3.2) is required for every $\eta\in T_x\mathcal M$ at points of $\mathcal N$ — a strengthening, needed because Lemma 3.1 is false under the literal reading, and the form that the cited result [16, Lemma 2.7] provides. (b) In Definition 3.2 the vector $\zeta$ depends on $\xi$, as the sentence after (3.10) says; a single $\zeta$ for all $\eta,\xi$ would force $q_x$ to be affine. $\mathcal S_x$ is taken as the largest admissible set $R_x^{-1}(\mathcal N)$. (c) $\kappa_\Omega$ is one constant for all $x,y,z\in\Omega$. (d) $R^{-1}$ is data with the right-inverse property on $\Omega$; local Lipschitzness of $g\circ R_x$ is made explicit from p. 5, where the Clarke subdifferential is defined for Lipschitz functions. Indices start at $k=0$.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, pp. 1, 4–10, (1.1), §2, Algorithm 1, (3.1), Assumption 3.1, Definition 3.1, Assumption 3.2, (3.5), Definition 3.2, Assumptions 3.3–3.4

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemProxGrad.Rate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- The objective of problem (1.1) (p. 1): `F(x) = f(x) + g(x)`. -/
def objective (f g : M → ℝ) : M → ℝ := fun y => f y + g y

/-- The constant `β = (L̃ − L)/2` of Lemma 3.1, (3.5) (p. 7). -/
noncomputable def beta (L Ltilde : ℝ) : ℝ := (Ltilde - L) / 2

/-- The standing assumptions of problem (1.1) (p. 1) and §2 (pp. 4–5), for a retraction `R` and
a field `grad` with `grad x ∈ T_xM`:
* `R` is a retraction (`R_x(0_x) = x`, `DR_x(0_x) = id`, each `R_x` smooth);
* `f` is differentiable and `grad` is its Riemannian gradient
  (`⟨grad f(x), η⟩_x = Df(x)[η]`, inner product of the Riemannian metric);
* `g` is continuous, and every pull-back `ĝ_x = g ∘ R_x : T_xM → ℝ` is locally Lipschitz, so that
  its Clarke subdifferential (p. 5) is the one of a Lipschitz function. -/
structure StandingAssumptions (f g : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) : Prop where
  isRetraction : RiemOpt.BFGS.IsRetraction R
  differentiable : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f
  isGradient : RiemOpt.FR.IsGradient f grad
  continuous_g : Continuous g
  lipschitz_pullback : ∀ x : M, LocallyLipschitz (fun η : TangentSpace 𝓘(ℝ, E) x => g (R x η))

/-- The model of Algorithm 1, step 2 (p. 6): for `x ∈ M` and `η ∈ T_xM`,
`ℓ_x(η) = ⟨grad f(x), η⟩_x + (L̃/2)‖η‖²_x + g(R_x(η))`. -/
noncomputable def ell (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (g : M → ℝ)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (Ltilde : ℝ) (x : M)
    (η : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  inner ℝ (grad x) η + Ltilde / 2 * ‖η‖ ^ 2 + g (R x η)

/-- A run of Algorithm 1 (RPG, p. 6) with parameter `L̃`: sequences `x_k ∈ M` and
`η_k = η*_{x_k} ∈ T_{x_k}M` such that for every `k`,
* `η*_{x_k}` is a stationary point of `ℓ_{x_k}` on `T_{x_k}M`, i.e. `0 ∈ ∂ℓ_{x_k}(η*_{x_k})`
  (Clarke subdifferential, p. 5);
* `ℓ_{x_k}(0) ≥ ℓ_{x_k}(η*_{x_k})` (3.1);
* `x_{k+1} = R_{x_k}(η*_{x_k})`. -/
structure IsRPGRun (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (g : M → ℝ)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (Ltilde : ℝ) (x : ℕ → M)
    (η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) : Prop where
  stationary : ∀ k, (0 : TangentSpace 𝓘(ℝ, E) (x k)) ∈ RiemProxGrad.Global.clarkeSubdiff (ell grad g R Ltilde (x k)) (η k)
  decrease : ∀ k, ell grad g R Ltilde (x k) (η k) ≤ ell grad g R Ltilde (x k) 0
  step : ∀ k, x (k + 1) = R (x k) (η k)

/-- Assumption 3.1 (p. 6): `F` is bounded from below and the RiemProxGrad.Global.sublevel set `Ω_{x₀}` is compact. -/
def Assumption31 (F : M → ℝ) (x₀ : M) : Prop :=
  BddBelow (Set.range F) ∧ IsCompact (RiemProxGrad.Global.sublevel F x₀)

/-- `L`-retraction-smoothness (Definition 3.1, (3.2), p. 7) in `N ⊆ M`, in the form used by the
proofs of Lemma 3.1 and Lemma 3.4: for every `x ∈ N` and **every** `η ∈ T_xM`,
`h(R_x(η)) ≤ h(x) + ⟨grad h(x), η⟩_x + (L/2)‖η‖²_x`.
(Definition 3.1 asks this only for `η` with `R_x(η) ∈ N`; the requirement for all `η` is a
strengthening, see the natural-language statement.) -/
def IsRetractionSmooth (h : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (L : ℝ) (N : Set M) : Prop :=
  ∀ x ∈ N, ∀ η : TangentSpace 𝓘(ℝ, E) x,
    h (R x η) ≤ h x + inner ℝ (grad x) η + L / 2 * ‖η‖ ^ 2

/-- Assumption 3.2 (p. 7): `f` is `L`-retraction-smooth with respect to `R` in `Ω_{x₀}`. -/
def Assumption32 (f g : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (L : ℝ) (x₀ : M) : Prop :=
  IsRetractionSmooth f grad R L (RiemProxGrad.Global.sublevel (objective f g) x₀)

/-- Retraction-convexity (Definition 3.2, (3.10), p. 9) of a **differentiable** `h` in `N ⊆ M`,
with `ζ = grad q_x(ξ)`, `q_x = h ∘ R_x`, and `S_x = R_x⁻¹(N)`: for every `x ∈ N` and all
`η, ξ ∈ T_xM` with `R_x(η), R_x(ξ) ∈ N`, `q_x(η) ≥ q_x(ξ) + Dq_x(ξ)[η − ξ]`. -/
def IsRetractionConvexDiff (h : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (N : Set M) : Prop :=
  ∀ x ∈ N, ∀ η ξ : TangentSpace 𝓘(ℝ, E) x, R x η ∈ N → R x ξ ∈ N →
    h (R x ξ) + fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) x => h (R x v)) ξ (η - ξ) ≤ h (R x η)

/-- Retraction-convexity (Definition 3.2, (3.10), p. 9) of a possibly nonsmooth `h` in `N ⊆ M`,
with `ζ` any Riemannian (Clarke) subgradient of `q_x = h ∘ R_x` at `ξ`, and `S_x = R_x⁻¹(N)`:
for every `x ∈ N`, all `η, ξ ∈ T_xM` with `R_x(η), R_x(ξ) ∈ N` and every `ζ ∈ ∂q_x(ξ)`,
`q_x(η) ≥ q_x(ξ) + ⟨ζ, η − ξ⟩_x`. -/
def IsRetractionConvex (h : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (N : Set M) : Prop :=
  ∀ x ∈ N, ∀ η ξ : TangentSpace 𝓘(ℝ, E) x, R x η ∈ N → R x ξ ∈ N →
    ∀ ζ ∈ RiemProxGrad.Global.clarkeSubdiff (fun v : TangentSpace 𝓘(ℝ, E) x => h (R x v)) ξ,
      h (R x ξ) + inner ℝ ζ (η - ξ) ≤ h (R x η)

/-- Assumption 3.3 (p. 10): `Ω` is an open set containing `Ω_{x₀}`, `f` is `L`-retraction-smooth
and retraction-convex with respect to `R` in `Ω`, and `g` is retraction-convex with respect to `R`
in `Ω`. -/
def Assumption33 (f g : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (L : ℝ) (x₀ : M) (Ω : Set M) : Prop :=
  IsOpen Ω ∧ RiemProxGrad.Global.sublevel (objective f g) x₀ ⊆ Ω ∧ IsRetractionSmooth f grad R L Ω ∧
    IsRetractionConvexDiff f R Ω ∧ IsRetractionConvex g R Ω

/-- An inverse retraction on `Ω`: `Rinv x y ∈ T_xM` with `R_x(R_x⁻¹(y)) = y` for all `x, y ∈ Ω`. -/
def IsInverseRetractionOn (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (Rinv : (x : M) → M → TangentSpace 𝓘(ℝ, E) x) (Ω : Set M) : Prop :=
  ∀ x ∈ Ω, ∀ y ∈ Ω, R x (Rinv x y) = y

/-- Assumption 3.4, (3.12) (p. 10), with one constant `κ_Ω`: for all `x, y, z ∈ Ω`, with
`η_x = R_x⁻¹(y)`, `ξ_x = R_x⁻¹(z)`, `ζ_y = R_y⁻¹(z)`,
`|‖ξ_x − η_x‖²_x − ‖ζ_y‖²_y| ≤ κ_Ω ‖η_x‖²_x`. -/
def Assumption34 (Rinv : (x : M) → M → TangentSpace 𝓘(ℝ, E) x) (Ω : Set M) (κ : ℝ) : Prop :=
  ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ z ∈ Ω,
    |‖Rinv x z - Rinv x y‖ ^ 2 - ‖Rinv y z‖ ^ 2| ≤ κ * ‖Rinv x y‖ ^ 2

end RiemProxGrad.Rate


