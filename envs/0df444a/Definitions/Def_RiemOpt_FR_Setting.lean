-- Prove2me | Definitions.Def_RiemOpt_FR_Setting
-- name    : RiemOpt_FR_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:06.091993+00:00
-- url     : https://prove2.me/theorems/9e2e4c5d-c9f6-495d-b950-9420a8c53314
-- title:
--   §2–§3.2, pp. 599–601, 610 — retraction, Wolfe and strong Wolfe conditions (1a), (1b), (2), cos θ_k, Riemannian Fletcher–Reeves run
-- statement:
--   Let $\mathcal M$ be a smooth manifold modelled on a real Hilbert space $E$, whose tangent spaces $T_x\mathcal M$ carry a Riemannian inner product $g_x$ with norm $\|\cdot\|_x$. For $f:\mathcal M\to\mathbb R$ write $\mathrm Df(x)\in (T_x\mathcal M)^*$ for its differential; its norm $\|\mathrm Df(x)\|_x$ is the dual (operator) norm.
--
--   1. **Gradient.** A field $\nabla f$ with $\nabla f(x)\in T_x\mathcal M$ is a gradient of $f$ if $g_x(\nabla f(x),v)=\mathrm Df(x)v$ for all $x$ and $v\in T_x\mathcal M$ (the Riesz representative of $\mathrm Df(x)$).
--   2. **Retraction.** A family $R=(R_x)_{x\in\mathcal M}$ of smooth maps $R_x:T_x\mathcal M\to\mathcal M$ with $R_x(0)=x$ and $\mathrm DR_x(0)=\mathrm{id}_{T_x\mathcal M}$. The associated transport is $T^{R_x}_{x,R_x(v)}=\mathrm DR_x(v):T_x\mathcal M\to T_{R_x(v)}\mathcal M$.
--   3. **Wolfe and strong Wolfe conditions.** For $p\in T_x\mathcal M$ and a step $\alpha$,
--   $$f(R_x(\alpha p))\le f(x)+c_1\alpha\,\mathrm Df(x)p, \tag{1a}$$
--   $$\mathrm Df(R_x(\alpha p))\,T^{R_x}_{x,R_x(\alpha p)}p\ \ge\ c_2\,\mathrm Df(x)p, \tag{1b}$$
--   $$\bigl|\mathrm Df(R_x(\alpha p))\,T^{R_x}_{x,R_x(\alpha p)}p\bigr|\ \le\ -c_2\,\mathrm Df(x)p. \tag{2}$$
--   The Wolfe conditions are (1a) and (1b); the strong Wolfe conditions are (1a) and (2).
--   4. **Angle.** For sequences $x_k\in\mathcal M$, $p_k\in T_{x_k}\mathcal M$,
--   $$\cos\theta_k=\frac{-\mathrm Df(x_k)p_k}{\|\mathrm Df(x_k)\|_{x_k}\,\|p_k\|_{x_k}}.$$
--   5. **Wolfe run of Algorithm 1.** Sequences $x_k$, $p_k$, $\alpha_k>0$ with $x_{k+1}=R_{x_k}(\alpha_kp_k)$, descent directions $\mathrm Df(x_k)p_k<0$, and $\alpha_k$ satisfying (1a), (1b) with $0<c_1<c_2<1$; $f$ is differentiable.
--   6. **Fletcher–Reeves run.** Sequences $x_k$, $p_k$, $\alpha_k>0$ with $x_{k+1}=R_{x_k}(\alpha_kp_k)$, $\alpha_k$ satisfying the strong Wolfe conditions (1a), (2) with $0<c_1<c_2<1$, and
--   $$p_0=-\nabla f(x_0),\qquad p_{k+1}=-\nabla f(x_{k+1})+\beta_{k+1}T^{R_{x_k}}_{x_k,x_{k+1}}p_k,\qquad \beta_{k+1}=\frac{\|\mathrm Df(x_{k+1})\|_{x_{k+1}}^2}{\|\mathrm Df(x_k)\|_{x_k}^2};$$
--   $f$ is differentiable with gradient $\nabla f$, and $\mathrm Df(x_k)\ne0$ for every $k$ (the algorithm never stops). That $p_k$ is a descent direction is not part of this definition.
--   7. **Lipschitz continuous differentiability on $\mathrm{span}\{p_k\}$** with uniform constant $L$: each $h_k(t)=f(R_{x_k}(tp_k))$ is differentiable on $\mathbb R$ and
--   $$|h_k'(s)-h_k'(t)|\le L\,|s-t|\,\|p_k\|_{x_k}^2\qquad\forall s,t\in\mathbb R,\ k\in\mathbb N.$$
--
--   These are the objects of Zoutendijk's theorem (Theorem 2) and of the convergence analysis of the Riemannian Fletcher–Reeves method (Lemma 14, Proposition 15).
--
--   **Formalization Note** The manifold uses Mathlib's `RiemannianBundle` on `TangentSpace 𝓘(ℝ, E) x`, so every norm and inner product on a tangent space is the Riemannian one, and `Df f x` is `mfderiv` read as a functional on $T_x\mathcal M$. The gradient is data with its defining (Riesz) property. One retraction family `R` is used for all $k$ (the paper allows $R_{x_k}$ to be chosen per step). Smoothness of $R_x$ is stated for the map out of the model space $E$, which carries the topology of $T_x\mathcal M$. The equation $x_{k+1}=R_{x_k}(\alpha_kp_k)$ is an explicit field: it is what makes the transported direction $T^{R_{x_k}}_{x_k,x_{k+1}}p_k\in T_{R_{x_k}(\alpha_kp_k)}\mathcal M$ a vector of $T_{x_{k+1}}\mathcal M$ (`transportedDir`, whose norm is that of $T_{x_{k+1}}\mathcal M$). The paper writes $\alpha_k\in\mathbb R$; positivity is required, as the Wolfe conditions are meant for positive steps (Theorem 2 is false for negative ones). $\beta_0=0$ is encoded by the separate formula for $p_0$. The restriction of $f_{R_{x_k}}=f\circ R_{x_k}$ to the line $\mathrm{span}\{p_k\}$ has derivative of norm $|h_k'(s)|/\|p_k\|$ at $sp_k$, which gives item 7. Indices start at $k=0$.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 599 (gradient, retraction, transport), p. 600 (Algorithm 1, (1a), (1b), (2)), p. 601 (strong Wolfe, cos θ_k, Theorem 2), p. 610 (§3.2, Fletcher–Reeves direction)

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- `grad` is a Riemannian gradient field of `f` (p. 599): `∇f(x) ∈ T_xM` is the Riesz
representative of `Df(x)`, i.e. `g_x(∇f(x), v) = RiemOpt.BFGS.Df(x)v` for all `v ∈ T_xM`. -/
def IsGradient (f : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Prop :=
  ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), inner ℝ (grad x) v = RiemOpt.BFGS.Df f x v

/-- The strong RiemOpt.BFGS.Wolfe conditions (pp. 600–601): (1a) together with (2),
`|RiemOpt.BFGS.Df(R_x(αp)) T^{R_x}_{x,R_x(αp)} p| ≤ −c₂ RiemOpt.BFGS.Df(x)p`. -/
def StrongWolfe (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ, E) x) (α : ℝ) : Prop :=
  f (R x (α • p)) ≤ f x + c₁ * α * RiemOpt.BFGS.Df f x p ∧
    |RiemOpt.BFGS.Df f (R x (α • p)) (RiemOpt.BFGS.transport R x (α • p) p)| ≤ -(c₂ * RiemOpt.BFGS.Df f x p)

/-- The transported previous direction `T^{R_{x_k}}_{x_k,x_{k+1}} p_k = DR_{x_k}(α_k p_k) p_k`
(p. 610), read as a vector of `T_{x_{k+1}}M`. This reading is meaningful because a run always
carries the equation `x_{k+1} = R_{x_k}(α_k p_k)` (see `IsFRRun.step`); in particular its norm
below is the Riemannian norm of `T_{x_{k+1}}M`. -/
noncomputable def transportedDir (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (x : ℕ → M)
    (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ) (k : ℕ) :
    TangentSpace 𝓘(ℝ, E) (x (k + 1)) :=
  RiemOpt.BFGS.transport R (x k) (α k • p k) (p k)

/-- The angle between the search direction and the negative gradient (p. 601):
`cos θ_k = −RiemOpt.BFGS.Df(x_k)p_k / (‖RiemOpt.BFGS.Df(x_k)‖_{x_k} ‖p_k‖_{x_k})`. -/
noncomputable def cosTheta (f : M → ℝ) (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k))
    (k : ℕ) : ℝ :=
  -RiemOpt.BFGS.Df (E := E) f (x k) (p k) / (‖RiemOpt.BFGS.Df (E := E) f (x k)‖ * ‖p k‖)

/-- A run of Algorithm 1 (p. 600) with descent directions and RiemOpt.BFGS.Wolfe step lengths (1a), (1b),
`0 < c₁ < c₂ < 1`, for a fixed retraction family `R`:
`x (k+1) = R_{x_k}(α_k p_k)`, `α_k > 0`, `Df(x_k)p_k < 0`, and `f` is differentiable. -/
structure IsWolfeRun (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ) : Prop where
  isRetraction : RiemOpt.BFGS.IsRetraction R
  differentiable : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  step : ∀ k, x (k + 1) = R (x k) (α k • p k)
  step_pos : ∀ k, 0 < α k
  descent : ∀ k, RiemOpt.BFGS.Df (E := E) f (x k) (p k) < 0
  wolfe : ∀ k, RiemOpt.BFGS.Wolfe f R c₁ c₂ (x k) (p k) (α k)

/-- A non-terminating run of Algorithm 1 with the Fletcher–Reeves search direction and strong
RiemOpt.BFGS.Wolfe step lengths (p. 610), `0 < c₁ < c₂ < 1`, for a fixed retraction family `R` and a gradient
field `grad` of `f`:
* `x (k+1) = R_{x_k}(α_k p_k)` with `α_k > 0`, and `α_k` satisfies (1a) and (2);
* `p_0 = −∇f(x_0)` (`β_0 = 0`) and
  `p_{k+1} = −∇f(x_{k+1}) + β_{k+1} T^{R_{x_k}}_{x_k,x_{k+1}} p_k`,
  `β_{k+1} = ‖RiemOpt.BFGS.Df(x_{k+1})‖² / ‖RiemOpt.BFGS.Df(x_k)‖²`;
* `f` is differentiable and `Df(x_k) ≠ 0` for all `k` (the algorithm never stops).
Descent of `p_k` is not assumed. -/
structure IsFRRun (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ) : Prop where
  isRetraction : RiemOpt.BFGS.IsRetraction R
  differentiable : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f
  isGradient : IsGradient f grad
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  step : ∀ k, x (k + 1) = R (x k) (α k • p k)
  step_pos : ∀ k, 0 < α k
  strongWolfe : ∀ k, StrongWolfe f R c₁ c₂ (x k) (p k) (α k)
  dir_zero : p 0 = -grad (x 0)
  dir_succ : ∀ k, p (k + 1) = -grad (x (k + 1)) +
    (‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2 / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2) • transportedDir R x p α k
  nonstationary : ∀ k, RiemOpt.BFGS.Df (E := E) f (x k) ≠ 0

/-- The pull-backs `f_{R_{x_k}}` are Lipschitz continuously differentiable on `span{p_k}` with
uniform Lipschitz constant `L` (Theorem 2, p. 601). On the line `span{p_k}` the pull-back is
`h_k(t) = f(R_{x_k}(t p_k))`; its derivative at `s p_k`, as a functional on `span{p_k}`, has norm
`|h_k'(s)| / ‖p_k‖`, so the condition reads: `h_k` is differentiable and
`|h_k'(s) − h_k'(t)| ≤ L |s − t| ‖p_k‖²` for all `s, t ∈ ℝ`. -/
def LineLipschitz (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (x : ℕ → M)
    (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (L : ℝ) : Prop :=
  ∀ k, Differentiable ℝ (fun t : ℝ ↦ f (R (x k) (t • p k))) ∧
    ∀ s t : ℝ, |deriv (fun r : ℝ ↦ f (R (x k) (r • p k))) s -
        deriv (fun r : ℝ ↦ f (R (x k) (r • p k))) t| ≤ L * |s - t| * ‖p k‖ ^ 2

end RiemOpt.FR


