-- Prove2me | Definitions.Def_RiemOpt_BFGS_Setting
-- name    : RiemOpt_BFGS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:51.491829+00:00
-- url     : https://prove2.me/theorems/60dc00b6-12ea-45f7-92e0-70ac4515c720
-- title:
--   §2–§3.1 and Appendix A, pp. 599–608, 620 — retraction, Wolfe conditions (1a)–(1b), Riemannian BFGS run (6), cos θ_k, q_k, uniform convexity
-- statement:
--   Let $\mathcal M$ be a smooth manifold modelled on a real Hilbert space $E$, whose tangent spaces $T_x\mathcal M$ carry a Riemannian inner product $g_x$ with norm $\|\cdot\|_x$. For $f:\mathcal M\to\mathbb R$ write $\mathrm Df(x)\in (T_x\mathcal M)^*$ for its differential; its norm $\|\mathrm Df(x)\|_x$ is the dual (operator) norm.
--
--   1. **Retraction.** A family $R=(R_x)_{x\in\mathcal M}$ of smooth maps $R_x:T_x\mathcal M\to\mathcal M$ with $R_x(0)=x$ and $\mathrm DR_x(0)=\mathrm{id}_{T_x\mathcal M}$. The associated transport is $T^{R_x}_{x,R_x(v)}=\mathrm DR_x(v):T_x\mathcal M\to T_{R_x(v)}\mathcal M$, and $f_{R_x}=f\circ R_x$.
--   2. **Wolfe conditions.** For $p\in T_x\mathcal M$ and a step $\alpha$,
--   $$f(R_x(\alpha p))\le f(x)+c_1\alpha\,\mathrm Df(x)p,\qquad \mathrm Df(R_x(\alpha p))\,T^{R_x}_{x,R_x(\alpha p)}p\ \ge\ c_2\,\mathrm Df(x)p. \tag{1a, 1b}$$
--   3. **BFGS run.** Sequences $x_k\in\mathcal M$, $p_k\in T_{x_k}\mathcal M$, $\alpha_k>0$, bounded bilinear forms $B_k$ on $T_{x_k}\mathcal M$ and invertible bounded linear maps $T_k:T_{x_k}\mathcal M\to T_{x_{k+1}}\mathcal M$ such that $x_{k+1}=R_{x_k}(\alpha_kp_k)$, $\alpha_k$ satisfies (1a)–(1b) with $0<c_1<c_2<1$, $B_k(p_k,\cdot)=-\mathrm Df(x_k)$ (6), and with $s_k=\alpha_kp_k$, $y_k=\mathrm Df_{R_{x_k}}(s_k)-\mathrm Df_{R_{x_k}}(0)$,
--   $$B_{k+1}(T_kv,T_kw)=B_k(v,w)-\frac{B_k(s_k,v)B_k(s_k,w)}{B_k(s_k,s_k)}+\frac{(y_kv)(y_kw)}{y_ks_k}\qquad\forall v,w\in T_{x_k}\mathcal M.$$
--   Moreover $f$ is differentiable, every $f_{R_{x_k}}$ is $C^2$, and $\mathrm Df(x_k)\neq0$ for all $k$ (the algorithm never stops).
--   4. **Angle and Rayleigh quotient** (Appendix A):
--   $$\cos\theta_k=\frac{B_k(s_k,s_k)}{\|s_k\|_{x_k}\,\|B_k(s_k,\cdot)\|_{x_k}},\qquad q_k=\frac{B_k(s_k,s_k)}{\|s_k\|_{x_k}^2}.$$
--   5. **Uniform convexity on the sublevel set** with constants $0<m<M$: for every $k$, the set $S_k=R_{x_k}^{-1}(\{x: f(x)\le f(x_0)\})\subseteq T_{x_k}\mathcal M$ is convex and $m\|v\|_{x_k}^2\le \mathrm D^2f_{R_{x_k}}(p)(v,v)\le M\|v\|_{x_k}^2$ for all $p\in S_k$, $v\in T_{x_k}\mathcal M$.
--   6. **Good indices.** For $r,\kappa,\rho,\sigma$: every $k\in\mathbb N$ has at least $\lfloor r(k+1)\rfloor$ indices $i\in\{0,\dots,k\}$ with $\cos\theta_i\ge\kappa$ and $\rho\le q_i/\cos\theta_i\le\sigma$.
--
--   These are the objects of the convergence analysis of the Riemannian BFGS method: Lemma 9, Proposition 10 and the steps of its proof in Appendix A are all stated with them.
--
--   **Formalization Note** The manifold uses Mathlib's `RiemannianBundle` on `TangentSpace 𝓘(ℝ, E) x`, so every norm on a tangent space is the Riemannian one, and `Df f x` is `mfderiv` read as a functional on $T_x\mathcal M$. One retraction family `R` is used for all $k$ (the paper allows $R_{x_k}$ to be chosen per step). Smoothness of $R_x$ is stated for the map out of the model space $E$, which carries the topology of $T_x\mathcal M$. The equation $x_{k+1}=R_{x_k}(\alpha_kp_k)$ is an explicit field: it is what makes $T_{x_{k+1}}\mathcal M$ the tangent space at the new point. $s_k:=\alpha_kp_k$ is the paper's definition (its reading $R_{x_k}^{-1}(x_{k+1})$ is not used). The paper writes $\alpha_k\in\mathbb R$; positivity is required, as the Wolfe conditions are meant for positive steps and Lemma 9's proof divides by $\alpha_k$. Non-termination $\mathrm Df(x_k)\ne0$ is assumed, as both iterations stop exactly when the gradient vanishes. $C^2$ regularity of $f_{R_{x_k}}$ replaces "smooth"; it is all the statements need. The convexity of $S_k$ is the standard reading of "uniformly convex on a set" and is what the appendix uses (Hessian bounds along segments $[0,s_k]$ and $[0,R_{x_k}^{-1}(x^*)]$). Indices start at $k=0$.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 599 (retraction, transport, f_{R_x}), p. 600 (Algorithm 1, (1a), (1b)), p. 606 ((6) and the BFGS update), p. 608 (Proposition 10, uniform convexity), p. 620 (Appendix A, cos θ_k, q_k), pp. 621–622 (good indices)

import Mathlib

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.BFGS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- The differential `Df(x) : T_xM → ℝ` of `f : M → ℝ` at `x` (p. 599), as a continuous linear
functional on the tangent space. Its operator norm, taken with respect to the Riemannian norm of
`T_xM`, is the dual norm `‖Df(x)‖_x`. -/
noncomputable def Df (f : M → ℝ) (x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x

/-- A retraction family (p. 599): for every `x`, `R x : T_xM → M` is smooth, `R x 0 = x` and
`DR_x(0) = id_{T_xM}`. (The tangent space `T_xM` is modelled on `E`; smoothness is taken for the
map out of the model space, whose topology is that of `T_xM`.) -/
def IsRetraction (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) : Prop :=
  ∀ x : M, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun v : E ↦ R x v) ∧ R x 0 = x ∧
    ∀ v : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E ↦ R x w) 0 v = v

/-- The transport attached to a retraction (p. 599): `T^{R_x}_{x,R_x(v)} = DR_x(v)`, a linear map
`T_xM → T_{R_x(v)}M`. -/
noncomputable def transport (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (R x v) :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E ↦ R x w) v

/-- The Wolfe conditions (1a), (1b) of p. 600 for the step length `α` along `p ∈ T_xM`:
`f(R_x(αp)) ≤ f(x) + c₁ α Df(x)p` and `Df(R_x(αp)) T^{R_x}_{x,R_x(αp)} p ≥ c₂ Df(x)p`. -/
def Wolfe (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ, E) x) (α : ℝ) : Prop :=
  f (R x (α • p)) ≤ f x + c₁ * α * Df f x p ∧
    c₂ * Df f x p ≤ Df f (R x (α • p)) (transport R x (α • p) p)

/-- The BFGS step `s_k = α_k p_k ∈ T_{x_k}M` (p. 606). -/
noncomputable def sVec (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ) (k : ℕ) :
    TangentSpace 𝓘(ℝ, E) (x k) :=
  α k • p k

/-- The BFGS gradient difference `y_k = Df_{R_{x_k}}(s_k) − Df_{R_{x_k}}(0)` (p. 606), a linear
functional on `T_{x_k}M`, where `f_{R_{x_k}} = f ∘ R_{x_k}`. -/
noncomputable def yVec (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (x : ℕ → M)
    (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ) (k : ℕ) :
    TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ :=
  fderiv ℝ (f ∘ R (x k)) (sVec x p α k) - fderiv ℝ (f ∘ R (x k)) 0

/-- The cosine of the angle (Appendix A, p. 620):
`cos θ_k = B_k(s_k, s_k) / (‖s_k‖_{x_k} ‖B_k(s_k, ·)‖_{x_k})`. -/
noncomputable def cosTheta (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (k : ℕ) : ℝ :=
  B k (sVec x p α k) (sVec x p α k) / (‖sVec x p α k‖ * ‖B k (sVec x p α k)‖)

/-- The Rayleigh quotient (Appendix A, p. 620): `q_k = B_k(s_k, s_k) / ‖s_k‖²_{x_k}`. -/
noncomputable def rayleighQ (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k))
    (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (k : ℕ) : ℝ :=
  B k (sVec x p α k) (sVec x p α k) / ‖sVec x p α k‖ ^ 2

/-- A non-terminating run of Algorithm 1 (p. 600) with the BFGS search direction (6) and update
(p. 606) and Wolfe step size control (1a), (1b) with `0 < c₁ < c₂ < 1`, for a fixed retraction
family `R`:
* `x (k+1) = R_{x_k}(α_k p_k)` with `α_k > 0`;
* `B_k(p_k, ·) = −Df(x_k)`;
* `B_{k+1}(T_k v, T_k w) = B_k(v,w) − B_k(s_k,v) B_k(s_k,w) / B_k(s_k,s_k) + (y_k v)(y_k w)/(y_k s_k)`
  for all `v, w ∈ T_{x_k}M`, with invertible `T_k : T_{x_k}M → T_{x_{k+1}}M`;
* `f` is differentiable, each `f ∘ R_{x_k}` is `C²`, and `Df(x_k) ≠ 0` (the algorithm never stops). -/
structure IsBFGSRun (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (B : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x k) →L[ℝ] ℝ)
    (T : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x (k + 1))) :
    Prop where
  isRetraction : IsRetraction R
  differentiable : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f
  contDiff_comp : ∀ k, ContDiff ℝ 2 (f ∘ R (x k))
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  step : ∀ k, x (k + 1) = R (x k) (α k • p k)
  step_pos : ∀ k, 0 < α k
  wolfe : ∀ k, Wolfe f R c₁ c₂ (x k) (p k) (α k)
  direction : ∀ k (v : TangentSpace 𝓘(ℝ, E) (x k)), B k (p k) v = - Df (E := E) f (x k) v
  update : ∀ k (v w : TangentSpace 𝓘(ℝ, E) (x k)),
    B (k + 1) (T k v) (T k w) =
      B k v w - B k (sVec x p α k) v * B k (sVec x p α k) w / B k (sVec x p α k) (sVec x p α k)
        + yVec f R x p α k v * yVec f R x p α k w / yVec f R x p α k (sVec x p α k)
  nonstationary : ∀ k, Df (E := E) f (x k) ≠ 0

/-- Uniform convexity of the `f_{R_{x_k}}` on the `f(x₀)`-sublevel set (Proposition 10, p. 608),
with constants `0 < m < Mc`: for every `k` the set
`S_k = R_{x_k}⁻¹({y : f(y) ≤ f(x₀)}) ⊆ T_{x_k}M` is convex, and for all `q ∈ S_k`, `v ∈ T_{x_k}M`,
`m ‖v‖² ≤ D²f_{R_{x_k}}(q)(v,v) ≤ Mc ‖v‖²`. -/
def UniformlyConvexOnSublevel (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (x : ℕ → M) (m Mc : ℝ) : Prop :=
  0 < m ∧ m < Mc ∧ ∀ k,
    Convex ℝ {q : TangentSpace 𝓘(ℝ, E) (x k) | f (R (x k) q) ≤ f (x 0)} ∧
    ∀ q : TangentSpace 𝓘(ℝ, E) (x k), f (R (x k) q) ≤ f (x 0) →
      ∀ v : TangentSpace 𝓘(ℝ, E) (x k),
        m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (f ∘ R (x k))) q v v ∧
        fderiv ℝ (fderiv ℝ (f ∘ R (x k))) q v v ≤ Mc * ‖v‖ ^ 2

/-- The good-index property of Appendix A (pp. 621–622) for given `r, κ, ρ, σ`: for every `k ∈ ℕ`
there are at least `⌊r(k+1)⌋` indices `i ∈ {0, …, k}` with `cos θ_i ≥ κ` and
`ρ ≤ q_i / cos θ_i ≤ σ`. -/
def HasGoodIndices (cosθ q : ℕ → ℝ) (r κ ρ σ : ℝ) : Prop :=
  ∀ k : ℕ, ∃ I ⊆ Finset.range (k + 1), ⌊r * (k + 1)⌋₊ ≤ I.card ∧
    ∀ i ∈ I, κ ≤ cosθ i ∧ ρ ≤ q i / cosθ i ∧ q i / cosθ i ≤ σ

end RiemOpt.BFGS


