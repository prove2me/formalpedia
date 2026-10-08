-- Prove2me | Definitions.Def_BarrierTR_Global_Setting
-- name    : BarrierTR_Global_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:36.483681+00:00
-- url     : https://prove2.me/theorems/e3948c25-693c-44d9-95ce-bf2d589e7064
-- title:
--   §1–§4 — problem (2.1)/(2.2), merit function (2.5), pred/vpred/hpred/ared (2.7), (2.17), (2.28), (3.1), Cauchy and range space conditions (2.14)–(2.34), LICQ and KKT
-- statement:
--   We consider the nonlinear program
--   $$\min f(x)\quad\text{s.t.}\quad g(x)\le 0,\qquad f:\mathbb R^n\to\mathbb R,\ g:\mathbb R^n\to\mathbb R^m,$$
--   problem (2.1), and for a barrier parameter $\mu>0$ the barrier problem (2.2), $\min f(x)-\mu\sum_{i=1}^m\ln s^{(i)}$ s.t. $g(x)+s=0$, with slacks $s>0$. This file fixes the objects that every statement of the mission uses.
--
--   1. **Spaces and matrices.** $x\in\mathbb R^n$, $s\in\mathbb R^m$, stacked vectors $z=(x,s)$, $d=(d_x,d_s)\in\mathbb R^{n+m}$, all with the Euclidean norm. $A(x)=(\nabla g^{(1)}(x),\dots,\nabla g^{(m)}(x))$ is the $n\times m$ matrix of constraint gradients (1.7), $S=\operatorname{diag}(s)$, $e=(1,\dots,1)$. The vectors $(A;S)w=(A w,Sw)$ and $(A;S^2)w$, the matrix $(A^\top\ S)$ and its spectral norm, and $(u_x,Du_s)$ with $D=\delta S^{-1}$ are defined explicitly.
--   2. **Merit function and reductions.** For $s>0$, $\phi(x,s;\nu)=f(x)+\nu\|g(x)+s\|-\mu\sum_i\ln s^{(i)}$ (2.5). At an iterate $(x,s)$ with penalty $\nu$ and symmetric matrix $B$,
--   $$\mathrm{pred}(d)=-\nabla f^\top d_x-\tfrac12 d_x^\top Bd_x+\nu\big(\|g+s\|-\|g+s+A^\top d_x+d_s\|\big)+\mu\big(e^\top S^{-1}d_s-\tfrac12 d_s^\top S^{-2}d_s\big)$$
--   (2.7), $\mathrm{ared}(d)=\phi(x,s;\nu)-\phi(x+d_x,s+d_s;\nu)$ (3.1), $\mathrm{vpred}(v)=\|g+s\|-\|g+s+A^\top v_x+v_s\|$ (2.17), $\mathrm{hpred}$ (2.28) and $\chi$ (2.41).
--   3. **Steepest descent directions.** $v^c=-(A;S^2)(g+s)$ (2.16) and $p^c=-Z_x^\top(\nabla f+Bv_x)+\mu Z_s^\top(S^{-1}e-S^{-2}v_s)$ (2.32), for a null-space basis $Z=(Z_x^\top\ Z_s^\top)^\top$ with $A^\top Z_x+Z_s=0$, $\|Z\|\le\gamma_Z$, $\sigma_{\min}(Z)\ge\gamma_Z^{-1}$ (2.29)–(2.30).
--   4. **Step conditions.** Feasibility for the vertical problem (2.9), $\|(v_x,\tilde Dv_s)\|_T\le\tilde\Delta$ with $\tilde D=\max(\beta,\tilde\Delta)S^{-1}$; the range space condition (2.14); the vertical Cauchy decrease condition (2.18)–(2.19); feasibility for the horizontal problem (2.26), $A^\top h_x+h_s=0$, $\|(h_x,Dh_s)\|_T\le\hat\Delta$ with $D=\max(\beta,\Delta)S^{-1}$; and the horizontal Cauchy decrease condition (2.33)–(2.34).
--   5. **Limits.** A stationary point of (2.2) ((1.5)–(1.6)); asymptotic feasibility $g(x_k)^+\to0$ and a limit point $(\bar g,\bar A)$ of $\{(g_k,A_k)\}$ failing the linear independence constraint qualification, i.e. $\{\bar A^{(i)}:\bar g^{(i)}=0\}$ rank deficient (Definitions 4.2); LICQ at a point; the KKT conditions $\nabla f+A\lambda=0$, $g\le0$, $\lambda\ge0$, $g^\top\lambda=0$; Lipschitz continuity on a set.
--
--   These definitions are shared by every lemma and theorem of the mission.
--
--   **Formalization Note** The merit function is real-valued; the paper's value $+\infty$ for $s\not>0$ is never needed because every use is guarded by positivity of the slacks. The Cauchy conditions (2.18), (2.33) are stated without the minimizers $\alpha^c_k,\theta^c_k$: $\mathrm{vpred}(v)\ge\gamma_1\,\mathrm{vpred}(\alpha v^c)$ for every $\alpha\in\mathbb R$ feasible for (2.19), and likewise for $\theta$ in (2.34). Since $\alpha^c_k$ maximizes $\mathrm{vpred}(\alpha v^c)$ over the same compact feasible interval, this is equivalent to (2.18) for $\gamma_1>0$. The limit point $(\bar g,\bar A)$ is a cluster point of the sequence, and rank deficiency of the columns is linear dependence of the indexed family, so two equal columns count as dependent. $\|\cdot\|_T$ is a seminorm that vanishes only at $0$, i.e. a norm.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, pp. 1–21, (1.5)–(1.8), (2.1)–(2.41), (3.1), Definitions 4.2, Theorem 5.1

import Mathlib

namespace BarrierTR.Global

open scoped RealInnerProductSpace
open Filter Topology

/-! # Setting of Byrd–Gilbert–Nocedal (INRIA RR-2896, 1996), §1–§4

Problem (2.1): `min f(x)` s.t. `g(x) ≤ 0`, with `f : ℝⁿ → ℝ`, `g : ℝⁿ → ℝᵐ`; barrier problem (2.2):
`min f(x) − μ Σᵢ ln s⁽ⁱ⁾` s.t. `g(x) + s = 0`. All norms `‖·‖` are Euclidean. -/

/-- The variable space `ℝⁿ` of `x` (Euclidean norm). -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The slack space `ℝᵐ` of `s` (Euclidean norm). -/
abbrev F (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The space `ℝⁿ⁺ᵐ` of stacked vectors `z = (x, s)`, `d = (d_x, d_s)`, with the Euclidean norm
`‖(a, b)‖ = √(‖a‖² + ‖b‖²)`. -/
abbrev Z (n m : ℕ) := WithLp 2 (E n × F m)

variable {n m : ℕ}

/-- The stacked vector `(a, b) ∈ ℝⁿ⁺ᵐ`. -/
def pair (a : E n) (b : F m) : Z n m := WithLp.toLp 2 (a, b)

/-- `A(x) = (∇g⁽¹⁾(x), …, ∇g⁽ᵐ⁾(x))` (1.7), the `n × m` matrix of constraint gradients, as the
linear map `w ↦ Σᵢ wᵢ ∇g⁽ⁱ⁾(x)`, i.e. the adjoint of the derivative of `g` at `x`. Its transpose
`A(x)ᵀ` is `fderiv ℝ g x`. -/
noncomputable def A (g : E n → F m) (x : E n) : F m →L[ℝ] E n :=
  ContinuousLinearMap.adjoint (fderiv ℝ g x)

/-- The diagonal matrix `diag(c)` acting on `ℝᵐ`: `(diag(c) w)⁽ⁱ⁾ = c⁽ⁱ⁾ w⁽ⁱ⁾`. With `c = s` it is
`S = diag(s)` (1.8); with `c⁽ⁱ⁾ = 1/s⁽ⁱ⁾` it is `S⁻¹`; with `c⁽ⁱ⁾ = (s⁽ⁱ⁾)²` it is `S²`. -/
noncomputable def diagL (c : Fin m → ℝ) : F m →L[ℝ] F m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i => c i * w i)
      map_add' := by
        intro u w
        ext i
        simp [mul_add]
      map_smul' := by
        intro r w
        ext i
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

/-- `S⁻¹e`, the vector with components `1/s⁽ⁱ⁾` (`e = (1, …, 1)`). -/
noncomputable def sInvE (s : F m) : F m := WithLp.toLp 2 (fun i => 1 / s i)

/-- Componentwise positive part `u⁺`, `(u⁺)⁽ⁱ⁾ = max(0, u⁽ⁱ⁾)` (p. 21). -/
noncomputable def pos (u : F m) : F m := WithLp.toLp 2 (fun i => max 0 (u i))

/-- `(A; S) w = (A(x) w, S w) ∈ ℝⁿ⁺ᵐ`, the transpose of the `m × (n+m)` matrix `(A(x)ᵀ  S)`
applied to `w ∈ ℝᵐ`. -/
noncomputable def stackAS (g : E n → F m) (x : E n) (s : F m) (w : F m) : Z n m :=
  pair (A g x w) (diagL (fun i => s i) w)

/-- The `m × (n+m)` matrix `(A(x)ᵀ  S)`, i.e. `(u_x, u_s) ↦ A(x)ᵀ u_x + S u_s`, as a continuous
linear map; `‖rowATS g x s‖` is its spectral norm `‖(A(x)ᵀ  S)‖`. -/
noncomputable def rowATS (g : E n → F m) (x : E n) (s : F m) : Z n m →L[ℝ] F m :=
  (fderiv ℝ g x).comp (WithLp.fstL 2 ℝ (E n) (F m)) +
    (diagL (fun i => s i)).comp (WithLp.sndL 2 ℝ (E n) (F m))

/-- `(u_x, D u_s)` with `D = δ S⁻¹` (1.23), (2.10): the vector whose `‖·‖_T`-norm is bounded in the
trust-region constraints (2.9), (2.26), (2.34), (2.37), (2.38). -/
noncomputable def scaleD (δ : ℝ) (s : F m) (u : Z n m) : Z n m :=
  pair u.fst (diagL (fun i => δ / s i) u.snd)

/-- The merit function (2.5) `φ(x, s; ν) = f(x) + ν‖g(x) + s‖ − μ Σᵢ ln s⁽ⁱ⁾`, for `s > 0`.
(For `s ≯ 0` the paper sets `φ = +∞`; every use below is guarded by positivity of the slacks.) -/
noncomputable def merit (f : E n → ℝ) (g : E n → F m) (μ ν : ℝ) (x : E n) (s : F m) : ℝ :=
  f x + ν * ‖g x + s‖ - μ * ∑ i, Real.log (s i)

/-- The predicted reduction (2.7) at the iterate `(x, s)` with penalty `ν` and matrix `B`:
`pred(d) = −∇f(x)ᵀd_x − ½ d_xᵀ B d_x + ν(‖g + s‖ − ‖g + s + Aᵀd_x + d_s‖)
  + μ(eᵀS⁻¹d_s − ½ d_sᵀS⁻²d_s)`. -/
noncomputable def pred (f : E n → ℝ) (g : E n → F m) (μ ν : ℝ) (x : E n) (s : F m)
    (B : E n →L[ℝ] E n) (d : Z n m) : ℝ :=
  -⟪gradient f x, d.fst⟫ - (1 / 2) * ⟪d.fst, B d.fst⟫
    + ν * (‖g x + s‖ - ‖g x + s + fderiv ℝ g x d.fst + d.snd‖)
    + μ * (∑ i, d.snd i / s i - (1 / 2) * ∑ i, (d.snd i / s i) ^ 2)

/-- The actual reduction (3.1): `ared(d) = φ(x, s; ν) − φ(x + d_x, s + d_s; ν)` (meaningful when
`s > 0` and `s + d_s > 0`). -/
noncomputable def ared (f : E n → ℝ) (g : E n → F m) (μ ν : ℝ) (x : E n) (s : F m)
    (d : Z n m) : ℝ :=
  merit f g μ ν x s - merit f g μ ν (x + d.fst) (s + d.snd)

/-- The vertical predicted reduction (2.17): `vpred(v) = ‖g + s‖ − ‖g + s + Aᵀv_x + v_s‖`. -/
noncomputable def vpred (g : E n → F m) (x : E n) (s : F m) (v : Z n m) : ℝ :=
  ‖g x + s‖ - ‖g x + s + fderiv ℝ g x v.fst + v.snd‖

/-- The horizontal predicted reduction (2.28), for the vertical step `v`:
`hpred(h) = −(∇f + B v_x)ᵀh_x − ½ h_xᵀ B h_x + μ(eᵀS⁻¹h_s − v_sᵀS⁻²h_s − ½ h_sᵀS⁻²h_s)`. -/
noncomputable def hpred (f : E n → ℝ) (μ : ℝ) (x : E n) (s : F m) (B : E n →L[ℝ] E n)
    (v h : Z n m) : ℝ :=
  -⟪gradient f x + B v.fst, h.fst⟫ - (1 / 2) * ⟪h.fst, B h.fst⟫
    + μ * (∑ i, h.snd i / s i - ∑ i, v.snd i * h.snd i / s i ^ 2
      - (1 / 2) * ∑ i, (h.snd i / s i) ^ 2)

/-- The term (2.41): `χ = −∇f(x)ᵀv_x − ½ v_xᵀ B v_x + μ(eᵀS⁻¹v_s − ½ v_sᵀS⁻²v_s)`. -/
noncomputable def chi (f : E n → ℝ) (μ : ℝ) (x : E n) (s : F m) (B : E n →L[ℝ] E n)
    (v : Z n m) : ℝ :=
  -⟪gradient f x, v.fst⟫ - (1 / 2) * ⟪v.fst, B v.fst⟫
    + μ * (∑ i, v.snd i / s i - (1 / 2) * ∑ i, (v.snd i / s i) ^ 2)

/-- The scaled steepest descent direction (2.16): `v^c = −(A; S²)(g + s)`. -/
noncomputable def vc (g : E n → F m) (x : E n) (s : F m) : Z n m :=
  pair (-(A g x (g x + s))) (-(diagL (fun i => s i ^ 2) (g x + s)))

/-- The range vector `(A; S²) w` of the range space condition (2.14). -/
noncomputable def rangeVec (g : E n → F m) (x : E n) (s : F m) (w : F m) : Z n m :=
  pair (A g x w) (diagL (fun i => s i ^ 2) w)

/-- `Z p = (Z_x p, Z_s p)` for the `(n+m) × n` null-space basis matrix `Z = (Z_xᵀ Z_sᵀ)ᵀ`. -/
noncomputable def zmap (Zx : E n →L[ℝ] E n) (Zs : E n →L[ℝ] F m) (p : E n) : Z n m :=
  pair (Zx p) (Zs p)

/-- The null-space basis conditions (2.29)–(2.30) on `Z = (Z_xᵀ Z_sᵀ)ᵀ` at `x`:
`A(x)ᵀ Z_x + Z_s = 0`, `‖Z‖ ≤ γ_Z` and `σ_min(Z) ≥ γ_Z⁻¹` (which makes `Z` of full rank `n`). -/
def IsNullBasis (g : E n → F m) (x : E n) (γZ : ℝ) (Zx : E n →L[ℝ] E n)
    (Zs : E n →L[ℝ] F m) : Prop :=
  (fderiv ℝ g x).comp Zx + Zs = 0 ∧
    (∀ p : E n, ‖zmap Zx Zs p‖ ≤ γZ * ‖p‖) ∧
    (∀ p : E n, γZ⁻¹ * ‖p‖ ≤ ‖zmap Zx Zs p‖)

/-- The steepest descent direction (2.32) of the horizontal problem in the variable `p`:
`p^c = −Z_xᵀ(∇f + B v_x) + μ Z_sᵀ(S⁻¹e − S⁻²v_s)`. -/
noncomputable def pc (f : E n → ℝ) (μ : ℝ) (x : E n) (s : F m) (B : E n →L[ℝ] E n)
    (Zx : E n →L[ℝ] E n) (Zs : E n →L[ℝ] F m) (v : Z n m) : E n :=
  -(ContinuousLinearMap.adjoint Zx (gradient f x + B v.fst))
    + μ • ContinuousLinearMap.adjoint Zs (WithLp.toLp 2 (fun i => 1 / s i - v.snd i / s i ^ 2))

/-! ## The vertical subproblem (2.9) and its conditions, with `Δ̃ = Δt`, `δ̃ = max(β, Δ̃)` -/

/-- Feasibility for the vertical problem (2.9): `‖(v_x, D̃ v_s)‖_T ≤ Δ̃`, `D̃ = max(β, Δ̃) S⁻¹`. -/
def VertFeasible (T : Seminorm ℝ (Z n m)) (β Δt : ℝ) (s : F m) (v : Z n m) : Prop :=
  T (scaleD (max β Δt) s v) ≤ Δt

/-- `v` solves (2.9): feasible and minimizing `‖g + s + Aᵀv_x + v_s‖` over the feasible set. -/
def IsVertSolution (T : Seminorm ℝ (Z n m)) (β Δt : ℝ) (g : E n → F m) (x : E n) (s : F m)
    (v : Z n m) : Prop :=
  VertFeasible T β Δt s v ∧
    ∀ u : Z n m, VertFeasible T β Δt s u →
      ‖g x + s + fderiv ℝ g x v.fst + v.snd‖ ≤ ‖g x + s + fderiv ℝ g x u.fst + u.snd‖

/-- Range space condition (2.14): `v = (A; S²) w` for some `w ∈ ℝᵐ`, whenever (2.9) has a solution
of that form. -/
def RangeSpaceCond (T : Seminorm ℝ (Z n m)) (β Δt : ℝ) (g : E n → F m) (x : E n) (s : F m)
    (v : Z n m) : Prop :=
  (∃ w : F m, IsVertSolution T β Δt g x s (rangeVec g x s w)) → ∃ w : F m, v = rangeVec g x s w

/-- Vertical Cauchy decrease condition (2.18)–(2.19), stated without the argmin `α^c`:
`vpred(v) ≥ γ₁ vpred(α v^c)` for every `α ∈ ℝ` with `‖α(v^c_x, D̃ v^c_s)‖_T ≤ Δ̃`. -/
def VertCauchy (T : Seminorm ℝ (Z n m)) (β Δt γ₁ : ℝ) (g : E n → F m) (x : E n) (s : F m)
    (v : Z n m) : Prop :=
  ∀ α : ℝ, T (α • scaleD (max β Δt) s (vc g x s)) ≤ Δt →
    γ₁ * vpred g x s (α • vc g x s) ≤ vpred g x s v

/-! ## The horizontal subproblem (2.26) and its condition, with `δ = max(β, Δ)` -/

/-- Feasibility for the horizontal problem (2.26): `Aᵀh_x + h_s = 0` and `‖(h_x, D h_s)‖_T ≤ Δ̂`,
`D = max(β, Δ) S⁻¹`. -/
def HorizFeasible (T : Seminorm ℝ (Z n m)) (β Δ Δhat : ℝ) (g : E n → F m) (x : E n) (s : F m)
    (h : Z n m) : Prop :=
  fderiv ℝ g x h.fst + h.snd = 0 ∧ T (scaleD (max β Δ) s h) ≤ Δhat

/-- Horizontal Cauchy decrease condition (2.33)–(2.34), without the argmin `θ^c`:
`hpred(h) ≥ γ₂ hpred(θ Z p^c)` for every `θ ∈ ℝ` with `‖θ(Z_x p^c, D Z_s p^c)‖_T ≤ Δ̂`. -/
def HorizCauchy (T : Seminorm ℝ (Z n m)) (β Δ Δhat γ₂ : ℝ) (f : E n → ℝ) (μ : ℝ) (x : E n)
    (s : F m) (B : E n →L[ℝ] E n) (Zx : E n →L[ℝ] E n) (Zs : E n →L[ℝ] F m) (v h : Z n m) :
    Prop :=
  ∀ θ : ℝ, T (θ • scaleD (max β Δ) s (zmap Zx Zs (pc f μ x s B Zx Zs v))) ≤ Δhat →
    γ₂ * hpred f μ x s B v (θ • zmap Zx Zs (pc f μ x s B Zx Zs v)) ≤ hpred f μ x s B v h

/-! ## Stationarity, feasibility, constraint qualification -/

/-- `(x, s)` is a stationary point of the barrier problem (2.2): the KKT system (1.5)–(1.6) with
`g(x) + s = 0`, i.e. `∃ λ, ∇f(x) + A(x)λ = 0` and `−μS⁻¹e + λ = 0`. -/
def IsBarrierStationary (f : E n → ℝ) (g : E n → F m) (μ : ℝ) (x : E n) (s : F m) : Prop :=
  g x + s = 0 ∧ ∃ lam : F m, gradient f x + A g x lam = 0 ∧ -(μ • sInvE s) + lam = 0

/-- Definitions 4.2: `{x_k}` is asymptotically feasible if `g(x_k)⁺ → 0`. -/
def IsAsymptoticallyFeasible (g : E n → F m) (x : ℕ → E n) : Prop :=
  Tendsto (fun k => pos (g (x k))) atTop (𝓝 0)

/-- Definitions 4.2: `{(g_k, A_k)}` (`g_k = g(x_k)`, `A_k = A(x_k)`) has a limit point `(ḡ, Ā)`
failing the linear independence constraint qualification, i.e. the family of columns
`{Ā⁽ⁱ⁾ : ḡ⁽ⁱ⁾ = 0}` (`Ā⁽ⁱ⁾ = Ā eᵢ`) is linearly dependent. -/
def HasLICQFailingLimitPoint (g : E n → F m) (x : ℕ → E n) : Prop :=
  ∃ (gbar : F m) (Abar : F m →L[ℝ] E n),
    MapClusterPt (gbar, Abar) atTop (fun k => (g (x k), A g (x k))) ∧
      ¬ LinearIndependent ℝ (fun i : {i : Fin m // gbar i = 0} => Abar (EuclideanSpace.single i.1 1))

/-- The linear independence constraint qualification at `x`: the gradients
`{∇g⁽ⁱ⁾(x) : g⁽ⁱ⁾(x) = 0}` of the active constraints are linearly independent. -/
def LICQAt (g : E n → F m) (x : E n) : Prop :=
  LinearIndependent ℝ (fun i : {i : Fin m // g x i = 0} => A g x (EuclideanSpace.single i.1 1))

/-- First-order optimality (KKT) conditions of (2.1) at `x` (Theorem 5.1):
`∃ λ ∈ ℝᵐ, ∇f(x) + A(x)λ = 0, g(x) ≤ 0, λ ≥ 0, g(x)ᵀλ = 0`. -/
def IsKKTPoint (f : E n → ℝ) (g : E n → F m) (x : E n) : Prop :=
  ∃ lam : F m, gradient f x + A g x lam = 0 ∧ (∀ i, g x i ≤ 0) ∧ (∀ i, 0 ≤ lam i) ∧
    ⟪g x, lam⟫ = 0

/-- `φ` is Lipschitz continuous on `X`: `‖φ x − φ y‖ ≤ L‖x − y‖` for all `x, y ∈ X`. -/
def LipOn {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] (X : Set α)
    (φ : α → β) : Prop :=
  ∃ L : ℝ, ∀ x ∈ X, ∀ y ∈ X, ‖φ x - φ y‖ ≤ L * ‖x - y‖

end BarrierTR.Global


