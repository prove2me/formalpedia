-- Prove2me | Definitions.Def_BSUMM_Rand_Setting
-- name    : BSUMM_Rand_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:29.029176+00:00
-- url     : https://prove2.me/theorems/760094ac-cf6d-4d1d-881f-680fbb76921a
-- title:
--   Problem (1.1) under Assumptions A and B: augmented Lagrangian (1.8), augmented dual (1.9), X(y), the proximal point of h + ι_X and the error bound (2.4)
-- statement:
--   This file fixes the model of Hong, Chang, Wang, Razaviyayn, Ma and Luo for the linearly constrained convex problem
--
--   $$\min_x\; f(x) := g(x_1,\dots,x_K) + \sum_{k=1}^K h_k(x_k) \quad\text{s.t.}\quad E_1x_1+\dots+E_Kx_K = q,\; x_k\in X_k,\; k=1,\dots,K. \tag{1.1}$$
--
--   **Data.** There are $K\ge 1$ blocks; block $k$ is a vector $x_k\in\mathbb R^{n_k}$ and $x=(x_1,\dots,x_K)\in\mathbb R^n$ carries the Euclidean norm $\|x\|^2=\sum_k\|x_k\|^2$. The matrices $E_k\in\mathbb R^{m\times n_k}$ give $Ex=\sum_k E_kx_k$, and $q\in\mathbb R^m$.
--
--   1. (Assumption A(b)) The smooth part is $g(x)=\ell(Ax)+\langle x,b\rangle$ with a matrix $A$, a vector $b$, and $\ell$ strictly convex and continuously differentiable.
--   2. (Assumption A(b)) The nonsmooth part is $h_k(x_k)=\lambda_k\|x_k\|_1+\sum_J w_J\|x_{k,J}\|_2$, where the coordinates of $x_k$ are partitioned into groups $J$, $\lambda_k\ge0$ and $w_J\ge0$. Write $h(x)=\sum_k h_k(x_k)$.
--   3. (Assumption A(c)) $X_k=\{x_k\mid C_kx_k\le c_k\}$ is compact, and $X=\prod_k X_k$.
--   4. (Assumption A(a)) The problem is feasible ($\exists x\in X$ with $Ex=q$), its minimum is attained and the dual optimal value is attained.
--
--   **Augmented Lagrangian and dual.** For a penalty $\rho>0$,
--
--   $$L(x;y)=f(x)+\langle y,q-Ex\rangle+\frac{\rho}{2}\|q-Ex\|^2,\qquad d(y)=\min_{x\in X}L(x;y), \tag{1.8, 1.9}$$
--
--   $X(y)=\arg\min_{x\in X}L(x;y)$, $f^*$ is the optimal value of (1.1), $d^*=\max_y d(y)$, and the optimality gaps are $\Delta_d=d^*-d(y)$ (2.15) and $\Delta_p=L(x;y)-d(y)$ (2.16). A point $x$ is primal optimal if it is feasible and minimizes $f$ among feasible points; $y$ is dual optimal if it maximizes $d$.
--
--   **Assumption B** on the approximation functions $u_k(v_k;x)$: for every $x\in X$ and every $k$,
--   (a) $u_k(x_k;x)=g(x)+\frac\rho2\|Ex-q\|^2$; (b) $u_k(v_k;x)\ge g(v_k,x_{-k})+\frac\rho2\|E_kv_k-q+E_{-k}x_{-k}\|^2$ for $v_k\in X_k$; (c) $\nabla u_k(x_k;x)=\nabla_k\big(g(x)+\frac\rho2\|Ex-q\|^2\big)$; (d) $u_k$ is continuous in $(v_k,x)$ and $\gamma_k$-strongly convex in $v_k$ on $X_k$, $\gamma_k>0$ independent of $x$; (e) $\nabla u_k(\cdot;x)$ is $L_k$-Lipschitz on $X_k$, $L_k>0$.
--
--   **Proximal gradient and error bound.** With $\operatorname{prox}(z)=\arg\min_{u\in X} h(u)+\frac12\|z-u\|^2$, the proximal gradient is $\tilde\nabla_xL(x;y)=x-\operatorname{prox}\big(x-\nabla_x(L(x;y)-h(x))\big)$ (2.3). The error bound (2.4) with constant $\tau$ says
--
--   $$\operatorname{dist}(x,X(y))\le\tau\,\|\tilde\nabla_xL(x;y)\|\qquad\text{for all } y\in\mathbb R^m,\ x\in X.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Blocks are `EuclideanSpace ℝ (Fin (n k))` and $x$ lives in `PiLp 2`, the Euclidean product. $\ell$ is real-valued on all of $\mathbb R^p$ (a specialization of the page, which allows an extended-valued $\ell$ differentiable on the interior of its domain); then $\operatorname{dom} f=\mathbb R^n$ and the Slater-type condition of A(a) is plain feasibility. The page's (1.9) prints $g$ and an unconstrained minimum; $d$ is read as $\min_{x\in X}L(x;y)$, which is what Lemma 2.1 and (2.19) use. The prox in (2.3) is printed over all of $\mathbb R^n$; here it includes the constraint $X$ (the prox of $h+\iota_X$), which is the reading the proof of Lemma 2.4 needs at (2.14). The error bound is a hypothesis of Theorem 2.1, not derived. $u_k$ is real-valued on $\mathbb R^{n_k}\times\mathbb R^n$ and required to be differentiable in $v$ at points of $X_k$. $d$, $f^*$, $d^*$ are real infima/suprema; they are the true values under Assumption A (nonempty compact $X$, attained dual).
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, pp. 1, 3, 5–9, 12, (1.1), (1.8), (1.9), Assumptions A–B, X(y), Definition 2.1, (2.3), (2.4), (2.15), (2.16)

import Mathlib

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- The data of problem (1.1) of Hong–Chang–Wang–Razaviyayn–Ma–Luo (arXiv:1401.7079v1, p. 1),
with `g(x) = ℓ(Ax) + ⟨x, b⟩` (Assumption A(b)), the mixed `ℓ₁/ℓ₂` regularizers `h_k`
(Assumption A(b)), the polyhedral blocks `X_k = {x_k | C_k x_k ≤ c_k}` (Assumption A(c)) and the
penalty parameter `ρ` of the augmented Lagrangian (1.8).

* `K` blocks, block `k` lives in `ℝ^{n k}`; the constraint space is `ℝ^m`; `A` maps into `ℝ^{pdim}`.
* `E k` is the matrix `E_k`, so `Ex = ∑_k E_k x_k`.
* the coordinates of block `k` are partitioned into the groups `J : Fin (ng k)` by `grp k`, with
  weights `w k J`, and `λ_k = lam k`. -/
structure Setting where
  K : ℕ
  n : Fin K → ℕ
  m : ℕ
  pdim : ℕ
  E : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) →L[ℝ] EuclideanSpace ℝ (Fin m)
  q : EuclideanSpace ℝ (Fin m)
  A : PiLp 2 (fun k : Fin K => EuclideanSpace ℝ (Fin (n k))) →L[ℝ] EuclideanSpace ℝ (Fin pdim)
  b : PiLp 2 (fun k : Fin K => EuclideanSpace ℝ (Fin (n k)))
  ell : EuclideanSpace ℝ (Fin pdim) → ℝ
  lam : Fin K → ℝ
  ng : Fin K → ℕ
  grp : (k : Fin K) → Fin (n k) → Fin (ng k)
  w : (k : Fin K) → Fin (ng k) → ℝ
  mc : Fin K → ℕ
  C : (k : Fin K) → Matrix (Fin (mc k)) (Fin (n k)) ℝ
  c : (k : Fin K) → Fin (mc k) → ℝ
  ρ : ℝ

namespace Setting

variable (S : Setting)

/-- The primal space `ℝⁿ = ∏_k ℝ^{n_k}` with the Euclidean norm `‖x‖² = ∑_k ‖x_k‖²`. -/
abbrev Xsp : Type := PiLp 2 (fun k : Fin S.K => EuclideanSpace ℝ (Fin (S.n k)))

/-- The dual space `ℝ^m`. -/
abbrev Ysp : Type := EuclideanSpace ℝ (Fin S.m)

/-- The linear map `x ↦ Ex = ∑_k E_k x_k`. -/
noncomputable def Emap : S.Xsp →L[ℝ] S.Ysp :=
  ∑ k, (S.E k).comp (PiLp.proj 2 (fun k : Fin S.K => EuclideanSpace ℝ (Fin (S.n k))) k)

/-- `x[k ↦ v] = (v, x_{-k})`: the vector `x` with its `k`-th block replaced by `v`. -/
noncomputable def upd (x : S.Xsp) (k : Fin S.K) (v : EuclideanSpace ℝ (Fin (S.n k))) : S.Xsp :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp x) k v)

/-- The smooth part `g(x) = ℓ(Ax) + ⟨x, b⟩`. -/
noncomputable def g (x : S.Xsp) : ℝ := S.ell (S.A x) + ⟪x, S.b⟫

/-- The block regularizer `h_k(x_k) = λ_k ‖x_k‖₁ + ∑_J w_J ‖x_{k,J}‖₂`. -/
noncomputable def h (k : Fin S.K) (v : EuclideanSpace ℝ (Fin (S.n k))) : ℝ :=
  S.lam k * ∑ i, |v i| +
    ∑ J, S.w k J * Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => S.grp k i = J), v i ^ 2)

/-- `h(x) = ∑_k h_k(x_k)`. -/
noncomputable def hsum (x : S.Xsp) : ℝ := ∑ k, S.h k (x k)

/-- The objective `f(x) = g(x) + h(x)` of (1.1). -/
noncomputable def f (x : S.Xsp) : ℝ := S.g x + S.hsum x

/-- The block feasible set `X_k = {x_k | C_k x_k ≤ c_k}`. -/
def Xk (k : Fin S.K) : Set (EuclideanSpace ℝ (Fin (S.n k))) :=
  {v | ∀ j, Matrix.mulVec (S.C k) (WithLp.ofLp v) j ≤ S.c k j}

/-- `X = ∏_k X_k`. -/
def Xset : Set S.Xsp := {x | ∀ k, x k ∈ S.Xk k}

/-- The augmented Lagrangian (1.8): `L(x; y) = f(x) + ⟨y, q - Ex⟩ + ρ/2 ‖q - Ex‖²`. -/
noncomputable def Lag (x : S.Xsp) (y : S.Ysp) : ℝ :=
  S.f x + ⟪y, S.q - S.Emap x⟫ + S.ρ / 2 * ‖S.q - S.Emap x‖ ^ 2

/-- The augmented dual function `d(y) = min_{x ∈ X} L(x; y)` ((1.9), read with the constraint
`x ∈ X` and the full objective, as Lemma 2.1 and (2.19) use it). -/
noncomputable def d (y : S.Ysp) : ℝ := ⨅ x : S.Xset, S.Lag x y

/-- `X(y)`: the minimizers of `L(·; y)` over `X`. -/
def Xopt (y : S.Ysp) : Set S.Xsp := {x | x ∈ S.Xset ∧ ∀ x' ∈ S.Xset, S.Lag x y ≤ S.Lag x' y}

/-- The optimal value `f*` of (1.1). -/
noncomputable def fstar : ℝ := ⨅ x : {x : S.Xsp // x ∈ S.Xset ∧ S.Emap x = S.q}, S.f x

/-- The dual optimal value `d* = max_y d(y)`. -/
noncomputable def dstar : ℝ := ⨆ y : S.Ysp, S.d y

/-- The dual optimality gap (2.15): `Δ_d = d* - d(y)`. -/
noncomputable def DeltaD (y : S.Ysp) : ℝ := S.dstar - S.d y

/-- The primal optimality gap (2.16): `Δ_p = L(x; y) - d(y)`. -/
noncomputable def DeltaP (x : S.Xsp) (y : S.Ysp) : ℝ := S.Lag x y - S.d y

/-- `x` is an optimal solution of (1.1). -/
def IsPrimalOpt (x : S.Xsp) : Prop :=
  x ∈ S.Xset ∧ S.Emap x = S.q ∧ ∀ x' ∈ S.Xset, S.Emap x' = S.q → S.f x ≤ S.f x'

/-- `y` is an optimal solution of the dual problem (1.10) `max_y d(y)`. -/
def IsDualOpt (y : S.Ysp) : Prop := ∀ y' : S.Ysp, S.d y' ≤ S.d y

/-- The standing Assumption A (pp. 6–7), together with `K ≥ 1` and `ρ > 0` from (1.1), (1.8). `ℓ` is taken
real-valued on all of `ℝ^{pdim}`, so `dom f = ℝⁿ` and the Slater-type condition of A(a) reads
`∃ x ∈ X, Ex = q`. -/
structure AssumptionA : Prop where
  K_pos : 0 < S.K
  rho_pos : 0 < S.ρ
  ell_strictConvex : StrictConvexOn ℝ Set.univ S.ell
  ell_contDiff : ContDiff ℝ 1 S.ell
  lam_nonneg : ∀ k, 0 ≤ S.lam k
  w_nonneg : ∀ k J, 0 ≤ S.w k J
  X_compact : ∀ k, IsCompact (S.Xk k)
  feasible : ∃ x ∈ S.Xset, S.Emap x = S.q
  primal_attained : ∃ x, S.IsPrimalOpt x
  dual_attained : ∃ y, S.IsDualOpt y

/-- The type of the approximation functions `u_k(v_k; x)` of (1.11): `u k v x = u_k(v; x)`. -/
abbrev UFun : Type := (k : Fin S.K) → EuclideanSpace ℝ (Fin (S.n k)) → S.Xsp → ℝ

/-- The smooth part of the augmented Lagrangian without the multiplier term,
`g(x) + ρ/2 ‖Ex - q‖²`, which the `u_k` majorize. -/
noncomputable def gPen (x : S.Xsp) : ℝ := S.g x + S.ρ / 2 * ‖S.Emap x - S.q‖ ^ 2

/-- Assumption B (p. 7) on the approximation functions `u_k`. The gradient `∇u_k(v; x)` is taken
in `v`; (d) states differentiability in `v` at the points of `X_k` (presupposed by the page's
`∇u_k`) and joint continuity on `X_k × X`. -/
structure AssumptionB (u : S.UFun) : Prop where
  /-- B(a) -/
  tight : ∀ x ∈ S.Xset, ∀ k, u k (x k) x = S.gPen x
  /-- B(b) -/
  upper : ∀ k, ∀ x ∈ S.Xset, ∀ v ∈ S.Xk k, S.gPen (S.upd x k v) ≤ u k v x
  /-- B(c) -/
  grad_eq : ∀ k, ∀ x ∈ S.Xset, gradient (fun v => u k v x) (x k) = (gradient S.gPen x) k
  /-- B(d), continuity -/
  cont : ∀ k, ContinuousOn (fun vx : EuclideanSpace ℝ (Fin (S.n k)) × S.Xsp => u k vx.1 vx.2)
    (S.Xk k ×ˢ S.Xset)
  /-- B(d), differentiability in `v` on `X_k` -/
  diff : ∀ k, ∀ x ∈ S.Xset, ∀ v ∈ S.Xk k, DifferentiableAt ℝ (fun v' => u k v' x) v
  /-- B(d), strong convexity in `v` with modulus `γ_k > 0` independent of `x` -/
  strongConvex : ∃ γ : Fin S.K → ℝ, (∀ k, 0 < γ k) ∧
    ∀ k, ∀ x ∈ S.Xset, ∀ v ∈ S.Xk k, ∀ vh ∈ S.Xk k,
      u k vh x + ⟪gradient (fun v' => u k v' x) vh, v - vh⟫ + γ k / 2 * ‖v - vh‖ ^ 2 ≤ u k v x
  /-- B(e), (2.1): Lipschitz gradient in `v` on `X_k` with constant `L_k > 0` -/
  lipschitz : ∃ L : Fin S.K → ℝ, (∀ k, 0 < L k) ∧
    ∀ k, ∀ x ∈ S.Xset, ∀ v ∈ S.Xk k, ∀ vh ∈ S.Xk k,
      ‖gradient (fun v' => u k v' x) v - gradient (fun v' => u k v' x) vh‖ ≤ L k * ‖v - vh‖

/-- `∇ₓ(L(x; y) - h(x))`, the gradient of the smooth part of the augmented Lagrangian in `x`. -/
noncomputable def gL (x : S.Xsp) (y : S.Ysp) : S.Xsp :=
  gradient (fun z => S.g z + ⟪y, S.q - S.Emap z⟫ + S.ρ / 2 * ‖S.q - S.Emap z‖ ^ 2) x

/-- `p` is the proximal point of `z` for `h + ι_X`:
`p = argmin_{u ∈ X} h(u) + ½‖z - u‖²`. With it, `x - p` for `z = x - ∇ₓ(L(x;y) - h(x))` is the
proximal gradient `∇̃ₓL(x; y)` of (2.3), read with the constraint `X` inside the prox. -/
def IsProxPt (z p : S.Xsp) : Prop :=
  p ∈ S.Xset ∧ ∀ v ∈ S.Xset, S.hsum p + ‖z - p‖ ^ 2 / 2 ≤ S.hsum v + ‖z - v‖ ^ 2 / 2

/-- The error bound (2.4) of Lemma 2.2 in its global form (part 2, `X` compact) with constant `τ`:
`dist(x, X(y)) ≤ τ ‖∇̃ₓL(x; y)‖` for every `y` and every `x ∈ X`. -/
def ErrorBoundWith (τ : ℝ) : Prop :=
  ∀ (y : S.Ysp) (x p : S.Xsp), x ∈ S.Xset → S.IsProxPt (x - S.gL x y) p →
    Metric.infDist x (S.Xopt y) ≤ τ * ‖x - p‖

end Setting

end BSUMM.Rand


