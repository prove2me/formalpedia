-- Prove2me | Definitions.Def_BSUMM_Det_Setting
-- name    : BSUMM_Det_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:27.004068+00:00
-- url     : https://prove2.me/theorems/bb6070fc-debe-407f-a573-524bed89e081
-- title:
--   Problem (1.1) under Assumptions A and B, the augmented Lagrangian (1.8), the augmented dual (1.9), the proximal gradient (2.3) and the BSUM-M run (1.12)
-- statement:
--   This file fixes the model of Hong, Chang, Wang, Razaviyayn, Ma and Luo: a linearly constrained convex problem with $K$ blocks, its augmented Lagrangian and augmented dual, the proximal-gradient optimality measure, the error bound, and the cyclic algorithm BSUM-M.
--
--   **Problem (1.1).** The variable is $x=(x_1,\dots,x_K)$ with $x_k\in\mathbb R^{n_k}$, $K\ge 1$, and $\mathbb R^n=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_K}$ carries the Euclidean norm $\|x\|^2=\sum_k\|x_k\|^2$. The problem is
--   $$\min_x\ f(x):=g(x)+\sum_{k=1}^K h_k(x_k)\quad\text{s.t.}\quad Ex:=\sum_{k=1}^K E_kx_k=q,\quad x_k\in X_k,$$
--   with linear maps $E_k:\mathbb R^{n_k}\to\mathbb R^m$ and $q\in\mathbb R^m$. Following Assumption A:
--
--   1. $g(x)=\ell(Ax)+\langle x,b\rangle$ with a linear map $A:\mathbb R^n\to\mathbb R^p$, $b\in\mathbb R^n$, and $\ell:\mathbb R^p\to\mathbb R$ strictly convex and continuously differentiable;
--   2. $h_k(x_k)=\lambda_k\|x_k\|_1+\sum_J w_J\|x_{k,J}\|_2$, where the coordinates of $x_k$ are partitioned into groups $J$ and $\lambda_k\ge0$, $w_J\ge0$;
--   3. $X_k=\{x_k\mid C_kx_k\le c_k\}$ is a compact polyhedron, and $X=\prod_kX_k$;
--   4. the feasible set $X\cap\{x\mid Ex=q\}$ is nonempty, and the dual optimal value is attained.
--
--   Write $h(x)=\sum_kh_k(x_k)$. For a penalty $\rho>0$ the **augmented Lagrangian** (1.8) is
--   $$L(x;y)=f(x)+\langle y,q-Ex\rangle+\frac\rho2\|q-Ex\|^2,$$
--   the **augmented dual function** is $d(y)=\min_{x\in X}L(x;y)$ with optimal value $d^*=\max_y d(y)$, and $X(y)=\arg\min_{x\in X}L(x;y)$. The primal optimal value is $f^*=\min\{f(x)\mid x\in X,\ Ex=q\}$. The **dual and primal optimality gaps** (2.15)–(2.16) are $\Delta_d=d^*-d(y)$ and $\Delta_p=L(x;y)-d(y)$. A point $x$ is primal optimal if it solves (1.1); $y$ is dual optimal if it maximizes $d$.
--
--   **Assumption B.** For each block $k$ an approximation function $u_k(v_k;x)$ is given, differentiable in $v_k$, such that for all $x\in X$ and $v_k,\hat v_k\in X_k$, with $G(x)=g(x)+\frac\rho2\|Ex-q\|^2$:
--
--   1. (a) $u_k(x_k;x)=G(x)$;
--   2. (b) $u_k(v_k;x)\ge G(v_k,x_{-k})$;
--   3. (c) $\nabla u_k(x_k;x)=\nabla_kG(x)$;
--   4. (d) $(v_k,x)\mapsto u_k(v_k;x)$ is continuous on $X_k\times X$, and $u_k(v_k;x)\ge u_k(\hat v_k;x)+\langle\nabla u_k(\hat v_k;x),v_k-\hat v_k\rangle+\frac{\gamma_k}2\|v_k-\hat v_k\|^2$ with $\gamma_k>0$ independent of $x$;
--   5. (e) $\|\nabla u_k(v_k;x)-\nabla u_k(\hat v_k;x)\|\le L_k\|v_k-\hat v_k\|$ with $L_k>0$.
--
--   **Proximal gradient and error bound.** The proximal gradient (2.3) is $\tilde\nabla_xL(x;y)=x-\operatorname{prox}(x-\nabla_x(L(x;y)-h(x)))$, where $\operatorname{prox}(z)=\arg\min_{u\in X}h(u)+\frac12\|z-u\|^2$ is the proximity operator of $h$ plus the indicator of $X$. The **error bound** (2.4) in its global form asks for a $\tau>0$ such that
--   $$\operatorname{dist}(x,X(y))\le\tau\,\|\tilde\nabla_xL(x;y)\|\qquad\text{for all }x\in X\text{ and all }y.$$
--
--   **BSUM-M (1.12).** Given stepsizes $\alpha^r$, a run starts from $x^1\in X$ and any $y^1$, and for every $r\ge1$ sets
--   $$y^{r+1}=y^r+\alpha^r(q-Ex^r),\qquad x_k^{r+1}=\arg\min_{x_k\in X_k}\ u_k(x_k;w_k^{r+1})-\langle y^{r+1},E_kx_k\rangle+h_k(x_k),$$
--   where $w_k^{r+1}=(x_1^{r+1},\dots,x_{k-1}^{r+1},x_k^r,\dots,x_K^r)$ is the Gauss–Seidel point.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Blocks are `Fin K`; the block space is `PiLp 2` of `EuclideanSpace`s. $\ell$ is taken real valued and $C^1$ on all of $\mathbb R^p$ (the paper allows an extended-valued $\ell$, $C^1$ on the interior of its domain); then $\operatorname{dom}f=\mathbb R^n$ and A(a)'s condition $X\cap\operatorname{int}(\operatorname{dom}f)\cap\{Ex=q\}\neq\emptyset$ is plain feasibility. The page's (1.9) prints $g(x)$ and an unconstrained minimum; $d$ here is $\min_{x\in X}L(x;y)$, the function Lemma 2.1 and the proof (2.19) actually use. The page's (2.3) prints the prox of $h$ over $\mathbb R^n$; the prox here includes the constraint $X$, which the paper's own optimality relation (2.14) requires. $d$, $d^*$ and $f^*$ are real infima/suprema; under Assumption A the sets involved are nonempty and compact and the values are attained. The argmin steps of the run are minimality predicates (the minimizer is unique by B(d)). The run starts at index 1 as on the page; the values at index 0 are unconstrained. $x^1\in X$ is implicit in the paper (Assumption B is only imposed on $X$).
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, pp. 1, 3, 5–9, 12, (1.1), (1.8), (1.9), (1.12), Assumptions A–B, X(y), Definition 2.1, (2.3), (2.4), (2.15), (2.16)

import Mathlib

noncomputable section

namespace BSUMM.Det

open scoped InnerProductSpace

/-- The block variable space `ℜⁿ = ℜ^{n_1} × ⋯ × ℜ^{n_K}` of problem (1.1) of Hong, Chang, Wang,
Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 1, with the Euclidean norm `‖x‖² = ∑_k ‖x_k‖²`
(an `L²` product, not the sup-norm product). -/
abbrev Xsp (K : ℕ) (n : Fin K → ℕ) : Type :=
  PiLp 2 (fun k : Fin K => EuclideanSpace ℝ (Fin (n k)))

/-- The data of problem (1.1) under the form fixed by Assumption A (pp. 1, 6–7):
* `E k : ℜ^{n_k} → ℜ^m` and `q ∈ ℜ^m` (the coupling constraint `∑_k E_k x_k = q`);
* `A : ℜⁿ → ℜ^p`, `b ∈ ℜⁿ` and `ℓ : ℜ^p → ℝ` with `g(x) = ℓ(Ax) + ⟨x, b⟩` (A(b));
* `lam k = λ_k`, a partition of the coordinates of block `k` into the groups `Fin (ng k)`
  (`grp k i` is the group of coordinate `i`) and weights `w k J = w_J`, so that
  `h_k(x_k) = λ_k ‖x_k‖₁ + ∑_J w_J ‖x_{k,J}‖₂` (A(b));
* `C k`, `c k` with `X_k = {x_k | C_k x_k ≤ c_k}` (A(c));
* the penalty parameter `ρ` of the augmented Lagrangian (1.8).
The sign, convexity and compactness conditions are in `Data.AssumptionA`. -/
structure Data (K : ℕ) (n : Fin K → ℕ) (m p : ℕ) where
  E : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) →L[ℝ] EuclideanSpace ℝ (Fin m)
  q : EuclideanSpace ℝ (Fin m)
  A : Xsp K n →L[ℝ] EuclideanSpace ℝ (Fin p)
  b : Xsp K n
  ℓ : EuclideanSpace ℝ (Fin p) → ℝ
  lam : Fin K → ℝ
  ng : Fin K → ℕ
  grp : (k : Fin K) → Fin (n k) → Fin (ng k)
  w : (k : Fin K) → Fin (ng k) → ℝ
  mc : Fin K → ℕ
  C : (k : Fin K) → Fin (mc k) → Fin (n k) → ℝ
  c : (k : Fin K) → Fin (mc k) → ℝ
  ρ : ℝ

/-- The point `(v, x_{−k})`: `x` with block `k` replaced by `v`. -/
def upd {K : ℕ} {n : Fin K → ℕ} (x : Xsp K n) (k : Fin K) (v : EuclideanSpace ℝ (Fin (n k))) : Xsp K n :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp x) k v)

/-- The Gauss–Seidel point `w^{r+1}_k` of (1.12): block `j` is `xnew j = x^{r+1}_j` for `j < k`
and `xold j = x^r_j` for `j ≥ k`. -/
def sweep {K : ℕ} {n : Fin K → ℕ} (xnew xold : Xsp K n) (k : Fin K) : Xsp K n :=
  WithLp.toLp 2 (fun j => if j < k then xnew j else xold j)

namespace Data

variable {K : ℕ} {n : Fin K → ℕ} {m p : ℕ} (D : Data K n m p)

/-- `Ex = ∑_k E_k x_k`. -/
def Emul (x : Xsp K n) : EuclideanSpace ℝ (Fin m) := ∑ k, D.E k (x k)

/-- The smooth part `g(x) = ℓ(Ax) + ⟨x, b⟩` (Assumption A(b)). -/
def g (x : Xsp K n) : ℝ := D.ℓ (D.A x) + ⟪x, D.b⟫_ℝ

/-- The nonsmooth part of block `k`, `h_k(x_k) = λ_k ‖x_k‖₁ + ∑_J w_J ‖x_{k,J}‖₂` (Assumption A(b)). -/
def hk (k : Fin K) (v : EuclideanSpace ℝ (Fin (n k))) : ℝ :=
  D.lam k * ∑ i, |v i| +
    ∑ J, D.w k J * Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => D.grp k i = J), v i ^ 2)

/-- `h(x) = ∑_k h_k(x_k)`. -/
def hsum (x : Xsp K n) : ℝ := ∑ k, D.hk k (x k)

/-- The objective `f(x) = g(x) + h(x)` of (1.1). -/
def f (x : Xsp K n) : ℝ := D.g x + D.hsum x

/-- The polyhedral block feasible set `X_k = {x_k | C_k x_k ≤ c_k}` (Assumption A(c)). -/
def Xk (k : Fin K) : Set (EuclideanSpace ℝ (Fin (n k))) :=
  {v | ∀ j, ∑ i, D.C k j i * v i ≤ D.c k j}

/-- The feasible set `X = ∏_k X_k`. -/
def Xset : Set (Xsp K n) := {x | ∀ k, x k ∈ D.Xk k}

/-- The augmented Lagrangian (1.8), `L(x; y) = f(x) + ⟨y, q − Ex⟩ + ρ/2 ‖q − Ex‖²`. -/
def Lag (x : Xsp K n) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  D.f x + ⟪y, D.q - D.Emul x⟫_ℝ + D.ρ / 2 * ‖D.q - D.Emul x‖ ^ 2

/-- The augmented dual function `d(y) = min_{x ∈ X} L(x; y)` (the reading of (1.9) used by
Lemma 2.1 and (2.19)); a real infimum over the feasible subtype, which under Assumption A is
nonempty and compact, so the infimum is attained. -/
def d (y : EuclideanSpace ℝ (Fin m)) : ℝ := ⨅ x : D.Xset, D.Lag x y

/-- The dual optimal value `d* = max_y d(y)` (p. 12), attained under Assumption A(a). -/
def dstar : ℝ := ⨆ y, D.d y

/-- The primal optimal value `f* = min {f(x) | x ∈ X, Ex = q}` (p. 8); the feasible set is
nonempty and compact under Assumption A. -/
def fstar : ℝ := ⨅ x : {x : Xsp K n // x ∈ D.Xset ∧ D.Emul x = D.q}, D.f x

/-- `X(y) = argmin_{x ∈ X} L(x; y)` (p. 8). -/
def Xopt (y : EuclideanSpace ℝ (Fin m)) : Set (Xsp K n) :=
  {x | x ∈ D.Xset ∧ ∀ x' ∈ D.Xset, D.Lag x y ≤ D.Lag x' y}

/-- The dual optimality gap `Δ_d = d* − d(y)` of (2.15). -/
def dualGap (y : EuclideanSpace ℝ (Fin m)) : ℝ := D.dstar - D.d y

/-- The primal optimality gap `Δ_p = L(x; y) − d(y)` of (2.16). -/
def primalGap (x : Xsp K n) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  D.Lag x y - D.d y

/-- `x` is a primal optimal solution of (1.1). -/
def IsPrimalOpt (x : Xsp K n) : Prop :=
  x ∈ D.Xset ∧ D.Emul x = D.q ∧ ∀ x' ∈ D.Xset, D.Emul x' = D.q → D.f x ≤ D.f x'

/-- `y` is a dual optimal solution: it maximizes `d` (1.10). -/
def IsDualOpt (y : EuclideanSpace ℝ (Fin m)) : Prop := ∀ y', D.d y' ≤ D.d y

/-- Assumption A (pp. 6–7), standing, in the form used by this formalization: `K ≥ 1` blocks;
`ρ > 0` (p. 3); `ℓ` strictly convex and continuously differentiable (taken real-valued on all of
`ℜ^p`); `λ_k ≥ 0`, `w_J ≥ 0`; every `X_k` compact; `X ∩ {x | Ex = q}` nonempty (with `h` real
valued, `dom f = ℜⁿ`); and the dual optimal value is attained. -/
structure AssumptionA : Prop where
  K_pos : 0 < K
  ρ_pos : 0 < D.ρ
  ℓ_strictConvex : StrictConvexOn ℝ Set.univ D.ℓ
  ℓ_contDiff : ContDiff ℝ 1 D.ℓ
  lam_nonneg : ∀ k, 0 ≤ D.lam k
  w_nonneg : ∀ k J, 0 ≤ D.w k J
  Xk_compact : ∀ k, IsCompact (D.Xk k)
  feasible : ∃ x ∈ D.Xset, D.Emul x = D.q
  dual_attained : ∃ ystar, ∀ y, D.d y ≤ D.d ystar

/-- The function `g(x) + ρ/2 ‖Ex − q‖²` that each `u_k(·; x)` upper-bounds (Assumption B). -/
def Gsm (x : Xsp K n) : ℝ := D.g x + D.ρ / 2 * ‖D.Emul x - D.q‖ ^ 2

/-- Assumption B (p. 7) on the approximation functions `u k v x = u_k(v; x)`, with `∇u_k` the
gradient in `v`. Each `u_k` is real valued on `ℜ^{n_k} × ℜⁿ`; the conditions are imposed for
`x ∈ X`, `v, v̂ ∈ X_k`. -/
structure AssumptionB (u : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) → Xsp K n → ℝ) : Prop where
  /-- B(a): `u_k(x_k; x) = g(x) + ρ/2 ‖Ex − q‖²`. -/
  tight : ∀ x ∈ D.Xset, ∀ k, u k (x k) x = D.Gsm x
  /-- B(b): `u_k(v_k; x) ≥ g(v_k, x_{−k}) + ρ/2 ‖E_k v_k − q + E_{−k} x_{−k}‖²`. -/
  upper : ∀ k, ∀ x ∈ D.Xset, ∀ v ∈ D.Xk k, D.Gsm (upd x k v) ≤ u k v x
  /-- Differentiability of `u_k(·; x)` at the points of `X_k`, so that `∇u_k` in (c)–(e) is a
  genuine gradient. -/
  differentiable : ∀ k, ∀ x ∈ D.Xset, ∀ v ∈ D.Xk k, DifferentiableAt ℝ (fun v' => u k v' x) v
  /-- B(c): `∇u_k(x_k; x) = ∇_k (g(x) + ρ/2 ‖Ex − q‖²)`. -/
  grad_eq : ∀ k, ∀ x ∈ D.Xset, gradient (fun v => u k v x) (x k) = (gradient D.Gsm x) k
  /-- B(d), first sentence: `u_k(v_k; x)` is continuous in `v_k` and `x`. -/
  continuous : ∀ k, ContinuousOn (fun z : EuclideanSpace ℝ (Fin (n k)) × Xsp K n => u k z.1 z.2)
    (D.Xk k ×ˢ D.Xset)
  /-- B(d): strong convexity in `v_k` with a modulus `γ_k > 0` independent of `x`. -/
  strongConvex : ∃ γ : Fin K → ℝ, (∀ k, 0 < γ k) ∧ ∀ k, ∀ x ∈ D.Xset, ∀ v ∈ D.Xk k,
    ∀ v' ∈ D.Xk k,
      u k v' x + ⟪gradient (fun z => u k z x) v', v - v'⟫_ℝ + γ k / 2 * ‖v - v'‖ ^ 2 ≤ u k v x
  /-- B(e), (2.1): `∇u_k(·; x)` is `L_k`-Lipschitz on `X_k`, `L_k > 0`. -/
  lipschitz : ∃ L : Fin K → ℝ, (∀ k, 0 < L k) ∧ ∀ k, ∀ x ∈ D.Xset, ∀ v ∈ D.Xk k,
    ∀ v' ∈ D.Xk k,
      ‖gradient (fun z => u k z x) v - gradient (fun z => u k z x) v'‖ ≤ L k * ‖v - v'‖

/-- The gradient in `x` of the smooth part of the augmented Lagrangian,
`∇_x (L(x; y) − h(x))`, as in (2.3). -/
def gL (x : Xsp K n) (y : EuclideanSpace ℝ (Fin m)) : Xsp K n :=
  gradient (fun z => D.g z + ⟪y, D.q - D.Emul z⟫_ℝ + D.ρ / 2 * ‖D.q - D.Emul z‖ ^ 2) x

/-- `p` is the proximal point of `z` for `h + ι_X`:
`p = argmin_{u ∈ X} h(u) + ½ ‖z − u‖²`. The proximal gradient (2.3) at `(x, y)` is then
`x − p` for `p` the proximal point of `x − ∇_x (L(x; y) − h(x))`. -/
def IsProxPt (z q' : Xsp K n) : Prop :=
  q' ∈ D.Xset ∧ ∀ u ∈ D.Xset, D.hsum q' + ‖z - q'‖ ^ 2 / 2 ≤ D.hsum u + ‖z - u‖ ^ 2 / 2

/-- The error bound (2.4) in its global form on `X` (Lemma 2.2, part 2): there is `τ > 0`,
independent of `y` and `x`, with `dist(x, X(y)) ≤ τ ‖∇̃_x L(x; y)‖` for all `x ∈ X` and all `y`. -/
def ErrorBound : Prop :=
  ∃ τ > 0, ∀ (y : EuclideanSpace ℝ (Fin m)) (x pr : Xsp K n), x ∈ D.Xset →
    D.IsProxPt (x - D.gL x y) pr → Metric.infDist x (D.Xopt y) ≤ τ * ‖x - pr‖

/-- A run of BSUM-M (1.12) with stepsizes `α`, started at iteration `r = 1` from `x¹ ∈ X` and any
`y¹`: for every `r ≥ 1`,
`y^{r+1} = y^r + α^r (q − Ex^r)` and, for every block `k`,
`x^{r+1}_k ∈ argmin_{x_k ∈ X_k} u_k(x_k; w^{r+1}_k) − ⟨y^{r+1}, E_k x_k⟩ + h_k(x_k)`.
The values at index `0` are unconstrained. -/
def IsRun (u : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) → Xsp K n → ℝ) (α : ℕ → ℝ)
    (x : ℕ → Xsp K n) (y : ℕ → EuclideanSpace ℝ (Fin m)) : Prop :=
  x 1 ∈ D.Xset ∧
  (∀ r, 1 ≤ r → y (r + 1) = y r + α r • (D.q - D.Emul (x r))) ∧
  (∀ r, 1 ≤ r → ∀ k, x (r + 1) k ∈ D.Xk k ∧ ∀ v ∈ D.Xk k,
    u k (x (r + 1) k) (sweep (x (r + 1)) (x r) k) - ⟪y (r + 1), D.E k (x (r + 1) k)⟫_ℝ
        + D.hk k (x (r + 1) k) ≤
      u k v (sweep (x (r + 1)) (x r) k) - ⟪y (r + 1), D.E k v⟫_ℝ + D.hk k v)

end Data

end BSUMM.Det

end


