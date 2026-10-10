-- Prove2me | Definitions.Def_ProxADMMLC_Conv_Setting
-- name    : ProxADMMLC_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:55.08131+00:00
-- url     : https://prove2.me/theorems/bedcc4ac-1950-4208-9527-7507fd0d0a3f
-- title:
--   §§1–3, pp. 2272–2282 — box P and [·]₊ (2.1), KKT (2.2)–(2.3), X*, W, Definition 2.1, Assumption 2.2, (2.4), K (2.5), Algorithm 2.2, (2.6)–(2.9), φ, Y*(z), (3.7)–(3.9)
-- statement:
--   This file fixes the objects of Zhang and Luo's analysis of a proximal inexact augmented Lagrangian method (a one-block proximal ADMM) for the linearly constrained, possibly nonconvex problem
--   $$\min_{x\in\mathbb R^n}\ f(x)\quad\text{subject to}\quad Ax=b,\ x\in P,\qquad P=\{x\in\mathbb R^n:\ \ell_i\le x_i\le u_i,\ i=1,\dots,n\}, \tag{1.1–1.2}$$
--   with $f$ differentiable, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, and $\ell_i<u_i$.
--
--   1. **Box and projection.** $P$ is the box above and $\{x\in P: Ax=b\}$ the feasible set. The projection $[x]_+$ onto $P$ is given coordinatewise by (2.1): $([x]_+)_i=\ell_i$ if $x_i<\ell_i$, $x_i$ if $x_i\in[\ell_i,u_i]$, and $u_i$ if $x_i>u_i$. The vector $(v)_+$ is the projection onto the nonnegative orthant, $((v)_+)_i=\max\{v_i,0\}$.
--   2. **KKT points.** $(x,y,\mu,\nu)$ solves the KKT system (2.2)–(2.3) if
--   $$\nabla f(x)+A^\top y-\mu+\nu=0,\quad Ax=b,\quad \ell\le x\le u,\quad \mu,\nu\ge0,\quad \mu_i(\ell_i-x_i)=0,\quad \nu_i(x_i-u_i)=0\ \ \forall i.$$
--   $X^*$ is the set of all $x$ for which multipliers exist (the stationary points), and $W$ the set of primal-dual pairs $(x,y)$ for which $\mu,\nu$ exist.
--   3. **Strict complementarity (Definition 2.1).** For every solution $(x,y,\mu,\nu)$ of the KKT system and every $i$, exactly one of $\mu_i$ and $\ell_i-x_i$ is zero, and exactly one of $\nu_i$ and $x_i-u_i$ is zero.
--   4. **Assumption 2.2.** (a) $0$ lies in the relative interior of $AP-b=\{Ax-b: x\in P\}$; (b) strict complementarity holds; (c) $f$ is differentiable and $\|\nabla f(x)-\nabla f(x')\|\le L\|x-x'\|$ for some $L>0$ and all $x,x'\in P$. A constant $\gamma$ (possibly negative) satisfies (2.4): $\langle\nabla f(x)-\nabla f(x'),x-x'\rangle\ge\gamma\|x-x'\|^2$ for all $x,x'\in P$.
--   5. **The proximal augmented Lagrangian (2.5)**, with constants $\Gamma,p$:
--   $$K(x,z;y)=f(x)+y^\top(Ax-b)+\frac\Gamma2\|Ax-b\|^2+\frac p2\|x-z\|^2,$$
--   and its gradient in $x$, $\nabla_xK(x,z;y)=\nabla f(x)+A^\top y+\Gamma A^\top(Ax-b)+p(x-z)$.
--   6. **Algorithm 2.2.** A run with parameters $\Gamma,p,c,\alpha,\beta$ is a triple of sequences with $x^0,z^0\in P$, $y^0\in\mathbb R^m$ arbitrary, and for every $t\ge0$
--   $$y^{t+1}=y^t+\alpha(Ax^t-b),\qquad x^{t+1}=[x^t-c\nabla_xK(x^t,z^t;y^{t+1})]_+,\qquad z^{t+1}=z^t+\beta(x^{t+1}-z^t).$$
--   The one-step maps $y^+=y+\alpha(Ax-b)$, $x^+=[x-c\nabla_xK(x,z;y^+)]_+$, $z^+=z+\beta(x^+-z)$ are (3.7)–(3.9).
--   7. **Value functions (2.6)–(2.9).** $x(y,z)$ is a minimizer of $K(\cdot,z;y)$ over $P$ and $d(y,z)=K(x(y,z),z;y)$ its minimum value; $x^*(z)$ is a minimizer of $f(x)+\frac p2\|x-z\|^2$ over the feasible set and $M(z)$ its minimum value. The potential of §3.1.1 is
--   $$\phi(x,z;y)=K(x,z;y)-2d(y,z)+2M(z).$$
--   8. **Dual solution set.** $Y^*(z)$ is the set of multipliers $w$ of the equality constraint of problem (2.8) at $x^*(z)$: those $w$ for which some $\mu,\nu\ge0$ satisfy $\nabla f(x^*(z))+p(x^*(z)-z)+A^\top w-\mu+\nu=0$, $\mu_i(x^*_i(z)-\ell_i)=0$ and $\nu_i(x^*_i(z)-u_i)=0$ (the system (3.16)).
--
--   These objects are the language of Theorem 2.4 and of every lemma of its proof.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (abbreviated `E n`), $A$ is a continuous linear map `E n →L[ℝ] E m` and $A^\top$ is its adjoint; the paper's $\sigma$ (the largest singular value of $A$) is the operator norm `‖A‖`. Assumption 2.2 is split into `Assump22a`, `StrictCompl`, `Assump22c` so that lemmas needing only part of it can say so; the relative interior is Mathlib's `intrinsicInterior`, and "exactly one of … is zero" is `Xor`. "$f$ is differentiable" is global differentiability; the Lipschitz bound and (2.4) hold on $P$ only, as on the page. The argmins $x(y,z)$ and $x^*(z)$ are not defined by choice: statements take a function `xs` with `IsXSel` (it is a minimizer of $K(\cdot,z;y)$ over $P$ for every $(y,z)$) or `xst` with `IsXStarSel`; when $p>-\gamma$ these minimizers are unique. `dval`, `Mval`, `phi` are the values at those selections.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), pp. 2272–2282, (1.1), (1.2), (2.1)–(2.9), Definition 2.1, Assumption 2.2, (2.4), (2.5), Algorithm 2.2, φ^t (§3.1.1, p. 2279), Y*(z) and (3.16) (Lemma 3.10, p. 2282), (3.7)–(3.9) (p. 2281)

import Mathlib

namespace ProxADMMLC.Conv

/-- `ℝⁿ` with the Euclidean norm and inner product. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- (1.2), p. 2272: the box `P = {x ∈ ℝⁿ | ℓᵢ ≤ xᵢ ≤ uᵢ, i = 1, …, n}`. -/
def box {n : ℕ} (ℓ u : Fin n → ℝ) : Set (E n) :=
  {x | ∀ i, ℓ i ≤ x i ∧ x i ≤ u i}

/-- The feasible set of (1.1), p. 2272: `{x ∈ P | Ax = b}`. -/
def feas {n m : ℕ} (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ) : Set (E n) :=
  box ℓ u ∩ {x | A x = b}

/-- (2.1), p. 2274: the projection `[x]₊` onto the box `P`, coordinatewise
`([x]₊)ᵢ = ℓᵢ` if `xᵢ < ℓᵢ`, `xᵢ` if `xᵢ ∈ [ℓᵢ, uᵢ]`, `uᵢ` if `xᵢ > uᵢ`. -/
noncomputable def boxProj {n : ℕ} (ℓ u : Fin n → ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => if x i < ℓ i then ℓ i else if x i ≤ u i then x i else u i)

/-- §2.1, p. 2274: `(v)₊`, the projection onto the nonnegative orthant, coordinatewise
`max (vᵢ, 0)`. -/
noncomputable def posPart {k : ℕ} (v : E k) : E k :=
  WithLp.toLp 2 (fun i => max (v i) 0)

/-- The KKT system (2.2)–(2.3), p. 2274, of (1.1) at `x` with multipliers `y, μ, ν`:
`∇f(x) + Aᵀy − μ + ν = 0`, `Ax = b`, `ℓᵢ ≤ xᵢ ≤ uᵢ`, `μ ⪰ 0`, `ν ⪰ 0`,
`μᵢ(ℓᵢ − xᵢ) = 0`, `νᵢ(xᵢ − uᵢ) = 0`. -/
def IsKKT {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (x : E n) (y : E m) (μ ν : E n) : Prop :=
  gradient f x + (ContinuousLinearMap.adjoint A) y - μ + ν = 0 ∧ A x = b ∧
    (∀ i, ℓ i ≤ x i ∧ x i ≤ u i) ∧ (∀ i, 0 ≤ μ i) ∧ (∀ i, 0 ≤ ν i) ∧
    (∀ i, μ i * (ℓ i - x i) = 0) ∧ (∀ i, ν i * (x i - u i) = 0)

/-- `X*`, p. 2274: the stationary points of (1.1), i.e. all `x` satisfying the KKT condition
for some multipliers. -/
def Xstar {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ) :
    Set (E n) :=
  {x | ∃ y μ ν, IsKKT f A b ℓ u x y μ ν}

/-- `W`, p. 2274: the primal-dual solutions `(x, y)` of (1.1). -/
def Wset {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ) :
    Set (E n × E m) :=
  {q | ∃ μ ν, IsKKT f A b ℓ u q.1 q.2 μ ν}

/-- Definition 2.1, p. 2274 (strict complementarity): for **all** solutions `(x*, y*, μ*, ν*)`
of the KKT system and every `i`, exactly one of `μ*ᵢ` and `ℓᵢ − x*ᵢ` is zero and exactly one of
`ν*ᵢ` and `x*ᵢ − uᵢ` is zero. -/
def StrictCompl {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ) :
    Prop :=
  ∀ x y μ ν, IsKKT f A b ℓ u x y μ ν →
    ∀ i, Xor (μ i = 0) (ℓ i - x i = 0) ∧ Xor (ν i = 0) (x i - u i = 0)

/-- Assumption 2.2(a), p. 2275: the origin is in the relative interior of
`AP − b = {Ax − b | x ∈ P}`. -/
def Assump22a {n m : ℕ} (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ) : Prop :=
  (0 : E m) ∈ intrinsicInterior ℝ ((fun x => A x - b) '' box ℓ u)

/-- Assumption 2.2(c), p. 2275: `f` is differentiable and
`‖∇f(x) − ∇f(x')‖ ≤ L‖x − x'‖` for some `L > 0` and all `x, x' ∈ P`. -/
def Assump22c {n : ℕ} (f : E n → ℝ) (ℓ u : Fin n → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ f ∧ 0 < L ∧
    ∀ x ∈ box ℓ u, ∀ x' ∈ box ℓ u, ‖gradient f x - gradient f x'‖ ≤ L * ‖x - x'‖

/-- Assumption 2.2, p. 2275: (a), (b) strict complementarity (Definition 2.1), and (c) with the
Lipschitz constant `L`. -/
def Assumption22 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (L : ℝ) : Prop :=
  Assump22a A b ℓ u ∧ StrictCompl f A b ℓ u ∧ Assump22c f ℓ u L

/-- (2.4), p. 2275: `γ` (possibly negative) satisfies
`⟨∇f(x) − ∇f(x'), x − x'⟩ ≥ γ‖x − x'‖²` for all `x, x' ∈ P`. -/
def MonoConst {n : ℕ} (f : E n → ℝ) (ℓ u : Fin n → ℝ) (γ : ℝ) : Prop :=
  ∀ x ∈ box ℓ u, ∀ x' ∈ box ℓ u,
    γ * ‖x - x'‖ ^ 2 ≤ inner ℝ (gradient f x - gradient f x') (x - x')

/-- (2.5), p. 2276: `K(x, z; y) = f(x) + yᵀ(Ax − b) + (Γ/2)‖Ax − b‖² + (p/2)‖x − z‖²`. -/
noncomputable def K {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p : ℝ)
    (x z : E n) (y : E m) : ℝ :=
  f x + inner ℝ y (A x - b) + Γ / 2 * ‖A x - b‖ ^ 2 + p / 2 * ‖x - z‖ ^ 2

/-- `∇ₓK(x, z; y) = ∇f(x) + Aᵀy + ΓAᵀ(Ax − b) + p(x − z)`, the gradient of (2.5) in `x`. -/
noncomputable def gradK {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p : ℝ)
    (x z : E n) (y : E m) : E n :=
  gradient f x + (ContinuousLinearMap.adjoint A) y +
    Γ • (ContinuousLinearMap.adjoint A) (A x - b) + p • (x - z)

/-- Algorithm 2.2, p. 2276: `(x, y, z)` is a run with parameters `Γ, p, c, α, β`:
`x⁰ ∈ P`, `z⁰ ∈ P`, `y⁰ ∈ ℝᵐ` arbitrary, and for every `t`
`y^{t+1} = y^t + α(Ax^t − b)`, `x^{t+1} = [x^t − c∇ₓK(x^t, z^t; y^{t+1})]₊`,
`z^{t+1} = z^t + β(x^{t+1} − z^t)`. -/
def IsRun {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (Γ p c α β : ℝ) (x : ℕ → E n) (y : ℕ → E m) (z : ℕ → E n) : Prop :=
  x 0 ∈ box ℓ u ∧ z 0 ∈ box ℓ u ∧ ∀ t,
    y (t + 1) = y t + α • (A (x t) - b) ∧
    x (t + 1) = boxProj ℓ u (x t - c • gradK f A b Γ p (x t) (z t) (y (t + 1))) ∧
    z (t + 1) = z t + β • (x (t + 1) - z t)

/-- (2.7), p. 2277: `xs` is a selection of `x(y, z) = argmin_{x ∈ P} K(x, z; y)`. -/
def IsXSel {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (Γ p : ℝ) (xs : E m → E n → E n) : Prop :=
  ∀ y z, xs y z ∈ box ℓ u ∧ ∀ x ∈ box ℓ u, K f A b Γ p (xs y z) z y ≤ K f A b Γ p x z y

/-- (2.9), p. 2277: `xst` is a selection of
`x*(z) = argmin_{x ∈ P, Ax = b} (f(x) + (p/2)‖x − z‖²)`. -/
def IsXStarSel {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (p : ℝ) (xst : E n → E n) : Prop :=
  ∀ z, xst z ∈ feas A b ℓ u ∧
    ∀ x ∈ feas A b ℓ u, f (xst z) + p / 2 * ‖xst z - z‖ ^ 2 ≤ f x + p / 2 * ‖x - z‖ ^ 2

/-- (2.6), p. 2277: `d(y, z) = min_{x ∈ P} K(x, z; y)`, the value at the selection `xs`. -/
noncomputable def dval {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p : ℝ)
    (xs : E m → E n → E n) (y : E m) (z : E n) : ℝ :=
  K f A b Γ p (xs y z) z y

/-- (2.8), p. 2277: `M(z) = min_{x ∈ P, Ax = b} (f(x) + (p/2)‖x − z‖²)`, the value at the
selection `xst`. -/
noncomputable def Mval {n : ℕ} (f : E n → ℝ) (p : ℝ) (xst : E n → E n) (z : E n) : ℝ :=
  f (xst z) + p / 2 * ‖xst z - z‖ ^ 2

/-- The potential function, §3.1.1, p. 2279:
`φ(x, z; y) = K(x, z; y) − 2d(y, z) + 2M(z)`. -/
noncomputable def phi {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p : ℝ)
    (xs : E m → E n → E n) (xst : E n → E n) (x z : E n) (y : E m) : ℝ :=
  K f A b Γ p x z y - 2 * dval f A b Γ p xs y z + 2 * Mval f p xst z

/-- `Y*(z)`, Lemma 3.10, p. 2282: the dual multipliers `w` of the equality constraint of (2.8)
at `x*(z)`, i.e. those for which (3.16) holds with some `μ, ν ⪰ 0`. -/
def Ystar {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (ℓ u : Fin n → ℝ) (p : ℝ)
    (xst : E n → E n) (z : E n) : Set (E m) :=
  {w | ∃ μ ν : E n,
    gradient f (xst z) + p • (xst z - z) + (ContinuousLinearMap.adjoint A) w - μ + ν = 0 ∧
    (∀ i, 0 ≤ μ i ∧ 0 ≤ ν i) ∧ (∀ i, μ i * (xst z i - ℓ i) = 0) ∧
    (∀ i, ν i * (xst z i - u i) = 0)}

/-- (3.7), p. 2281: `y⁺ = y + α(Ax − b)`. -/
def yPlus {n m : ℕ} (A : E n →L[ℝ] E m) (b : E m) (α : ℝ) (x : E n) (y : E m) : E m :=
  y + α • (A x - b)

/-- (3.8), p. 2281: `x⁺ = [x − c∇ₓK(x, z; y⁺)]₊`. -/
noncomputable def xPlus {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m)
    (ℓ u : Fin n → ℝ) (Γ p c α : ℝ) (x z : E n) (y : E m) : E n :=
  boxProj ℓ u (x - c • gradK f A b Γ p x z (yPlus A b α x y))

/-- (3.9), p. 2281: `z⁺ = z + β(x⁺ − z)`. -/
noncomputable def zPlus {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m)
    (ℓ u : Fin n → ℝ) (Γ p c α β : ℝ) (x z : E n) (y : E m) : E n :=
  z + β • (xPlus f A b ℓ u Γ p c α x z y - z)

end ProxADMMLC.Conv


