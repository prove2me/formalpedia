-- Prove2me | Definitions.Def_TrustIPM_barrier
-- name    : TrustIPM_barrier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:48.463141+00:00
-- url     : https://prove2.me/theorems/07ad94e8-cf81-4270-a6a5-37ab1b673cee
-- title:
--   Problem data — log barrier $\psi_\mu$, model $\mathcal M^{\psi_\mu}_x$, Lagrangian and Assumptions 1–3
-- statement:
--   The paper studies $\min_{x\in\mathbb R^n} f(x)$ subject to $a(x)\ge0$, with $f:\mathbb R^n\to\mathbb R$ and $a:\mathbb R^n\to\mathbb R^m$ thrice differentiable and $n,m$ positive integers. This module fixes the objects built from these data.
--
--   1. The **strictly feasible set** $\mathcal X:=\{x\in\mathbb R^n: a(x)>0\}$.
--   2. The **log barrier** $\psi_\mu(x):=f(x)-\mu\sum_{i=1}^m\log a_i(x)$, $\mu>0$, its gradient $\nabla\psi_\mu$ and Hessian $\nabla^2\psi_\mu$, and the **model** $\mathcal M^{\psi_\mu}_x(u):=\tfrac12u^T\nabla^2\psi_\mu(x)u+\nabla\psi_\mu(x)^Tu$.
--   3. The **Lagrangian** $\mathcal L(x,y):=f(x)-y^Ta(x)$ with $\nabla_x\mathcal L$ and $\nabla^2_{xx}\mathcal L$; the Jacobian products $\nabla a(x)d$ and $\nabla a(x)^Tw$; the dual estimate $y=\mu S^{-1}\mathbf 1$ with $S=\mathrm{diag}(a(x))$; and the vector $S^{-1}\nabla a(x)d$.
--   4. The norms $\|y\|_1$, $\|y\|_2$, $\|y\|_\infty$ on $\mathbb R^m$.
--   5. **Assumption 1**: $f$ and every $a_i$ are thrice differentiable on $\mathbb R^n$, $L_1,L_2\in(0,\infty)$, and on $\mathcal X$ the functions $f$ and $a_i$ have $L_1$-Lipschitz first and $L_2$-Lipschitz second derivatives (Definition 1).
--   6. **Assumption 2**: $\psi^*_\mu:=\inf_{x\in\mathcal X}\psi_\mu(x)>-\infty$ for the given $\mu\in(0,\infty)$, and $x^{(0)}\in\mathcal X$.
--   7. **Assumption 3**: $\tau_c=(\tau_l^2\mu/L_1)^{1/2}\in(0,1]$ and $L_2^2\mu/L_1^3\in(0,1]$.
--
--   These are the standing hypotheses of every lemma and of Theorem 1.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; vectors of $\mathbb R^m$ are functions `Fin m → ℝ` and the three norms are written out (Lean's default norm there is the sup norm). Gradients are Mathlib's `gradient`, Hessians the derivative of the gradient, so $\|\nabla^2f(x)\|$ is the operator (spectral) norm. $\nabla\psi_\mu$, $\nabla^2\psi_\mu$ are those of the function $\psi_\mu$ itself, which equal the classical formulas on the open set $\mathcal X$. "Thrice differentiable" is three nested Fréchet derivatives, without continuity of the third. $\psi^*_\mu$ is `sInf` of the image, and "$>-\infty$" is `BddBelow`.
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, §1, p.1; (3), p.2; p.3 (model, notation, Definition 1, Assumptions 1–2); Assumption 3, p.15

import Mathlib
import Definitions.Def_TrustIPM_HasLipDerivOn
import Definitions.Def_TrustIPM_trsModel
open scoped InnerProductSpace RealInnerProductSpace

namespace TrustIPM

/-- `ℝⁿ` with the Euclidean norm `‖·‖₂` (Hinder & Ye, *Worst-case iteration bounds for log barrier
methods on problems with nonconvex constraints*, arXiv:1807.00404v5, §1, p.1 and §1.1, p.3). -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The `ℓ₁` norm `‖y‖₁ = Σᵢ |yᵢ|` of a vector of `ℝᵐ` (Hinder & Ye, arXiv:1807.00404v5, used in
Algorithm 1 line 16, p.5, and in (SIP1.c), (SIP2), p.7).

**Formalization Note** Vectors of `ℝᵐ` (constraint values, dual variables) are `Fin m → ℝ`. Lean's
built-in norm on `Fin m → ℝ` is the sup norm, so the three norms the paper uses on `ℝᵐ` are written
out: `norm1`, `norm2`, `normInf`. -/
def norm1 {m : ℕ} (y : Fin m → ℝ) : ℝ := ∑ i, |y i|

/-- The Euclidean norm `‖y‖₂ = (Σᵢ yᵢ²)^{1/2}` of a vector of `ℝᵐ` (Hinder & Ye,
arXiv:1807.00404v5, §1.1, p.3; used in (8), p.9, (12)–(13), p.11, (15), p.12). -/
noncomputable def norm2 {m : ℕ} (y : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, y i ^ 2)

/-- The sup norm `‖y‖∞ = maxᵢ |yᵢ|` of a vector of `ℝᵐ` (Hinder & Ye, arXiv:1807.00404v5, Lemma 6,
p.11).

**Formalization Note** Written as `⨆ i, |y i|`; for `m ≥ 1` (the paper's standing assumption, p.1)
this is the maximum. -/
noncomputable def normInf {m : ℕ} (y : Fin m → ℝ) : ℝ := ⨆ i, |y i|

/-- The **strictly feasible set** `X := {x ∈ ℝⁿ : a(x) > 0}` (Hinder & Ye, arXiv:1807.00404v5, p.2,
below (3)).

**Formalization Note** The constraint map `a : ℝⁿ → ℝᵐ` is given by its components
`a : Fin m → ℝⁿ → ℝ`, so `a i x` is `aᵢ(x)`. -/
def feasibleSet {n m : ℕ} (a : Fin m → E n → ℝ) : Set (E n) := {x | ∀ i, 0 < a i x}

/-- The **log barrier** `ψµ(x) := f(x) − µ Σᵢ₌₁ᵐ log(aᵢ(x))` (Hinder & Ye, arXiv:1807.00404v5, (3),
p.2).

**Formalization Note** `log` is `Real.log`, which is `log |t|` for `t ≠ 0` and `0` at `0`; the paper
only evaluates `ψµ` on `X`, and every statement of this mission evaluates it on `X` only (or concludes
membership in `X` first). -/
noncomputable def barrier {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ : ℝ) (x : E n) : ℝ :=
  f x - μ * ∑ i, Real.log (a i x)

/-- The **Hessian** `∇²w(x)` of `w : ℝⁿ → ℝ`, as the derivative of the gradient (Hinder & Ye,
arXiv:1807.00404v5, §1.1, p.3).

**Formalization Note** The gradient `∇w` is Mathlib's `gradient` (the Riesz representative of
`fderiv`), and `∇²w(x)` is `fderiv ℝ (gradient w) x : ℝⁿ →L[ℝ] ℝⁿ`; its operator norm is the
spectral norm `‖·‖₂` of the paper. -/
noncomputable def hess {n : ℕ} (w : E n → ℝ) (x : E n) : E n →L[ℝ] E n :=
  fderiv ℝ (gradient w) x

/-- The **trust-region model of the log barrier** `M^{ψµ}_x(u) := ½ uᵀ∇²ψµ(x)u + ∇ψµ(x)ᵀu`
(Hinder & Ye, arXiv:1807.00404v5, p.3).

**Formalization Note** `∇ψµ` and `∇²ψµ` are the gradient and Hessian of the function `barrier f a µ`
itself. Since `X` is open (the `aᵢ` are continuous) these are the paper's derivatives at every
`x ∈ X`, where they equal `∇f(x) − µ Σ ∇aᵢ(x)/aᵢ(x)` and
`∇²f(x) − µ Σ ∇²aᵢ(x)/aᵢ(x) + µ Σ ∇aᵢ(x)∇aᵢ(x)ᵀ/aᵢ(x)²` when `f`, `a` are twice differentiable. -/
noncomputable def model {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ : ℝ) (x u : E n) : ℝ :=
  trsModel (hess (barrier f a μ) x) (gradient (barrier f a μ) x) u

/-- The **Lagrangian** `L(x, y) := f(x) − yᵀa(x)` (Hinder & Ye, arXiv:1807.00404v5, §1.1, p.3). -/
def lagrangian {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (x : E n) (y : Fin m → ℝ) : ℝ :=
  f x - ∑ i, y i * a i x

/-- The gradient `∇ₓL(x, y)` of the Lagrangian in `x` (Hinder & Ye, arXiv:1807.00404v5, (SIP1.c),
p.7). -/
noncomputable def gradLag {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (x : E n)
    (y : Fin m → ℝ) : E n :=
  gradient (fun z => lagrangian f a z y) x

/-- The Hessian `∇²ₓₓL(x, y)` of the Lagrangian in `x` (Hinder & Ye, arXiv:1807.00404v5, (SIP2),
p.7). -/
noncomputable def hessLag {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (x : E n)
    (y : Fin m → ℝ) : E n →L[ℝ] E n :=
  hess (fun z => lagrangian f a z y) x

/-- The Jacobian-vector product `∇a(x)d ∈ ℝᵐ`, whose `i`th entry is `∇aᵢ(x)ᵀd` (Hinder & Ye,
arXiv:1807.00404v5, p.3: "the matrix ∇a(x) is the m × n Jacobian of a(x) where the ith row consists of
∇aᵢ(x)"). -/
noncomputable def jac {n m : ℕ} (a : Fin m → E n → ℝ) (x d : E n) : Fin m → ℝ :=
  fun i => fderiv ℝ (a i) x d

/-- The transposed Jacobian-vector product `∇a(x)ᵀw = Σᵢ wᵢ ∇aᵢ(x) ∈ ℝⁿ`, i.e. `wᵀ∇ₓa(x)` (Hinder &
Ye, arXiv:1807.00404v5, Lemma 7, (15), p.12). -/
noncomputable def jacT {n m : ℕ} (a : Fin m → E n → ℝ) (x : E n) (w : Fin m → ℝ) : E n :=
  ∑ i, w i • gradient (a i) x

/-- The dual estimate `y = µS⁻¹1`, `S = diag(a(x))`, i.e. `yᵢ = µ/aᵢ(x)` (Hinder & Ye,
arXiv:1807.00404v5, Algorithm 1, lines 14–15, p.5). -/
noncomputable def centralDual {n m : ℕ} (a : Fin m → E n → ℝ) (μ : ℝ) (x : E n) : Fin m → ℝ :=
  fun i => μ / a i x

/-- The vector `S⁻¹d_s` with `S = diag(a(x))` and `d_s = ∇a(x)d`, i.e. `(∇aᵢ(x)ᵀd / aᵢ(x))ᵢ` (Hinder &
Ye, arXiv:1807.00404v5, Algorithm 1, lines 18 and 20, p.5; (8), p.9; (21), p.14). -/
noncomputable def scaledSlackDir {n m : ℕ} (a : Fin m → E n → ℝ) (x d : E n) : Fin m → ℝ :=
  fun i => jac a x d i / a i x

/-- `w` is **thrice differentiable on `ℝⁿ`** (Hinder & Ye, arXiv:1807.00404v5, §1, p.1, and
Assumption 1, p.3).

**Formalization Note** Three nested Fréchet derivatives exist everywhere. Continuity of the third
derivative (`ContDiff ℝ 3`) is **not** required, since the paper does not require it. -/
def ThriceDifferentiable {n : ℕ} (w : E n → ℝ) : Prop :=
  Differentiable ℝ w ∧ Differentiable ℝ (fderiv ℝ w) ∧ Differentiable ℝ (fderiv ℝ (fderiv ℝ w))

/-- **Assumption 1 (Lipschitz derivatives)** (Hinder & Ye, arXiv:1807.00404v5, Assumption 1, p.3):
`f` and each `aᵢ` are thrice differentiable on `ℝⁿ`, `L₁, L₂ ∈ (0, ∞)`, and on `X` the functions `f`
and each `aᵢ` have `L₁`-Lipschitz first derivatives and `L₂`-Lipschitz second derivatives, in the
directional sense of Definition 1. -/
def Assumption1 {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (L₁ L₂ : ℝ) : Prop :=
  0 < L₁ ∧ 0 < L₂ ∧ ThriceDifferentiable f ∧ (∀ i, ThriceDifferentiable (a i)) ∧
    HasLipDerivOnDir 1 L₁ f (feasibleSet a) ∧ HasLipDerivOnDir 2 L₂ f (feasibleSet a) ∧
    ∀ i, HasLipDerivOnDir 1 L₁ (a i) (feasibleSet a) ∧ HasLipDerivOnDir 2 L₂ (a i) (feasibleSet a)

/-- The infimum `ψ*µ := inf_{x ∈ X} ψµ(x)` of the log barrier (Hinder & Ye, arXiv:1807.00404v5,
Assumption 2, p.3).

**Formalization Note** `sInf` of the image; it is the paper's infimum when `X` is nonempty and the
image is bounded below, which is what `Assumption2` asserts. -/
noncomputable def barrierInf {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ : ℝ) : ℝ :=
  sInf (barrier f a μ '' feasibleSet a)

/-- **Assumption 2** (Hinder & Ye, arXiv:1807.00404v5, Assumption 2, p.3): for the given
`µ ∈ (0, ∞)` the barrier is bounded below on `X` (`ψ*µ > −∞`), and the starting point is strictly
feasible, `x⁽⁰⁾ ∈ X`.

**Formalization Note** "`ψ*µ > −∞`" is `BddBelow (ψµ '' X)`. -/
def Assumption2 {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ : ℝ) (x₀ : E n) : Prop :=
  0 < μ ∧ BddBelow (barrier f a μ '' feasibleSet a) ∧ x₀ ∈ feasibleSet a

/-- The complementarity tolerance fixed by Assumption 3, `τ_c = (τ_l²µ/L₁)^{1/2}` (Hinder & Ye,
arXiv:1807.00404v5, Assumption 3, p.15). -/
noncomputable def tauC (L₁ μ τl : ℝ) : ℝ := Real.sqrt (τl ^ 2 * μ / L₁)

/-- **Assumption 3 (Sufficiently small µ)** (Hinder & Ye, arXiv:1807.00404v5, Assumption 3, p.15):
`τ_c = (τ_l²µ/L₁)^{1/2} ∈ (0, 1]` and `L₂²µ/L₁³ ∈ (0, 1]`. -/
def Assumption3 (L₁ L₂ μ τl : ℝ) : Prop :=
  0 < tauC L₁ μ τl ∧ tauC L₁ μ τl ≤ 1 ∧ 0 < L₂ ^ 2 * μ / L₁ ^ 3 ∧ L₂ ^ 2 * μ / L₁ ^ 3 ≤ 1

end TrustIPM


