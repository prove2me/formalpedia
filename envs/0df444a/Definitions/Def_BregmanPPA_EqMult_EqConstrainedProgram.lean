-- Prove2me | Definitions.Def_BregmanPPA_EqMult_EqConstrainedProgram
-- name    : BregmanPPA_EqMult_EqConstrainedProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:59.570618+00:00
-- url     : https://prove2.me/theorems/9298659f-bdc0-46db-96fd-c681a0fff68c
-- title:
--   Problem (7), its dual functional $d$, optimal multipliers, and recursion (9) of the nonquadratic method of multipliers
-- statement:
--   Let $f : \mathbb R^n \to (-\infty, +\infty]$, let $A$ be an $m\times n$ matrix (a linear map $\mathbb R^n \to \mathbb R^m$), $b \in \mathbb R^m$, and $X \subseteq \mathbb R^n$. This file sets up §4.1 of Eckstein (1993).
--
--   1. **Indicator and $f_X$** (§3, p. 210). $\delta_X(x) = 0$ for $x \in X$ and $+\infty$ otherwise; $f_X = f + \delta_X$.
--
--   2. **Problem (7) and its standing assumptions** (p. 212):
--   $$\text{minimize } f(x) \quad\text{such that}\quad Ax = b,\ x \in X,$$
--   where $X$ is closed and convex, $f$ is convex and lower semicontinuous with values in $(-\infty,+\infty]$, and $\inf\{f(x) \mid x \in X\} < \infty$. A point $x$ *solves (7)* if $x \in X$, $Ax = b$ and $f(x) \le f(y)$ for every $y \in X$ with $Ay = b$.
--
--   3. **Dual functional** (p. 212):
--   $$d(p) = \inf_{x\in X}\bigl\{ f(x) + \langle p, Ax - b\rangle\bigr\},\qquad p \in \mathbb R^m,$$
--   with values in $[-\infty, +\infty]$, and $-d$ its negative. An *optimal multiplier* (Lagrange multiplier) is a maximizer of $d$ over $\mathbb R^m$, i.e. a solution of the dual problem (8).
--
--   4. **Recursion (9)** (p. 212). With $h^*(z) = \sup_{p}\{\langle p, z\rangle - h(p)\}$ the convex conjugate of $h : \mathbb R^m \to \mathbb R$ and $c_k$ real scalars, a sequence $\{(x^k,p^k)\}$ conforms to (9) when for every $k$
--   $$x^{k+1} \in \operatorname*{arg\,min}_{x\in X}\Bigl\{ f(x) + \frac{1}{c_k}\, h^*\bigl(\nabla h(p^k) + c_k(Ax - b)\bigr)\Bigr\},\qquad p^{k+1} = \nabla h^*\bigl(\nabla h(p^k) + c_k(Ax^{k+1} - b)\bigr).$$
--
--   5. **Polyhedral sets and functions** (used in the existence clause of Theorem 6): a set is polyhedral if it is the intersection of finitely many closed half-spaces; a function $f : \mathbb R^n \to [-\infty,+\infty]$ is polyhedral if its epigraph $\{(x,\mu) \in \mathbb R^n\times\mathbb R \mid f(x) \le \mu\}$ is a polyhedral set.
--
--   These are the data of the nonquadratic method of multipliers: (9) is the classical method of multipliers when $h(p) = \tfrac12\|p\|^2$, and other Bregman functions $h$ give nonquadratic penalties.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $A$ a continuous linear map `EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)`; every $m\times n$ matrix is such a map and conversely, and $A^{\mathsf T}$ is its adjoint. Functions into $(-\infty,+\infty]$ are `EReal`-valued, with "never $-\infty$" a separate hypothesis; $f_X$ is the extended-real sum. The arg min in (9) is a minimality predicate, not a choice function, since the minimizer need not be unique (remark on p. 214). The conjugate $h^*$ is the published `fenchelConjugate` (an `EReal` supremum over all of $\mathbb R^m$); (9) uses its real value, which is faithful in every theorem of this mission because they assume $\operatorname{im}\nabla h = \mathbb R^m$, under which $h^*$ is finite everywhere ($z = \nabla h(q)$ gives $h^*(z) = \langle q, z\rangle - h(q)$).
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 210 (δ_X, f_X); p. 212, problems (7), (7′), the dual functional d and the dual problem (8); p. 212, recursion (9); p. 213 (polyhedral, in Theorem 6)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_fenchelConjugate
import Definitions.Def_BregmanPPA_Convergence_Model

open InertialFB.IFB ConvexOptimization

namespace BregmanPPA.EqMult

variable {n m : ℕ}

/-- The convex indicator function `δ_X` of `X` (§3, p. 210): `0` on `X`, `+∞` off `X`. -/
noncomputable def indicatorE {H : Type*} (X : Set H) (x : H) : EReal :=
  open Classical in if x ∈ X then 0 else ⊤

/-- `f_X = f + δ_X` (§3, p. 210), the extended-real sum. -/
noncomputable def fX {H : Type*} (X : Set H) (f : H → EReal) : H → EReal :=
  fun x => f x + indicatorE X x

/-- The standing assumptions on problem (7) (p. 212): `X ⊆ ℝⁿ` is closed and convex,
`f : ℝⁿ → (−∞, +∞]` is convex and lower semicontinuous, and `inf {f x | x ∈ X} < ∞`. -/
structure IsEqProgram (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop where
  closed : IsClosed X
  convex : Convex ℝ X
  ne_bot : ∀ x, f x ≠ ⊥
  convexFn : IsConvexFn f
  lsc : LowerSemicontinuous f
  finite_on_X : ∃ x ∈ X, f x ≠ ⊤

/-- The dual functional of (7) (p. 212): `d(p) = inf_{x ∈ X} {f(x) + ⟪p, Ax − b⟫}`. -/
noncomputable def dualEq (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (p : EuclideanSpace ℝ (Fin m)) : EReal :=
  ⨅ x ∈ X, f x + ((inner ℝ p (A x - b) : ℝ) : EReal)

/-- `−d`, the closed proper convex function whose subdifferential `∂(−d)` the method is a
Bregman proximal point algorithm for. -/
noncomputable def negDual (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (p : EuclideanSpace ℝ (Fin m)) : EReal :=
  -(dualEq A b X f p)

/-- An optimal (Lagrange) multiplier of (7): a solution of the dual problem (8),
`maximize d(p)` over `p ∈ ℝᵐ`. -/
def IsOptimalMultiplier (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (p : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ q, dualEq A b X f q ≤ dualEq A b X f p

/-- `x` solves (7): `x ∈ X`, `Ax = b`, and `f x ≤ f y` for every feasible `y`. -/
def IsSolution7 (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ X ∧ A x = b ∧ ∀ y ∈ X, A y = b → f x ≤ f y

/-- A sequence `{(x^k, p^k)}` conforming to recursion (9) (p. 212): for every `k`,
`x^{k+1} ∈ argmin_{x ∈ X} { f(x) + (1/c_k) h*(∇h(p^k) + c_k(Ax − b)) }` and
`p^{k+1} = ∇h*(∇h(p^k) + c_k(Ax^{k+1} − b))`, where `h*` is the convex conjugate of `h`.
The real value of `h*` is used (`toReal`); the theorems using this predicate assume
`im ∇h = ℝᵐ`, under which `h*` is finite everywhere. -/
def IsEqMultRun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (h : EuclideanSpace ℝ (Fin m) → ℝ) (c : ℕ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ k, x (k + 1) ∈ X ∧
    (∀ y ∈ X, f (x (k + 1)) +
        (((c k)⁻¹ * (fenchelConjugate h (gradient h (p k) + c k • (A (x (k + 1)) - b))).toReal
          : ℝ) : EReal) ≤
      f y + (((c k)⁻¹ * (fenchelConjugate h (gradient h (p k) + c k • (A y - b))).toReal
          : ℝ) : EReal)) ∧
    p (k + 1) = gradient (fun z => (fenchelConjugate h z).toReal)
      (gradient h (p k) + c k • (A (x (k + 1)) - b))

/-- A polyhedral convex set: the intersection of finitely many closed half-spaces
`{x | ⟪a_i, x⟫ ≤ β_i}` (no half-space at all gives the whole space). -/
def IsPolyhedralSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (X : Set H) :
    Prop :=
  ∃ (k : ℕ) (a : Fin k → H) (β : Fin k → ℝ), X = {x | ∀ i, inner ℝ (a i) x ≤ β i}

/-- A polyhedral convex function `f : H → [−∞, +∞]`: its epigraph
`{(x, μ) ∈ H × ℝ | f x ≤ μ}` is a polyhedral convex set, i.e. the intersection of finitely many
closed half-spaces `{(x, μ) | ⟪a_i, x⟫ + α_i μ ≤ β_i}` of `H × ℝ`. -/
def IsPolyhedralFn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → EReal) :
    Prop :=
  ∃ (k : ℕ) (a : Fin k → H) (α β : Fin k → ℝ),
    {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} = {q | ∀ i, inner ℝ (a i) q.1 + α i * q.2 ≤ β i}

end BregmanPPA.EqMult


