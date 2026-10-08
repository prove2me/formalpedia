-- Prove2me | Definitions.Def_PenaltyLag_Rate_Basic
-- name    : PenaltyLag_Rate_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:17.353825+00:00
-- url     : https://prove2.me/theorems/7264bcef-7ef6-4bd7-b2e0-a056cb738efc
-- title:
--   Problem (P) on ℝⁿ, the Lagrangians $L_0$ and $L_r$, their duals, Kuhn–Tucker vectors, Hessian forms, and the standing assumptions of §5
-- statement:
--   The objects of §5 of Rockafellar's dual approach to the convex program
--   $$
--   \text{(P)}\qquad \text{minimize } f_0(x) \text{ over } x \in X \text{ subject to } f_i(x) \le 0,\ i = 1, \dots, m,
--   $$
--   where, in §5, $X \subset \mathbb R^n$. Primal points live in $\mathbb R^n$ and multipliers $y = (y_1, \dots, y_m)$ in $\mathbb R^m$, both with the Euclidean norm $|\cdot|$ and inner product $u \cdot v$.
--
--   1. $\theta(t) = \max\{0, t\}$ (1.2), and the **penalty Lagrangian** (2.3), for a parameter $r > 0$:
--   $$
--   L_r(x, y) = f_0(x) + \frac{1}{4r} \sum_{i=1}^m \big[\theta(y_i + 2 r f_i(x))^2 - y_i^2\big].
--   $$
--   2. The ordinary Lagrangian is $L_0(x,y)=f_0(x)+\sum_i y_i f_i(x)$ when $y\geq0$, and $-\infty$ otherwise (3.2). Its dual objective is $g_0(y)=\inf_{x\in X}L_0(x,y)$. The penalty dual objective is $g_r(y) = \inf_{x \in X} L_r(x, y)$ of $(D_r)$, with values in $[-\infty, +\infty]$; $\sup g_r$ is its supremum over all $y \in \mathbb R^m$. A **maximizing sequence** for $(D_r)$ is a sequence $\{y^k\}$ with $g_r(y^k) \to \sup g_r$ (p. 364).
--   3. The infimum in (P), $\inf\{f_0(x) : x \in X,\ f_i(x) \le 0 \ \forall i\}$ ($+\infty$ if there is no feasible point); an **optimal solution** to (P) is a feasible point attaining it. A **Kuhn–Tucker vector** for (P) relative to $L_r$ or $L_0$ (3.17) is a $y$ for which the corresponding dual objective satisfies $-\infty < g(y) = \inf$ in (P).
--   4. The ordinary **Kuhn–Tucker conditions** for a pair $(\bar x, \bar y)$ (Corollary 3.4): $\bar y_i \ge 0$, $f_i(\bar x) \le 0$, $\bar y_i f_i(\bar x) = 0$ for every $i$, and $\bar x \in X$ minimizes $f_0 + \sum_i \bar y_i f_i$ over $X$.
--   5. The **active set** $I = \{i : f_i(\bar x) = 0\}$ and the seminorm $|y|_I = (\sum_{i \in I} y_i^2)^{1/2}$.
--   6. The Hessian quadratic form $z \cdot \nabla^2 \varphi(x) z$ of a real function $\varphi$, and, for (5.1), $z \cdot H(x, y) z$ with
--   $$
--   H(x, y) = \nabla^2 f_0(x) + \sum_{i \in I} y_i \nabla^2 f_i(x).
--   $$
--   7. The **standing assumptions of §5** (p. 368) on a pair $(\bar x, \bar y)$: $\bar x \in \operatorname{int} X$ is an optimal solution to (P); $f_0, f_1, \dots, f_m$ are twice continuously differentiable on a neighborhood of $\bar x$; $\bar y$ satisfies with $\bar x$ the Kuhn–Tucker conditions; and
--      (i) $\bar y_i \neq 0$ for $i \in I$;
--      (ii) the vectors $\nabla f_i(\bar x)$, $i \in I$, are linearly independent;
--      (iii) $z \cdot H(\bar x, \bar y) z > 0$ for every nonzero $z \in \mathbb R^n$ with $z \cdot \nabla f_i(\bar x) = 0$ for all $i \in I$.
--
--   These are the objects every statement of the mission is about: (i)–(iii) are the classical second-order sufficient conditions, under which the paper analyzes how fast the dual method of Theorem 4.1 converges.
--
--   **Formalization Note** $g_0$, $g_r$, $\sup g_r$ and the infimum in (P) are computed in `EReal` $= [-\infty, +\infty]$, so that $-\infty$ and $+\infty$ are never replaced by a junk value; `grR` is $g_r$ coerced to $\mathbb R$ and is used only where the statement also asserts that $g_r$ is finite. `Lr` is meaningful only for $r > 0$ (Lean's $1/0 = 0$); $L_0$ is a separate definition. The functions $f_i$ are total functions on $\mathbb R^n$; the paper's convexity assumption (p. 358) is a separate hypothesis `ConvexOn ℝ X` of every theorem, and smoothness is assumed only on a neighborhood of $\bar x$ (field `smooth`). Constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$) and $f_0$ is a separate argument. The Hessian form is $z \cdot D(\nabla\varphi)(x) z$, the derivative of the gradient; it is the genuine Hessian wherever $\varphi$ is $C^2$ near $x$, which holds at $\bar x$ by the `smooth` field. The assumption "$\bar x$ is an optimal solution" is kept as stated although it also follows from the Kuhn–Tucker conditions.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), pp. 354–368: (P), (1.2), (2.3), (3.2), (D_r), (D_0), (3.17), Corollary 3.4 (p. 362), maximizing sequence (p. 364), §5 standing assumptions (i)–(iii) and (5.1) (p. 368)

import Mathlib

namespace PenaltyLag.Rate

open Filter Topology

/-- The primal space ℝⁿ with the Euclidean norm |·| and inner product (§5: X ⊂ ℝⁿ). -/
abbrev Pt (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- ℝ^m with the Euclidean norm |·| and the inner product u·y (indices `Fin m`, 0-based). -/
abbrev Mult (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- θ(t) = max{0, t} (1.2). -/
def theta (t : ℝ) : ℝ := max 0 t

/-- The penalty Lagrangian L_r (2.3). Meaningful for r > 0; every statement assumes it. -/
noncomputable def Lr {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ) (x : Pt n)
    (y : Mult m) : ℝ :=
  f₀ x + (1 / (4 * r)) * ∑ i, (theta (y i + 2 * r * f i x) ^ 2 - y i ^ 2)

/-- The ordinary Lagrangian L₀ (3.2), equal to −∞ unless y is componentwise nonnegative. -/
noncomputable def L0 {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (x : Pt n) (y : Mult m) : EReal :=
  if ∀ i, 0 ≤ y i then ((f₀ x + ∑ i, y i * f i x : ℝ) : EReal) else ⊥

/-- g_r(y) = inf_{x ∈ X} L_r(x, y), the objective of (D_r), valued in [−∞, +∞]. -/
noncomputable def gr {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ)
    (y : Mult m) : EReal :=
  ⨅ x ∈ X, (Lr f₀ f r x y : EReal)

/-- g₀(y) = inf_{x ∈ X} L₀(x, y), the objective of the ordinary dual problem (D₀). -/
noncomputable def g0 {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (y : Mult m) : EReal :=
  ⨅ x ∈ X, L0 f₀ f x y

/-- g_r as a real function; used only where g_r is finite (it is 0 at ±∞). -/
noncomputable def grR {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ)
    (y : Mult m) : ℝ :=
  (gr X f₀ f r y).toReal

/-- inf in (P): the infimum of f₀ over the feasible set {x ∈ X | fᵢ(x) ≤ 0 ∀ i}
(+∞ if it is empty). -/
noncomputable def primalValue {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ)
    (f : Fin m → Pt n → ℝ) : EReal :=
  ⨅ x ∈ X, ⨅ (_ : ∀ i, f i x ≤ 0), (f₀ x : EReal)

/-- x is an optimal solution to (P): feasible, and f₀(x) ≤ f₀(x') for every feasible x'. -/
def IsPrimalOptimal {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (x : Pt n) : Prop :=
  x ∈ X ∧ (∀ i, f i x ≤ 0) ∧ ∀ x' ∈ X, (∀ i, f i x' ≤ 0) → f₀ x ≤ f₀ x'

/-- A Kuhn–Tucker vector for (P) relative to L_r (3.17): −∞ < inf_{x∈X} L_r(x, y) = inf in (P). -/
def IsKTVector {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ)
    (y : Mult m) : Prop :=
  ⊥ < gr X f₀ f r y ∧ gr X f₀ f r y = primalValue X f₀ f

/-- A Kuhn–Tucker vector for the ordinary Lagrangian L₀ (3.17 with r = 0). -/
def IsKTVector0 {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (y : Mult m) : Prop :=
  ⊥ < g0 X f₀ f y ∧ g0 X f₀ f y = primalValue X f₀ f

/-- The ordinary Kuhn–Tucker conditions for the pair (x, y) (Corollary 3.4 (i), (ii)):
yᵢ ≥ 0, fᵢ(x) ≤ 0, yᵢ fᵢ(x) = 0 for every i, and x ∈ X minimizes f₀ + Σᵢ yᵢ fᵢ over X. -/
def KTConditions {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (x : Pt n) (y : Mult m) : Prop :=
  (∀ i, 0 ≤ y i ∧ f i x ≤ 0 ∧ y i * f i x = 0) ∧
    x ∈ X ∧ ∀ x' ∈ X, f₀ x + ∑ i, y i * f i x ≤ f₀ x' + ∑ i, y i * f i x'

/-- A maximizing sequence for (D_r) (p. 364): g_r(yᵏ) → sup_y g_r(y) in [−∞, +∞]. -/
def IsMaximizing {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ)
    (y : ℕ → Mult m) : Prop :=
  Tendsto (fun k => gr X f₀ f r (y k)) atTop (𝓝 (⨆ y', gr X f₀ f r y'))

/-- The active index set I = {i | fᵢ(x̄) = 0} (p. 368). -/
noncomputable def activeSet {n m : ℕ} (f : Fin m → Pt n → ℝ) (x : Pt n) : Finset (Fin m) := by
  classical exact Finset.univ.filter (fun i => f i x = 0)

/-- |y|_I = (Σ_{i∈I} yᵢ²)^{1/2} (Corollary 5.2). -/
noncomputable def normOn {m : ℕ} (I : Finset (Fin m)) (y : Mult m) : ℝ :=
  Real.sqrt (∑ i ∈ I, y i ^ 2)

/-- The Hessian quadratic form z·∇²φ(x)z, computed as the derivative of the gradient. -/
noncomputable def hessForm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (φ : F → ℝ) (x z : F) : ℝ :=
  inner ℝ z (fderiv ℝ (gradient φ) x z)

/-- z·H(x, y)z with H(x, y) = ∇²f₀(x) + Σ_{i∈I} yᵢ ∇²fᵢ(x) (5.1). -/
noncomputable def Hform {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (I : Finset (Fin m))
    (x : Pt n) (y : Mult m) (z : Pt n) : ℝ :=
  hessForm f₀ x z + ∑ i ∈ I, y i * hessForm (f i) x z

/-- The standing assumptions of §5 (p. 368): x̄ ∈ int X is an optimal solution to (P); f₀, …, fₘ
are C² on a neighborhood of x̄; ȳ satisfies with x̄ the Kuhn–Tucker conditions; and
(i) ȳᵢ ≠ 0 for i ∈ I, (ii) the ∇fᵢ(x̄), i ∈ I, are linearly independent,
(iii) z·H(x̄, ȳ)z > 0 for every nonzero z with z·∇fᵢ(x̄) = 0 for all i ∈ I. -/
structure Sec5Assumptions {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (xbar : Pt n) (ybar : Mult m) : Prop where
  interior_mem : xbar ∈ interior X
  optimal : IsPrimalOptimal X f₀ f xbar
  smooth : ∃ U ∈ 𝓝 xbar, ContDiffOn ℝ 2 f₀ U ∧ ∀ i, ContDiffOn ℝ 2 (f i) U
  kuhnTucker : KTConditions X f₀ f xbar ybar
  strictComp : ∀ i ∈ activeSet f xbar, ybar i ≠ 0
  licq : LinearIndependent ℝ (fun i : activeSet f xbar => gradient (f i) xbar)
  secondOrder : ∀ z : Pt n, z ≠ 0 →
    (∀ i ∈ activeSet f xbar, inner ℝ z (gradient (f i) xbar) = 0) →
    0 < Hform f₀ f (activeSet f xbar) xbar ybar z

end PenaltyLag.Rate


