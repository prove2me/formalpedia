-- Prove2me | Definitions.Def_ProxNewton_Exact_Basic
-- name    : ProxNewton_Exact_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:30:50.8315+00:00
-- url     : https://prove2.me/theorems/11d09199-b86e-43bb-9642-efffeee10996
-- title:
--   Composite problem (1.1), search direction (2.9), backtracking Algorithm 1 and the Dennis–Moré criterion (3.2)
-- statement:
--   This file fixes the objects of Lee, Sun & Saunders' analysis of proximal Newton-type methods for the composite problem
--   $$\min_{x\in\mathbb R^n} f(x) := g(x) + h(x), \qquad (1.1)$$
--   where $g$ is smooth and $h$ is a proper closed convex function that may take the value $+\infty$.
--
--   1. **Nonsmooth part.** $h$ is described by its effective domain $D=\operatorname{dom} h$ and its finite values on $D$. We require $D\neq\emptyset$ convex, $h$ convex on $D$, and the extended function ($h$ on $D$, $+\infty$ off $D$) lower semicontinuous. The objective $f$ is the extended-valued function equal to $g+h$ on $D$ and $+\infty$ elsewhere. A point $x^\star$ is *optimal* if $x^\star\in D$ and $f(x^\star)\le f(y)$ for all $y\in D$.
--   2. **Strong convexity (Definition 3.2).** $g$ is strongly convex with constant $m$ if $g(y)\ge g(x)+\nabla g(x)^T(y-x)+\tfrac m2\|x-y\|^2$ for all $x,y$. The Hessian $\nabla^2 g(x)$ is the derivative of the gradient map.
--   3. **Matrices.** A matrix $H$ is *positive definite* if it is symmetric and $v^THv>0$ for $v\neq0$; $H\succeq mI$ and $mI\preceq H\preceq MI$ are the usual Loewner bounds for symmetric $H$.
--   4. **Search direction (2.9).** Given $x$ and $H$, $\Delta x$ is a search direction if $x+\Delta x\in D$ and $\Delta x$ minimizes
--   $$d\mapsto \nabla g(x)^Td+\tfrac12 d^THd+h(x+d)$$
--   over all $d$ with $x+d\in D$. The predicted decrease (2.19) is $\lambda=\nabla g(x)^T\Delta x+h(x+\Delta x)-h(x)$.
--   5. **Sufficient descent and backtracking.** A step length $t$ satisfies the sufficient descent condition (2.19) if $f(x+t\Delta x)\le f(x)+\alpha t\lambda$. With a backtracking factor $\beta\in(0,1)$, the backtracking step is $t=\beta^{j}$ where $j\ge0$ is the least integer for which $\beta^j$ satisfies (2.19); in particular the unit step is tried first.
--   6. **Algorithm 1.** A run is a sequence $(x_k,H_k,\Delta x_k,t_k)_{k\ge0}$ with $x_0\in D$ and, for every $k$: $H_k$ positive definite, $\Delta x_k$ a search direction at $x_k$ with $H_k$, $t_k$ the backtracking step, and $x_{k+1}=x_k+t_k\Delta x_k$. The *proximal Newton method* is the case $H_k=\nabla^2 g(x_k)$; a *proximal quasi-Newton method* allows any $H_k$.
--   7. **Dennis–Moré criterion (3.2).** $\|(H_k-\nabla^2 g(x^\star))(x_{k+1}-x_k)\|/\|x_{k+1}-x_k\|\to0$, stated as: for every $\varepsilon>0$, eventually $\|(H_k-\nabla^2 g(x^\star))(x_{k+1}-x_k)\|\le\varepsilon\|x_{k+1}-x_k\|$.
--
--   These are the objects every statement of the mission refers to.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`; matrices are continuous linear operators. The constant $g(x_k)$ of the quadratic model $\hat g_k$ is dropped from the subproblem, which does not change its minimizers. The search direction is a predicate (uniqueness is a theorem, not part of the definition). The paper's backtracking line search is only cited ("[4]"); the least-$j$ rule with factor $\beta$ is the Boyd–Vandenberghe convention. Algorithm 1's stopping test is dropped: runs are infinite sequences indexed from $k=0$. The Dennis–Moré ratio is written without division; when $x_{k+1}=x_k$ the inequality holds trivially.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 1, Eq. (1.1); p. 3 (standing assumptions of §2); p. 5, Eq. (2.9); p. 7, Eq. (2.19); p. 8, Algorithm 1; p. 11, Definition 3.2; p. 12, Eq. (3.2)

import Mathlib

open scoped RealInnerProductSpace

namespace ProxNewton.Exact

/-! Objects of Lee, Sun & Saunders, *Proximal Newton-type methods for minimizing composite
functions*, arXiv:1206.1623v13: problem (1.1), §2.2 (search direction (2.9), λ (2.19),
Algorithm 1), Definition 3.2 and the Dennis–Moré criterion (3.2). The space is
`EuclideanSpace ℝ (Fin n)` (the paper's `ℝⁿ` with `⟨x, y⟩ = xᵀy`). -/

/-- The nonsmooth part `h` of (1.1) is a proper closed convex function that may take the value
`+∞`. It is encoded by its effective domain `D` and its (finite) values `h` on `D`: `D` is
nonempty and convex, `h` is convex on `D`, and the extended-valued function equal to `h` on `D`
and to `+∞` off `D` is lower semicontinuous (i.e. closed). Values of `h` off `D` are never read. -/
def IsProperClosedConvex {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  D.Nonempty ∧ Convex ℝ D ∧ ConvexOn ℝ D h ∧
    LowerSemicontinuous (fun x => by
      classical exact if x ∈ D then ((h x : ℝ) : EReal) else (⊤ : EReal))

/-- The composite objective `f = g + h` of problem (1.1), as an extended-valued function:
`f x = g x + h x` for `x ∈ D = dom f`, and `f x = +∞` otherwise. -/
noncomputable def compositeObj {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → EReal := fun x => by
  classical exact if x ∈ D then ((g x + h x : ℝ) : EReal) else (⊤ : EReal)

/-- `xstar` is an optimal solution of (1.1): it lies in `dom f = D` and
`f xstar ≤ f y` for every `y ∈ D`. -/
def IsMinimizer {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) : Prop :=
  xstar ∈ D ∧ ∀ y ∈ D, g xstar + h xstar ≤ g y + h y

/-- Definition 3.2, (3.1): `g` is strongly convex with constant `m`:
`g y ≥ g x + ∇g(x)ᵀ(y − x) + (m/2)‖x − y‖²` for all `x, y`. -/
def StronglyConvexWith {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin n),
    g x + ⟪gradient g x, y - x⟫ + m / 2 * ‖x - y‖ ^ 2 ≤ g y

/-- The Hessian `∇²g(x)`, as the derivative of the gradient map, a linear operator on `ℝⁿ`. -/
noncomputable def hessian {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (gradient g) x

/-- `H` is a symmetric positive definite matrix: `H` is self-adjoint and `vᵀHv > 0` for `v ≠ 0`. -/
def IsPosDef {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric ∧
    ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < ⟪H v, v⟫

/-- `H ⪰ mI` for a symmetric `H`: `H` is self-adjoint and `m‖v‖² ≤ vᵀHv` for all `v`. -/
def IsLowerBounded {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (m : ℝ) : Prop :=
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric ∧
    ∀ v : EuclideanSpace ℝ (Fin n), m * ‖v‖ ^ 2 ≤ ⟪H v, v⟫

/-- `mI ⪯ H ⪯ MI` for a symmetric `H`: `H` is self-adjoint and
`m‖v‖² ≤ vᵀHv ≤ M‖v‖²` for all `v`. -/
def IsBoundedBetween {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (m M : ℝ) : Prop :=
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric ∧
    ∀ v : EuclideanSpace ℝ (Fin n), m * ‖v‖ ^ 2 ≤ ⟪H v, v⟫ ∧ ⟪H v, v⟫ ≤ M * ‖v‖ ^ 2

/-- Search direction (2.9): `Δ` minimizes the subproblem
`d ↦ ∇g(x)ᵀd + ½ dᵀHd + h(x + d)` over `{d | x + d ∈ D}` (the constant `g x` of the model
`ĝ` is dropped), and `x + Δ ∈ D`. -/
def IsSearchDirection {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n)) : Prop :=
  x + Δ ∈ D ∧ ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ D →
    ⟪gradient g x, Δ⟫ + 1 / 2 * ⟪H Δ, Δ⟫ + h (x + Δ) ≤
      ⟪gradient g x, d⟫ + 1 / 2 * ⟪H d, d⟫ + h (x + d)

/-- The predicted decrease (2.19): `λ = ∇g(x)ᵀΔ + h(x + Δ) − h(x)`. -/
noncomputable def predDecrease {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (x Δ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪gradient g x, Δ⟫ + h (x + Δ) - h x

/-- The sufficient descent condition (2.19) for step length `t`:
`f(x + tΔ) ≤ f(x) + α t λ`, with `f` the extended-valued objective (so `x + tΔ ∈ D` is
part of the condition) and `f(x) = g x + h x` (used at points `x ∈ D`). -/
def SufficientDescent {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Prop :=
  compositeObj g D h (x + t • Δ) ≤ ((g x + h x + α * t * predDecrease g h x Δ : ℝ) : EReal)

/-- Backtracking line search with factor `β`: `t = β ^ j` where `j` is the least natural
number such that the step `β ^ j` satisfies the sufficient descent condition (2.19). The unit
step `β ^ 0 = 1` is tried first. -/
def IsBacktrackingStep {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α β : ℝ)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Prop :=
  ∃ j : ℕ, t = β ^ j ∧ SufficientDescent g D h α x Δ (β ^ j) ∧
    ∀ i : ℕ, i < j → ¬ SufficientDescent g D h α x Δ (β ^ i)

/-- A run of Algorithm 1 (generic proximal Newton-type method, p. 8) with sufficient-descent
parameter `α` and backtracking factor `β`: `x 0 ∈ D`, and for every `k`, `H k` is symmetric
positive definite, `Δ k` is the search direction (2.9) at `x k` with `H k`, `t k` is the
backtracking step, and `x (k+1) = x k + t k • Δ k`. The run is infinite (no stopping test). -/
def IsProxNewtonTypeRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) : Prop :=
  x 0 ∈ D ∧ ∀ k : ℕ, IsPosDef (H k) ∧ IsSearchDirection g D h (x k) (H k) (Δ k) ∧
    IsBacktrackingStep g D h α β (x k) (Δ k) (t k) ∧ x (k + 1) = x k + t k • Δ k

/-- A run of the proximal Newton method: a run of Algorithm 1 with `H k = ∇²g(x k)`. -/
def IsProxNewtonRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) : Prop :=
  IsProxNewtonTypeRun g D h α β x H Δ t ∧ ∀ k : ℕ, H k = hessian g (x k)

/-- The Dennis–Moré criterion (3.2), division-free:
`‖(H k − ∇²g(xstar))(x (k+1) − x k)‖ / ‖x (k+1) − x k‖ → 0`, written as: for every `ε > 0`,
eventually `‖(H k − ∇²g(xstar))(x (k+1) − x k)‖ ≤ ε ‖x (k+1) − x k‖`. -/
def DennisMore {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop,
    ‖(H k - hessian g xstar) (x (k + 1) - x k)‖ ≤ ε * ‖x (k + 1) - x k‖

end ProxNewton.Exact


