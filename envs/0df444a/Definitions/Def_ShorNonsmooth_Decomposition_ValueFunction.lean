-- Prove2me | Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction
-- name    : ShorNonsmooth_Decomposition_ValueFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:20:35.834731+00:00
-- url     : https://prove2.me/theorems/1b8a5bcb-ae00-4fd2-b97a-7c15af723e00
-- title:
--   Decomposition with respect to variables: the value function $\Phi$, Slater's condition, Kuhn–Tucker multipliers and partial subgradients
-- statement:
--   Let $E^x_l$ and $E^y_m$ be Euclidean spaces with inner product $(\cdot,\cdot)$, and consider the convex program with two blocks of variables
--   $$
--   \min_{x,y} f_0(x,y) \quad \text{subject to} \quad f_i(x,y) \le 0,\ i = 1,\dots,n. \qquad (4.1)\text{–}(4.2)
--   $$
--   1. A function $F(x,y)$ is **jointly convex** if it is convex as a function of $z = (x,y)$ on $E^x_l \times E^y_m$.
--   2. For fixed $x$, $D(x) = \{y : f_i(x,y) \le 0,\ i = 1,\dots,n\}$ is the feasible set of the subproblem (4.3)–(4.4) $\min_{y \in D(x)} f_0(x,y)$; a point $y$ is an **optimal value of $y$** if $y \in D(x)$ and $f_0(x,y) \le f_0(x,y')$ for all $y' \in D(x)$, and the **minimum is attained** at $x$ if such a $y$ exists.
--   3. The **value function** is
--   $$
--   \Phi(x) = \min_{y \in D(x)} f_0(x,y). \qquad (4.5)
--   $$
--   4. The **Slater condition** holds for (4.4) at $x$ if some $y$ has $f_i(x,y) < 0$ for all $i$.
--   5. The **Lagrange function** is $L_U(x,y) = f_0(x,y) + \sum_{i=1}^n U_i f_i(x,y)$.
--   6. $U = (U_1,\dots,U_n)$ are **Kuhn–Tucker multipliers** of (4.3)–(4.4) at $x$ relative to an optimal $\bar y$ if $U_i \ge 0$, $U_i f_i(x,\bar y) = 0$ for all $i$, and $\bar y$ minimizes $L_U(x,\cdot)$ over the whole space $E^y_m$; for an optimal $\bar y$ this is the condition $\Phi(x) = \min_y L_U(x,y)$.
--   7. A pair $(g^x, g^y)$ is a **subgradient of $F$ at $(\bar x,\bar y)$**, with projections $g^x$ on $E^x_l$ and $g^y$ on $E^y_m$, if $F(x,y) - F(\bar x,\bar y) \ge (g^x, x-\bar x) + (g^y, y - \bar y)$ for all $(x,y)$.
--   8. A vector $g$ is a **subgradient of $\Phi$ at $\bar x$ on a set $W$** if $\Phi(x) - \Phi(\bar x) \ge (g, x - \bar x)$ for all $x \in W$.
--
--   These are the objects of Theorem 4.1 and its Corollary: decomposition with respect to variables minimizes $\Phi$ by a subgradient method, and the subgradient of $\Phi$ is computed from the Lagrange multipliers of the subproblem.
--
--   **Formalization Note** $E^x_l$ and $E^y_m$ are `EuclideanSpace ℝ (Fin l)` and `EuclideanSpace ℝ (Fin m)`; constraints are indexed by `Fin n`. $\Phi$ is written as a real infimum `sInf (f₀ x '' D x)`: this is the book's minimum wherever the minimum is attained, and every theorem assumes attainment at the points where it uses $\Phi$ (elsewhere the infimum is Lean's default value `0`).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 93–95, formulas (4.1)–(4.5), Theorem 4.1 (Lagrange function L_U, Kuhn–Tucker multipliers); p. 9, inequality (1.3) (subgradient)

import Mathlib

namespace ShorNonsmooth.Decomposition

/-! Shor (1985), §4.1, pp. 93–95: decomposition with respect to variables.
The variables are split as `x ∈ E^x_l = EuclideanSpace ℝ (Fin l)` and
`y ∈ E^y_m = EuclideanSpace ℝ (Fin m)`; the problem (4.1)–(4.2) is
`min f₀(x, y)` subject to `f i (x, y) ≤ 0`, `i = 1, …, n` (indexed here by `Fin n`). -/

/-- A function `F(x, y)` of the two blocks of variables is **(jointly) convex**: convex as a function
of `z = (x, y)` on the whole space `E^x_l × E^y_m` (the standing assumption of §4.1, p. 94:
"`f₀` and `f_i` … are convex functions"). -/
def JointlyConvex {l m : ℕ}
    (F : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m) => F z.1 z.2)

/-- p. 94, (4.4) and the line after (4.5): `D(x)` is the set of all `y` with `f i (x, y) ≤ 0` for
every `i`. -/
def feasibleY {l m n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | ∀ i, f i x y ≤ 0}

/-- `y` is an **optimal value of `y`** in problem (4.3)–(4.4) for the fixed `x`: it is feasible and
minimizes `f₀(x, ·)` over `D(x)`. -/
def IsOptimalY {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin m)) : Prop :=
  y ∈ feasibleY f x ∧ ∀ y' ∈ feasibleY f x, f₀ x y ≤ f₀ x y'

/-- A **solution to problem (4.3)–(4.4) exists** at `x`: the minimum in (4.5) is attained. -/
def MinAttained {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) : Prop :=
  ∃ y, IsOptimalY f₀ f x y

/-- p. 94, (4.5): the **value function** `Φ(x) = min_{y ∈ D(x)} f₀(x, y)`.
It is written as a real infimum; the book defines `Φ` only where the minimum is attained
(`MinAttained`), and there this infimum is the minimum. Every theorem about `Φ` assumes attainment
at the points it uses (elsewhere the value of `sInf` is Lean's junk value `0`). -/
noncomputable def valueFn {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) : ℝ :=
  sInf (f₀ x '' feasibleY f x)

/-- The **Slater constraint qualification** for (4.4) at `x`: some `y` satisfies every constraint
strictly, `f i (x, y) < 0` for all `i`. -/
def SlaterAt {l m n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) : Prop :=
  ∃ y, ∀ i, f i x y < 0

/-- p. 94: the **Lagrange function** `L_U(x, y) = f₀(x, y) + Σ_{i=1}^n U_i f_i(x, y)`. -/
def lagrangian {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (U : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  f₀ x y + ∑ i, U i * f i x y

/-- p. 95: `U = (U_i)` are **Kuhn–Tucker (Lagrange) multipliers of (4.3)–(4.4)** at the fixed `x`,
relative to the optimal point `ȳ`: `U_i ≥ 0`, complementary slackness `U_i f_i(x, ȳ) = 0`, and `ȳ`
minimizes `L_U(x, ·)` over all `y`. For an optimal `ȳ` this is the book's condition
`Φ(x) = min_y [f₀(x, y) + Σ U_i f_i(x, y)]` with `U ≥ 0`. -/
def IsKuhnTuckerMultiplier {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) (ybar : EuclideanSpace ℝ (Fin m)) (U : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ U i) ∧ (∀ i, U i * f i x ybar = 0) ∧
    ∀ y, lagrangian f₀ f U x ybar ≤ lagrangian f₀ f U x y

/-- A **subgradient of `F(z) = F(x, y)` at `z̄ = (x̄, ȳ)`** (Shor p. 9, (1.3), in `E_{l+m}`), written
through its projections `gx` on `E^x_l` and `gy` on `E^y_m`:
`F(x, y) − F(x̄, ȳ) ≥ (gx, x − x̄) + (gy, y − ȳ)` for all `(x, y)`. -/
def IsJointSubgradient {l m : ℕ}
    (F : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin l)) (ybar : EuclideanSpace ℝ (Fin m))
    (gx : EuclideanSpace ℝ (Fin l)) (gy : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ x y, F x y - F xbar ybar ≥ inner ℝ gx (x - xbar) + inner ℝ gy (y - ybar)

/-- A **subgradient of `Φ` at `x̄` on the convex set `W`** (Shor p. 9, (1.3), for a function convex
on a set): `Φ(x) − Φ(x̄) ≥ (g, x − x̄)` for all `x ∈ W`. -/
def IsSubgradientOn {l : ℕ} (Φ : EuclideanSpace ℝ (Fin l) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin l))) (xbar g : EuclideanSpace ℝ (Fin l)) : Prop :=
  ∀ x ∈ W, Φ x - Φ xbar ≥ inner ℝ g (x - xbar)

end ShorNonsmooth.Decomposition


