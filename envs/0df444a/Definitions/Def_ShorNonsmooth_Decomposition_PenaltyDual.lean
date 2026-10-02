-- Prove2me | Definitions.Def_ShorNonsmooth_Decomposition_PenaltyDual
-- name    : ShorNonsmooth_Decomposition_PenaltyDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:20:57.628985+00:00
-- url     : https://prove2.me/theorems/07fac4c8-f87d-481e-bfa5-fecfc2698f20
-- title:
--   Convex program (4.178): solution set, Lagrange multiplier vectors, nonsmooth penalty (4.179) and dual function (4.187)
-- statement:
--   Let $E_N$ be Euclidean space and $f_0, f_1, \dots, f_m : E_N \to \mathbb{R}$. Consider the program
--   $$
--   \min f_0(x) \quad \text{s.t.} \quad f_i(x) \le 0,\ i = 1,\dots,m. \qquad (4.178)
--   $$
--   1. The **feasible set** is $\{x : f_i(x) \le 0 \text{ for all } i\}$ and the **solution set** is the set of feasible points minimizing $f_0$ over it.
--   2. A vector $\bar y \in \mathbb{R}^m$ is a **Lagrange multiplier vector** of (4.178) if $\bar y \ge 0$, the optimal value $f^* = \inf\{f_0(x) : x \text{ feasible}\}$ is a finite real number, and
--   $$
--   f_0(x) + \sum_{i=1}^m \bar y_i f_i(x) \ge f^* \quad \text{for every } x \in E_N .
--   $$
--   3. A **nonsmooth penalty function** is a convex $p : \mathbb{R} \to \mathbb{R}$ with $p(t) = 0$ for $t \le 0$ and $p(t) > 0$ for $t > 0$; the **penalized function** is
--   $$
--   S(x) = f_0(x) + \sum_{i=1}^m p_i[f_i(x)]. \qquad (4.179)
--   $$
--   4. For a set $X \subseteq E_N$, the **dual function** is
--   $$
--   \Phi(u) = \min_{x \in X}\Big[f_0(x) + \sum_{i=1}^m u_i f_i(x)\Big]. \qquad (4.187)
--   $$
--
--   These objects carry Theorem 4.2 (exactness of nonsmooth penalties) and Theorem 4.3 (the Lagrangian dual bound).
--
--   **Formalization Note** $E_N$ is `EuclideanSpace ℝ (Fin N)`. $f^*$ is expressed as the greatest lower bound (`IsGLB`) of the objective values on the feasible set, so a multiplier vector exists only when that set is nonempty and bounded below. $\Phi$ is written as a real infimum over $X$; it is the book's minimum wherever that minimum is attained, which the theorem using it assumes.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 146, formulas (4.178)–(4.179); p. 147, Theorem 4.2 (Lagrange multiplier vector); p. 148, formulas (4.185)–(4.187)

import Mathlib

namespace ShorNonsmooth.Decomposition

/-! Shor (1985), §4.7, pp. 146–148: the convex program (4.178) `min f₀(x)` s.t. `f i x ≤ 0`,
its nonsmooth penalty function (4.179), and the Lagrangian dual function (4.187). Here
`x ∈ E_N = EuclideanSpace ℝ (Fin N)` and the constraints are indexed by `Fin m`. -/

/-- The feasible set `{x : f_i(x) ≤ 0, i = 1, …, m}` of (4.178) / (4.186) (on the whole space). -/
def feasibleSet {N m : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {x | ∀ i, f i x ≤ 0}

/-- The set of **minimum points (solutions) of (4.178)**: feasible points minimizing `f₀` over the
feasible set. -/
def solutionSet {N m : ℕ} (f₀ : EuclideanSpace ℝ (Fin N) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | x ∈ feasibleSet f ∧ ∀ x' ∈ feasibleSet f, f₀ x ≤ f₀ x'}

/-- `ȳ` is a **Lagrange multiplier vector of problem (4.178)**: `ȳ ≥ 0`, the optimal value
`f* = inf {f₀(x) : f_i(x) ≤ 0}` is a finite real number, and
`f₀(x) + Σ ȳ_i f_i(x) ≥ f*` for every `x` (so `inf_x L(x, ȳ) = f*`). -/
def IsLagrangeMultiplierVector {N m : ℕ} (f₀ : EuclideanSpace ℝ (Fin N) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ) (ybar : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ ybar i) ∧ ∃ fstar : ℝ, IsGLB (f₀ '' feasibleSet f) fstar ∧
    ∀ x, fstar ≤ f₀ x + ∑ i, ybar i * f i x

/-- p. 146: a **nonsmooth penalty function** `p : ℝ → ℝ` — convex, with `p(t) = 0` for `t ≤ 0` and
`p(t) > 0` for `t > 0`. -/
def IsPenaltyFunction (p : ℝ → ℝ) : Prop :=
  ConvexOn ℝ Set.univ p ∧ (∀ t ≤ 0, p t = 0) ∧ ∀ t, 0 < t → 0 < p t

/-- p. 146, (4.179): the **penalized function** `S(x) = f₀(x) + Σ_{i=1}^m p_i[f_i(x)]`. -/
def penalized {N m : ℕ} (f₀ : EuclideanSpace ℝ (Fin N) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ) (p : Fin m → ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  f₀ x + ∑ i, p i (f i x)

/-- p. 148, (4.187): the **dual function** `Φ(u) = min_{x ∈ X} [f₀(x) + Σ_{i=1}^m u_i f_i(x)]`,
written as a real infimum over `X`; it is the minimum wherever that minimum is attained (the
hypothesis of the theorem that uses it; elsewhere `sInf` may take Lean's junk value `0`). -/
noncomputable def dualFn {N m : ℕ} (X : Set (EuclideanSpace ℝ (Fin N)))
    (f₀ : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (u : Fin m → ℝ) : ℝ :=
  sInf ((fun x => f₀ x + ∑ i, u i * f i x) '' X)

end ShorNonsmooth.Decomposition


