-- Prove2me | Definitions.Def_PenaltyLag_Exact_Basic
-- name    : PenaltyLag_Exact_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:41.396188+00:00
-- url     : https://prove2.me/theorems/898514b5-002f-41b2-977e-c4d6abeeec28
-- title:
--   Problem (P), the penalty Lagrangian $L_r$ (2.3), $L_0$ (3.2), the duals $g_r$, $g_0$, normality, Kuhn–Tucker vectors (3.17), saddle points and the Kuhn–Tucker conditions
-- statement:
--   Let $E$ be a real vector space, $X \subseteq E$, and $f_0, f_1, \dots, f_m : X \to \mathbb R$. The nonlinear program is
--   $$
--   \text{(P)}\qquad \text{minimize } f_0(x) \text{ over } x \in X \text{ subject to } f_i(x) \le 0,\ i = 1, \dots, m.
--   $$
--   A point $x$ is **feasible** if $x \in X$ and $f_i(x) \le 0$ for all $i$; the **optimal value** (the "inf in (P)") is the infimum of $f_0$ over the feasible points, an element of $[-\infty, +\infty]$ (it is $+\infty$ when no point is feasible). A point $\bar x$ is an **optimal solution** to (P) if it is feasible and $f_0(\bar x) \le f_0(x)$ for every feasible $x$.
--
--   Multiplier vectors $y = (y_1, \dots, y_m)$ range over $\mathbb R^m$ with no sign restriction. With $\theta(t) = \max\{0, t\}$ (1.2) and a parameter $r > 0$, the **penalty Lagrangian** (2.3) is
--   $$
--   L_r(x, y) = f_0(x) + \frac{1}{4r} \sum_{i=1}^m \big[\theta(y_i + 2 r f_i(x))^2 - y_i^2\big],
--   $$
--   and the **ordinary Lagrangian** (3.2) is $L_0(x, y) = f_0(x) + \sum_{i} y_i f_i(x)$ if $y \ge 0$ and $L_0(x, y) = -\infty$ otherwise. The dual objectives are
--   $$
--   g_r(y) = \inf_{x \in X} L_r(x, y), \qquad g_0(y) = \inf_{x \in X} L_0(x, y),
--   $$
--   with values in $[-\infty, +\infty)$; problem $(D_r)$ maximizes $g_r$ over $\mathbb R^m$ and $(D_0)$ maximizes $g_0$. The **dual optimal value** is $\sup_y g_0(y)$, and (P) is **normal** if this equals the optimal value of (P) (p. 361). A vector $\bar y$ is an **optimal solution to $(D_r)$** if $g_r(\bar y) = \sup_y g_r(y)$ and $g_r(\bar y) > -\infty$ (by the paper's convention, dual optimal solutions are not said to exist when $g_r \equiv -\infty$).
--
--   A **Kuhn–Tucker vector** for (P) relative to $L_r$ (3.17) is a $\bar y \in \mathbb R^m$ with
--   $$
--   -\infty < \inf_{x \in X} L_r(x, \bar y) = \inf \text{ in (P)},
--   $$
--   and relative to $L_0$ the same with $L_0$ in place of $L_r$. A pair $(\bar x, \bar y)$ is a **saddle point** of $L_r$ (resp. $L_0$) if $\bar x \in X$ and
--   $$
--   L_r(\bar x, y) \le L_r(\bar x, \bar y) \le L_r(x, \bar y) \qquad \text{for all } x \in X,\ y \in \mathbb R^m.
--   $$
--   The **ordinary Kuhn–Tucker conditions** (Corollary 3.4) for $(\bar x, \bar y)$ are: (i) $\bar y_i \ge 0$, $f_i(\bar x) \le 0$, $\bar y_i f_i(\bar x) = 0$ for $i = 1, \dots, m$; (ii) $\bar x \in X$ minimizes $f_0 + \sum_i \bar y_i f_i$ over $X$.
--
--   These are the objects in which every statement of the mission is written.
--
--   **Formalization Note** The paper's standing assumption (p. 358), that $X$ is a nonempty convex set and $f_0, \dots, f_m$ are convex, is not part of the definitions; every theorem of the mission assumes it. The functions $f_i$ are total functions `E → ℝ`, of which only the values on $X$ enter any statement. Constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$) and $f_0$ is a separate argument. $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`. The values $g_r$, $g_0$, $L_0$, the optimal value of (P) and the dual optimal value are extended reals (`EReal`), so that $\pm\infty$ are represented and no infimum returns a junk value. `Lr` is meaningful only for $r > 0$ (at $r = 0$ Lean's $1/0 = 0$ would make it $f_0$), which is why $L_0$ is a separate definition and every statement about $L_r$ assumes $r > 0$. The paper uses "saddle point" in the sense of Rockafellar's *Convex Analysis*, §36 (minimum in $x$ over $X$, maximum in $y$ over $\mathbb R^m$), which is the definition used here; for $L_0$ the comparison is in the extended reals.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), pp. 354–362, (P) p. 354, (1.2) p. 355, (2.3) p. 357, (3.2) p. 358, (D_r) p. 359, normality and (3.17) p. 361, Corollary 3.4 (i)–(ii) p. 362

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

namespace PenaltyLag.Exact

/-- inf in (P): the infimum of f₀ over the feasible set {x ∈ X : fᵢ(x) ≤ 0 ∀ i}
(+∞ if it is empty, −∞ if f₀ is unbounded below on it). -/
noncomputable def primalValue {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ)
    (f : Fin m → E → ℝ) : EReal :=
  ⨅ x ∈ X, ⨅ (_ : ∀ i, f i x ≤ 0), (f₀ x : EReal)

/-- x̄ is an optimal solution to (P): feasible, and f₀(x̄) ≤ f₀(x) for every feasible x. -/
def IsOptimal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (xbar : E) :
    Prop :=
  xbar ∈ X ∧ (∀ i, f i xbar ≤ 0) ∧ ∀ x ∈ X, (∀ i, f i x ≤ 0) → f₀ xbar ≤ f₀ x

/-- (P) is normal (p. 361): the dual optimal value equals the primal optimal value. -/
def IsNormal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) : Prop :=
  PenaltyLag.Asymptotic.dualValue X f₀ f = primalValue X f₀ f

/-- ȳ is an optimal solution to (D_r): g_r(ȳ) = sup_y g_r(y). By the convention of p. 361,
no dual optimal solution exists when g_r ≡ −∞; hence the clause g_r(ȳ) ≠ −∞. -/
def IsDualOptimal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  PenaltyLag.Asymptotic.gr X f₀ f r ybar ≠ ⊥ ∧ PenaltyLag.Asymptotic.gr X f₀ f r ybar = ⨆ y, PenaltyLag.Asymptotic.gr X f₀ f r y

/-- ȳ is a Kuhn–Tucker vector for (P) relative to L_r, r > 0 (3.17):
−∞ < inf_{x ∈ X} L_r(x, ȳ) = inf in (P). -/
def IsKTVector {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  ⊥ < PenaltyLag.Asymptotic.gr X f₀ f r ybar ∧ PenaltyLag.Asymptotic.gr X f₀ f r ybar = primalValue X f₀ f

/-- ȳ is a Kuhn–Tucker vector for (P) relative to L₀ ((3.17) with L₀ in place of L_r). -/
def IsKTVector0 {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  ⊥ < PenaltyLag.Asymptotic.g0 X f₀ f ybar ∧ PenaltyLag.Asymptotic.g0 X f₀ f ybar = primalValue X f₀ f

/-- (x̄, ȳ) is a saddle point of L_r on X × ℝ^m (minimum in x over X, maximum in y over ℝ^m):
L_r(x̄, y) ≤ L_r(x̄, ȳ) ≤ L_r(x, ȳ) for all x ∈ X, y ∈ ℝ^m, with x̄ ∈ X. -/
def IsSaddle {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (xbar : E)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  xbar ∈ X ∧ (∀ y, PenaltyLag.Asymptotic.Lr f₀ f r xbar y ≤ PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar) ∧ ∀ x ∈ X, PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar ≤ PenaltyLag.Asymptotic.Lr f₀ f r x ybar

/-- (x̄, ȳ) is a saddle point of the (extended-real valued) ordinary Lagrangian L₀ on X × ℝ^m. -/
def IsSaddle0 {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (xbar : E)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  xbar ∈ X ∧ (∀ y, PenaltyLag.Asymptotic.L0 f₀ f xbar y ≤ PenaltyLag.Asymptotic.L0 f₀ f xbar ybar) ∧ ∀ x ∈ X, PenaltyLag.Asymptotic.L0 f₀ f xbar ybar ≤ PenaltyLag.Asymptotic.L0 f₀ f x ybar

/-- The ordinary Kuhn–Tucker conditions (i), (ii) of Corollary 3.4:
(i) ȳᵢ ≥ 0, fᵢ(x̄) ≤ 0, ȳᵢ fᵢ(x̄) = 0 for every i; (ii) x̄ ∈ X minimizes f₀ + Σ ȳᵢ fᵢ over X. -/
def KuhnTuckerConditions {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  (∀ i, 0 ≤ ybar i ∧ f i xbar ≤ 0 ∧ ybar i * f i xbar = 0) ∧
  xbar ∈ X ∧ ∀ x ∈ X, f₀ xbar + ∑ i, ybar i * f i xbar ≤ f₀ x + ∑ i, ybar i * f i x

end PenaltyLag.Exact


