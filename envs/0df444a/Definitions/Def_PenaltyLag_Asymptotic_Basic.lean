-- Prove2me | Definitions.Def_PenaltyLag_Asymptotic_Basic
-- name    : PenaltyLag_Asymptotic_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:05.832227+00:00
-- url     : https://prove2.me/theorems/26faa178-2840-4e9c-8633-0b7d24498813
-- title:
--   Problem (P), the penalty Lagrangian $L_r$ (2.3), $L_0$ (3.2), $F_r$ (3.4), the duals $g_r$, $g_0$, and asymptotically minimizing sequences
-- statement:
--   The objects of Rockafellar's dual approach to the convex program
--   $$
--   \text{(P)}\qquad \text{minimize } f_0(x) \text{ over } x \in X \text{ subject to } f_i(x) \le 0,\ i = 1, \dots, m,
--   $$
--   where $X$ is a subset of a real vector space $E$ and $f_0, \dots, f_m$ are real functions. Multipliers $y = (y_1, \dots, y_m)$ live in $\mathbb R^m$ with the Euclidean norm $|\cdot|$ and inner product $u \cdot y$.
--
--   1. $\theta(t) = \max\{0, t\}$ (1.2).
--   2. The **penalty Lagrangian** (2.3), for a parameter $r > 0$:
--   $$
--   L_r(x, y) = f_0(x) + \frac{1}{4r} \sum_{i=1}^m \big[\theta(y_i + 2 r f_i(x))^2 - y_i^2\big].
--   $$
--   3. The **ordinary Lagrangian** (3.2): $L_0(x, y) = f_0(x) + \sum_i y_i f_i(x)$ if $y \ge 0$ and $L_0(x, y) = -\infty$ otherwise.
--   4. The perturbation function (3.4): $F_r(x, u) = f_0(x) + r \sum_i u_i^2$ if $u_i \ge f_i(x)$ for all $i$, and $+\infty$ otherwise.
--   5. The dual objectives $g_r(y) = \inf_{x \in X} L_r(x, y)$ of $(D_r)$ and $g_0(y) = \inf_{x \in X} L_0(x, y)$ of $(D_0)$, with values in $[-\infty, +\infty]$; the **dual optimal value** $\sup_y g_0(y)$.
--   6. A **maximizing sequence** for $(D_r)$ is a sequence $\{y^k\}$ in $\mathbb R^m$ with $g_r(y^k) \to \sup g_r$, the supremum over all of $\mathbb R^m$.
--   7. A sequence $\{x^k\}$ in $X$ is **asymptotically feasible** for (P) if $\limsup_k f_i(x^k) \le 0$ for $i = 1, \dots, m$ (4.5). The **asymptotic optimal value** in (P) is the infimum of $\limsup_k f_0(x^k)$ over all asymptotically feasible sequences, and an asymptotically feasible sequence attaining it is **asymptotically minimizing**.
--
--   These are the objects every statement of the mission is about; the asymptotic notions replace feasibility and optimality when (P) need not have feasible or optimal points.
--
--   **Formalization Note** The infima $g_r$, $g_0$, the dual value, the asymptotic optimal value and every $\limsup$ are computed in `EReal` $= [-\infty, +\infty]$, so that $-\infty$ and $+\infty$ (no asymptotically feasible sequence) are represented and never replaced by a junk value. `grR` is $g_r$ coerced to $\mathbb R$; it is used only in statements whose hypotheses make $g_r$ finite. `Lr` is meaningful only for $r > 0$ (Lean's $1/0 = 0$), which every statement assumes; $L_0$ is a separate definition. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is not built into these objects; it is a hypothesis of every theorem that uses them. The same objects serve the missions on asymptotically minimizing sequences (§4) and on exact minimization at a dual optimal solution (§3).
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), pp. 354–364, (P), (1.2), (2.3), (3.2), (3.4), (D_r), (4.5)

import Mathlib

namespace PenaltyLag.Asymptotic

open Filter Topology

/-- ℝ^m with the Euclidean norm |·| and the inner product u·y (indices `Fin m`, 0-based). -/
abbrev Mult (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- θ(t) = max{0, t} (1.2). -/
def theta (t : ℝ) : ℝ := max 0 t

/-- The penalty Lagrangian L_r (2.3). Meaningful for r > 0; every statement assumes it. -/
noncomputable def Lr {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (x : E)
    (y : Mult m) : ℝ :=
  f₀ x + (1 / (4 * r)) * ∑ i, (theta (y i + 2 * r * f i x) ^ 2 - y i ^ 2)

/-- The ordinary Lagrangian L₀ (3.2): f₀(x) + Σ yᵢ fᵢ(x) if y ≥ 0, −∞ otherwise. -/
noncomputable def L0 {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (x : E)
    (y : Mult m) : EReal :=
  if ∀ i, 0 ≤ y i then ((f₀ x + ∑ i, y i * f i x : ℝ) : EReal) else ⊥

/-- F_r (3.4): f₀(x) + r Σ uᵢ² if uᵢ ≥ fᵢ(x) for all i, +∞ otherwise. -/
noncomputable def Fr {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (x : E)
    (u : Mult m) : EReal :=
  if ∀ i, f i x ≤ u i then ((f₀ x + r * ∑ i, u i ^ 2 : ℝ) : EReal) else ⊤

/-- g_r(y) = inf_{x ∈ X} L_r(x, y), the objective of (D_r), valued in [−∞, +∞]. -/
noncomputable def gr {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (y : Mult m) : EReal :=
  ⨅ x ∈ X, (Lr f₀ f r x y : EReal)

/-- g₀(y) = inf_{x ∈ X} L₀(x, y), the objective of the ordinary dual (D₀). -/
noncomputable def g0 {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (y : Mult m) : EReal :=
  ⨅ x ∈ X, L0 f₀ f x y

/-- g_r as a real function; used only where g_r is known to be finite (it is 0 at ±∞). -/
noncomputable def grR {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (y : Mult m) : ℝ :=
  (gr X f₀ f r y).toReal

/-- The dual optimal value sup_y g₀(y) (= sup_y g_r(y) for r > 0, Theorem 3.2). -/
noncomputable def dualValue {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) :
    EReal :=
  ⨆ y, g0 X f₀ f y

/-- A maximizing sequence for (D_r) (p. 364): g_r(yᵏ) → sup_y g_r(y) in [−∞, +∞]. -/
def IsMaximizing {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (y : ℕ → Mult m) : Prop :=
  Tendsto (fun k => gr X f₀ f r (y k)) atTop (𝓝 (⨆ y', gr X f₀ f r y'))

/-- Asymptotically feasible for (P) (4.5): xᵏ ∈ X and lim sup_k fᵢ(xᵏ) ≤ 0 for every i. -/
def IsAsympFeasible {E : Type*} {m : ℕ} (X : Set E) (f : Fin m → E → ℝ) (x : ℕ → E) : Prop :=
  (∀ k, x k ∈ X) ∧ ∀ i, limsup (fun k => (f i (x k) : EReal)) atTop ≤ 0

/-- The asymptotic optimal value in (P) (p. 364): the infimum of lim sup_k f₀(xᵏ) over all
asymptotically feasible sequences (+∞ if there are none). -/
noncomputable def asympValue {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ)
    (f : Fin m → E → ℝ) : EReal :=
  ⨅ (x : ℕ → E) (_ : IsAsympFeasible X f x), limsup (fun k => (f₀ (x k) : EReal)) atTop

/-- An asymptotically minimizing sequence for (P) (p. 364): asymptotically feasible, with
lim sup_k f₀(xᵏ) equal to the asymptotic optimal value. -/
def IsAsympMinimizing {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (x : ℕ → E) : Prop :=
  IsAsympFeasible X f x ∧ limsup (fun k => (f₀ (x k) : EReal)) atTop = asympValue X f₀ f

end PenaltyLag.Asymptotic


