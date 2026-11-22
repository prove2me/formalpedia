-- Prove2me | Definitions.Def_KarimiPL_Rel_Conditions
-- name    : KarimiPL_Rel_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:25.26186+00:00
-- url     : https://prove2.me/theorems/954bbde9-1a60-45c6-9f7d-e4bc9b31a725
-- title:
--   Appendix A, pp. 11–12 — the solution set X*, projections x_p onto it, and the conditions SC, ESC, WSC, RSI, EB, QG
-- statement:
--   Throughout, $f:\mathbb R^d\to\mathbb R$ and $\nabla f$ denotes its gradient. The **solution set** is the set of global minimizers
--   $$\mathcal X^*=\{x\in\mathbb R^d:\ f(x)\le f(y)\ \text{for all }y\}.$$
--   A map $p:\mathbb R^d\to\mathbb R^d$ is a **projection onto $\mathcal X^*$** if for every $x$ the point $x_p:=p(x)$ lies in $\mathcal X^*$ and is nearest to $x$ among the points of $\mathcal X^*$, i.e. $\|x-x_p\|=\operatorname{dist}(x,\mathcal X^*)$. When $\mathcal X^*$ is not convex a nearest point need not be unique, so $p$ is a selection of nearest points; every condition below refers to a fixed such $p$.
--
--   For a constant $\mu$ the following conditions are defined (the paper requires $\mu>0$):
--
--   1. **Strong convexity** (SC): $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac\mu2\|y-x\|^2$ for all $x,y$.
--   2. **Essential strong convexity** (ESC): the same inequality for all $x,y$ with $x_p=y_p$.
--   3. **Weak strong convexity** (WSC): $f^*\ge f(x)+\langle\nabla f(x),x_p-x\rangle+\frac\mu2\|x_p-x\|^2$ for all $x$, where $f^*=f(x_p)$ is the optimal value.
--   4. **Restricted secant inequality** (RSI): $\langle\nabla f(x),x-x_p\rangle\ge\mu\|x_p-x\|^2$ for all $x$.
--   5. **Error bound** (EB): $\|\nabla f(x)\|\ge\mu\|x_p-x\|$ for all $x$.
--   6. **Quadratic growth** (QG), relative to a value $f^*$: $f(x)-f^*\ge\frac\mu2\|x_p-x\|^2$ for all $x$.
--
--   Finally, for a family of conditions $C(\mu)$, "$C$ holds" means that $C(\mu)$ holds for some $\mu>0$.
--
--   The Polyak–Łojasiewicz condition (PL), $\frac12\|\nabla f(x)\|^2\ge\mu(f(x)-f^*)$, is the published predicate `ShiOptRates.PolyakLojasiewicz` and is not redefined here.
--
--   These are the seven conditions compared in Theorem 2; the mission's theorems state implications among them.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, abbreviated `E d`. The projection is an explicit map `p` constrained by `IsProjSel f p` (membership in $\mathcal X^*$ and $\|x-p(x)\|=$ `Metric.infDist x X*`), not a `Classical.choose`, so the choice of nearest point is visible in every statement. In WSC the optimal value $f^*$ is written $f(p(x))$, its value on $\mathcal X^*$; in QG it is an explicit argument, which the theorems set to $f(x^*)$ for a global minimizer $x^*$. The sign condition $\mu>0$ is not part of the predicates: it is a separate hypothesis of every theorem, and part of `Holds`.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, list of conditions 1–7, pp. 11–12; standing assumption X* ≠ ∅, §2, p. 2

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass

namespace KarimiPL.Rel

open scoped InnerProductSpace

/-- The space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The solution set `X* = {x | f x ≤ f y for all y}` of `min f`. -/
def solSet {d : ℕ} (f : E d → ℝ) : Set (E d) :=
  {x | ∀ y, f x ≤ f y}

/-- `p` is a projection onto the solution set: for every `x`, `p x ∈ X*` and `p x` is a
point of `X*` nearest to `x` (`‖x - p x‖ = dist(x, X*)`). This is the paper's `x_p`. -/
def IsProjSel {d : ℕ} (f : E d → ℝ) (p : E d → E d) : Prop :=
  ∀ x, p x ∈ solSet f ∧ ‖x - p x‖ = Metric.infDist x (solSet f)

/-- Strong convexity (SC) with constant `μ`. -/
def SC {d : ℕ} (f : E d → ℝ) (μ : ℝ) : Prop :=
  ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

/-- Essential strong convexity (ESC) with constant `μ`, for the projection `p`. -/
def ESC {d : ℕ} (f : E d → ℝ) (p : E d → E d) (μ : ℝ) : Prop :=
  ∀ x y, p x = p y → f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

/-- Weak strong convexity (WSC) with constant `μ`, for the projection `p`; `f* = f (p x)`. -/
def WSC {d : ℕ} (f : E d → ℝ) (p : E d → E d) (μ : ℝ) : Prop :=
  ∀ x, f x + ⟪gradient f x, p x - x⟫_ℝ + μ / 2 * ‖p x - x‖ ^ 2 ≤ f (p x)

/-- Restricted secant inequality (RSI) with constant `μ`, for the projection `p`. -/
def RSI {d : ℕ} (f : E d → ℝ) (p : E d → E d) (μ : ℝ) : Prop :=
  ∀ x, μ * ‖p x - x‖ ^ 2 ≤ ⟪gradient f x, x - p x⟫_ℝ

/-- Error bound (EB) with constant `μ`, for the projection `p`. -/
def EB {d : ℕ} (f : E d → ℝ) (p : E d → E d) (μ : ℝ) : Prop :=
  ∀ x, μ * ‖p x - x‖ ≤ ‖gradient f x‖

/-- Quadratic growth (QG) with constant `μ`, for the projection `p` and optimal value `fstar`. -/
def QG {d : ℕ} (f : E d → ℝ) (p : E d → E d) (fstar μ : ℝ) : Prop :=
  ∀ x, μ / 2 * ‖p x - x‖ ^ 2 ≤ f x - fstar

/-- `Holds C`: the condition `C μ` holds for some constant `μ > 0`. -/
def Holds (C : ℝ → Prop) : Prop :=
  ∃ μ, 0 < μ ∧ C μ

end KarimiPL.Rel


