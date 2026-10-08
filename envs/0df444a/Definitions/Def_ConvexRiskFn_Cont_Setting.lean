-- Prove2me | Definitions.Def_ConvexRiskFn_Cont_Setting
-- name    : ConvexRiskFn_Cont_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:13.653966+00:00
-- url     : https://prove2.me/theorems/ed99e1b8-e2f1-4a45-a743-0aec24480f77
-- title:
--   §1 and §3.1, pp. 433–437 — domain, properness, axioms (A1)–(A2), algebraic subgradient (3.1) and subdifferential of an extended-real risk function
-- statement:
--   Let $\mathcal X$ be a real vector space (in §3.1 a Banach space with its strong topology) and let $\rho:\mathcal X\to\overline{\mathbb R}=[-\infty,+\infty]$ be a **risk function**. Smaller values of $X$ are better (costs). This file fixes the following notions.
--
--   1. The **domain** $\operatorname{dom}\rho := \{X\in\mathcal X : \rho(X)<+\infty\}$, and $\rho$ is **proper** if $\rho(X)>-\infty$ for all $X$ and $\operatorname{dom}\rho\neq\emptyset$ (p. 435).
--   2. **(A1) Convexity** (p. 433): for all $X,Y\in\mathcal X$ and $\alpha\in[0,1]$,
--   $$\rho(\alpha X+(1-\alpha)Y)\le \alpha\rho(X)+(1-\alpha)\rho(Y).$$
--   3. **(A2) Monotonicity** (p. 433): if $Y\succeq X$ then $\rho(Y)\ge\rho(X)$.
--   4. A linear functional $l:\mathcal X\to\mathbb R$, not necessarily continuous, is an **algebraic subgradient** of $\rho$ at $\bar X$ if
--   $$\rho(X)\ge\rho(\bar X)+l(X-\bar X)\qquad\forall X\in\mathcal X.\tag{3.1}$$
--   5. For a normed space, with $\mathcal Y:=\mathcal X^*$, the **subdifferential** $\partial\rho(\bar X)$ is the set of continuous linear functionals $l\in\mathcal X^*$ satisfying (3.1); $\rho$ is **subdifferentiable** at $\bar X$ if $\partial\rho(\bar X)\neq\emptyset$.
--
--   These are the objects in which Proposition 3.1 (continuity and subdifferentiability of a proper convex monotone risk function on a Banach lattice) is stated.
--
--   **Formalization Note** $\overline{\mathbb R}$ is Lean's `EReal`. The right-hand side of (A1) is computed with `EReal` arithmetic, where $0\cdot(+\infty)=0$; for a proper $\rho$ no sum $(+\infty)+(-\infty)$ occurs, so this agrees with the paper's convention. The order $Y\succeq X$ is the order of the type, `X ≤ Y`. The paper defines (3.1) for $\bar X\in\operatorname{dom}\rho$; the predicate is stated for every $\bar X$, and each theorem that uses it carries the hypothesis on $\bar X$ it needs.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 433, axioms (A1)–(A2); p. 435, definition of proper and dom(ρ); p. 436, §3.1, (3.1) and the subdifferential ∂ρ(X̄) with 𝒴 := 𝒳*

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Cont

variable {E : Type*}

/-- `ρ` is proper: `ρ X > -∞` for every `X` and `dom ρ` is nonempty (p. 435). -/
def IsProper (ρ : E → EReal) : Prop := (∀ X, ⊥ < ρ X) ∧ (ConvexRiskFn.Dual.dom ρ).Nonempty

/-- (A2) Monotonicity (p. 433): if `Y ⪰ X` then `ρ(Y) ≥ ρ(X)`. -/
def A2 [Preorder E] (ρ : E → EReal) : Prop := ∀ X Y : E, X ≤ Y → ρ X ≤ ρ Y

/-- (3.1), p. 436: a linear functional `l` (not necessarily continuous) is an algebraic
subgradient of `ρ` at `Xbar` if `ρ(X) ≥ ρ(Xbar) + l(X − Xbar)` for all `X`. -/
def IsAlgSubgradient [AddCommGroup E] [Module ℝ E] (ρ : E → EReal) (Xbar : E)
    (l : E →ₗ[ℝ] ℝ) : Prop :=
  ∀ X : E, ρ Xbar + ((l (X - Xbar) : ℝ) : EReal) ≤ ρ X

/-- The subdifferential `∂ρ(Xbar)` (p. 436), with `𝒴 := 𝒳*`: the continuous linear
functionals satisfying (3.1). -/
def subdiff [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : E → EReal) (Xbar : E) :
    Set (E →L[ℝ] ℝ) :=
  {l | ∀ X : E, ρ Xbar + ((l (X - Xbar) : ℝ) : EReal) ≤ ρ X}

end ConvexRiskFn.Cont


