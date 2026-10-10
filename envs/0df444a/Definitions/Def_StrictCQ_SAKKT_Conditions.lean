-- Prove2me | Definitions.Def_StrictCQ_SAKKT_Conditions
-- name    : StrictCQ_SAKKT_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:31:53.838657+00:00
-- url     : https://prove2.me/theorems/482050fe-0304-4c9d-a22d-174c8042968a
-- title:
--   SAKKT (p. 10), AGP(γ) (4.1), SAKKT-regularity (Definition 4.3)
-- statement:
--   Three conditions at a point $x^*\in\mathbb R^n$ for the constraint system of problem (1.1) and an objective $f$.
--
--   1. **SAKKT** (Strong Approximate KKT, p. 10). $x^*$ satisfies SAKKT for $f$ if there are a sequence $x^k\to x^*$, multipliers $\lambda^k\in\mathbb R^m$ and $\mu^k\in\mathbb R^p_+$, with $\mu^k_j=0$ whenever $g_j(x^k)<0$, such that
--   $$\lim_{k\to\infty}\ \nabla f(x^k)+\sum_{i=1}^m\lambda^k_i\nabla h_i(x^k)+\sum_{j=1}^p\mu^k_j\nabla g_j(x^k)=0. \tag{1.2}$$
--   2. **AGP($\gamma$)** (4.1), for $\gamma\in[-\infty,0]$. $x^*$ satisfies AGP($\gamma$) for $f$ if there is a sequence $x^k\to x^*$ such that
--   $$P_{\Omega(x^k,\gamma)}\big(x^k-\nabla f(x^k)\big)-x^k\to 0.$$
--   The mission uses $\gamma=0$.
--   3. **SAKKT-regularity** (Definition 4.3). $x^*$ is SAKKT-regular if the set-valued map $x\mapsto N_{\Omega(x,0)}(x)$ is outer semicontinuous at $x^*$:
--   $$\limsup_{x\to x^*}N_{\Omega(x,0)}(x)\subset N_{\Omega(x^*,0)}(x^*).$$
--
--   SAKKT is a sequential optimality condition: every local minimizer satisfies it, with or without a constraint qualification. SAKKT-regularity is the constraint property that the goal theorem identifies as the weakest one making SAKKT imply KKT.
--
--   **Formalization Note** In SAKKT the support condition $\mu^k_j=0$ is imposed at the iterates $x^k$, not at $x^*$, and no complementarity limit is added. The page writes "$x^k\to x$"; the limit is the point $x^*$ under consideration. AGP is stated with the projection as a predicate: there are points $y^k$ that are Euclidean projections of $x^k-\nabla f(x^k)$ onto $\Omega(x^k,\gamma)$ with $y^k-x^k\to0$; since these sets are nonempty, closed and convex, the projection exists and is unique, so this is the page's condition. Definition 4.3 is the inclusion; its trailing identity $N_{\Omega(x^*,0)}(x^*)=L_\Omega(x^*)^\circ$ is a separate theorem of the mission. The outer limit is the sequential one of (1.6).
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 2 (1.2), p. 6 (4.1), p. 10 SAKKT and Definition 4.3

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

variable {n m p : ℕ}

/-- SAKKT at `xs` for the objective `f` (p. 10): there are `xᵏ → xs`, `λᵏ ∈ ℝᵐ` and `μᵏ ∈ ℝᵖ₊`
with `μⱼᵏ = 0` whenever `gⱼ(xᵏ) < 0`, such that the AKKT residual (1.2)
`∇f(xᵏ) + Σ λᵢᵏ ∇hᵢ(xᵏ) + Σ μⱼᵏ ∇gⱼ(xᵏ)` tends to `0`. -/
def Constraints.SAKKT (C : Constraints n m p) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ),
    Tendsto x atTop (𝓝 xs) ∧ (∀ k j, 0 ≤ mu k j) ∧ (∀ k j, C.g j (x k) < 0 → mu k j = 0) ∧
    Tendsto (fun k => gradient f (x k) + ∑ i, lam k i • gradient (C.h i) (x k) +
      ∑ j, mu k j • gradient (C.g j) (x k)) atTop (𝓝 0)

/-- AGP(γ) at `xs` for the objective `f`, (4.1): there are `xᵏ → xs` and projections
`yᵏ = P_{Ω(xᵏ,γ)}(xᵏ - ∇f(xᵏ))` with `yᵏ - xᵏ → 0`. This mission uses it at `γ = 0` only. -/
def Constraints.AGP (C : Constraints n m p) (γ : EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ x y : ℕ → EuclideanSpace ℝ (Fin n), Tendsto x atTop (𝓝 xs) ∧
    (∀ k, StrictCQ.AGP.IsProj (C.linSet (x k) γ) (x k - gradient f (x k)) (y k)) ∧
    Tendsto (fun k => y k - x k) atTop (𝓝 0)

/-- SAKKT-regularity, Definition 4.3: the map `x ↦ N_{Ω(x,0)}(x)` is outer semicontinuous at
`xs`. -/
def Constraints.SAKKTRegular (C : Constraints n m p) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  StrictCQ.AGP.outerLimitWithin (fun x => StrictCQ.AGP.normalCone (C.linSet x 0) x) Set.univ xs ⊆
    StrictCQ.AGP.normalCone (C.linSet xs 0) xs

end StrictCQ.SAKKT


