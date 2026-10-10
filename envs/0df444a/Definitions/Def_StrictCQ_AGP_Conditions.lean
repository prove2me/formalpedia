-- Prove2me | Definitions.Def_StrictCQ_AGP_Conditions
-- name    : StrictCQ_AGP_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:29.549778+00:00
-- url     : https://prove2.me/theorems/edf06760-fbda-4cb8-a37a-5a9e0d23940a
-- title:
--   (4.1), Definition 4.1, p. 6 — the AGP(γ) condition and AGP-regularity
-- statement:
--   Let $h,g$ be the constraint data of problem (1.1) and $x^*\in\mathbb R^n$.
--
--   1. **AGP($\gamma$)** (4.1). For $\gamma\in[-\infty,0]$ and an objective $f$, the point $x^*$ satisfies AGP($\gamma$) if there is a sequence $x^k\to x^*$ such that
--   $$P_{\Omega(x^k,\gamma)}\big(x^k-\nabla f(x^k)\big)-x^k\to 0,$$
--   where $P_{\Omega(x^k,\gamma)}$ is the Euclidean projection onto the closed convex set $\Omega(x^k,\gamma)$ of (4.2).
--   2. **AGP-regularity** (Definition 4.1). The point $x^*$ is AGP-regular if the set-valued map $(x,\varepsilon)\in\mathbb R^n\times\mathbb R^n\rightrightarrows N_{\Omega(x,-\infty)}(x+\varepsilon)$ is outer semicontinuous at $(x^*,0)$:
--   $$\limsup_{(x,\varepsilon)\to(x^*,0)}N_{\Omega(x,-\infty)}(x+\varepsilon)\subset N_{\Omega(x^*,-\infty)}(x^*).$$
--
--   AGP is a sequential optimality condition used as a stopping criterion for inexact-restoration methods; AGP-regularity is the constraint qualification that Theorem 4.2 identifies as the weakest one under which AGP implies KKT.
--
--   **Formalization Note** "$P(z^k)-x^k\to0$" is stated as: there are points $y^k$ that are projections of $x^k-\nabla f(x^k)$ onto $\Omega(x^k,\gamma)$ with $y^k-x^k\to0$; since these sets are nonempty, closed and convex, the projection exists and is unique, so this is equivalent. The outer limit is the sequential one of (1.6). The equality $N_{\Omega(x^*,-\infty)}(x^*)=L_\Omega(x^*)^\circ$ that the paper appends to Definition 4.1 is not part of the definition; it is a separate theorem of the mission. The predicate accepts any $\gamma$, but theorems use it only for $\gamma\in[-\infty,0)$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 6, (4.1), (4.2), Definition 4.1, (4.5), (4.6)

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

variable {n m p : ℕ}

/-- AGP(γ) at `xs` for the objective `f`, (4.1): there are `xᵏ → xs` and projections
`yᵏ = P_{Ω(xᵏ,γ)}(xᵏ - ∇f(xᵏ))` with `yᵏ - xᵏ → 0`. -/
def Constraints.AGP (C : Constraints n m p) (γ : EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ x y : ℕ → EuclideanSpace ℝ (Fin n), Tendsto x atTop (𝓝 xs) ∧
    (∀ k, IsProj (C.linSet (x k) γ) (x k - gradient f (x k)) (y k)) ∧
    Tendsto (fun k => y k - x k) atTop (𝓝 0)

/-- AGP-regularity, Definition 4.1: the map `(x, ε) ↦ N_{Ω(x,-∞)}(x + ε)` is outer semicontinuous
at `(xs, 0)`. -/
def Constraints.AGPRegular (C : Constraints n m p) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  outerLimitWithin
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        normalCone (C.linSet q.1 ⊥) (q.1 + q.2))
      Set.univ (xs, 0) ⊆
    normalCone (C.linSet xs ⊥) xs

end StrictCQ.AGP


