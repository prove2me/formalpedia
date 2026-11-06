-- Prove2me | Definitions.Def_BinaryQueryLB_IsChart
-- name    : BinaryQueryLB_IsChart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:49.832941+00:00
-- url     : https://prove2.me/theorems/2a79b1d1-78ff-48f2-97e2-6854e76670e5
-- title:
--   First-order chart
-- statement:
--   A **first-order chart** $G$ assigns to every $f\in F(d,R,M)$ and every $y\in X$ a subgradient
--   $$
--   G(f,y)\in\partial f(y)=\{g\in\mathbb R^d:\ f(x)-f(y)\ge\langle g,x-y\rangle\ \text{for all }x\in\mathbb R^d\}.
--   $$
--   The chart fixes which subgradient the oracle reports, so repeated queries at the same point see the same subgradient.
--
--   **Formalization Note** $\partial f(y)$ is the platform's subdifferential `ShorNonsmooth.Subdiff.subdifferential` with domain all of $\mathbb R^d$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.2, p.11

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Definitions.Def_BinaryQueryLB_ProblemClass
import Definitions.Def_BinaryQueryLB_Chart
import Definitions.Def_BinaryQueryLB_Box

namespace BinaryQueryLB

/-- **First-order chart (Definition 2.2).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.2, p.11: "A first-order chart
`G` assigns to every `f ∈ F(d, R, M)` and every `y ∈ X` a subgradient `G(f, y) ∈ ∂f(y)`."

**Formalization Note.** `∂f(y)` is the (global) subdifferential of the convex `f : ℝ^d → ℝ`,
`ShorNonsmooth.Subdiff.subdifferential Set.univ f y = {g | ∀ x, f x − f y ≥ ⟨g, x − y⟩}`
(platform definition 3f41475b, reused with domain `Set.univ`). -/
def IsChart (d : ℕ) (R M : ℝ) (G : Chart d) : Prop :=
  ∀ f ∈ ProblemClass d R M, ∀ y ∈ Box d R,
    G f y ∈ ShorNonsmooth.Subdiff.subdifferential Set.univ f y

end BinaryQueryLB


