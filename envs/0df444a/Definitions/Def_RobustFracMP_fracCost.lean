-- Prove2me | Definitions.Def_RobustFracMP_fracCost
-- name    : RobustFracMP_fracCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:45.382678+00:00
-- url     : https://prove2.me/theorems/fec9d094-c2b8-4235-98d6-14d6a9f2196a
-- title:
--   Clustering cost $\mathrm{cost}_z(y)$ of a fractional center set
-- statement:
--   Let $(P,\mathrm{dist})$ be a finite metric space and $z\ge1$. For a fractional center set $y\in\mathbb R^P_{\ge0}$ with $\|y\|_1\ge1$, the **clustering cost** is the cheapest assignment cost of a feasible assignment:
--
--   $$\mathrm{cost}_z(y)=\min_{x\sim y}\sigma_z(x).$$
--
--   It is the cost part of the Power-$z$ Facility Location objective and the quantity bounded by every LMP guarantee of the mission.
--
--   **Formalization Note** The minimum is written as the infimum of the set of assignment costs of feasible assignments. For $y\ge0$ with $\sum_q y_q\ge1$ the set is nonempty and bounded below by $0$, and the infimum is attained, so it is the paper's minimum. The condition $\|y\|_1\ge1$ is not built into the definition: when no feasible assignment exists the Lean value is the junk $0$, and every statement of the mission that bounds $\mathrm{cost}_z(y)$ also asserts or assumes a condition implying $\sum_q y_q\ge1$.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Section 2, definition of cost_z(P, y), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_RobustFracMP_assignCost
import Definitions.Def_RobustFracMP_Feasible

set_option autoImplicit false

namespace RobustFracMP

/-- **Clustering cost cost_z(y) of a fractional center set.**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Section 2, p.11 (PDF p.13): "We can then define the clustering cost of a fractional center set
y ∈ ℝ^F_{≥0} with ‖y‖₁ ≥ 1 as cost_z(P, y) := min_{x∼y} σ_z(P, x)."

**Formalization Note.** The minimum is written as `sInf` of the set of assignment costs of feasible
assignments. When `y ≥ 0` and `Σ y ≥ 1` this set is nonempty, bounded below by `0`, and its infimum
is attained (a linear program over a nonempty compact polyhedron), so `sInf` is the paper's `min`.
The paper defines `cost_z(y)` only when `‖y‖₁ ≥ 1`; that condition is **not** bundled here. Outside
it the set is empty and `sInf ∅ = 0` is a junk value, so every statement of the mission that bounds
`fracCost z y` also establishes or assumes a condition implying `Σ y ≥ 1`. -/
noncomputable def fracCost {P : Type*} [Fintype P] [MetricSpace P] (z : ℕ) (y : P → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ x : P → P → ℝ, Feasible x y ∧ assignCost z x = c}

end RobustFracMP


