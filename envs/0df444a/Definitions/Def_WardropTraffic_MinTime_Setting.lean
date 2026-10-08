-- Prove2me | Definitions.Def_WardropTraffic_MinTime_Setting
-- name    : WardropTraffic_MinTime_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:37.072517+00:00
-- url     : https://prove2.me/theorems/585006ec-11a4-44e1-b7b8-3fcda8045390
-- title:
--   pp. 344–346 — D alternative routes, journey time (22) tᵢ = bᵢ/(1 − qᵢ/pᵢ), feasible splits, Z = Σqᵢtᵢ, T = Z/Q (25)–(26), criterion (2)
-- statement:
--   A flow of traffic $Q$ has the choice of $D$ alternative routes $i = 1, \dots, D$ from a given origin to a given destination. Route $i$ is described by two positive constants: $b_i$, the journey time on route $i$ when no additional traffic uses it, and $p_i$, the additional flow at which the route's speed would fall to zero.
--
--   1. **Journey time (22).** When an additional flow $x$ follows route $i$, its journey time is
--   $$
--   t_i(x) = \frac{b_i}{1 - x/p_i}.
--   $$
--   2. **Feasible split.** A vector $q = (q_1, \dots, q_D)$ is a feasible split of $Q$ when $0 \le q_i < p_i$ for every $i$ and $\sum_{i=1}^D q_i = Q$.
--   3. **Additional vehicles en route.** $z_i = q_i t_i(q_i)$ is the average number of additional vehicles on route $i$ at an instant, and $Z(q) = \sum_{i=1}^D q_i\, t_i(q_i)$ is their total.
--   4. **Average journey time (25)–(26).**
--   $$
--   T(q) = \sum_{i=1}^{D} \frac{q_i t_i(q_i)}{Q} = \frac{Z(q)}{Q}.
--   $$
--   5. **Criterion (2), minimum average time.** A split $q$ satisfies criterion (2) when it is feasible and $T(q) \le T(z)$ for every feasible split $z$ of $Q$.
--   6. **The routes below $\varepsilon$.** $U(\varepsilon) = \{ i : b_i < \varepsilon \}$, the set the paper calls "the first $j$ routes" after labelling the routes so that $b_1 < b_2 < \dots < b_D$ and choosing $j$ with $b_j < \varepsilon < b_{j+1}$.
--
--   Criterion (2) is Wardrop's second principle, the system optimum: it minimizes the vehicle-hours spent on the journey.
--
--   **Formalization Note** The bound $q_i < p_i$ is the range in which (22) is a positive, finite journey time (positive speed). Without it Lean's convention $b_i/0 = 0$ would give a route at capacity journey time $0$, and a "minimum" could put flow there for free; the bound applies to the competitors $z$ as well. The labelling $b_1 < \dots < b_D$ is not assumed; $U(\varepsilon)$ replaces "the first $j$ routes", which also covers ties. The same route model is defined in mission II of this series (namespace `WardropTraffic.EqualTimes`); it is restated here because unpublished drafts cannot import each other.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 344, (22) and the conditions qᵢ ≥ 0, Σqᵢ = Q; p. 345, criterion (2); p. 346, (25)–(26)

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

namespace WardropTraffic.MinTime

/-- `Z = ∑ z_i = ∑ q_i t_i`, the total number of additional vehicles on the routes. -/
noncomputable def totalExtra {D : ℕ} (b p : Fin D → ℝ) (q : Fin D → ℝ) : ℝ :=
  ∑ i, q i * WardropTraffic.EqualTimes.routeTime b p i (q i)

/-- The average journey time (25)–(26): `T = ∑ q_i t_i / Q = Z / Q`. -/
noncomputable def avgTime {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ) (q : Fin D → ℝ) : ℝ :=
  totalExtra b p q / Q

/-- Criterion (2): `q` is a feasible split of `Q` whose average journey time is not larger
than that of any other feasible split of `Q`. -/
def IsMinAvgTime {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ) (q : Fin D → ℝ) : Prop :=
  WardropTraffic.EqualTimes.IsFeasible p Q q ∧ ∀ z, WardropTraffic.EqualTimes.IsFeasible p Q z → avgTime b p Q q ≤ avgTime b p Q z

end WardropTraffic.MinTime


