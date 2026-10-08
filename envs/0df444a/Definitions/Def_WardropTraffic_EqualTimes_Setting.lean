-- Prove2me | Definitions.Def_WardropTraffic_EqualTimes_Setting
-- name    : WardropTraffic_EqualTimes_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:07.96908+00:00
-- url     : https://prove2.me/theorems/726d662c-4c66-4049-a7e8-94cddfe26038
-- title:
--   pp. 344–345 — D alternative routes, journey time (22) tᵢ = bᵢ/(1 − qᵢ/pᵢ), feasible splits, equal-times criterion (1)
-- statement:
--   A flow of traffic $Q$ has the choice of $D$ alternative routes $i = 1, \dots, D$ from a given origin to a given destination. Route $i$ is described by two positive constants: $b_i$, the journey time on route $i$ when no additional traffic uses it, and $p_i$, the additional flow at which the route's speed would fall to zero.
--
--   1. **Journey time (22).** When an additional flow $x$ follows route $i$, its journey time is
--   $$
--   t_i(x) = \frac{b_i}{1 - x/p_i}.
--   $$
--   2. **Feasible split.** A vector $q = (q_1, \dots, q_D)$ is a feasible split of $Q$ when $0 \le q_i < p_i$ for every $i$ and $\sum_{i=1}^D q_i = Q$.
--   3. **Equal-times criterion (1).** A feasible split $q$ of $Q$ satisfies the equal-times criterion with common time $t$ when every route actually used ($q_i > 0$) has journey time $t_i(q_i) = t$, and every unused route ($q_i = 0$) has $t \le b_i$: the time $b_i$ that a single vehicle would experience on it is not less than $t$.
--   4. **Strict variant.** The same criterion with $t < b_i$ on unused routes, as printed; it implies the weak form, and the file records this implication.
--   5. **The routes below $t$.** $U(t) = \{ i : b_i < t \}$, the set the paper calls "the first $j$ routes" after labelling the routes so that $b_1 < b_2 < \dots < b_D$.
--
--   Criterion (1) is Wardrop's first principle: in equilibrium no driver can reduce their journey time by choosing another route.
--
--   **Formalization Note** The bound $q_i < p_i$ is the range in which (22) is a positive, finite journey time (positive speed); without it Lean's convention $b_i/0 = 0$ would give a route at capacity journey time $0$. The criterion uses the weak comparison $t \le b_i$ on unused routes: the paper's own case split "$b_j < t \not> b_{j+1}$" allows $t = b_{j+1}$, and with the strict form a split need not exist at the boundary values of $Q$. The labelling $b_1 < \dots < b_D$ is not assumed; $U(t)$ replaces "the first $j$ routes", which also covers ties.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 344, (22) and the conditions qᵢ ≥ 0, Σqᵢ = Q; p. 345, criterion (1)

import Mathlib

namespace WardropTraffic.EqualTimes

/-- Journey time (22) on route `i` when the additional flow on it is `x`:
`t_i = b_i / (1 - x / p_i)`. -/
noncomputable def routeTime {D : ℕ} (b p : Fin D → ℝ) (i : Fin D) (x : ℝ) : ℝ :=
  b i / (1 - x / p i)

/-- A feasible split of the total flow `Q` over the `D` routes: every route flow is
nonnegative and below `p_i` (the range in which (22) is a positive finite journey time),
and the flows add up to `Q`. -/
def IsFeasible {D : ℕ} (p : Fin D → ℝ) (Q : ℝ) (q : Fin D → ℝ) : Prop :=
  (∀ i, 0 ≤ q i ∧ q i < p i) ∧ ∑ i, q i = Q

/-- Criterion (1), weak form: the split `q` of `Q` is feasible, every used route has
journey time `t`, and on every unused route the time `b_i` of a single vehicle is at
least `t`. -/
def IsEqualTimes {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ) (q : Fin D → ℝ) (t : ℝ) : Prop :=
  IsFeasible p Q q ∧ (∀ i, 0 < q i → routeTime b p i (q i) = t) ∧ (∀ i, q i = 0 → t ≤ b i)

/-- Criterion (1) as printed, with the strict comparison `t < b_i` on unused routes. -/
def IsEqualTimesStrict {D : ℕ} (b p : Fin D → ℝ) (Q : ℝ) (q : Fin D → ℝ) (t : ℝ) : Prop :=
  IsFeasible p Q q ∧ (∀ i, 0 < q i → routeTime b p i (q i) = t) ∧ (∀ i, q i = 0 → t < b i)

/-- The strict form of criterion (1) implies the weak form. -/
theorem IsEqualTimesStrict.isEqualTimes {D : ℕ} {b p : Fin D → ℝ} {Q : ℝ} {q : Fin D → ℝ}
    {t : ℝ} (h : IsEqualTimesStrict b p Q q t) : IsEqualTimes b p Q q t :=
  ⟨h.1, h.2.1, fun i hi => le_of_lt (h.2.2 i hi)⟩

/-- The routes whose empty-route time `b_i` is below `t` (the paper's "first j routes"
when `b_1 < b_2 < ⋯ < b_D`). -/
noncomputable def usedSet {D : ℕ} (b : Fin D → ℝ) (t : ℝ) : Finset (Fin D) :=
  Finset.univ.filter (fun i => b i < t)

end WardropTraffic.EqualTimes


