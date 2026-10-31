-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_pausedTour
-- name    : ContPatrol_MetricGraph_pausedTour
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:44.053988+00:00
-- url     : https://prove2.me/theorems/585eab6e-79e2-437f-95fa-1a0b36e8a652
-- title:
--   Definition 5: the leaf-pausing tour $S_2^\alpha$
-- statement:
--   Let $S_2$ be a double tour of Theorem 3. The tour $S_2^\alpha$ follows the same trajectory as $S_2$ at unit speed, starting at time $0$ from the tail of its first dart, but stops for time $\alpha$ whenever it reaches a leaf node. Its **period** $L$ is the total time of one round: the sum of the lengths of the darts, plus $\alpha$ for each arrival at a leaf node.
--
--   The randomized periodic extension of $S_2^\alpha$ is the Patroller's optimal strategy in Theorem 6.
--
--   **Formalization Note** The tour is written as a first dart followed by a list of darts. Outside $[0,L]$ the function is constant; only its values on $[0,L]$ enter, through the periodic extension.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Definition 5, p.14

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_Point

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- The position at time `s` of a unit-speed traversal of the dart `d`: its tail for `s ≤ 0`, the
point at distance `s` from the tail along the edge for `0 < s < λ(e)`, and its head for
`s ≥ λ(e)`. -/
noncomputable def dartPos (G : MetricGraph V E) (d : E × Bool) (s : ℝ) : G.Point :=
  if h : 0 < s ∧ s < G.len d.1 then
    Sum.inr ⟨d.1, if d.2 then ⟨s, h.1, h.2⟩ else ⟨G.len d.1 - s, by linarith [h.2], by linarith [h.1]⟩⟩
  else if s ≤ 0 then Sum.inl (G.tail d) else Sum.inl (G.head d)

/-- The time spent on a dart by the leaf-pausing tour: its length, plus a stop of `α` at its head
if the head is a leaf node (degree 1). -/
def segDur [Fintype E] [DecidableEq V] (G : MetricGraph V E) (α : ℝ) (d : E × Bool) : ℝ :=
  G.len d.1 + if G.deg (G.head d) = 1 then α else 0

/-- The position at time `t` of the leaf-pausing walk along the darts `d :: ds`, started at the
tail of `d` at time `0`; after the last dart it stays at that dart's head. -/
noncomputable def walkPos [Fintype E] [DecidableEq V] (G : MetricGraph V E) (α : ℝ) :
    E × Bool → List (E × Bool) → ℝ → G.Point
  | d, [], t => G.dartPos d t
  | d, d' :: ds, t =>
      if t < G.segDur α d then G.dartPos d t else walkPos G α d' ds (t - G.segDur α d)

/-- **The leaf-pausing tour S₂^α (Definition 5).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Definition 5,
p.14: "Suppose S2 is a tour given by Theorem 3. We denote by S2^α the tour that follows the same
trajectory as S2 but stops for time α whenever it reaches a leaf node."

For the closed dart walk `S₂ = d :: ds`, `G.pausedTour α d ds : ℝ → Q` traverses the darts in
order at unit speed starting at time `0` from the tail of `d`, stopping for time `α` at the head of
each dart that is a leaf node. Its period is `G.pausedPeriod α (d :: ds)`, the sum of the dart
lengths and of `α` for each arrival at a leaf.

**Formalization Note.** The tour is written as `d :: ds` so that the first dart (the start point)
is explicit. Outside `[0, period]` the function is constant (the start point before time 0, the
last head afterwards); only its values on `[0, period]` are used, through the periodic extension
of Definition 4. -/
noncomputable def pausedTour [Fintype E] [DecidableEq V] (G : MetricGraph V E) (α : ℝ) (d : E × Bool)
    (ds : List (E × Bool)) : ℝ → G.Point :=
  G.walkPos α d ds

/-- The period `L` of the leaf-pausing tour: the total time of one round of `S₂^α`. -/
def pausedPeriod [Fintype E] [DecidableEq V] (G : MetricGraph V E) (α : ℝ)
    (w : List (E × Bool)) : ℝ :=
  (w.map (G.segDur α)).sum

end MetricGraph

end ContPatrol


