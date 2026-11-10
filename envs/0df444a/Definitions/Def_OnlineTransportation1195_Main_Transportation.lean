-- Prove2me | Definitions.Def_OnlineTransportation1195_Main_Transportation
-- name    : OnlineTransportation1195_Main_Transportation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:34:23.320256+00:00
-- url     : https://prove2.me/theorems/7a2e8d53-223b-4dcc-a552-3228a76a7165
-- title:
--   Capacitated transportation instances, assignments and offline optimum
-- statement:
--   A static instance consists of a real metric on $n$ labeled points, a subset $G$ of distinct garages, and natural capacities $c_g$, including zero. There are $k=\sum_{g\in G}c_g$ cars. Each arrival sequence is an arbitrary function from the $k$ arrival times to the metric points, allowing repeated locations.
--
--   Give garage $g$ exactly $c_g$ distinguishable slots. A complete feasible assignment is a bijection from cars to slots. Every feasible garage assignment lifts to such a bijection because the number of cars equals total capacity; slot identities do not affect cost. If $a$ is an assignment and $v_t$ the arrivals, define
--
--   $$\operatorname{cost}(v,a)=\sum_{t=0}^{k-1}d(v_t,a_t),\qquad \operatorname{OPT}(v)=\min_a\operatorname{cost}(v,a).$$
--
--   The minimum ranges over the nonempty finite set of slot permutations. When $k=0$, its sole assignment has zero cost. This is the common offline benchmark for all online statements. Point and time indices start at zero; neither arbitrary real metrics nor non-unit capacities are restricted.
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), §1 online transportation model, PDF / printed p. 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Mathlib

open scoped BigOperators

namespace OnlineTransportation1195.Main

/-- Static data of §1 (Anand et al., STOC 2027 submission #1195, p.1).
Only capacities on the garage set are used; zero capacities are permitted. -/
structure TransportationInstance (n : ℕ) where
  metric : MetricSpace (Fin n)
  garages : Finset (Fin n)
  capacity : {g // g ∈ garages} → ℕ

namespace TransportationInstance

variable {n : ℕ} (I : TransportationInstance n)

/-- Individual parking slots; no slot is present at a zero-capacity garage. -/
abbrev Slot := Σ g : {g // g ∈ I.garages}, Fin (I.capacity g)

/-- Total capacity, equal to the sum of the garage capacities. -/
def k : ℕ := Fintype.card I.Slot

abbrev Time := Fin I.k
abbrev Arrivals := I.Time → Fin n

/-- A permutation assigns every arrival a different slot. Since there are exactly k
cars, these represent exactly the capacity-feasible complete garage assignments,
up to the irrelevant names of slots within each garage. -/
abbrev Assignment := Equiv.Perm I.Time

noncomputable def garageOf (a : I.Assignment) (t : I.Time) : Fin n :=
  ((Fintype.equivFin I.Slot).symm (a t)).1.val

/-- The sum of original metric distances, not the length of an auxiliary path. -/
noncomputable def cost (r : I.Arrivals) (a : I.Assignment) : ℝ :=
  letI := I.metric
  ∑ t, dist (r t) (I.garageOf a t)

/-- A genuine finite minimum. The identity permutation witnesses nonemptiness,
including k=0. Every capacity-feasible garage assignment lifts to a slot permutation. -/
noncomputable def opt (r : I.Arrivals) : ℝ := by
  classical
  exact (Finset.univ.image (I.cost r)).min' (Finset.image_nonempty.mpr
    ⟨Equiv.refl I.Time, Finset.mem_univ _⟩)

end TransportationInstance
end OnlineTransportation1195.Main


