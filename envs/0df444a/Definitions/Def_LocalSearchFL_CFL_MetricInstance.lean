-- Prove2me | Definitions.Def_LocalSearchFL_CFL_MetricInstance
-- name    : LocalSearchFL_CFL_MetricInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:19:51.038378+00:00
-- url     : https://prove2.me/theorems/3abe6fec-5fd8-461b-8fab-2777c89b6a97
-- title:
--   Metric instance: clients, facilities, and a symmetric nonnegative distance with the triangle inequality
-- statement:
--   This file fixes the input of the metric facility location problems of Arya et al.
--
--   We are given a set $C$ of **clients** and a set $F$ of **facilities**, together with a distance $d(x,y)$ between any two points $x, y \in C \cup F$. The distance is required to be
--
--   1. nonnegative: $d(x,y) \ge 0$;
--   2. symmetric: $d(x,y) = d(y,x)$;
--   3. subject to the triangle inequality: $d(x,z) \le d(x,y) + d(y,z)$.
--
--   The cost of serving client $j \in C$ by (a copy of) facility $i \in F$ is
--   $$c_{ji} = d(j,i),$$
--   and the distance between two facilities $i, i'$ is $c_{ii'} = d(i,i')$.
--
--   Every statement of the mission is about such an instance. Distances between facilities enter the analysis of the capacitated problem directly (the quantities $c_{ss'}$ and $c_{so}$), which is why the distance is defined on all of $C \cup F$ and not only between clients and facilities.
--
--   **Formalization Note** Clients and facilities are types `Cl` and `Fa`; the distance lives on the disjoint union `Cl ⊕ Fa`, `c j i` abbreviates `d (inl j) (inr i)` and `cf i i'` abbreviates `d (inr i) (inr i')`. The axiom $d(x,x) = 0$ is not imposed, since the paper neither states nor uses it. Finiteness of $C$ is imposed in the statements by a `Fintype` instance.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, pp. 546–547, §2

import Mathlib

namespace LocalSearchFL.CFL

/-- A **metric instance** of the facility location problems (Arya et al. 2004, §2, pp. 546–547):
a set of clients `Cl`, a set of facilities `Fa`, and a distance `d` on the disjoint union
`Cl ⊕ Fa` that is nonnegative, symmetric and satisfies the triangle inequality. The distance is
defined between any two points (client–facility, client–client, facility–facility) because the
analysis of §5 uses facility–facility distances `c_{ss'}` and `c_{so}` and applies the triangle
inequality through clients. `d x x = 0` is not assumed. -/
structure MetricInstance (Cl Fa : Type) where
  /-- The distance between two points of `Cl ⊕ Fa`. -/
  d : Cl ⊕ Fa → Cl ⊕ Fa → ℝ
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The service cost `c_{ji}` of serving client `j` by (a copy of) facility `i`. -/
def MetricInstance.c {Cl Fa : Type} (I : MetricInstance Cl Fa) (j : Cl) (i : Fa) : ℝ :=
  I.d (Sum.inl j) (Sum.inr i)

/-- The distance `c_{ii'}` between two facilities. -/
def MetricInstance.cf {Cl Fa : Type} (I : MetricInstance Cl Fa) (i i' : Fa) : ℝ :=
  I.d (Sum.inr i) (Sum.inr i')

end LocalSearchFL.CFL


