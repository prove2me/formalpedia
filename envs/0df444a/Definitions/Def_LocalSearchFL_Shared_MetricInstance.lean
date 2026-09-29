-- Prove2me | Definitions.Def_LocalSearchFL_Shared_MetricInstance
-- name    : LocalSearchFL_Shared_MetricInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:08:29.116371+00:00
-- url     : https://prove2.me/theorems/4e07d5c2-531e-4905-bd84-fdab3b93a6d8
-- title:
--   Metric instance: clients, facilities, and a symmetric nonnegative distance with the triangle inequality
-- statement:
--   This file fixes the input of the metric facility location problems of Arya et al.
--
--   We are given a finite set $C$ of **clients** and a finite set $F$ of **facilities**, together with a distance $d(x,y)$ between any two points $x, y \in C \cup F$. The distance is required to be
--
--   1. nonnegative: $d(x,y) \ge 0$;
--   2. symmetric: $d(x,y) = d(y,x)$;
--   3. subject to the triangle inequality: $d(x,z) \le d(x,y) + d(y,z)$.
--
--   The cost of serving client $j \in C$ by facility $i \in F$ is
--   $$c_{ji} = d(j,i).$$
--
--   Every statement of the k-median missions is about such an instance. The distance is defined between all pairs of points, not only between clients and facilities, because the analysis of local search applies the triangle inequality along paths that alternate between clients and facilities.
--
--   Used by two missions of this paper: 01-kmedian-swap (single-swap k-median, §3.1–3.2; the instance of §2, pp. 546–547) and 02-kmedian-multiswap (p-swap k-median, §3.3–3.4; the instance of §2, pp. 546–547).
--
--   **Formalization Note** Clients and facilities are types `Cl` and `Fa`; the distance lives on the disjoint union `Cl ⊕ Fa`, and `c j i` abbreviates `d (inl j) (inr i)`. The axiom $d(x,x) = 0$ is not imposed, since the paper neither states nor uses it (positive self-distances are allowed); finiteness of $C$ and $F$ is imposed where it is needed, by `Fintype` instances in the statements.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, pp. 546–547, §2

import Mathlib

namespace LocalSearchFL.Shared

/-- A **metric instance** of the facility location problems (Arya et al. 2004, §2, pp. 546–547):
a finite set of clients `Cl`, a finite set of facilities `Fa`, and a distance `d` on the disjoint
union `Cl ⊕ Fa` that is nonnegative, symmetric and satisfies the triangle inequality. The distance
is defined between any two points (client–facility, client–client, facility–facility) because the
analysis applies the triangle inequality along client–facility–client–facility paths.
`d x x = 0` is not assumed. -/
structure MetricInstance (Cl Fa : Type) where
  /-- The distance between two points of `Cl ⊕ Fa`. -/
  d : Cl ⊕ Fa → Cl ⊕ Fa → ℝ
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The service cost `c_{ji}` of serving client `j` by facility `i`: the distance between them. -/
def MetricInstance.c {Cl Fa : Type} (I : MetricInstance Cl Fa) (j : Cl) (i : Fa) : ℝ :=
  I.d (Sum.inl j) (Sum.inr i)

end LocalSearchFL.Shared


