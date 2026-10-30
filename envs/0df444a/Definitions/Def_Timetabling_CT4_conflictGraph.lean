-- Prove2me | Definitions.Def_Timetabling_CT4_conflictGraph
-- name    : Timetabling_CT4_conflictGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:37:07.796258+00:00
-- url     : https://prove2.me/theorems/01e44613-243f-4586-8a07-ce9e5efb0ad0
-- title:
--   The conflict graph $G$ of Proposition 2.4
-- statement:
--   For a CT4 instance with $n$ teachers, the **conflict graph** $G$ has the $2n$ nodes $x_1, \bar x_1, \dots, x_n, \bar x_n$; $x_j$ and $\bar x_j$ correspond to the two possible schedules of teacher $t_j$. Two distinct nodes $u$, $w$ are linked when
--
--   1. they belong to the same teacher (in particular $x_j$ and $\bar x_j$ are linked), or
--   2. their schedules are not compatible: they share a slot $(i, k)$, i.e. both teachers would meet class $c_i$ at period $k$, violating (13).
--
--   Constraint (13) is the only constraint of CT4 between two teachers, so sharing a slot is exactly incompatibility. A timetable is then a stable set of $n$ nodes of $G$.
--
--   **Formalization Note** Nodes are `Fin n × Bool` with `(j, true)` $= x_j$; a decidability instance for adjacency is included. For the instance of Table 1 the graph has the ten edges forced by the printed schedules; Figure 2 draws the same graph with the labels $x_2$, $\bar x_2$ exchanged.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "We construct a graph G with 2n nodes ... we link 2 nodes in G if the corresponding schedules are not compatible (in particular, nodes x_j and x̄_j are linked)"; Figure 2, p. 155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_sched

namespace Timetabling.CT4

/-- **The conflict graph `G` of the proof of Proposition 2.4.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"We construct a graph G with 2n nodes (where n is the number of teachers) as follows: For teacher
t_j introduce 2 nodes x_j, x̄_j corresponding to his possible schedules; we link 2 nodes in G if
the corresponding schedules are not compatible (in particular, nodes x_j and x̄_j are linked)."

Nodes are `Fin n × Bool`. Two distinct nodes `u`, `w` are adjacent when they belong to the same
teacher (`u.1 = w.1`), or when their schedules `sched I u`, `sched I w` share a slot `(i, k)`:
both teachers would meet class `c_i` at period `k`, which violates (13).

**Formalization Note.** Constraint (13) is the only constraint of CT4 that involves two
teachers, so sharing a slot is exactly incompatibility. A decidability instance is provided for
the adjacency relation. -/
def conflictGraph {m n p : ℕ} (I : Instance m n p) : SimpleGraph (Fin n × Bool) where
  Adj u w := u ≠ w ∧ (u.1 = w.1 ∨ ∃ x, x ∈ sched I u ∧ x ∈ sched I w)
  symm := ⟨fun _ _ ⟨h, h'⟩ => ⟨Ne.symm h, h'.imp Eq.symm fun ⟨x, hu, hw⟩ => ⟨x, hw, hu⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {m n p : ℕ} (I : Instance m n p) : DecidableRel (conflictGraph I).Adj := fun u w =>
  decidable_of_iff (u ≠ w ∧ (u.1 = w.1 ∨ ∃ x ∈ sched I u, x ∈ sched I w)) Iff.rfl

end Timetabling.CT4


