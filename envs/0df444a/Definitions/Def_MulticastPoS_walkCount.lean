-- Prove2me | Definitions.Def_MulticastPoS_walkCount
-- name    : MulticastPoS_walkCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:53.66219+00:00
-- url     : https://prove2.me/theorems/d34cb4a6-8ef9-4097-ae12-5228e318fdee
-- title:
--   Number of players whose walk uses an edge
-- statement:
--   For a family of walks $(W_i)_{i}$ in $G$, one per player, and an edge $f$, the count
--
--   $$
--   \sum_i \mathbf 1[f\in W_i]
--   $$
--
--   is the number of players whose walk traverses $f$ at least once. With $W_i=L_i$ the local segments it is $A_f$; with $W_i$ the copied tail of player $i$ (the representative's path, or the empty walk for the residual group) it is $D_f$.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 5.1, p.9

import Mathlib

namespace MulticastPoS

/-- The number of players whose walk uses an edge (Huang–Yuan, *An O(log log n) Upper Bound on
the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript
(sha256 dd0e08d0…f6d4), Section 5.1, p.9): for a family of walks `W i`, the count
`Σᵢ 1[f ∈ Wᵢ]`. With `W i = Lᵢ` (the local segments) this is `A_f`; with `W i` the copied tail
of player `i` (the representative's path, or the empty walk) it is `D_f`. -/
def walkCount {V ι : Type*} [Fintype ι] [DecidableEq V] {G : SimpleGraph V} {a b : ι → V}
    (W : ∀ i, G.Walk (a i) (b i)) (f : Sym2 V) : ℕ :=
  (Finset.univ.filter (fun i => f ∈ (W i).edges)).card

end MulticastPoS


