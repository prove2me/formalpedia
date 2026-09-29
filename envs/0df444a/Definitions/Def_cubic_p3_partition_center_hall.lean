-- Prove2me | Definitions.Def_cubic_p3_partition_center_hall
-- name    : cubic_p3_partition_center_hall
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-16T09:19:32.918553+00:00
-- url     : https://prove2.me/theorems/44432a28-3572-496c-9937-c725460aea74
-- title:
--   Center-set Hall predicates for P3-factors
-- statement:
--   Defines the one-third-size center condition and the two-fold external-neighbour Hall condition used to characterize non-induced $P_3$-factors in finite simple graphs.
-- source:
--   Derived formal interface for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section

variable {V : Type u}

/-- A finite set has one third of the ambient vertices. -/
def p12CenterSize [Fintype V] (C : Finset V) : Prop :=
  3 * C.card = Fintype.card V

/-- The vertices outside `C` adjacent to at least one member of `A`. -/
noncomputable def p12ExternalNeighborFinset [Fintype V] (G : SimpleGraph V)
    (C A : Finset V) : Finset V := by
  classical
  exact A.biUnion (fun v => G.neighborFinset v \ C)

/-- The two-fold Hall condition for the center set `C`. -/
def p12CenterHall [Fintype V] (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ A : Finset V, A ⊆ C →
    2 * A.card ≤ (p12ExternalNeighborFinset G C A).card

end

end CubicP3Partition


