-- Prove2me | Definitions.Def_cubic_p3_partition_external_boundary
-- name    : cubic_p3_partition_external_boundary
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-16T10:15:58.581774+00:00
-- url     : https://prove2.me/theorems/87f4a2d3-06e6-4d7a-b7dc-3b45653d318d
-- title:
--   External vertex boundary of a finite vertex set
-- statement:
--   Defines the external vertex boundary $N(Q)\setminus Q$ of a finite vertex set in a simple graph.
-- source:
--   Derived formal interface for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29.

import Definitions.Def_cubic_p3_partition_models

namespace R03ThreeVertexSeparatorCandidate

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The external vertex boundary of a finite set. -/
noncomputable def externalBoundary
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V) : Finset V :=
  Q.biUnion (fun v => G.neighborFinset v) \ Q


end R03ThreeVertexSeparatorCandidate


