-- Prove2me | Definitions.Def_TreeStack_Branch
-- name    : TreeStack_Branch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:07:49.002859+00:00
-- url     : https://prove2.me/theorems/f030efb7-e00a-4718-8dce-3673507dcd87
-- title:
--   Branch
-- statement:
--   Definitions and structural lemmas for Branch, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean

import Mathlib
import Definitions.Def_TreeStack_Basic
set_option autoImplicit false
namespace TreeStack
structure OrientedBranch {V : Type*} [Fintype V] (T : FiniteTree V) where
  root : V
  parent : V
  adj : T.graph.Adj root parent
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
noncomputable def deletedGraph (B : OrientedBranch T) : SimpleGraph V :=
  T.graph.deleteEdges {s(B.root, B.parent)}
noncomputable def component (B : OrientedBranch T) :
    B.deletedGraph.ConnectedComponent :=
  B.deletedGraph.connectedComponentMk B.root
noncomputable def vertices (B : OrientedBranch T) : Finset V := by
  classical
  exact B.component.supp.toFinset
noncomputable def card (B : OrientedBranch T) : ℕ :=
  B.vertices.card
structure Child (B : OrientedBranch T) where
  vertex : V
  adj : T.graph.Adj B.root vertex
  ne_parent : vertex ≠ B.parent
def childBranch (B : OrientedBranch T) (c : B.Child) : OrientedBranch T where
  root := c.vertex
  parent := B.root
  adj := c.adj.symm
end OrientedBranch
end TreeStack


