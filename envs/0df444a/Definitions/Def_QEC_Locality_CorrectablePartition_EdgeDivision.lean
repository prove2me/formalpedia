-- Prove2me | Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
-- name    : QEC_Locality_CorrectablePartition_EdgeDivision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:04:58.567883+00:00
-- url     : https://prove2.me/theorems/33997f1b-09f0-4fb5-aea2-1e1203399572
-- title:
--   Edge Division
-- statement:
--   Definitions and structural lemmas for Edge Division, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
set_option autoImplicit false
namespace QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def IsSpanningSubgraph (H G : ConnectivityGraph ι) : Prop :=
  ∀ ⦃x y : ι⦄, H.adjacent x y → G.adjacent x y
noncomputable def directedEdgeFinset (G : ConnectivityGraph ι) : Finset (ι × ι) := by
  classical
  exact Finset.univ.filter fun edge => decide (G.adjacent edge.1 edge.2)
def edgeIncidentVertices (edges : Finset (ι × ι)) : Finset ι :=
  edges.biUnion fun edge => {edge.1, edge.2}
def IsEdgeDivision {m : Type w} [DecidableEq m]
    (G : ConnectivityGraph ι) (regions : m → Finset (ι × ι))
    (active : Finset m) : Prop :=
  (∀ i, i ∈ active → regions i ⊆ directedEdgeFinset G) ∧
    (∀ i, i ∈ active → ∀ x y, (x, y) ∈ regions i ↔ (y, x) ∈ regions i) ∧
    ∀ edge, edge ∈ directedEdgeFinset G →
      ∃! i, i ∈ active ∧ edge ∈ regions i
noncomputable def edgeDivisionSharedBoundary {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m) : Finset ι := by
  classical
  exact Finset.univ.filter fun x => decide
    (∃ i ∈ active, ∃ j ∈ active, i ≠ j ∧
      x ∈ edgeIncidentVertices (regions i) ∧
      x ∈ edgeIncidentVertices (regions j))
noncomputable def edgeDivisionInterior {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m) (i : m) : Finset ι :=
  edgeIncidentVertices (regions i) \ edgeDivisionSharedBoundary regions active
noncomputable def graphIsolatedVertices (G : ConnectivityGraph ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun x => decide (∀ y, ¬ G.adjacent x y)
end QEC.Locality


