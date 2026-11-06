-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
-- name    : QEC_Locality_SeparatorProfile_EdgeDivision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:06:59.027303+00:00
-- url     : https://prove2.me/theorems/33fb43f2-e64b-48ce-a7b3-0dc9a82e4844
-- title:
--   Edge Division
-- statement:
--   Definitions and structural lemmas for Edge Division, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
namespace QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def reverseDirectedEdge (edge : ι × ι) : ι × ι :=
  (edge.2, edge.1)
noncomputable def finiteVertexIndex (x : ι) : Fin (Fintype.card ι) :=
  Fintype.equivFin ι x
noncomputable def canonicalEdgeOwner (edge : ι × ι) : ι × ι :=
  if finiteVertexIndex edge.1 < finiteVertexIndex edge.2 then edge
  else reverseDirectedEdge edge
noncomputable def canonicalEdgeRepresentatives (G : ConnectivityGraph ι) :
    Finset (ι × ι) :=
  (directedEdgeFinset G).image canonicalEdgeOwner
noncomputable def canonicalEdgeRegion (G : ConnectivityGraph ι)
    (owner : ι × ι) : Finset (ι × ι) :=
  (directedEdgeFinset G).filter fun edge => canonicalEdgeOwner edge = owner
noncomputable def totalEdgeRegion (G : ConnectivityGraph ι) (_ : Unit) :
    Finset (ι × ι) :=
  directedEdgeFinset G
def totalEdgeActive : Finset Unit :=
  {()}
def HasSingleUndirectedEdge (G : ConnectivityGraph ι) (x y : ι) : Prop :=
  G.adjacent x y ∧
    ∀ ⦃a b : ι⦄, G.adjacent a b →
      (a = x ∧ b = y) ∨ (a = y ∧ b = x)
def emptyEdgeRegion (_ : Unit) : Finset (ι × ι) :=
  ∅
def emptyEdgeActive : Finset Unit :=
  ∅
end QEC.Locality


