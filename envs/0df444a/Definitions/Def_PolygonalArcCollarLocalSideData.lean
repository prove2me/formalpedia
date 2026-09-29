-- Prove2me | Definitions.Def_PolygonalArcCollarLocalSideData
-- name    : PolygonalArcCollarLocalSideData
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T23:51:41.073907+00:00
-- url     : https://prove2.me/theorems/369a3d0e-577e-4587-a61e-231b68b1727e
-- title:
--   PolygonalArcCollarLocalSideData
-- statement:
--   Structural local side data for a polygonal-arc collar: open vertex collars and left/right side pieces with connectivity, disjointness, attachment, and carrier-control properties.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarLocalSideData.lean#L1-142

import Definitions.Def_PolygonalArcCollarOrientedSeparatedTubeData
import Definitions.Def_PolygonalArcCollarVertexLocalPieceData

-- [TABLET NODE: PolygonalArcCollarLocalSideData]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarLocalSideData.lean#L1-142
structure PolygonalArcCollarLocalSideData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins orientedTubes.toPolygonalArcCollarSeparatedTubeData) where
  vertexCollar : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  leftSidePiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  rightSidePiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  vertexCollar_open : ∀ i, IsOpen (vertexCollar i)
  leftSidePiece_open : ∀ i, IsOpen (leftSidePiece i)
  rightSidePiece_open : ∀ i, IsOpen (rightSidePiece i)
  vertexCollar_subset_vertexDisk :
    ∀ i, vertexCollar i ⊆ vertexLocalPieces.vertexDisk i
  interior_vertexCollar_eq_vertexDisk :
    ∀ i, 0 < i.1 → i.1 + 1 < γ.vertices.length →
      vertexCollar i = vertexLocalPieces.vertexDisk i
  endpoint_vertexCollar_omits_vertex :
    ∀ i, (i.1 = 0 ∨ i.1 + 1 = γ.vertices.length) →
      γ.vertices[i.1] ∉ vertexCollar i
  vertexCollar_subset_eta_neighborhood :
    ∀ i, ∀ z ∈ vertexCollar i, ∃ p ∈ γ.carrier, dist z p < η
  vertexCollar_carrier_subset_incident_segments :
    ∀ i, ∀ z ∈ vertexCollar i, z ∈ γ.carrier →
      ∃ j : ℕ, ∃ hj : j + 1 < γ.vertices.length,
        z ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] ∧
          (i.1 = j ∨ i.1 = j + 1)
  outgoing_germ_subset_vertexCollar :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo (0 : ℝ)
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) ⊆
        vertexCollar ⟨j, Nat.lt_of_succ_lt hj⟩
  incoming_germ_subset_vertexCollar :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        vertexCollar ⟨j + 1, hj⟩
  outgoing_germ_subset_closure_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo (0 : ℝ)
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) ⊆
        closure (leftSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩)
  outgoing_germ_subset_closure_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo (0 : ℝ)
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) ⊆
        closure (rightSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩)
  incoming_germ_subset_closure_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        closure (leftSidePiece ⟨j + 1, hj⟩)
  incoming_germ_subset_closure_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        closure (rightSidePiece ⟨j + 1, hj⟩)
  interior_vertex_mem_closure_leftSidePiece :
    ∀ i, 0 < i.1 → i.1 + 1 < γ.vertices.length →
      γ.vertices[i.1] ∈ closure (leftSidePiece i)
  interior_vertex_mem_closure_rightSidePiece :
    ∀ i, 0 < i.1 → i.1 + 1 < γ.vertices.length →
      γ.vertices[i.1] ∈ closure (rightSidePiece i)
  leftSidePiece_subset_vertexCollar :
    ∀ i, leftSidePiece i ⊆ vertexCollar i
  rightSidePiece_subset_vertexCollar :
    ∀ i, rightSidePiece i ⊆ vertexCollar i
  leftSidePiece_connected : ∀ i, IsConnected (leftSidePiece i)
  rightSidePiece_connected : ∀ i, IsConnected (rightSidePiece i)
  leftSidePiece_disjoint_carrier :
    ∀ i, Disjoint (leftSidePiece i) γ.carrier
  rightSidePiece_disjoint_carrier :
    ∀ i, Disjoint (rightSidePiece i) γ.carrier
  local_sidePieces_disjoint :
    ∀ i, Disjoint (leftSidePiece i) (rightSidePiece i)
  leftHalf_disjoint_carrier :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      Disjoint
        (orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj)
        γ.carrier
  rightHalf_disjoint_carrier :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      Disjoint
        (orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj)
        γ.carrier
  leftHalf_disjoint_rightHalf :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        Disjoint
          (orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj)
          (orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf k hk)
  leftHalf_inter_vertexCollar_subset_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length),
        orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj ∩
          vertexCollar i ⊆ leftSidePiece i
  rightHalf_inter_vertexCollar_subset_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length),
        orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj ∩
          vertexCollar i ⊆ rightSidePiece i
  vertexCollar_without_arc :
    ∀ i, vertexCollar i \ γ.relativeInterior =
      leftSidePiece i ∪ rightSidePiece i
  outgoingLeftAttachment_subset_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.outgoingLeftAttachment j hj ⊆
        leftSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩
  outgoingRightAttachment_subset_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.outgoingRightAttachment j hj ⊆
        rightSidePiece ⟨j, Nat.lt_of_succ_lt hj⟩
  incomingLeftAttachment_subset_leftSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.incomingLeftAttachment j hj ⊆
        leftSidePiece ⟨j + 1, hj⟩
  incomingRightAttachment_subset_rightSidePiece :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      vertexLocalPieces.incomingRightAttachment j hj ⊆
        rightSidePiece ⟨j + 1, hj⟩


