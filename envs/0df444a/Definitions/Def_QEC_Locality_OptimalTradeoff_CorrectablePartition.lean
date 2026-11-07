-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
-- name    : QEC_Locality_OptimalTradeoff_CorrectablePartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:07:54.812516+00:00
-- url     : https://prove2.me/theorems/43a7d735-f984-4ac4-a0d9-86eb37150363
-- title:
--   Correctable Partition
-- statement:
--   Definitions and structural lemmas for Correctable Partition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
local instance instClassicalDecidableCorrectable (p : Prop) : Decidable p :=
  Classical.propDecidable p
def daiLiGridCellCenter (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : ℝ × ℝ :=
  (origin.1 + ((cell.1 : ℝ) + 1 / 2) * w,
    origin.2 + ((cell.2 : ℝ) + 1 / 2) * w)
def daiLiGridCellClosedQubits (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : Finset ι :=
  squareQubits embedding (daiLiGridCellCenter w origin cell) (w / 2)
def daiLiGridCellClosedSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : FiniteSubsystem ι :=
  ⟨daiLiGridCellClosedQubits embedding w origin cell⟩
def daiLiGridClosedCellsContaining (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (q : ι) : Finset (ℤ × ℤ) :=
  (embedding.gridOccupiedCells w origin).filter fun cell =>
    q ∈ daiLiGridCellClosedQubits embedding w origin cell
def daiLiBadGridCells
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) : Finset (ℤ × ℤ) :=
  (embedding.gridOccupiedCells w origin).filter fun cell =>
    IsBadInteractionSquare P embedding threshold d
      (daiLiGridCellCenter w origin cell) (w / 2)
def daiLiGridClosedTotalF
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w : ℝ)
    (origin : ℝ × ℝ) : Nat :=
  ∑ cell ∈ embedding.gridOccupiedCells w origin,
    regionInteractionCounter P embedding threshold
      (daiLiGridCellClosedQubits embedding w origin cell)
def daiLiBadGridTotalF
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) : Nat :=
  ∑ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
    regionInteractionCounter P embedding threshold
      (daiLiGridCellClosedQubits embedding w origin cell)
def daiLiRectangleVertex (rectangle : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 4 → ℝ × ℝ
  | 0 => rectangle.1
  | 1 => (rectangle.1.1, rectangle.2.2)
  | 2 => (rectangle.2.1, rectangle.1.2)
  | 3 => rectangle.2
abbrev DaiLiBadGridRectangleVertexIndex
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :=
  Σ cell : {cell // cell ∈ cells}, Σ _ : Fin (rectangles cell).length, Fin 4
def daiLiBadGridRectangleVertexPoint
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiBadGridRectangleVertexIndex cells rectangles → ℝ × ℝ
  | ⟨cell, rectangle, vertex⟩ =>
      daiLiRectangleVertex (rectangles cell.1)[rectangle] vertex
def daiLiVertexNeighborhoodQubits (embedding : UnitSeparatedEmbedding2D ι)
    (ell : ℝ) (vertex : ℝ × ℝ) : Finset ι :=
  embedding.qubitsInRectangle (vertex.1 - 2 * ell, vertex.2 - 2 * ell)
    (vertex.1 + 2 * ell, vertex.2 + 2 * ell)
def daiLiBadGridRectangleVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ)
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : Finset ι :=
  Finset.univ.biUnion fun vertex : DaiLiBadGridRectangleVertexIndex cells rectangles =>
    daiLiVertexNeighborhoodQubits embedding ell
      (daiLiBadGridRectangleVertexPoint cells rectangles vertex)
def daiLiKGeDSeparator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : Finset ι :=
  gridVertexBufferQubits embedding w ell t ∪
    longInteractionEndpointQubits P embedding threshold ∪
      daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles
abbrev DaiLiGridSideIndex := ℤ × ℤ × Bool
def daiLiGridSideStripQubits (embedding : UnitSeparatedEmbedding2D ι)
    (w edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ)
    (side : DaiLiGridSideIndex) : Finset ι :=
  if side.2.2 then
    embedding.qubitsInRectangle
      (origin.1 + (side.1 : ℝ) * w - edgeRadius,
        origin.2 + (side.2.1 : ℝ) * w + vertexRadius)
      (origin.1 + (side.1 : ℝ) * w + edgeRadius,
        origin.2 + ((side.2.1 : ℝ) + 1) * w - vertexRadius)
  else
    embedding.qubitsInRectangle
      (origin.1 + (side.1 : ℝ) * w + vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w - edgeRadius)
      (origin.1 + ((side.1 : ℝ) + 1) * w - vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w + edgeRadius)
def daiLiGridSideStripSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (w edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ)
    (side : DaiLiGridSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side⟩
def daiLiGridSideCandidates (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) : Finset DaiLiGridSideIndex := by
  classical
  exact (embedding.gridOccupiedCells w origin).biUnion fun cell =>
    {(cell.1, cell.2, true), (cell.1 + 1, cell.2, true),
      (cell.1, cell.2, false), (cell.1, cell.2 + 1, false)}
def daiLiGridVertexCandidates (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (embedding.gridOccupiedCells w origin).biUnion fun cell =>
    {(cell.1, cell.2), (cell.1 + 1, cell.2),
      (cell.1, cell.2 + 1), (cell.1 + 1, cell.2 + 1)}
def daiLiFiniteGridVertexBuffer (embedding : UnitSeparatedEmbedding2D ι)
    (w ell : ℝ) (origin : ℝ × ℝ) : Finset ι :=
  (daiLiGridVertexCandidates embedding w origin).biUnion fun vertex =>
    daiLiVertexNeighborhoodQubits embedding ell
      (origin.1 + (vertex.1 : ℝ) * w, origin.2 + (vertex.2 : ℝ) * w)
def daiLiFiniteGridSideBuffer (embedding : UnitSeparatedEmbedding2D ι)
    (w edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ) : Finset ι :=
  (daiLiGridSideCandidates embedding w origin).biUnion fun side =>
    daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side
def daiLiGridSideGoodQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (origin : ℝ × ℝ) (side : DaiLiGridSideIndex) : Finset ι :=
  daiLiGridSideStripQubits embedding w ell (2 * ell) origin side \
    longInteractionEndpointQubits P embedding threshold
def daiLiGridSideGoodSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (origin : ℝ × ℝ) (side : DaiLiGridSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiGridSideGoodQubits P embedding threshold w ell origin side⟩
def daiLiGridSideGoodFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (origin : ℝ × ℝ) : DaiLiGridSideIndex → FiniteSubsystem ι :=
  daiLiGridSideGoodSubsystem P embedding threshold w ell origin
def daiLiRectangleCenter (lower upper : ℝ × ℝ) : ℝ × ℝ :=
  ((lower.1 + upper.1) / 2, (lower.2 + upper.2) / 2)
def daiLiRectangleHorizontalRadius (lower upper : ℝ × ℝ) : ℝ :=
  (upper.1 - lower.1) / 2
def daiLiRectangleVerticalRadius (lower upper : ℝ × ℝ) : ℝ :=
  (upper.2 - lower.2) / 2
def daiLiRectangleSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (lower upper : ℝ × ℝ) : FiniteSubsystem ι :=
  ⟨embedding.qubitsInRectangle lower upper⟩
abbrev DaiLiKGeDRegionIndex :=
  Sum (ℤ × ℤ) ((ℤ × ℤ) × ℕ)
def daiLiKGeDRegionCandidates
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Finset DaiLiKGeDRegionIndex := by
  classical
  let bad := daiLiBadGridCells P embedding threshold d w origin
  exact ((embedding.gridOccupiedCells w origin \ bad).image (fun cell => Sum.inl cell)) ∪
    bad.biUnion fun cell =>
      (Finset.range (rectangles cell).length).image
        (fun slot => Sum.inr (cell, slot))
def daiLiKGeDRegionRectangle
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) : (ℝ × ℝ) × (ℝ × ℝ) :=
  match region with
  | Sum.inl cell => (gridCellLower w origin cell, gridCellUpper w origin cell)
  | Sum.inr (cell, slot) => (rectangles cell).getD slot ((0, 0), (0, 0))
def daiLiKGeDRegionHostCell : DaiLiKGeDRegionIndex → ℤ × ℤ
  | Sum.inl cell => cell
  | Sum.inr (cell, _) => cell
def daiLiKGeDRegionCoreQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) : Finset ι :=
  let rectangle := daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region
  (embedding.qubitsInRectangle rectangle.1 rectangle.2).filter fun q =>
    q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles ∧
      rectangle.1.1 + ell < (embedding.point q).1 ∧
        (embedding.point q).1 < rectangle.2.1 - ell ∧
          rectangle.1.2 + ell < (embedding.point q).2 ∧
            (embedding.point q).2 < rectangle.2.2 - ell
def daiLiKGeDRegionCoreSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) : FiniteSubsystem ι :=
  ⟨daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region⟩
def daiLiKGeDRegionCoreFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiKGeDRegionIndex → FiniteSubsystem ι :=
  daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t cells rectangles
abbrev DaiLiKGeDInternalSideIndex := (ℤ × ℤ) × ℕ
def daiLiKGeDInternalSideCandidates
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Finset DaiLiKGeDInternalSideIndex := by
  classical
  exact (daiLiBadGridCells P embedding threshold d w origin).biUnion fun cell =>
    ((Finset.range (rectangles cell).length).filter fun slot =>
      slot + 1 < (rectangles cell).length).image fun slot => (cell, slot)
def daiLiKGeDInternalSideRectangle
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) : (ℝ × ℝ) × (ℝ × ℝ) :=
  daiLiKGeDRegionRectangle embedding w origin rectangles (Sum.inr side)
def daiLiKGeDInternalSideQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) : Finset ι :=
  daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles side).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles side).2 3 \
    daiLiKGeDSeparator P embedding threshold w ell t cells rectangles
def daiLiKGeDInternalSideSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiKGeDInternalSideQubits P embedding threshold w ell t cells rectangles side⟩
def daiLiKGeDInternalSideFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiKGeDInternalSideIndex → FiniteSubsystem ι :=
  daiLiKGeDInternalSideSubsystem P embedding threshold w ell t cells rectangles
def daiLiKGeDGridSideQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiGridSideIndex) : Finset ι :=
  daiLiGridSideStripQubits embedding w ell (2 * ell) (gridOrigin w t) side \
    daiLiKGeDSeparator P embedding threshold w ell t cells rectangles
def daiLiKGeDGridSideSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiGridSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiKGeDGridSideQubits P embedding threshold w ell t cells rectangles side⟩
def daiLiKGeDGridSideFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiGridSideIndex → FiniteSubsystem ι :=
  daiLiKGeDGridSideSubsystem P embedding threshold w ell t cells rectangles
def daiLiKGeDGridSideUnionSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  familyUnionSubsystem (daiLiKGeDGridSideFamily P embedding threshold w ell t cells rectangles)
    (daiLiGridSideCandidates embedding w (gridOrigin w t))
def daiLiKGeDInternalSideUnionSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  familyUnionSubsystem (daiLiKGeDInternalSideFamily P embedding threshold w ell t cells rectangles)
    (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)
def daiLiKGeDBSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  unionSubsystem
    (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles)
    (daiLiKGeDInternalSideUnionSubsystem P embedding d threshold w ell t cells rectangles)
def daiLiKGeDASubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  familyUnionSubsystem
    (daiLiKGeDRegionCoreFamily P embedding threshold w ell t cells rectangles)
    (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)
def daiLiKGeDTrimmedBSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  ⟨(daiLiKGeDBSubsystem P embedding d threshold w ell t cells rectangles).selected \
    (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected⟩
def daiLiKGeDResidualSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  ⟨Finset.univ \
    ((daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected ∪
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected)⟩
end QEC.Locality


