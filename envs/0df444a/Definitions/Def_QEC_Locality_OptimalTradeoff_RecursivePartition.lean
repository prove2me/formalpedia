-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
-- name    : QEC_Locality_OptimalTradeoff_RecursivePartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:47:56.873609+00:00
-- url     : https://prove2.me/theorems/a397b67f-4f85-40d2-adcf-4935c6fdf472
-- title:
--   Recursive Partition
-- statement:
--   Definitions and structural lemmas for Recursive Partition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
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
local instance instClassicalDecidableRecursive (p : Prop) : Decidable p :=
  Classical.propDecidable p
def regionInteractionCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) : Nat :=
  ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q
def centeredSquare (center : ℝ × ℝ) (radius : ℝ) : Set (ℝ × ℝ) :=
  rectangle (center.1 - radius, center.2 - radius)
    (center.1 + radius, center.2 + radius)
def squareQubits (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (radius : ℝ) : Finset ι :=
  embedding.qubitsInRectangle
    (center.1 - radius, center.2 - radius)
    (center.1 + radius, center.2 + radius)
def squareSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (radius : ℝ) : FiniteSubsystem ι :=
  ⟨squareQubits embedding center radius⟩
def longNeighborsOf
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) : Finset ι := by
  classical
  exact region.biUnion fun q =>
    (P.longInteractionGraph embedding threshold).neighborFinset q
def longOutsideNeighborsOf
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) : Finset ι :=
  longNeighborsOf P embedding threshold region \ region
def squareGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) : FiniteSubsystem ι :=
  ⟨(squareQubits embedding center outerRadius \
      squareQubits embedding center (outerRadius - threshold)) ∪
    longOutsideNeighborsOf P embedding threshold
      (squareQubits embedding center (outerRadius - threshold))⟩
def squareShellStrips (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerRadius threshold : ℝ) : Fin 4 → Finset ι
  | 0 => embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 - outerRadius + threshold, center.2 + outerRadius)
  | 1 => embedding.qubitsInRectangle
      (center.1 + outerRadius - threshold, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 + outerRadius)
  | 2 => embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 - outerRadius + threshold)
  | 3 => embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 + outerRadius - threshold)
      (center.1 + outerRadius, center.2 + outerRadius)
def squareShellCover (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerRadius threshold : ℝ) : Finset ι :=
  Finset.univ.biUnion (squareShellStrips embedding center outerRadius threshold)
def squareGrowthRadius (baseRadius threshold : ℝ) (step : Nat) : ℝ :=
  baseRadius + step * threshold
def centeredRectangle (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) :
    Set (ℝ × ℝ) :=
  rectangle (center.1 - horizontalRadius, center.2 - verticalRadius)
    (center.1 + horizontalRadius, center.2 + verticalRadius)
def centeredRectangleQubits (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) : Finset ι :=
  embedding.qubitsInRectangle
    (center.1 - horizontalRadius, center.2 - verticalRadius)
    (center.1 + horizontalRadius, center.2 + verticalRadius)
def centeredRectangleSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) : FiniteSubsystem ι :=
  ⟨centeredRectangleQubits embedding center horizontalRadius verticalRadius⟩
def centeredRectangleGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ) : FiniteSubsystem ι :=
  ⟨(centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
      centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
        (outerVerticalRadius - threshold)) ∪
    longOutsideNeighborsOf P embedding threshold
      (centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
        (outerVerticalRadius - threshold))⟩
def centeredRectangleShellStrips (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    Fin 4 → Finset ι
  | 0 => embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 - outerHorizontalRadius + threshold, center.2 + outerVerticalRadius)
  | 1 => embedding.qubitsInRectangle
      (center.1 + outerHorizontalRadius - threshold, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)
  | 2 => embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 - outerVerticalRadius + threshold)
  | 3 => embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 + outerVerticalRadius - threshold)
      (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)
def centeredRectangleShellCover (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    Finset ι :=
  Finset.univ.biUnion
    (centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold)
def centeredRectangleExternalCollar (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ) : Finset ι :=
  centeredRectangleQubits embedding center (outerHorizontalRadius + threshold)
    (outerVerticalRadius + threshold) \
      centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius
def centeredRectangleGeneralGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) : FiniteSubsystem ι :=
  ⟨((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
      centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius) ∪
    centeredRectangleExternalCollar embedding center outerHorizontalRadius outerVerticalRadius
      threshold) ∪
    longOutsideNeighborsOf P embedding threshold
      (centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius)⟩
def centeredRectangleClippedGrowthRadius
    (baseRadius targetRadius threshold : ℝ) (step : ℕ) : ℝ :=
  min targetRadius (baseRadius + step * threshold)
def daiLiRectangleSideStripQubits (embedding : UnitSeparatedEmbedding2D ι)
    (ell : ℝ) (lower upper : ℝ × ℝ) : Fin 4 → Finset ι
  | 0 => embedding.qubitsInRectangle
      (lower.1 - ell, lower.2 + 2 * ell)
      (lower.1 + ell, upper.2 - 2 * ell)
  | 1 => embedding.qubitsInRectangle
      (upper.1 - ell, lower.2 + 2 * ell)
      (upper.1 + ell, upper.2 - 2 * ell)
  | 2 => embedding.qubitsInRectangle
      (lower.1 + 2 * ell, lower.2 - ell)
      (upper.1 - 2 * ell, lower.2 + ell)
  | 3 => embedding.qubitsInRectangle
      (lower.1 + 2 * ell, upper.2 - ell)
      (upper.1 - 2 * ell, upper.2 + ell)
def daiLiRectangleSideStripSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (ell : ℝ) (lower upper : ℝ × ℝ) (side : Fin 4) : FiniteSubsystem ι :=
  ⟨daiLiRectangleSideStripQubits embedding ell lower upper side⟩
def gridBadLongIncidences
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset (P.daiLiLongIncidenceIndex embedding threshold) :=
  Finset.univ.filter fun incidence =>
    edgeBad w (2 * ell) t (P.daiLiLongIncidencePoint embedding threshold incidence)
def gridBadLongEndpointQubits
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  (gridBadLongIncidences P embedding threshold w ell t).image Sigma.fst
def gridBadPointSet
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  (Finset.univ.filter fun q => vertexBad w (2 * ell) t (embedding.point q)) ∪
    gridBadLongEndpointQubits P embedding threshold w ell t
def IsGoodInteractionRegion
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (region : Finset ι) : Prop :=
  10 * regionInteractionCounter P embedding threshold region < d
def IsBadInteractionRegion
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (region : Finset ι) : Prop :=
  d ≤ 10 * regionInteractionCounter P embedding threshold region
def IsGoodInteractionSquare
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (center : ℝ × ℝ) (radius : ℝ) : Prop :=
  IsGoodInteractionRegion P embedding threshold d
    (squareQubits embedding center radius)
def IsBadInteractionSquare
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (center : ℝ × ℝ) (radius : ℝ) : Prop :=
  IsBadInteractionRegion P embedding threshold d
    (squareQubits embedding center radius)
def longInteractionEndpointQubits
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) : Finset ι :=
  Finset.univ.filter fun q => 0 < P.daiLiInteractionCounter embedding threshold q
def lowerHorizontalRectangleQubits
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle lower upper).filter fun q =>
    (embedding.point q).2 ≤ cut
def upperHorizontalRectangleQubits
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle lower upper).filter fun q =>
    cut < (embedding.point q).2
def gridVertexBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q => vertexBad w (2 * ell) t (embedding.point q)
def gridEdgeBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q =>
    ¬ vertexBad w (2 * ell) t (embedding.point q) ∧
      edgeBad w ell t (embedding.point q)
def gridWideEdgeBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q =>
    ¬ vertexBad w (2 * ell) t (embedding.point q) ∧
      edgeBad w (2 * ell) t (embedding.point q)
def gridInteriorQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q =>
    ¬ vertexBad w (2 * ell) t (embedding.point q) ∧
      ¬ edgeBad w ell t (embedding.point q)
def caseDGeKPieceFamily {α : Type*}
    (badQubits : FiniteSubsystem ι) (edgeStrips : α → FiniteSubsystem ι) :
    Option α → FiniteSubsystem ι
  | none => badQubits
  | some a => edgeStrips a
def caseDGeKPieceIndices {α : Type*} [DecidableEq α] (s : Finset α) :
    Finset (Option α) :=
  insert none (s.image some)
end QEC.Locality


