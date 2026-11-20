-- Prove2me | Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
-- name    : QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:15:56.19798+00:00
-- url     : https://prove2.me/theorems/c1381b3c-5a02-4ac0-aa05-0cbe76b4559a
-- title:
--   Square Partition
-- statement:
--   Definitions and structural lemmas for Square Partition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open Semantics
universe u v
namespace BPTSquareLattice
def tileIndex (L : BPTSquareLattice) (blockWidth : Nat) (site : L.Site) : Nat × Nat :=
  (site.1.val / blockWidth, site.2.val / blockWidth)
def tile (L : BPTSquareLattice) (blockWidth : Nat) (index : Nat × Nat) :
    Finset L.Site :=
  L.square (index.1 * blockWidth, index.2 * blockWidth) blockWidth
def expandedTile (L : BPTSquareLattice) (blockWidth margin : Nat) (index : Nat × Nat) :
    Finset L.Site :=
  L.square (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
    (blockWidth + margin + margin)
def squareInnerCore (L : BPTSquareLattice) (origin : Nat × Nat) (width margin : Nat) :
    Finset L.Site :=
  L.square (origin.1 + margin, origin.2 + margin) (width - margin - margin)
def squareBoundaryFrame (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.square (origin.1 - margin, origin.2 - margin) (width + margin + margin) \
    L.squareInnerCore origin width margin
def rectangle (L : BPTSquareLattice) (origin : Nat × Nat)
    (rowWidth columnWidth : Nat) : Finset L.Site :=
  Finset.univ.filter fun site =>
    origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + rowWidth ∧
      origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + columnWidth
def squareBoundaryFrameLowerRow (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 - margin, origin.2 - margin) (margin + margin)
    (width + margin + margin)
def squareBoundaryFrameUpperRow (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 + width - margin, origin.2 - margin) (margin + margin)
    (width + margin + margin)
def squareBoundaryFrameLowerColumn (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 - margin, origin.2 - margin) (width + margin + margin)
    (margin + margin)
def squareBoundaryFrameUpperColumn (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 - margin, origin.2 + width - margin) (width + margin + margin)
    (margin + margin)
def squareBoundaryFrameStripCover (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.squareBoundaryFrameLowerRow origin width margin ∪
    L.squareBoundaryFrameUpperRow origin width margin ∪
      L.squareBoundaryFrameLowerColumn origin width margin ∪
        L.squareBoundaryFrameUpperColumn origin width margin
def squareGrowthInside (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.square origin width ∩ L.squareBoundaryFrameStripCover origin width margin
def squareGrowthOutside (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.squareBoundaryFrameStripCover origin width margin \ L.square origin width
def squareFits (L : BPTSquareLattice) (origin : Nat × Nat) (width : Nat) : Prop :=
  origin.1 + width ≤ L.rows ∧ origin.2 + width ≤ L.columns
def checkerboardEven (L : BPTSquareLattice) (blockWidth : Nat) (site : L.Site) : Prop :=
  Even (site.1.val / blockWidth + site.2.val / blockWidth)
def CoordinateRangeSeparated (L : BPTSquareLattice) (range : Nat)
    (left right : Finset L.Site) : Prop :=
  ∀ leftSite ∈ left, ∀ rightSite ∈ right,
    range ≤ leftSite.1.val - rightSite.1.val ∨
      range ≤ rightSite.1.val - leftSite.1.val ∨
        range ≤ leftSite.2.val - rightSite.2.val ∨
          range ≤ rightSite.2.val - leftSite.2.val
def cornerCutout (L : BPTSquareLattice) (blockWidth margin : Nat) (site : L.Site) : Prop :=
  (site.1.val % blockWidth < margin ∨ blockWidth - margin ≤ site.1.val % blockWidth) ∧
    (site.2.val % blockWidth < margin ∨ blockWidth - margin ≤ site.2.val % blockWidth)
def squarePartitionC (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset L.Site :=
  Finset.univ.filter (cornerCutout L blockWidth margin)
def cornerCutoutTileCover (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
    L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
      margin margin ∪
      L.rectangle (index.1 * blockWidth + blockWidth - margin, index.2 * blockWidth)
        margin margin ∪
        L.rectangle (index.1 * blockWidth + blockWidth - margin,
          index.2 * blockWidth + blockWidth - margin) margin margin
def cornerCutoutTileExpandedCover (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
    (margin + margin + margin) (margin + margin + margin) ∪
    L.rectangle (index.1 * blockWidth - margin,
      index.2 * blockWidth + blockWidth - margin - margin)
      (margin + margin + margin) (margin + margin + margin) ∪
      L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
        index.2 * blockWidth - margin)
        (margin + margin + margin) (margin + margin + margin) ∪
        L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
          index.2 * blockWidth + blockWidth - margin - margin)
          (margin + margin + margin) (margin + margin + margin)
def squarePartitionA (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset L.Site :=
  Finset.univ.filter fun site =>
    ¬ cornerCutout L blockWidth margin site ∧ checkerboardEven L blockWidth site
def squarePartitionB (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset L.Site :=
  Finset.univ.filter fun site =>
    ¬ cornerCutout L blockWidth margin site ∧ ¬ checkerboardEven L blockWidth site
def occupiedTileIndices (L : BPTSquareLattice) (blockWidth : Nat) :
    Finset (Nat × Nat) :=
  Finset.univ.image (L.tileIndex blockWidth)
def squarePartitionAComponent (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.tile blockWidth index ∩ L.squarePartitionA blockWidth margin
def squarePartitionBComponent (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.tile blockWidth index ∩ L.squarePartitionB blockWidth margin
def squarePartitionAComponents (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset (Finset L.Site) :=
  (((L.occupiedTileIndices blockWidth).filter fun index => Even (index.1 + index.2)).image
    fun index => L.squarePartitionAComponent blockWidth margin index).filter
      Finset.Nonempty
def squarePartitionBComponents (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset (Finset L.Site) :=
  (((L.occupiedTileIndices blockWidth).filter fun index => ¬ Even (index.1 + index.2)).image
    fun index => L.squarePartitionBComponent blockWidth margin index).filter
      Finset.Nonempty
end BPTSquareLattice
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def AllFittingSquaresRecoverable (M : BPTCommutingProjectorModel L kappa)
    (width : Nat) : Prop :=
  ∀ origin, L.lattice.squareFits origin width →
    M.RegionErasureRecoverable (L.lattice.square origin width)
def AllSquareBlocksRecoverable (M : BPTCommutingProjectorModel L kappa)
    (width : Nat) : Prop :=
  ∀ origin, M.RegionErasureRecoverable (L.lattice.square origin width)
def LocallyMaximalCorrectableSquareScale (M : BPTCommutingProjectorModel L kappa)
    (width : Nat) : Prop :=
  M.AllSquareBlocksRecoverable width ∧
    ¬ M.AllSquareBlocksRecoverable
      (width + M.interactionRange + M.interactionRange)
end BPTCommutingProjectorModel
namespace BPTSquareLattice
end BPTSquareLattice
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


