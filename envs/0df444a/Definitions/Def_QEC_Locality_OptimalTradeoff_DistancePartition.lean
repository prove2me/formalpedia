-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
-- name    : QEC_Locality_OptimalTradeoff_DistancePartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:13:14.321597+00:00
-- url     : https://prove2.me/theorems/fd72cd98-25d5-434f-9f37-f8c47dbf2fdc
-- title:
--   Distance Partition
-- statement:
--   Definitions and structural lemmas for Distance Partition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
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
local instance instClassicalDecidableDGeK (p : Prop) : Decidable p :=
  Classical.propDecidable p
def daiLiDGeKBPrimeQubits (embedding : UnitSeparatedEmbedding2D ι)
    (w ell : ℝ) (t : GridTranslation w) : Finset ι :=
  gridWideEdgeBufferQubits embedding w ell t
def daiLiDGeKBPrimeBadEndpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  gridBadLongEndpointQubits P embedding threshold w ell t
def daiLiDGeKCrossingEndpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  daiLiDGeKBPrimeBadEndpoints P embedding threshold w ell t ∪
    longNeighborsOf P embedding threshold
      (daiLiDGeKBPrimeBadEndpoints P embedding threshold w ell t)
def daiLiDGeKSeparator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  gridVertexBufferQubits embedding w ell t ∪
    daiLiDGeKCrossingEndpoints P embedding threshold w ell t
def daiLiDGeKExceptionalBadQubits
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  longInteractionEndpointQubits P embedding threshold \
    daiLiDGeKSeparator P embedding threshold w ell t
def daiLiDGeKExceptionalSubsystem
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : FiniteSubsystem ι :=
  ⟨daiLiDGeKExceptionalBadQubits P embedding threshold w ell t⟩
def daiLiDGeKGoodBFamily
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : DaiLiGridSideIndex → FiniteSubsystem ι :=
  daiLiGridSideGoodFamily P embedding threshold w ell (gridOrigin w t)
def daiLiDGeKGoodBIndices
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ)
    (t : GridTranslation w) : Finset DaiLiGridSideIndex :=
  daiLiGridSideCandidates embedding w (gridOrigin w t)
def daiLiDGeKBSubsystem
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : FiniteSubsystem ι :=
  familyUnionSubsystem
    (caseDGeKPieceFamily
      (daiLiDGeKExceptionalSubsystem P embedding threshold w ell t)
      (daiLiDGeKGoodBFamily P embedding threshold w ell t))
    (caseDGeKPieceIndices (daiLiDGeKGoodBIndices embedding w t))
def daiLiDGeKASubsystem
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) : FiniteSubsystem ι :=
  daiLiKGeDASubsystem P embedding d threshold w ell t
    (daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (fun _ => [])
def daiLiDGeKTrimmedBSubsystem
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) : FiniteSubsystem ι :=
  ⟨(daiLiDGeKBSubsystem P embedding threshold w ell t).selected \
    (daiLiDGeKASubsystem P embedding d threshold w ell t).selected⟩
def daiLiDGeKResidualSubsystem
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) : FiniteSubsystem ι :=
  ⟨Finset.univ \
    ((daiLiDGeKASubsystem P embedding d threshold w ell t).selected ∪
      (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected)⟩
def daiLiPrincipalFourthRootScale (k d n : ℝ) : ℝ :=
  (1 / 100 : ℝ) * Real.rpow (k * d ^ 2 / n) (1 / 4 : ℝ)
def daiLiDGeKGridWidth (d ell : ℝ) : ℝ := d / (100 * ell)
end QEC.Locality


