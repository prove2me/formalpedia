-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
-- name    : QEC_Locality_OptimalTradeoff_BadSquareSubdivision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:49:26.805199+00:00
-- url     : https://prove2.me/theorems/cf3ff401-22e8-49d8-8d5e-fb14cf12faa1
-- title:
--   Bad Square Subdivision
-- statement:
--   Definitions and structural lemmas for Bad Square Subdivision, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
def daiLiVerticalQubitSupport
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ) : Finset ℝ :=
  (embedding.qubitsInRectangle lower upper).image fun q => (embedding.point q).2
def daiLiGlobalVerticalQubitSupport (embedding : UnitSeparatedEmbedding2D ι) : Finset ℝ :=
  Finset.univ.image fun q => (embedding.point q).2
def daiLiBelowHorizontalCut
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle rectangleLower rectangleUpper).filter fun q =>
    (embedding.point q).2 < cut
def daiLiAtOrAboveHorizontalCut
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle rectangleLower rectangleUpper).filter fun q =>
    cut ≤ (embedding.point q).2
def DaiLiShortHeight (ell lower upper : ℝ) : Prop :=
  5 * ell ≤ upper - lower ∧ upper - lower ≤ 10 * ell
inductive DaiLiHorizontalAtomization (support : Finset ℝ) (ell : ℝ) :
    ℝ → ℝ → List (ℝ × ℝ) → Prop
  | single {lower upper : ℝ}
      (hHeight : DaiLiShortHeight ell lower upper) :
      DaiLiHorizontalAtomization support ell lower upper [(lower, upper)]
  | cons {lower cut upper : ℝ} {tail : List (ℝ × ℝ)}
      (hCutFree : cut ∉ support)
      (hHeight : DaiLiShortHeight ell lower cut)
      (hTail : DaiLiHorizontalAtomization support ell cut upper tail) :
      DaiLiHorizontalAtomization support ell lower upper ((lower, cut) :: tail)
def DaiLiAtomAdjacent (first second : ℝ × ℝ) : Prop :=
  first.2 = second.1
def daiLiAtomQubits
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atom : ℝ × ℝ) : Finset ι :=
  embedding.qubitsInRectangle (left, atom.1) (right, atom.2)
def daiLiAtomCounters
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (atoms : List (ℝ × ℝ)) : List Nat :=
  atoms.map fun atom =>
    regionInteractionCounter P embedding threshold (daiLiAtomQubits embedding left right atom)
def daiLiAtomQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atoms : List (ℝ × ℝ)) : Finset ι :=
  atoms.foldr (fun atom covered => daiLiAtomQubits embedding left right atom ∪ covered) ∅
abbrev DaiLiAtomicCounter := Nat
def daiLiAtomicMass (bands : List DaiLiAtomicCounter) : Nat :=
  bands.sum
def DaiLiLowCounter (d : Nat) (bands : List DaiLiAtomicCounter) : Prop :=
  10 * daiLiAtomicMass bands ≤ d
def DaiLiShortAtomicBand (bands : List DaiLiAtomicCounter) : Prop :=
  bands.length ≤ 1
def daiLiAtomicPiecesMass (pieces : List (List DaiLiAtomicCounter)) : Nat :=
  (pieces.map daiLiAtomicMass).sum
def DaiLiAtomicPieceAdmissible (d : Nat) (piece : List DaiLiAtomicCounter) : Prop :=
  piece ≠ [] ∧ (DaiLiLowCounter d piece ∨ DaiLiShortAtomicBand piece)
def daiLiGreedyScan (d : Nat) : List DaiLiAtomicCounter →
    List DaiLiAtomicCounter → List (List DaiLiAtomicCounter) →
      List (List DaiLiAtomicCounter)
  | [], pending, emitted =>
      if pending = [] then emitted.reverse else (pending :: emitted).reverse
  | a :: rest, pending, emitted =>
      if hLow : 10 * (daiLiAtomicMass pending + a) ≤ d then
        daiLiGreedyScan d rest (pending ++ [a]) emitted
      else if hPending : pending = [] then
        daiLiGreedyScan d rest [] ([a] :: emitted)
      else
        daiLiGreedyScan d rest [] ([a] :: pending :: emitted)
def daiLiGreedyAtomicSubdivision (d : Nat) (bands : List DaiLiAtomicCounter) :
    List (List DaiLiAtomicCounter) :=
  daiLiGreedyScan d bands [] []
def daiLiGreedyScanWith {α : Type*} (weight : α → Nat) (d : Nat) : List α →
    List α → List (List α) → List (List α)
  | [], pending, emitted =>
      if pending = [] then emitted.reverse else (pending :: emitted).reverse
  | a :: rest, pending, emitted =>
      if hLow : 10 * ((pending.map weight).sum + weight a) ≤ d then
        daiLiGreedyScanWith weight d rest (pending ++ [a]) emitted
      else if hPending : pending = [] then
        daiLiGreedyScanWith weight d rest [] ([a] :: emitted)
      else
        daiLiGreedyScanWith weight d rest [] ([a] :: pending :: emitted)
def daiLiGreedySubdivisionWith {α : Type*} (weight : α → Nat) (d : Nat)
    (bands : List α) : List (List α) :=
  daiLiGreedyScanWith weight d bands [] []
def daiLiPhysicalGreedySubdivision
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) : List (List (ℝ × ℝ)) :=
  daiLiGreedySubdivisionWith
    (fun atom => regionInteractionCounter P embedding threshold
      (daiLiAtomQubits embedding left right atom)) d atoms
def daiLiAtomGroupLower : List (ℝ × ℝ) → ℝ
  | [] => 0
  | atom :: _ => atom.1
def daiLiAtomGroupUpper : List (ℝ × ℝ) → ℝ
  | [] => 0
  | [atom] => atom.2
  | _ :: tail => daiLiAtomGroupUpper tail
def daiLiAtomGroupRectangle (left right : ℝ) (group : List (ℝ × ℝ)) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  ((left, daiLiAtomGroupLower group), (right, daiLiAtomGroupUpper group))
def daiLiPhysicalGreedyRectangles
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) : List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).map
    (daiLiAtomGroupRectangle left right)
def daiLiRectangleQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι)
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ))) : Finset ι :=
  rectangles.foldr (fun rectangle covered =>
    embedding.qubitsInRectangle rectangle.1 rectangle.2 ∪ covered) ∅
def DaiLiPairwiseDisjointQubitRectangles
    (embedding : UnitSeparatedEmbedding2D ι)
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ))) : Prop :=
  (rectangles.map fun rectangle =>
    embedding.qubitsInRectangle rectangle.1 rectangle.2).Pairwise Disjoint
end QEC.Locality


