-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
-- name    : QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:29:28.611234+00:00
-- url     : https://prove2.me/theorems/ee992f19-41f1-4c13-a65b-d8a97e894177
-- title:
--   Alternating Strip Distance
-- statement:
--   Definitions and structural lemmas for Alternating Strip Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian
open PauliSymplectic
structure AlternatingWidthDecomposition (L r : Nat) where
  widths : List Nat
  sum_widths : widths.sum = L
  even_length : Even widths.length
  width_eq : ∀ w ∈ widths, w = r - 1 ∨ w = r
def alternatingWidths (a b r : Nat) : List Nat :=
  List.replicate a (r - 1) ++ List.replicate b r
namespace StripGeometry
abbrev Site (L : Nat) := Fin L × Fin L
def openVerticalInterval (L start width : Nat) : Finset (Site L) :=
  Finset.univ.filter fun p => start ≤ p.1.val ∧ p.1.val < start + width
def periodicVerticalInterval (L start width : Nat) : Finset (Site L) :=
  let s := start % L
  Finset.univ.filter fun p =>
    (s ≤ p.1.val ∧ p.1.val < s + width) ∨
      p.1.val + L < s + width
def OpenIntervalSeparated
    (L r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ start width, width ≤ r →
    Disjoint (openVerticalInterval L start width) A ∨
      Disjoint (openVerticalInterval L start width) B
def PeriodicIntervalSeparated
    (L r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ start width, width ≤ r →
    Disjoint (periodicVerticalInterval L start width) A ∨
      Disjoint (periodicVerticalInterval L start width) B
def OpenSeparatedByGap
    {L : Nat} (r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ B, p.1.val + r ≤ q.1.val
def PeriodicSeparatedByGaps
    (L r : Nat) (A B : Finset (Site L)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ B,
    p.1.val + r ≤ q.1.val ∧ r + q.1.val ≤ L + p.1.val
def openStripListAux (L start : Nat) : List Nat → List (Finset (Site L))
  | [] => []
  | width :: widths =>
      openVerticalInterval L start width ::
        openStripListAux L (start + width) widths
def firstParity {α : Type*} : List α → List α
  | [] => []
  | [A] => [A]
  | A :: _ :: regions => A :: firstParity regions
def secondParity {α : Type*} : List α → List α
  | [] => []
  | [_] => []
  | _ :: B :: regions => B :: secondParity regions
def HasOpenIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ openVerticalInterval L start width
def HasPeriodicIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ periodicVerticalInterval L start width
end StripGeometry
def NoSharedGenerator
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R T : Finset ι) : Prop :=
  ∀ j, ¬ (H.GeneratorMeets R j ∧ H.GeneratorMeets T j)
def regionUnion {ι : Type*} [DecidableEq ι] : List (Finset ι) → Finset ι
  | [] => ∅
  | R :: regions => R ∪ regionUnion regions
namespace StripGeometry
end StripGeometry
def RegionsPairwise
    {α : Type*} (relation : α → α → Prop) (regions : List α) : Prop :=
  ∀ R ∈ regions, ∀ T ∈ regions, R ≠ T → relation R T
def restrictionVectorSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (regions : List (Finset ι)) (E : Binary ι) :
    SymplecticVector (ZMod 2) ι :=
  (regions.map fun R => (Locality.restrictBinaryTo R E).vector).sum
def NoLocalLogical
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Prop :=
  ¬ ∃ P : Binary ι,
      H.code.1.InBinaryNormalizer P ∧
      ¬ H.code.1.InGeneratedGroupUpToSign P ∧
      support P ⊆ R
end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC


