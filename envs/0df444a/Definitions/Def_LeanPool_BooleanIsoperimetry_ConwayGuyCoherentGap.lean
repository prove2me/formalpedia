-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
-- name    : LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:32.585085+00:00
-- url     : https://prove2.me/theorems/b58d5549-db14-49aa-b512-e5e8215a06de
-- title:
--   Conway Guy Coherent Gap
-- statement:
--   Definitions and structural lemmas for Conway Guy Coherent Gap, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis


set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry.CoherentGap
def triangular : ℕ → ℕ
  | 0 => 0
  | index + 1 => triangular index + index + 1
lemma self_le_triangular (index : ℕ) : index ≤ triangular index := by
  induction index with
  | zero => simp [triangular]
  | succ index inductionHypothesis =>
      simp only [triangular]
      omega
lemma triangular_mono : Monotone triangular := by
  intro first second hle
  induction second, hle using Nat.le_induction with
  | base => exact le_rfl
  | succ second hfirst inductionHypothesis =>
      simp only [triangular]
      omega
lemma triangular_add_index (index : ℕ) :
    triangular index + index + 1 = triangular (index + 1) := by
  rfl
theorem guideWitness (dimension : ℕ) :
    ∃ width, dimension - 1 ≤ triangular width :=
  ⟨dimension, (Nat.sub_le dimension 1).trans (self_le_triangular dimension)⟩
noncomputable def guide (dimension : ℕ) : ℕ :=
  Nat.find (guideWitness dimension)
lemma guide_upper (dimension : ℕ) :
    dimension - 1 ≤ triangular (guide dimension) :=
  Nat.find_spec (guideWitness dimension)
lemma guide_pos {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    0 < guide dimension := by
  by_contra hnot
  have hzero : guide dimension = 0 := Nat.eq_zero_of_not_pos hnot
  have := guide_upper dimension
  simp [hzero, triangular] at this
  omega
lemma guide_lower {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    triangular (guide dimension - 1) + 2 ≤ dimension := by
  have hpositive := guide_pos hdimension
  have hpred : guide dimension - 1 < guide dimension := by omega
  have hminimal :=
    Nat.find_min (guideWitness dimension) hpred
  have hnot : ¬ dimension - 1 ≤ triangular (guide dimension - 1) := hminimal
  omega
lemma guide_le_dimension {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    guide dimension ≤ dimension := by
  have hpositive := guide_pos hdimension
  have hlower := guide_lower hdimension
  have htriangular := self_le_triangular (guide dimension - 1)
  omega
lemma correction_deep_bound {dimension index : ℕ}
    (hdimension : 2 ≤ dimension)
    (hindex : index < guide dimension - 1) :
    triangular index + index + 3 ≤ dimension := by
  have hindex_le : index + 1 ≤ guide dimension - 1 := by omega
  have htriangular :=
    triangular_mono hindex_le
  have hlower := guide_lower hdimension
  have hstep := triangular_add_index index
  omega
noncomputable def positiveIndex (offset : ℕ)
    (index : Fin (guide (offset + 2))) : Fin (offset + 2) :=
  ⟨index.val, index.isLt.trans_le (guide_le_dimension (by omega))⟩
noncomputable def negativeIndex (offset : ℕ)
    (index : Fin (guide (offset + 2) - 1)) : Fin (offset + 2) := by
  have hdeep := correction_deep_bound (dimension := offset + 2)
    (index := index.val) (by omega) index.isLt
  exact ⟨offset + 2 - triangular index.val - 1, by omega⟩
noncomputable def correctionFor (offset : ℕ)
    (index : Fin (guide (offset + 2) - 1)) :
    Correction (offset + 2) where
  sourceOffset := offset + 2 - index.val - 3
  sourceCoordinate := by
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    exact ⟨offset + 2 - triangular index.val - index.val - 3, by omega⟩
  steps := index.val + 2
  steps_pos := by omega
  dimension_eq := by
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    omega
noncomputable def corrections (offset : ℕ) :
    List (Correction (offset + 2)) :=
  List.ofFn (correctionFor offset)
noncomputable def principal (offset : ℕ) : Relation (offset + 2) :=
  (∑ index : Fin (guide (offset + 2)),
      basis (positiveIndex offset index)) -
    ∑ index : Fin (guide (offset + 2) - 1),
      basis (negativeIndex offset index)
@[simp]
lemma coordinateSum_basis {n : ℕ} (coordinate : Fin n) :
    coordinateSum (basis coordinate) = 1 := by
  classical
  simp [coordinateSum, basis]
@[simp]
lemma castRelation_apply {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (relation : Relation firstDimension) (coordinate : Fin secondDimension) :
    castRelation hdimension relation coordinate =
      relation (Fin.cast hdimension.symm coordinate) := by
  subst secondDimension
  rfl
def difference (blockGuide : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | index + 1 =>
      ∑ offset ∈ Finset.range (blockGuide (index + 2)),
        difference blockGuide (index - offset)
termination_by index => index
decreasing_by omega
noncomputable def conwayGuyDifference (index : ℕ) : ℕ :=
  difference guide index
noncomputable def conwayGuyHeight (dimension : ℕ) : ℤ :=
  ∑ index ∈ Finset.range dimension, (conwayGuyDifference index : ℤ)
@[simp]
lemma conwayGuyHeight_zero : conwayGuyHeight 0 = 0 := by
  simp [conwayGuyHeight]
@[simp]
lemma conwayGuyHeight_one : conwayGuyHeight 1 = 1 := by
  simp [conwayGuyHeight, conwayGuyDifference, difference]
structure ConwayGuyArithmetic where
  /-- Block guide for the recurrence. -/
  guide : ℕ → ℕ
  /-- Cumulative heights of the recurrence. -/
  height : ℕ → ℤ
  /-- The zero-dimensional height. -/
  height_zero : height 0 = 0
noncomputable def conwayGuyArithmetic : ConwayGuyArithmetic where
  guide := guide
  height := conwayGuyHeight
  height_zero := conwayGuyHeight_zero
def ConwayGuyArithmetic.weights (data : ConwayGuyArithmetic)
    (dimension : ℕ) : Relation dimension :=
  fun coordinate =>
    data.height dimension -
      data.height (dimension - (coordinate.val + 1))
def ConwayGuyArithmetic.head (data : ConwayGuyArithmetic)
    (dimension : ℕ) : ℤ :=
  data.height (dimension + 1) - data.height dimension
lemma ConwayGuyArithmetic.weights_step (data : ConwayGuyArithmetic)
    (dimension : ℕ) :
    data.weights (dimension + 1) =
      extendWeights (data.head dimension) (data.weights dimension) := by
  funext coordinate
  refine Fin.cases ?_ (fun previous => ?_) coordinate
  · simp [ConwayGuyArithmetic.weights, ConwayGuyArithmetic.head, extendWeights]
  · simp only [ConwayGuyArithmetic.weights, ConwayGuyArithmetic.head,
      extendWeights, Fin.cases_succ]
    have hindex :
        dimension + 1 - (previous.succ.val + 1) =
          dimension - (previous.val + 1) := by
      change dimension + 1 - ((previous.val + 1) + 1) =
        dimension - (previous.val + 1)
      omega
    rw [hindex]
    ring
def ConwayGuyArithmetic.tower (data : ConwayGuyArithmetic) : WeightTower where
  weights := data.weights
  head := data.head
  step := data.weights_step
end BooleanIsoperimetry.CoherentGap


