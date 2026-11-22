-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyOrderBridge
-- name    : LeanPool_BooleanIsoperimetry_ConwayGuyOrderBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:35:19.333799+00:00
-- url     : https://prove2.me/theorems/2caeeaff-5537-4b23-b7ba-e63a363820a1
-- title:
--   Conway Guy Order Bridge
-- statement:
--   Definitions and structural lemmas for Conway Guy Order Bridge, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyOrderBridge.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyRigidity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyNormalizedChamberRigidity
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff


set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry.CoherentGap
def integerSubsetWeight {n : ℕ} (weights : Relation n) (vertex : Cube n) : ℤ :=
  ∑ coordinate ∈ vertex, weights coordinate
def realSubsetWeight {n : ℕ} (weights : Fin n → ℝ) (vertex : Cube n) : ℝ :=
  ∑ coordinate ∈ vertex, weights coordinate
def positiveSupport {n : ℕ} (relation : Relation n) : Cube n :=
  Finset.univ.filter fun coordinate => relation coordinate = 1
def negativeSupport {n : ℕ} (relation : Relation n) : Cube n :=
  Finset.univ.filter fun coordinate => relation coordinate = -1
def IsConsecutiveSubsetGap {n : ℕ} (weights : Relation n)
    (lower upper : Cube n) : Prop :=
  integerSubsetWeight weights lower < integerSubsetWeight weights upper ∧
    ∀ middle,
      ¬(integerSubsetWeight weights lower <
          integerSubsetWeight weights middle ∧
        integerSubsetWeight weights middle <
          integerSubsetWeight weights upper)
def SatisfiesNormalizedConsecutiveGaps {n : ℕ} (reference : Relation n)
    (candidate : Fin n → ℝ) : Prop :=
  ∀ lower upper,
    IsConsecutiveSubsetGap reference lower upper →
      1 ≤ realSubsetWeight candidate upper -
        realSubsetWeight candidate lower
lemma dot_eq_support_difference {n : ℕ} (weights relation : Relation n)
    (hvalues : ∀ coordinate,
      relation coordinate = -1 ∨
        relation coordinate = 0 ∨ relation coordinate = 1) :
    dot relation weights =
      integerSubsetWeight weights (positiveSupport relation) -
        integerSubsetWeight weights (negativeSupport relation) := by
  classical
  unfold dot integerSubsetWeight positiveSupport negativeSupport
  calc
    (∑ coordinate, relation coordinate * weights coordinate) =
        ∑ coordinate,
          ((if relation coordinate = 1 then weights coordinate else 0) -
            if relation coordinate = -1 then weights coordinate else 0) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rcases hvalues coordinate with hnegative | hzero | hpositive
      · simp [hnegative]
      · simp [hzero]
      · simp [hpositive]
    _ =
        (∑ coordinate,
          if relation coordinate = 1 then weights coordinate else 0) -
          ∑ coordinate,
            if relation coordinate = -1 then weights coordinate else 0 := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ coordinate ∈ Finset.univ.filter
          (fun coordinate => relation coordinate = 1), weights coordinate) -
          ∑ coordinate ∈ Finset.univ.filter
            (fun coordinate => relation coordinate = -1), weights coordinate := by
      simp only [Finset.sum_filter]
lemma realDot_eq_support_difference {n : ℕ} (candidate : Fin n → ℝ)
    (relation : Relation n)
    (hvalues : ∀ coordinate,
      relation coordinate = -1 ∨
        relation coordinate = 0 ∨ relation coordinate = 1) :
    realDot relation candidate =
      realSubsetWeight candidate (positiveSupport relation) -
        realSubsetWeight candidate (negativeSupport relation) := by
  classical
  unfold realDot realSubsetWeight positiveSupport negativeSupport
  calc
    (∑ coordinate, (relation coordinate : ℝ) * candidate coordinate) =
        ∑ coordinate,
          ((if relation coordinate = 1 then candidate coordinate else 0) -
            if relation coordinate = -1 then candidate coordinate else 0) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rcases hvalues coordinate with hnegative | hzero | hpositive
      · simp [hnegative]
      · simp [hzero]
      · simp [hpositive]
    _ =
        (∑ coordinate,
          if relation coordinate = 1 then candidate coordinate else 0) -
          ∑ coordinate,
            if relation coordinate = -1 then candidate coordinate else 0 := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ coordinate ∈ Finset.univ.filter
          (fun coordinate => relation coordinate = 1), candidate coordinate) -
          ∑ coordinate ∈ Finset.univ.filter
            (fun coordinate => relation coordinate = -1), candidate coordinate := by
      simp only [Finset.sum_filter]
lemma unitRelation_support_gap {n : ℕ} {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    integerSubsetWeight weights (positiveSupport relation) =
      integerSubsetWeight weights (negativeSupport relation) + 1 := by
  have hdot := hrelation.2.1
  rw [dot_eq_support_difference weights relation hrelation.1] at hdot
  omega
lemma consecutive_of_integer_gap_one {n : ℕ} {weights : Relation n}
    {lower upper : Cube n}
    (hgap : integerSubsetWeight weights upper =
      integerSubsetWeight weights lower + 1) :
    IsConsecutiveSubsetGap weights lower upper := by
  constructor
  · omega
  · intro middle hbetween
    omega
theorem unitRelation_isConsecutiveSubsetGap {n : ℕ}
    {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    IsConsecutiveSubsetGap weights
      (negativeSupport relation) (positiveSupport relation) :=
  consecutive_of_integer_gap_one (unitRelation_support_gap hrelation)
theorem normalizedConsecutiveGaps_imply_unitRelations {n : ℕ}
    {reference : Relation n} {candidate : Fin n → ℝ}
    (hnormalized : SatisfiesNormalizedConsecutiveGaps reference candidate) :
    ∀ relation, IsLiftableUnit reference relation →
      1 ≤ realDot relation candidate := by
  intro relation hrelation
  have hgap := hnormalized (negativeSupport relation) (positiveSupport relation)
    (unitRelation_isConsecutiveSubsetGap hrelation)
  rw [realDot_eq_support_difference candidate relation hrelation.1]
  exact hgap
theorem conwayGuyRigidity_of_normalizedConsecutiveGaps {n : ℕ}
    (candidate : Fin n → ℝ)
    (hnormalized : SatisfiesNormalizedConsecutiveGaps
      (conwayGuyArithmetic.tower.weights n) candidate) :
    ∀ coordinate,
      (conwayGuyArithmetic.tower.weights n coordinate : ℝ) ≤
        candidate coordinate :=
  conwayGuyNormalizedChamberRigidity candidate
    (normalizedConsecutiveGaps_imply_unitRelations hnormalized)
end BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry
alias conwayGuyGapRigidity :=
  CoherentGap.conwayGuyRigidity_of_normalizedConsecutiveGaps
end BooleanIsoperimetry


