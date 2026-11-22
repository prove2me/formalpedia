-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
-- name    : LeanPool_BooleanIsoperimetry_CoherentGap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:13:54.851141+00:00
-- url     : https://prove2.me/theorems/7c2c9528-d71b-4348-8f8d-1dc83a9638ea
-- title:
--   Coherent Gap
-- statement:
--   Definitions and structural lemmas for Coherent Gap, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry.CoherentGap
abbrev Relation (n : ℕ) := Fin n → ℤ
def coordinateSum {n : ℕ} (relation : Relation n) : ℤ :=
  ∑ i, relation i
def dot {n : ℕ} (relation weights : Relation n) : ℤ :=
  ∑ i, relation i * weights i
def basis {n : ℕ} (coordinate : Fin n) : Relation n :=
  fun i => if i = coordinate then 1 else 0
def IsLiftableUnit {n : ℕ} (weights relation : Relation n) : Prop :=
  (∀ i, relation i = -1 ∨ relation i = 0 ∨ relation i = 1) ∧
    dot relation weights = 1 ∧
    (coordinateSum relation = -1 ∨
      coordinateSum relation = 0 ∨ coordinateSum relation = 1)
def aggregate {n : ℕ} (relations : List (Relation n)) : Relation n :=
  relations.sum
structure Certificate {n : ℕ} (weights target : Relation n) where
  /-- Relations listed with their certificate multiplicities. -/
  relations : List (Relation n)
  /-- Every listed relation is a liftable unit relation. -/
  valid : ∀ relation ∈ relations, IsLiftableUnit weights relation
  /-- The listed relations sum to the certificate target. -/
  target_eq : aggregate relations = target
lemma coordinateSum_add {n : ℕ} (first second : Relation n) :
    coordinateSum (first + second) =
      coordinateSum first + coordinateSum second := by
  simp [coordinateSum, Finset.sum_add_distrib]
@[simp]
lemma dot_basis {n : ℕ} (coordinate : Fin n) (weights : Relation n) :
    dot (basis coordinate) weights = weights coordinate := by
  classical
  simp [dot, basis]
def Certificate.singleton {n : ℕ} {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    Certificate weights relation where
  relations := [relation]
  valid := by simpa
  target_eq := by simp [aggregate]
def Certificate.add {n : ℕ} {weights firstTarget secondTarget : Relation n}
    (first : Certificate weights firstTarget)
    (second : Certificate weights secondTarget) :
    Certificate weights (firstTarget + secondTarget) where
  relations := first.relations ++ second.relations
  valid := by
    intro relation hrelation
    rcases List.mem_append.mp hrelation with hfirst | hsecond
    · exact first.valid relation hfirst
    · exact second.valid relation hsecond
  target_eq := by
    unfold aggregate
    rw [List.sum_append]
    simpa only [aggregate] using
      congrArg₂ (fun firstRelation secondRelation =>
        firstRelation + secondRelation) first.target_eq second.target_eq
def Certificate.castTarget {n : ℕ} {weights firstTarget secondTarget : Relation n}
    (certificate : Certificate weights firstTarget)
    (htarget : firstTarget = secondTarget) :
    Certificate weights secondTarget := by
  subst secondTarget
  exact certificate
def Certificate.sum {n : ℕ} {weights : Relation n} :
    (certificates : List (Σ target, Certificate weights target)) →
      Certificate weights (certificates.map Sigma.fst).sum
  | [] =>
      { relations := []
        valid := by simp
        target_eq := by simp [aggregate] }
  | ⟨target, certificate⟩ :: certificates => by
      simpa using certificate.add (Certificate.sum certificates)
def extendWeights {n : ℕ} (head : ℤ) (weights : Relation n) : Relation (n + 1) :=
  Fin.cases head fun i => head + weights i
def lift {n : ℕ} (relation : Relation n) : Relation (n + 1) :=
  Fin.cases (-coordinateSum relation) relation
@[simp]
lemma coordinateSum_lift {n : ℕ} (relation : Relation n) :
    coordinateSum (lift relation) = 0 := by
  simp [coordinateSum, lift, Fin.sum_univ_succ]
lemma lift_add {n : ℕ} (first second : Relation n) :
    lift (first + second) = lift first + lift second := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [lift, coordinateSum_add, add_comm]
  · simp [lift]
lemma lift_aggregate {n : ℕ} (relations : List (Relation n)) :
    aggregate (relations.map lift) = lift (aggregate relations) := by
  induction relations with
  | nil =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [aggregate, lift, coordinateSum]
  | cons relation relations inductionHypothesis =>
      change lift relation + aggregate (relations.map lift) =
        lift (relation + aggregate relations)
      rw [inductionHypothesis, lift_add]
def iteratedLift {n : ℕ} (relation : Relation n) :
    (steps : ℕ) → Relation (n + steps)
  | 0 => relation
  | steps + 1 => lift (iteratedLift relation steps)
def castRelation {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (relation : Relation firstDimension) : Relation secondDimension := by
  subst secondDimension
  exact relation
lemma dot_lift_extendWeights {n : ℕ} (head : ℤ)
    (weights relation : Relation n) :
    dot (lift relation) (extendWeights head weights) = dot relation weights := by
  simp only [dot, lift, extendWeights, Fin.sum_univ_succ, Fin.cases_zero,
    Fin.cases_succ, neg_mul, Finset.sum_add_distrib, mul_add]
  rw [← Finset.sum_mul]
  simp [coordinateSum]
lemma IsLiftableUnit.lift {n : ℕ} {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) (head : ℤ) :
    IsLiftableUnit (extendWeights head weights) (lift relation) := by
  refine ⟨?_, dot_lift_extendWeights head weights relation ▸ hrelation.2.1, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rcases hrelation.2.2 with hsum | hsum | hsum
      · right
        right
        change -coordinateSum relation = 1
        rw [hsum]
        norm_num
      · right
        left
        change -coordinateSum relation = 0
        rw [hsum]
        norm_num
      · left
        change -coordinateSum relation = -1
        rw [hsum]
    · change relation j = -1 ∨ relation j = 0 ∨ relation j = 1
      exact hrelation.1 j
  · simp [coordinateSum_lift]
def Certificate.lift {n : ℕ} {weights target : Relation n}
    (certificate : Certificate weights target) (head : ℤ) :
    Certificate (extendWeights head weights) (lift target) where
  relations := certificate.relations.map CoherentGap.lift
  valid := by
    intro relation hrelation
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hrelation
    exact (certificate.valid source hsource).lift head
  target_eq := by
    rw [lift_aggregate, certificate.target_eq]
@[simp]
lemma lift_basis {n : ℕ} (coordinate : Fin n) :
    lift (basis coordinate) =
      basis coordinate.succ - basis (0 : Fin (n + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hne : (0 : Fin (n + 1)) ≠ coordinate.succ := by
      intro heq
      have hval := congrArg Fin.val heq
      simp at hval
    simp [lift, coordinateSum, basis, hne]
  · simp [lift, basis]
structure WeightTower where
  /-- The reference row in each dimension. -/
  weights : (n : ℕ) → Relation n
  /-- The coordinate adjoined when passing from dimension `n` to `n + 1`. -/
  head : ℕ → ℤ
  /-- Every row is obtained from the preceding row by the dimension lift. -/
  step : ∀ n, weights (n + 1) = extendWeights (head n) (weights n)
def WeightTower.liftCertificate (tower : WeightTower) {n : ℕ}
    {target : Relation n} (certificate : Certificate (tower.weights n) target) :
    Certificate (tower.weights (n + 1)) (lift target) := by
  rw [tower.step]
  exact certificate.lift (tower.head n)
def WeightTower.iteratedLiftCertificate (tower : WeightTower) {n : ℕ}
    {target : Relation n} (certificate : Certificate (tower.weights n) target) :
    (steps : ℕ) →
      Certificate (tower.weights (n + steps)) (iteratedLift target steps)
  | 0 => certificate
  | steps + 1 =>
      tower.liftCertificate
        (tower.iteratedLiftCertificate certificate steps)
def Certificate.castDimension {firstDimension secondDimension : ℕ}
    (tower : WeightTower) {target : Relation firstDimension}
    (certificate : Certificate (tower.weights firstDimension) target)
    (hdimension : firstDimension = secondDimension) :
    Certificate (tower.weights secondDimension)
      (castRelation hdimension target) := by
  subst secondDimension
  exact certificate
structure Correction (dimension : ℕ) where
  /-- The source dimension is `sourceOffset + 1`. -/
  sourceOffset : ℕ
  /-- The smaller-dimensional coordinate whose certificate is lifted. -/
  sourceCoordinate : Fin (sourceOffset + 1)
  /-- Number of dimension lifts. -/
  steps : ℕ
  /-- Every correction comes from a strictly smaller dimension. -/
  steps_pos : 0 < steps
  /-- Lifting reaches the target dimension exactly. -/
  dimension_eq : (sourceOffset + 1) + steps = dimension
lemma Correction.sourceDimension_lt {dimension : ℕ}
    (correction : Correction dimension) :
    correction.sourceOffset + 1 < dimension := by
  calc
    correction.sourceOffset + 1 <
        (correction.sourceOffset + 1) + correction.steps :=
      Nat.lt_add_of_pos_right correction.steps_pos
    _ = dimension := correction.dimension_eq
def Correction.target {dimension : ℕ}
    (correction : Correction dimension) : Relation dimension :=
  castRelation correction.dimension_eq
    (iteratedLift (basis correction.sourceCoordinate) correction.steps)
def Correction.liftCertificate {dimension : ℕ}
    (correction : Correction dimension) (tower : WeightTower)
    (certificate : Certificate (tower.weights (correction.sourceOffset + 1))
      (basis correction.sourceCoordinate)) :
    Certificate (tower.weights dimension) correction.target := by
  unfold Correction.target
  exact Certificate.castDimension tower
    (tower.iteratedLiftCertificate certificate correction.steps)
    correction.dimension_eq
structure FirstCoordinateRecurrence (tower : WeightTower) where
  /-- First-coordinate certificate in dimension one. -/
  base : Certificate (tower.weights 1) (basis 0)
  /-- The new principal relation in dimension `offset + 2`. -/
  principal : ∀ offset, Relation (offset + 2)
  /-- Every principal relation belongs to the liftable unit system. -/
  principal_valid :
    ∀ offset, IsLiftableUnit (tower.weights (offset + 2)) (principal offset)
  /-- Smaller-dimensional certificate lifts used to cancel the principal relation. -/
  corrections : ∀ offset, List (Correction (offset + 2))
  /-- The principal relation plus all correction targets is the first basis vector. -/
  decomposition : ∀ offset,
    principal offset +
      ((corrections offset).map Correction.target).sum = basis 0
def allCoordinatesOfFirst (tower : WeightTower)
    (first : ∀ n, Certificate (tower.weights (n + 1)) (basis 0)) :
    ∀ n (coordinate : Fin n), Certificate (tower.weights n) (basis coordinate)
  | 0, coordinate => Fin.elim0 coordinate
  | n + 1, coordinate => by
      refine Fin.cases (first n) (fun previous => ?_) coordinate
      have shifted := tower.liftCertificate
        (allCoordinatesOfFirst tower first n previous)
      exact (first n).add shifted |>.castTarget (by
        rw [lift_basis]
        simp)
theorem recurrenceCertificate_exists (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) :
    ∀ dimension (coordinate : Fin dimension),
      Nonempty (Certificate (tower.weights dimension) (basis coordinate)) := by
  intro dimension
  induction dimension using Nat.strong_induction_on with
  | h dimension inductionHypothesis =>
      intro coordinate
      rcases dimension with _ | dimension
      · exact Fin.elim0 coordinate
      rcases dimension with _ | offset
      · change Fin 1 at coordinate
        have hcoordinate : coordinate = 0 := Fin.eq_zero coordinate
        subst coordinate
        exact ⟨recurrence.base⟩
      · let correctionCertificates :
            List (Σ target, Certificate (tower.weights (offset + 2)) target) :=
          (recurrence.corrections offset).map fun correction =>
            ⟨correction.target,
              correction.liftCertificate tower
                (Classical.choice
                  (inductionHypothesis (correction.sourceOffset + 1)
                    correction.sourceDimension_lt correction.sourceCoordinate))⟩
        let combined :=
          (Certificate.singleton (recurrence.principal_valid offset)).add
            (Certificate.sum correctionCertificates)
        have htarget :
            recurrence.principal offset +
              (correctionCertificates.map Sigma.fst).sum = basis 0 := by
          have hcorrections :
              correctionCertificates.map Sigma.fst =
                (recurrence.corrections offset).map Correction.target := by
            simp [correctionCertificates]
          rw [hcorrections]
          exact recurrence.decomposition offset
        let first : Certificate (tower.weights (offset + 2)) (basis 0) :=
          combined.castTarget htarget
        refine Fin.cases ⟨first⟩ (fun previous => ?_) coordinate
        have previousCertificate :=
          Classical.choice
            (inductionHypothesis (offset + 1) (by omega) previous)
        have shifted := tower.liftCertificate previousCertificate
        refine ⟨(first.add shifted).castTarget ?_⟩
        rw [lift_basis]
        simp
noncomputable def recurrenceCertificates (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) :
    ∀ n (coordinate : Fin n),
      Certificate (tower.weights n) (basis coordinate) :=
  fun n coordinate =>
    Classical.choice (recurrenceCertificate_exists tower recurrence n coordinate)
def realDot {n : ℕ} (relation : Relation n) (candidate : Fin n → ℝ) : ℝ :=
  ∑ i, (relation i : ℝ) * candidate i
end BooleanIsoperimetry.CoherentGap


