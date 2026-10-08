-- Prove2me | Definitions.Def_MidpointLenses
-- name    : MidpointLenses
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.242999+00:00
-- url     : https://prove2.me/theorems/b356d1ba-c1b3-4d4b-9f5f-124d46ac80e0
-- statement:
--   This block builds a Banach-space framework from tests over families of disjoint segments in a vertex set V. A SegmentSystem on V specifies which finite subsets of V count as segments, requiring every singleton to be a segment. A SegmentFamily is a finite collection of pairwise disjoint segments; its column for a vertex v is the 0/1 vector in Euclidean space indexed by the family's sets recording which set contains v, and its test is the linear map sending a finitely supported real function u on V to the vector of block sums of u over the sets, with seminorm equal to the Euclidean norm of that vector. The segmentSeminorm is the pointwise supremum of these seminorms over all segment families, which is finite because each is bounded by the l1 norm. Singleton families show that each coordinate satisfies |u(v)| ≤ segmentSeminorm(u), so this seminorm is a genuine norm on the space Test(V) of finitely supported real functions, making it a real normed space, and evaluation at each vertex is a continuous linear functional of norm at most 1. Primal(V) is the completion of Test(V), FullDual(V) is its continuous dual, unitVector(v) is the basis element at v, and coordinate(v) is the extension of evaluation at v. CoordinatePredual(V) is the closed linear span of these coordinate functionals inside the dual. For a finite set H of vertices, head(H,x) is the sum over v in H of x(unitVector v) times coordinate(v), and tail(H,x) is x minus head(H,x). Auxiliary notions include IsInterval, meaning a set equals all vertices between two ancestor-related endpoints a and b, and Ancestral, meaning a set closed under ancestors. Two concrete segment systems are given: on infinite vertices, which are lists of naturals, segments are intervals under the list-prefix order, and on ForestVertex, pairs (n, list) with n ≥ 1 and list length at most n, segments are intervals in the ancestor order that requires equal first coordinates and a prefix relation on the lists. The abbreviations J, X, JInfinite and BInfinite denote the primal and dual spaces for the forest system and the primal and coordinate predual for the infinite system.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MidpointLenses.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MidpointLenses.lean; bytes 16..13144
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

/-!
# Segment tests, their completion, and coordinate functionals
-/



open scoped BigOperators
open Finset

namespace SegmentLenses

abbrev InfiniteVertex := List ℕ

def ForestVertex := {p : ℕ × List ℕ // 1 ≤ p.1 ∧ p.2.length ≤ p.1}

def ForestAncestor (a b : ForestVertex) : Prop :=
  a.val.1 = b.val.1 ∧ a.val.2.IsPrefix b.val.2

def IsInterval {V : Type*} (ancestor : V → V → Prop) (S : Finset V) : Prop :=
  ∃ a b, ancestor a b ∧ ∀ v, v ∈ S ↔ ancestor a v ∧ ancestor v b

def Ancestral {V : Type*} (ancestor : V → V → Prop) (H : Finset V) : Prop :=
  ∀ ⦃a b⦄, b ∈ H → ancestor a b → a ∈ H

class SegmentSystem (V : Type*) where
  isSegment : Finset V → Prop
  singleton : ∀ v, isSegment {v}

structure SegmentFamily (V : Type*) [SegmentSystem V] where
  sets : Finset (Finset V)
  segment : ∀ S ∈ sets, SegmentSystem.isSegment S
  disjoint : (sets : Set (Finset V)).PairwiseDisjoint id

namespace SegmentFamily

variable {V : Type*} [SegmentSystem V]

def column (F : SegmentFamily V) (v : V) : EuclideanSpace ℝ F.sets :=
  by classical exact WithLp.toLp 2 (fun S => if v ∈ S.val then 1 else 0)

def test (F : SegmentFamily V) : (V →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ F.sets :=
  Finsupp.linearCombination ℝ F.column

def seminorm (F : SegmentFamily V) : Seminorm ℝ (V →₀ ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ F.sets)).comp F.test

def singleton (v : V) : SegmentFamily V where
  sets := {{v}}
  segment := by
    intro S h
    have he : S = {v} := Finset.mem_singleton.mp h
    rw [he]
    exact SegmentSystem.singleton v
  disjoint := by
    intro S hS T hT hne
    simp only [Finset.mem_coe, Finset.mem_singleton] at hS hT
    exact False.elim (hne (hS.trans hT.symm))

end SegmentFamily

def segmentSeminorm (V : Type*) [SegmentSystem V] : Seminorm ℝ (V →₀ ℝ) :=
  ⨆ F : SegmentFamily V, F.seminorm

def Test (V : Type*) := V →₀ ℝ

namespace Test

variable {V : Type*}
instance : AddCommGroup (Test V) := inferInstanceAs (AddCommGroup (V →₀ ℝ))
instance : Module ℝ (Test V) := inferInstanceAs (Module ℝ (V →₀ ℝ))

def coeff (u : Test V) : V →₀ ℝ := u

def ofFinsupp (u : V →₀ ℝ) : Test V := u

variable [SegmentSystem V]
instance : Norm (Test V) where norm u := segmentSeminorm V u.coeff

instance : NormedAddCommGroup (Test V) := by
  have norm_column_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
    classical
    by_cases hv : ∃ S ∈ F.sets, v ∈ S
    · obtain ⟨S, hS, hvS⟩ := hv
      have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
        ext T
        change (if v ∈ T.val then (1 : ℝ) else 0) = _
        by_cases hTS : T = ⟨S, hS⟩
        · subst T
          simp [hvS]
        · have hn : v ∉ T.val := by
            intro hvT
            have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
            exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
          simp [hTS, hn]
      rw [he, PiLp.norm_single]
      norm_num
    · have he : F.column v = 0 := by
        ext S
        have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
        simp [SegmentFamily.column, hn]
      rw [he, norm_zero]
      norm_num
  have test_apply {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
      F.test u S = ∑ v ∈ S.val, u v := by
    classical
    simp only [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, SegmentFamily.column,
      smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_subset
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv hnv
      have hnot : v ∉ u.support := by
        intro hvs
        exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
      exact Finsupp.notMem_support_iff.mp hnot
  have norm_test_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
    classical
    rw [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum]
    calc
      ‖∑ v ∈ u.support, u v • F.column v‖ ≤
          ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_column_le F v)
  have seminorm_sq {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
    change ‖F.test u‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [test_apply]
  have singleton_seminorm {V : Type _} [SegmentSystem V] (v : V) (u : V →₀ ℝ) :
      (SegmentFamily.singleton v).seminorm u = |u v| := by
    have h := seminorm_sq (SegmentFamily.singleton v) u
    have hh : (∑ S : (SegmentFamily.singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
      exact (Finset.sum_coe_sort (SegmentFamily.singleton v).sets
        (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [SegmentFamily.singleton])
    rw [hh] at h
    have hn := apply_nonneg (SegmentFamily.singleton v).seminorm u
    nlinarith [sq_abs (u v), abs_nonneg (u v)]
  have segmentTests_bdd (V : Type _) [SegmentSystem V] :
      BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
    rw [Seminorm.bddAbove_iff]
    refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
    rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
    exact norm_test_le F u
  have le_segmentSeminorm {V : Type _} [SegmentSystem V]
      (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
    have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
    exact Seminorm.le_def.mp h u
  have abs_coord_le {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
      |u v| ≤ segmentSeminorm V u := by
    rw [← singleton_seminorm v u]
    exact le_segmentSeminorm _ _
  have segmentSeminorm_eq_zero {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) :
      segmentSeminorm V u = 0 ↔ u = 0 := by
    constructor
    · intro h
      ext v
      have hh := abs_coord_le u v
      rw [h] at hh
      simpa using hh
    · rintro rfl
      exact map_zero _
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg u := apply_nonneg (segmentSeminorm V) u.coeff
    norm_smul c u := map_smul_eq_mul (segmentSeminorm V) c u.coeff
    norm_triangle u v := map_add_le_add (segmentSeminorm V) u.coeff v.coeff
    norm_eq_zero_iff u := segmentSeminorm_eq_zero u.coeff }
instance : NormedSpace ℝ (Test V) where
  norm_smul_le c u := le_of_eq (map_smul_eq_mul (segmentSeminorm V) c u.coeff)

def evaluation (v : V) : Test V →L[ℝ] ℝ := by
  have norm_column_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
    classical
    by_cases hv : ∃ S ∈ F.sets, v ∈ S
    · obtain ⟨S, hS, hvS⟩ := hv
      have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
        ext T
        change (if v ∈ T.val then (1 : ℝ) else 0) = _
        by_cases hTS : T = ⟨S, hS⟩
        · subst T
          simp [hvS]
        · have hn : v ∉ T.val := by
            intro hvT
            have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
            exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
          simp [hTS, hn]
      rw [he, PiLp.norm_single]
      norm_num
    · have he : F.column v = 0 := by
        ext S
        have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
        simp [SegmentFamily.column, hn]
      rw [he, norm_zero]
      norm_num
  have test_apply {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
      F.test u S = ∑ v ∈ S.val, u v := by
    classical
    simp only [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, SegmentFamily.column,
      smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_subset
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv hnv
      have hnot : v ∉ u.support := by
        intro hvs
        exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
      exact Finsupp.notMem_support_iff.mp hnot
  have norm_test_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
    classical
    rw [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum]
    calc
      ‖∑ v ∈ u.support, u v • F.column v‖ ≤
          ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_column_le F v)
  have seminorm_sq {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
    change ‖F.test u‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [test_apply]
  have singleton_seminorm {V : Type _} [SegmentSystem V] (v : V) (u : V →₀ ℝ) :
      (SegmentFamily.singleton v).seminorm u = |u v| := by
    have h := seminorm_sq (SegmentFamily.singleton v) u
    have hh : (∑ S : (SegmentFamily.singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
      exact (Finset.sum_coe_sort (SegmentFamily.singleton v).sets
        (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [SegmentFamily.singleton])
    rw [hh] at h
    have hn := apply_nonneg (SegmentFamily.singleton v).seminorm u
    nlinarith [sq_abs (u v), abs_nonneg (u v)]
  have segmentTests_bdd (V : Type _) [SegmentSystem V] :
      BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
    rw [Seminorm.bddAbove_iff]
    refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
    rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
    exact norm_test_le F u
  have le_segmentSeminorm {V : Type _} [SegmentSystem V]
      (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
    have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
    exact Seminorm.le_def.mp h u
  have abs_coord_le {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
      |u v| ≤ segmentSeminorm V u := by
    rw [← singleton_seminorm v u]
    exact le_segmentSeminorm _ _
  exact let f : Test V →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.coeff v
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    f.mkContinuous 1 (fun u => by
      change |u.coeff v| ≤ 1 * segmentSeminorm V u.coeff
      simpa only [one_mul] using abs_coord_le u.coeff v)

end Test

abbrev Primal (V : Type*) [SegmentSystem V] := UniformSpace.Completion (Test V)

abbrev FullDual (V : Type*) [SegmentSystem V] := StrongDual ℝ (Primal V)

def unitVector {V : Type*} [SegmentSystem V] (v : V) : Primal V :=
  (Test.ofFinsupp (Finsupp.single v 1) : Test V)

def coordinate {V : Type*} [SegmentSystem V] (v : V) : FullDual V :=
  (Test.evaluation v).extend UniformSpace.Completion.toComplL

def coordinateSpan (V : Type*) [SegmentSystem V] : Submodule ℝ (FullDual V) :=
  (Submodule.span ℝ (Set.range (coordinate (V := V)))).topologicalClosure

abbrev CoordinatePredual (V : Type*) [SegmentSystem V] : Type _ := ↥(coordinateSpan V)

def head {V : Type*} [SegmentSystem V] (H : Finset V) (x : FullDual V) : FullDual V :=
  ∑ v ∈ H, x (unitVector v) • coordinate v

def tail {V : Type*} [SegmentSystem V] (H : Finset V) (x : FullDual V) : FullDual V :=
  x - head H x

instance infiniteSegments : SegmentSystem InfiniteVertex where
  isSegment := IsInterval List.IsPrefix
  singleton v := by
    refine ⟨v, v, List.prefix_rfl, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · rintro ⟨hvw, hwv⟩
      exact hwv.eq_of_length (Nat.le_antisymm hwv.length_le hvw.length_le)

instance forestSegments : SegmentSystem ForestVertex where
  isSegment := IsInterval ForestAncestor
  singleton v := by
    refine ⟨v, v, ⟨rfl, List.prefix_rfl⟩, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨⟨rfl, List.prefix_rfl⟩, ⟨rfl, List.prefix_rfl⟩⟩
    · rintro ⟨hvw, hwv⟩
      exact Subtype.ext (Prod.ext hwv.1 (hwv.2.eq_of_length (Nat.le_antisymm hwv.2.length_le hvw.2.length_le)))

abbrev J := Primal ForestVertex

abbrev X := FullDual ForestVertex

abbrev JInfinite := Primal InfiniteVertex

abbrev BInfinite := CoordinatePredual InfiniteVertex



end SegmentLenses
end
end OAI


