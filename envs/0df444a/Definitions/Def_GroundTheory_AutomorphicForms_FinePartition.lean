-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
-- name    : GroundTheory_AutomorphicForms_FinePartition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:11.283721+00:00
-- url     : https://prove2.me/theorems/adb445a4-7cac-4a2e-90ee-13a8340e8c62
-- title:
--   Fine Partition
-- statement:
--   Definitions and structural lemmas for Fine Partition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Set Filter Topology Uniformity UniformSpace Function
structure MeasurablePartition (X : Type*) [MeasurableSpace X] where

  n : ℕ

  E : ℕ → Set X
  measurableSet : ∀ i, MeasurableSet (E i)
  disjoint : Pairwise (Disjoint on E)
  exists_mem : ∀ x, ∃ i < n, x ∈ E i
namespace MeasurablePartition
variable {X : Type*} [MeasurableSpace X]
instance : Inhabited (MeasurablePartition X) where
  default :=
    { n := 1
      E := fun i => if i = 0 then univ else ∅
      measurableSet := fun i => by split_ifs <;> simp
      disjoint := by
        intro i j hij
        simp only [Function.onFun]
        by_cases hi : i = 0
        · have hj : j ≠ 0 := fun h => hij (hi.trans h.symm)
          simp [hj]
        · simp [hi]
      exists_mem := fun x => ⟨0, Nat.one_pos, by simp⟩ }
variable (p : MeasurablePartition X)
open Classical in

noncomputable def index (x : X) : ℕ := Nat.find (p.exists_mem x)
def IsFine (V : SetRel X X) : Prop := ∀ i, ∀ x ∈ p.E i, ∀ y ∈ p.E i, (x, y) ∈ V
theorem exists_isFine [UniformSpace X] [CompactSpace X] [OpensMeasurableSpace X] {V : SetRel X X}
    (hV : V ∈ 𝓤 X) : ∃ p : MeasurablePartition X, p.IsFine V := by
  obtain ⟨W, hW, hWo, hWs, hWV⟩ := comp_open_symm_mem_uniformity_sets hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ball x W)
    (fun x => isOpen_ball x hWo) (fun x _ => mem_iUnion.2 ⟨x, mem_ball_self x hW⟩)
  let L := t.toList
  let F : ℕ → Set X := fun i => if h : i < L.length then ball (L.get ⟨i, h⟩) W else ∅
  have hF : ∀ i, MeasurableSet (F i) := by
    intro i
    simp only [F]
    split_ifs
    · exact (isOpen_ball _ hWo).measurableSet
    · exact MeasurableSet.empty
  have hFn : ∀ i, L.length ≤ i → F i = ∅ := by
    intro i hi
    simp only [F, dif_neg (not_lt.2 hi)]
  refine ⟨⟨L.length, disjointed F, MeasurableSet.disjointed hF, disjoint_disjointed F, ?_⟩, ?_⟩
  · intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 (Finset.mem_toList.2 hy)
    have hxF : x ∈ F i := by
      show x ∈ (if h : (i : ℕ) < L.length then ball (L.get ⟨i, h⟩) W else ∅)
      rw [dif_pos i.2]
      exact (show L.get ⟨i, i.2⟩ = y from hi) ▸ hxy
    have hx : x ∈ ⋃ j, disjointed F j := by
      rw [iUnion_disjointed]
      exact mem_iUnion.2 ⟨i, hxF⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    refine ⟨j, ?_, hj⟩
    by_contra hjn
    have := disjointed_subset F j hj
    rw [hFn j (not_lt.1 hjn)] at this
    exact this
  · intro i x hx y hy
    have hxF := disjointed_subset F i hx
    have hyF := disjointed_subset F i hy
    simp only [F] at hxF hyF
    split_ifs at hxF hyF with h
    · have := hWs
      have hx' : L.get ⟨i, h⟩ ∈ ball x W := mem_ball_symmetry.1 hxF
      exact hWV (mem_ball_comp hx' hyF)
    · exact hxF.elim
end MeasurablePartition
open MeasurablePartition
section Filter
variable (X : Type*) [UniformSpace X]
def fineFilter : Filter (SetRel X X) := (𝓤 X).smallSets ⊓ 𝓟 {V | V ∈ 𝓤 X}
instance : (fineFilter X).NeBot := by
  refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
  obtain ⟨t, ht, htU⟩ := (hasBasis_smallSets _).mem_iff.1 hU
  exact ⟨t, htU (mem_powerset subset_rfl), ht⟩
variable {X}
variable [MeasurableSpace X] [CompactSpace X] [OpensMeasurableSpace X]
open Classical in

noncomputable def finePart (V : SetRel X X) : MeasurablePartition X :=
  if h : V ∈ 𝓤 X then (exists_isFine h).choose else default
end Filter
section Measurable
variable {X Y : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [UniformSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]
end Measurable
end GroundTheory.Automorphic


