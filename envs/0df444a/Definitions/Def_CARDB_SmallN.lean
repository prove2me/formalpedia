-- Prove2me | Definitions.Def_CARDB_SmallN
-- name    : CARDB_SmallN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:43:51.569028+00:00
-- url     : https://prove2.me/theorems/d748257d-16cb-429d-934a-ed1457974004
-- title:
--   Small N
-- statement:
--   Definitions and structural lemmas for Small N, from Lars Warren Ericson (catskillsresearch/cardb; see pinned Apache-2.0 LICENSE and NOTICE)'s pinned CARDB: The number of distinct topological bases of a finite set development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/SmallN.lean

import Definitions.Def_CARDB
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
set_option autoImplicit true
open Set TopologicalSpace
def subsetOfNat (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => k.testBit i.val
def familyOfNat (n m : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.range (2 ^ n)).filter (fun j => m.testBit j)).image (subsetOfNat n)
def coversNat (n m : ℕ) : Bool :=
  (List.range n).all fun i =>
    (List.range (2 ^ n)).any fun j =>
      m.testBit j && j.testBit i
def interNat (n m : ℕ) : Bool :=
  (List.range (2 ^ n)).all fun j =>
    (List.range (2 ^ n)).all fun k =>
      !m.testBit j || !m.testBit k ||
        (List.range n).all fun i =>
          !(j.testBit i && k.testBit i) ||
            (List.range (2 ^ n)).any fun w =>
              m.testBit w && w.testBit i &&
                (List.range n).all fun t =>
                  !w.testBit t || (j.testBit t && k.testBit t)
def isBasisNat (n m : ℕ) : Bool :=
  coversNat n m && interNat n m
def numBases (n : ℕ) : ℕ :=
  (List.range (2 ^ (2 ^ n))).countP (fun m => isBasisNat n m)
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
variable {n : ℕ}
def familyOf (B : Finset (Finset (Fin n))) : Set (Set (Fin n)) :=
  {U | ∃ s ∈ B, (s : Set (Fin n)) = U}
lemma mem_subsetOfNat {k : ℕ} {i : Fin n} :
    i ∈ subsetOfNat n k ↔ k.testBit i.val := by
  simp [subsetOfNat]
lemma testBit_sum_two_pow_finset (s : Finset ℕ) {k : ℕ} :
    (∑ i ∈ s, 2 ^ i).testBit k ↔ k ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]
def bitmaskSubset (s : Finset (Fin n)) : ℕ :=
  ∑ i ∈ s, 2 ^ i.val
lemma bitmaskSubset_eq_image (s : Finset (Fin n)) :
    bitmaskSubset s = ∑ i ∈ s.image Fin.val, 2 ^ i := by
  refine (Finset.sum_image ?_).symm
  intro a _ b _ h
  exact Fin.val_injective h
lemma subsetOfNat_bitmaskSubset (s : Finset (Fin n)) :
    subsetOfNat n (bitmaskSubset s) = s := by
  ext i
  rw [mem_subsetOfNat, bitmaskSubset_eq_image, testBit_sum_two_pow_finset, Finset.mem_image]
  exact ⟨fun ⟨j, hj, hij⟩ => Fin.ext hij ▸ hj, fun hi => ⟨i, hi, rfl⟩⟩
lemma sum_range_two_pow (k : ℕ) :
    ∑ i ∈ Finset.range k, 2 ^ i = 2 ^ k - 1 := by
  have h := geom_sum_mul_add (1 : ℕ) k
  simp at h
  exact Nat.eq_sub_of_add_eq h
lemma image_val_subset_range (s : Finset (Fin n)) :
    s.image Fin.val ⊆ Finset.range n := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr j.isLt
lemma bitmaskSubset_lt (s : Finset (Fin n)) : bitmaskSubset s < 2 ^ n := by
  have hle : bitmaskSubset s ≤ ∑ i ∈ Finset.range n, 2 ^ i := by
    rw [bitmaskSubset_eq_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg (image_val_subset_range s)
      (fun _ _ _ => Nat.zero_le _)
  rw [sum_range_two_pow] at hle
  exact hle.trans_lt (Nat.sub_lt (pow_pos (by decide) n) (by decide))
lemma bitmaskSubset_inj : Function.Injective (bitmaskSubset (n := n)) := by
  intro s t h
  simpa [subsetOfNat_bitmaskSubset] using congrArg (subsetOfNat n) h
lemma bitmaskSubset_subsetOfNat {j : ℕ} (hj : j < 2 ^ n) :
    bitmaskSubset (subsetOfNat n j) = j := by
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  rw [bitmaskSubset_eq_image, testBit_sum_two_pow_finset, Finset.mem_image]
  simp only [mem_subsetOfNat]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hk
    by_cases hkn : k < n
    · exact ⟨⟨k, hkn⟩, hk, rfl⟩
    · have : j < 2 ^ k :=
        hj.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (le_of_not_gt hkn))
      cases Nat.testBit_lt_two_pow this ▸ hk
def bitmaskFamily (B : Finset (Finset (Fin n))) : ℕ :=
  ∑ s ∈ B, 2 ^ bitmaskSubset s
lemma bitmaskFamily_eq_image (B : Finset (Finset (Fin n))) :
    bitmaskFamily B = ∑ j ∈ B.image bitmaskSubset, 2 ^ j := by
  refine (Finset.sum_image ?_).symm
  intro a _ b _ h
  exact bitmaskSubset_inj h
lemma image_bitmaskSubset_subset_range (B : Finset (Finset (Fin n))) :
    B.image bitmaskSubset ⊆ Finset.range (2 ^ n) := by
  intro j hj
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr (bitmaskSubset_lt s)
lemma testBit_bitmaskFamily {B : Finset (Finset (Fin n))} {j : ℕ} :
    (bitmaskFamily B).testBit j ↔ ∃ s ∈ B, bitmaskSubset s = j := by
  rw [bitmaskFamily_eq_image, testBit_sum_two_pow_finset, Finset.mem_image]
lemma bitmaskFamily_lt (B : Finset (Finset (Fin n))) :
    bitmaskFamily B < 2 ^ (2 ^ n) := by
  have hle : bitmaskFamily B ≤ ∑ j ∈ Finset.range (2 ^ n), 2 ^ j := by
    rw [bitmaskFamily_eq_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg (image_bitmaskSubset_subset_range B)
      (fun _ _ _ => Nat.zero_le _)
  rw [sum_range_two_pow] at hle
  exact hle.trans_lt (Nat.sub_lt (pow_pos (by decide) _) (by decide))
lemma mem_familyOfNat {m : ℕ} {s : Finset (Fin n)} :
    s ∈ familyOfNat n m ↔ ∃ j < 2 ^ n, m.testBit j = true ∧ subsetOfNat n j = s := by
  constructor
  · intro hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨j, hj.1, hj.2, rfl⟩
  · rintro ⟨j, hj, hbit, rfl⟩
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hbit⟩, rfl⟩
lemma familyOfNat_bitmaskFamily (B : Finset (Finset (Fin n))) :
    familyOfNat n (bitmaskFamily B) = B := by
  ext s
  constructor
  · intro hs
    obtain ⟨j, hj, hbit, hsj⟩ := mem_familyOfNat.mp hs
    obtain ⟨t, ht, rfl⟩ := testBit_bitmaskFamily.mp hbit
    rwa [← hsj, subsetOfNat_bitmaskSubset]
  · intro hs
    exact mem_familyOfNat.mpr
      ⟨bitmaskSubset s, bitmaskSubset_lt s,
        testBit_bitmaskFamily.mpr ⟨s, hs, rfl⟩, subsetOfNat_bitmaskSubset s⟩
lemma bitmaskFamily_familyOfNat {m : ℕ} (hm : m < 2 ^ (2 ^ n)) :
    bitmaskFamily (familyOfNat n m) = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 2 ^ n
  · apply Bool.eq_iff_iff.mpr
    rw [testBit_bitmaskFamily]
    constructor
    · rintro ⟨s, hs, hjs⟩
      obtain ⟨k, hk, hbit, rfl⟩ := mem_familyOfNat.mp hs
      rw [bitmaskSubset_subsetOfNat hk] at hjs
      rwa [← hjs]
    · intro hbit
      exact ⟨subsetOfNat n j,
        mem_familyOfNat.mpr ⟨j, hj, hbit, rfl⟩, bitmaskSubset_subsetOfNat hj⟩
  · have hj' : 2 ^ (2 ^ n) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (le_of_not_gt hj)
    have hmj : m < 2 ^ j := hm.trans_le hj'
    have hBj : bitmaskFamily (familyOfNat n m) < 2 ^ j :=
      (bitmaskFamily_lt _).trans_le hj'
    rw [Nat.testBit_lt_two_pow hmj, Nat.testBit_lt_two_pow hBj]
lemma coversNat_iff (m : ℕ) :
    coversNat n m = true ↔ ∀ i : Fin n, ∃ j < 2 ^ n, m.testBit j = true ∧ j.testBit i.val = true := by
  simp [coversNat, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩
lemma sUnion_familyOf (B : Finset (Finset (Fin n))) :
    ⋃₀ familyOf B = {x | ∃ s ∈ B, x ∈ s} := by
  ext x
  constructor
  · rintro ⟨U, ⟨s, hs, rfl⟩, hx⟩
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨↑s, ⟨s, hs, rfl⟩, hx⟩
lemma covers_familyOfNat (m : ℕ) :
    ⋃₀ familyOf (familyOfNat n m) = univ ↔ coversNat n m = true := by
  rw [coversNat_iff, eq_univ_iff_forall, sUnion_familyOf]
  constructor
  · intro h i
    obtain ⟨s, hs, hi⟩ := h i
    obtain ⟨j, hj, hbit, rfl⟩ := mem_familyOfNat.mp hs
    exact ⟨j, hj, hbit, mem_subsetOfNat.mp hi⟩
  · intro h i
    obtain ⟨j, hj, hbit, hi⟩ := h i
    exact ⟨subsetOfNat n j, mem_familyOfNat.mpr ⟨j, hj, hbit, rfl⟩, mem_subsetOfNat.mpr hi⟩
lemma mem_familyOf {B : Finset (Finset (Fin n))} {U : Set (Fin n)} :
    U ∈ familyOf B ↔ ∃ s ∈ B, (s : Set (Fin n)) = U :=
  Iff.rfl
lemma interNat_spec (m : ℕ) :
    interNat n m = true ↔
      ∀ j < 2 ^ n, ∀ k < 2 ^ n, m.testBit j = true → m.testBit k = true →
        ∀ i < n, j.testBit i = true → k.testBit i = true →
          ∃ w < 2 ^ n, m.testBit w = true ∧ w.testBit i = true ∧
            ∀ t < n, w.testBit t = true → j.testBit t = true ∧ k.testBit t = true := by
  constructor
  · intro h j hj k hk hjB hkB i hi hji hki
    simp only [interNat, List.all_eq_true, List.mem_range] at h
    have hjk := h j hj k hk
    rw [hjB, hkB] at hjk
    simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at hjk
    have hi' := hjk i hi
    rw [hji, hki] at hi'
    simp only [Bool.true_and, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range, Bool.and_eq_true] at hi'
    obtain ⟨w, hw, ⟨⟨hwB, hwi⟩, hrest⟩⟩ := hi'
    refine ⟨w, hw, hwB, hwi, ?_⟩
    simp only [List.all_eq_true, List.mem_range] at hrest
    intro t ht hwt
    have ht' := hrest t ht
    rw [hwt] at ht'
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at ht'
    exact ht'
  · intro h
    simp only [interNat, List.all_eq_true, List.mem_range]
    intro j hj k hk
    cases hjB : m.testBit j <;> cases hkB : m.testBit k
    · rfl
    · rfl
    · rfl
    · apply (List.all_eq_true).2
      intro i hi
      cases hji : j.testBit i <;> cases hki : k.testBit i
      · rfl
      · rfl
      · rfl
      · apply (List.any_eq_true).2
        obtain ⟨w, hw, hwB, hwi, hsub⟩ := h j hj k hk hjB hkB i (List.mem_range.mp hi) hji hki
        refine ⟨w, List.mem_range.mpr hw, ?_⟩
        simp only [hwB, hwi, Bool.true_and]
        apply (List.all_eq_true).2
        intro t ht
        cases hwt : w.testBit t
        · rfl
        · simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
          exact hsub t (List.mem_range.mp ht) hwt
lemma inter_familyOfNat (m : ℕ) :
    (∀ U V, U ∈ familyOf (familyOfNat n m) → V ∈ familyOf (familyOfNat n m) →
      ∀ x ∈ U ∩ V, ∃ W ∈ familyOf (familyOfNat n m), x ∈ W ∧ W ⊆ U ∩ V) ↔
      interNat n m = true := by
  rw [interNat_spec]
  constructor
  · intro hinter j hj k hk hjB hkB i hi hji hki
    have hU : (subsetOfNat n j : Set (Fin n)) ∈ familyOf (familyOfNat n m) :=
      mem_familyOf.mpr ⟨subsetOfNat n j, mem_familyOfNat.mpr ⟨j, hj, hjB, rfl⟩, rfl⟩
    have hV : (subsetOfNat n k : Set (Fin n)) ∈ familyOf (familyOfNat n m) :=
      mem_familyOf.mpr ⟨subsetOfNat n k, mem_familyOfNat.mpr ⟨k, hk, hkB, rfl⟩, rfl⟩
    have hx : (⟨i, hi⟩ : Fin n) ∈
        (subsetOfNat n j : Set (Fin n)) ∩ (subsetOfNat n k : Set (Fin n)) :=
      ⟨mem_subsetOfNat.mpr hji, mem_subsetOfNat.mpr hki⟩
    obtain ⟨W, hW, hxW, hWU⟩ := hinter _ _ hU hV _ hx
    obtain ⟨wset, hwset, rfl⟩ := mem_familyOf.mp hW
    obtain ⟨w, hw, hwB, rfl⟩ := mem_familyOfNat.mp hwset
    refine ⟨w, hw, hwB, mem_subsetOfNat.mp hxW, ?_⟩
    intro t ht hwt
    have hy := hWU (mem_subsetOfNat (k := w) (i := ⟨t, ht⟩) |>.mpr hwt)
    exact ⟨mem_subsetOfNat.mp hy.1, mem_subsetOfNat.mp hy.2⟩
  · intro hinter U V hU hV x hx
    obtain ⟨U₀, hU₀, rfl⟩ := mem_familyOf.mp hU
    obtain ⟨V₀, hV₀, rfl⟩ := mem_familyOf.mp hV
    obtain ⟨j, hj, hjB, rfl⟩ := mem_familyOfNat.mp hU₀
    obtain ⟨k, hk, hkB, rfl⟩ := mem_familyOfNat.mp hV₀
    obtain ⟨w, hw, hwB, hwi, hsub⟩ :=
      hinter j hj k hk hjB hkB x.val x.isLt
        (mem_subsetOfNat.mp hx.1) (mem_subsetOfNat.mp hx.2)
    refine ⟨↑(subsetOfNat n w),
      mem_familyOf.mpr ⟨subsetOfNat n w, mem_familyOfNat.mpr ⟨w, hw, hwB, rfl⟩, rfl⟩,
      mem_subsetOfNat.mpr hwi, ?_⟩
    intro y hy
    have := hsub y.val y.isLt (mem_subsetOfNat.mp hy)
    exact ⟨mem_subsetOfNat.mpr this.1, mem_subsetOfNat.mpr this.2⟩
lemma isBasis_familyOfNat (m : ℕ) :
    IsBasis (familyOf (familyOfNat n m)) ↔ isBasisNat n m = true := by
  constructor
  · intro h
    simp only [isBasisNat, Bool.and_eq_true]
    exact ⟨(covers_familyOfNat m).mp h.1, (inter_familyOfNat m).mp h.2⟩
  · intro h
    simp only [isBasisNat, Bool.and_eq_true] at h
    exact ⟨(covers_familyOfNat m).mpr h.1, (inter_familyOfNat m).mpr h.2⟩
noncomputable def toFinsetFamily (S : Set (Set (Fin n))) : Finset (Finset (Fin n)) :=
  (Fintype.finsetEquivSet.symm S).image
    (Fintype.finsetEquivSet.symm : Set (Fin n) → Finset (Fin n))
lemma mem_toFinsetFamily {S : Set (Set (Fin n))} {s : Finset (Fin n)} :
    s ∈ toFinsetFamily S ↔ (s : Set (Fin n)) ∈ S := by
  constructor
  · intro hs
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hs
    have : U ∈ S := by
      have : U ∈ (↑(Fintype.finsetEquivSet.symm S) : Set (Set (Fin n))) := hU
      simpa [Fintype.finsetEquivSet] using this
    simpa [Fintype.finsetEquivSet] using this
  · intro hs
    refine Finset.mem_image.mpr ⟨↑s, ?_, ?_⟩
    · have : (↑s : Set (Fin n)) ∈ (↑(Fintype.finsetEquivSet.symm S) : Set (Set (Fin n))) := by
        simpa [Fintype.finsetEquivSet] using hs
      exact this
    · simp [Fintype.finsetEquivSet]
lemma familyOf_toFinsetFamily (S : Set (Set (Fin n))) :
    familyOf (toFinsetFamily S) = S := by
  ext U
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (mem_toFinsetFamily.mp hs)
  · intro hU
    refine ⟨Fintype.finsetEquivSet.symm U, ?_, ?_⟩
    · rw [mem_toFinsetFamily]
      simpa [Fintype.finsetEquivSet] using hU
    · simp [Fintype.finsetEquivSet]
lemma toFinsetFamily_familyOf (B : Finset (Finset (Fin n))) :
    toFinsetFamily (familyOf B) = B := by
  ext s
  rw [mem_toFinsetFamily]
  constructor
  · rintro ⟨t, ht, hts⟩
    exact Finset.coe_injective hts ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩
noncomputable def validBasisEquivMask (n : ℕ) :
    ValidBasis (Fin n) ≃ { m : Fin (2 ^ (2 ^ n)) // isBasisNat n m.val = true } where
  toFun := fun B =>
    ⟨⟨bitmaskFamily (toFinsetFamily B.1), bitmaskFamily_lt _⟩, by
      rw [← isBasis_familyOfNat, familyOfNat_bitmaskFamily, familyOf_toFinsetFamily]
      exact B.2⟩
  invFun := fun m =>
    ⟨familyOf (familyOfNat n m.1.val), (isBasis_familyOfNat m.1.val).2 m.2⟩
  left_inv := fun B => by
    apply Subtype.ext
    simp [familyOfNat_bitmaskFamily, familyOf_toFinsetFamily]
  right_inv := fun m => by
    apply Subtype.ext
    apply Fin.ext
    simp [toFinsetFamily_familyOf, bitmaskFamily_familyOfNat m.1.isLt]


