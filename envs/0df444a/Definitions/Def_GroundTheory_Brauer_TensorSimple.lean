-- Prove2me | Definitions.Def_GroundTheory_Brauer_TensorSimple
-- name    : GroundTheory_Brauer_TensorSimple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:58.595579+00:00
-- url     : https://prove2.me/theorems/aea248f9-c12d-4ef3-9f23-c8ef83d787a4
-- title:
--   Tensor Simple
-- statement:
--   Definitions and structural lemmas for Tensor Simple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/TensorSimple.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open TensorProduct Algebra.TensorProduct
section Coefficients
variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
variable {κ : Type*} [DecidableEq κ] (𝒞 : Module.Basis κ K B)
theorem coeff_tmul_one_mul (a : A) (x : A ⊗[K] B) (i : κ) :
    TensorProduct.equivFinsuppOfBasisRight 𝒞 ((a ⊗ₜ[K] (1 : B)) * x) i =
      a * TensorProduct.equivFinsuppOfBasisRight 𝒞 x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a' b =>
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [mul_add, map_add, Finsupp.add_apply, hx, hy]
theorem coeff_mul_tmul_one (a : A) (x : A ⊗[K] B) (i : κ) :
    TensorProduct.equivFinsuppOfBasisRight 𝒞 (x * (a ⊗ₜ[K] (1 : B))) i =
      TensorProduct.equivFinsuppOfBasisRight 𝒞 x i * a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a' b =>
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [add_mul, map_add, Finsupp.add_apply, hx, hy]
theorem support_coeff_tmul_one_mul (a : A) (x : A ⊗[K] B) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞 ((a ⊗ₜ[K] (1 : B)) * x)).support ⊆
      (TensorProduct.equivFinsuppOfBasisRight 𝒞 x).support := by
  intro i hi
  rw [Finsupp.mem_support_iff, coeff_tmul_one_mul] at hi
  rw [Finsupp.mem_support_iff]
  intro h
  exact hi (by rw [h, mul_zero])
theorem support_coeff_mul_tmul_one (a : A) (x : A ⊗[K] B) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞 (x * (a ⊗ₜ[K] (1 : B)))).support ⊆
      (TensorProduct.equivFinsuppOfBasisRight 𝒞 x).support := by
  intro i hi
  rw [Finsupp.mem_support_iff, coeff_mul_tmul_one] at hi
  rw [Finsupp.mem_support_iff]
  intro h
  exact hi (by rw [h, zero_mul])
end Coefficients
section Central
variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
theorem exists_eq_one_tmul_of_commute [Algebra.IsCentral K A] (x : A ⊗[K] B)
    (h : ∀ a : A, (a ⊗ₜ[K] (1 : B)) * x = x * (a ⊗ₜ[K] (1 : B))) :
    ∃ b : B, x = (1 : A) ⊗ₜ[K] b := by
  classical
  let 𝒞 := Module.Basis.ofVectorSpace K B
  let φ := TensorProduct.equivFinsuppOfBasisRight (M := A) 𝒞
  have hc : ∀ i, ∃ k : K, φ x i = algebraMap K A k := fun i ↦ by
    rw [← Algebra.IsCentral.mem_center_iff (K := K), Subalgebra.mem_center_iff]
    intro a
    have := congrArg (fun y ↦ φ y i) (h a)
    simpa only [φ, coeff_tmul_one_mul, coeff_mul_tmul_one] using this
  choose k hk using hc
  refine ⟨(φ x).sum fun i _ ↦ k i • 𝒞 i, ?_⟩
  conv_lhs => rw [← φ.symm_apply_apply x]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum, Finsupp.sum,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hk i, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
variable (K A B)
theorem center_tensorProduct_eq_map_includeRight [Algebra.IsCentral K A] :
    Subalgebra.center K (A ⊗[K] B) = (Subalgebra.center K B).map includeRight := by
  refine le_antisymm ?_ (Algebra.TensorProduct.includeRight_map_center_le K A B)
  intro x hx
  rw [Subalgebra.mem_center_iff] at hx
  obtain ⟨b, rfl⟩ := exists_eq_one_tmul_of_commute x fun a ↦ hx _
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [Subsingleton.elim (1 : A) 0, zero_tmul, map_zero]
  · have hb : b ∈ Subalgebra.center K B := by
      rw [Subalgebra.mem_center_iff]
      intro c
      have hinj : Function.Injective (includeRight : B →ₐ[K] A ⊗[K] B) :=
        Algebra.TensorProduct.includeRight_injective (algebraMap K A).injective
      apply hinj
      have := hx ((1 : A) ⊗ₜ[K] c)
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
    exact ⟨b, hb, rfl⟩
instance isCentral_tensorProduct [Algebra.IsCentral K A] [Algebra.IsCentral K B] :
    Algebra.IsCentral K (A ⊗[K] B) where
  out := by
    rw [center_tensorProduct_eq_map_includeRight, Algebra.IsCentral.center_eq_bot, Algebra.map_bot]
end Central
section Simple
variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
theorem exists_one_tmul_mem_of_ne_bot [Algebra.IsCentral K A] [IsSimpleRing A]
    (I : TwoSidedIdeal (A ⊗[K] B)) (hI : I ≠ ⊥) :
    ∃ b : B, b ≠ 0 ∧ (1 : A) ⊗ₜ[K] b ∈ I := by
  classical
  let 𝒞 := Module.Basis.ofVectorSpace K B
  let φ := TensorProduct.equivFinsuppOfBasisRight (M := A) 𝒞
  have hex : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ (φ x).support.card = n := by
    by_contra hne
    apply hI
    ext x
    rw [TwoSidedIdeal.mem_bot]
    refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ I.zero_mem⟩
    by_contra hx0
    exact hne ⟨_, x, hx, hx0, rfl⟩
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ I, y ≠ 0 → Nat.find hex ≤ (φ y).support.card :=
    fun y hy hy0 ↦ Nat.find_min' hex ⟨y, hy, hy0, rfl⟩
  set n := Nat.find hex
  have hφx : φ x ≠ 0 := fun h ↦ hx0 (φ.map_eq_zero_iff.mp h)
  obtain ⟨i₀, hi₀⟩ := Finsupp.support_nonempty_iff.mpr hφx

  let J : TwoSidedIdeal A := TwoSidedIdeal.mk'
    {a | ∃ y ∈ I, (φ y).support ⊆ (φ x).support ∧ φ y i₀ = a}
    ⟨0, I.zero_mem, by simp, by simp⟩
    (by
      rintro _ _ ⟨y, hy, hys, rfl⟩ ⟨z, hz, hzs, rfl⟩
      refine ⟨y + z, I.add_mem hy hz, ?_, by simp⟩
      rw [map_add]
      exact Finsupp.support_add.trans (Finset.union_subset hys hzs))
    (by
      rintro _ ⟨y, hy, hys, rfl⟩
      refine ⟨-y, I.neg_mem hy, ?_, by simp⟩
      rw [map_neg, Finsupp.support_neg]
      exact hys)
    (by
      rintro a _ ⟨y, hy, hys, rfl⟩
      exact ⟨(a ⊗ₜ[K] (1 : B)) * y, I.mul_mem_left _ _ hy,
        (support_coeff_tmul_one_mul 𝒞 a y).trans hys, coeff_tmul_one_mul 𝒞 a y i₀⟩)
    (by
      rintro _ a ⟨y, hy, hys, rfl⟩
      exact ⟨y * (a ⊗ₜ[K] (1 : B)), I.mul_mem_right _ _ hy,
        (support_coeff_mul_tmul_one 𝒞 a y).trans hys, coeff_mul_tmul_one 𝒞 a y i₀⟩)
  have h1J : (1 : A) ∈ J :=
    IsSimpleRing.one_mem_of_ne_zero_mem J (Finsupp.mem_support_iff.mp hi₀)
      ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr ⟨x, hxI, subset_rfl, rfl⟩)
  obtain ⟨y, hyI, hys, hy1⟩ := (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp h1J
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy1
  have hyeq : (φ y).support = (φ x).support :=
    Finset.eq_of_subset_of_card_le hys (hxn ▸ hmin y hyI hy0)
  have hcomm : ∀ a : A, (a ⊗ₜ[K] (1 : B)) * y = y * (a ⊗ₜ[K] (1 : B)) := by
    intro a
    rw [← sub_eq_zero]
    by_contra hz0
    have hzI : (a ⊗ₜ[K] (1 : B)) * y - y * (a ⊗ₜ[K] (1 : B)) ∈ I :=
      I.sub_mem (I.mul_mem_left _ _ hyI) (I.mul_mem_right _ _ hyI)
    have hsub : (φ ((a ⊗ₜ[K] (1 : B)) * y - y * (a ⊗ₜ[K] (1 : B)))).support ⊆
        (φ y).support.erase i₀ := by
      intro i hi
      rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply, coeff_tmul_one_mul,
        coeff_mul_tmul_one] at hi
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · rintro rfl
        exact hi (by rw [hy1, mul_one, one_mul, sub_self])
      · rw [Finsupp.mem_support_iff]
        intro h
        exact hi (by rw [h, mul_zero, zero_mul, sub_zero])
    have hi₀y : i₀ ∈ (φ y).support := hyeq ▸ hi₀
    have := (hmin _ hzI hz0).trans (Finset.card_le_card hsub)
    rw [Finset.card_erase_of_mem hi₀y, hyeq, hxn] at this
    have hn : 0 < n := hxn ▸ Finset.card_pos.mpr ⟨i₀, hi₀⟩
    omega
  obtain ⟨b, rfl⟩ := exists_eq_one_tmul_of_commute y hcomm
  refine ⟨b, ?_, hyI⟩
  rintro rfl
  exact hy0 (tmul_zero _ _)
instance isSimpleRing_tensorProduct [Algebra.IsCentral K A] [IsSimpleRing A] [IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ ?_
  refine or_iff_not_imp_left.mpr fun hI ↦ ?_
  obtain ⟨b, hb0, hbI⟩ := exists_one_tmul_mem_of_ne_bot I hI
  let J : TwoSidedIdeal B := TwoSidedIdeal.mk' {c | (1 : A) ⊗ₜ[K] c ∈ I}
    (by simp [I.zero_mem])
    (fun hx hy ↦ by simpa [tmul_add] using I.add_mem hx hy)
    (fun hx ↦ by simpa [tmul_neg] using I.neg_mem hx)
    (fun {x _} hy ↦ by
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using I.mul_mem_left ((1 : A) ⊗ₜ[K] x) _ hy)
    (fun {_ y} hx ↦ by
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using I.mul_mem_right _ ((1 : A) ⊗ₜ[K] y) hx)
  have h1 : (1 : B) ∈ J := IsSimpleRing.one_mem_of_ne_zero_mem J hb0
    ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr hbI)
  simp only [J, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq] at h1
  rw [← Algebra.TensorProduct.one_def] at h1
  exact (TwoSidedIdeal.one_mem_iff I).mp h1
instance isSimpleRing_tensorProduct_of_right [Algebra.IsCentral K A] [IsSimpleRing A]
    [IsSimpleRing B] : IsSimpleRing (B ⊗[K] A) :=
  IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm K A B).toRingEquiv
    isSimpleRing_tensorProduct
end Simple
section CSA
universe u v
variable {K : Type u} [Field K]
noncomputable def tensorCSA (A B : CSA.{u, v} K) : CSA.{u, v} K where
  toAlgCat := AlgCat.of K (A ⊗[K] B)
end CSA
end GroundTheory.Brauer


