-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:06.34691+00:00
-- url     : https://prove2.me/theorems/7e08ce2a-d0bd-52b2-a433-684324a8d0ff
-- title:
--   Functoriality Norm
-- statement:
--   Definitions and structural lemmas for Functoriality Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule_of_normal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk


set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
section DoubleCoset
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
def doubleCosetMap {K K' S M : Subgroup G} (hK'K : K' ≤ K) {τ : G} (hτ : τ ∈ K)
    (hM : ∀ k ∈ K', k ∈ M → τ * k * τ⁻¹ ∈ S) : K' ⧸ M.subgroupOf K' → K ⧸ S.subgroupOf K :=
  Quotient.map' (fun k : K' => (⟨k * τ⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem hτ)⟩ : K)) fun k k' h => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
    have := hM _ (K'.mul_mem (K'.inv_mem k.2) k'.2) (by simpa using h)
    simpa [mul_assoc] using this
theorem coe_norm_eq_prod_norm_inf {K K' S : Subgroup G} (hK'K : K' ≤ K)
    [(S.subgroupOf K).FiniteIndex] {ι : Type*} [Fintype ι] (τ : ι → G) (hτ : ∀ i, τ i ∈ K)
    (M : ι → Subgroup G) [∀ i, ((M i).subgroupOf K').FiniteIndex]
    (hM : ∀ i, ∀ k ∈ K', k ∈ M i ↔ τ i * k * (τ i)⁻¹ ∈ S)
    (hcover : ∀ c ∈ K, ∃ i, ∃ k ∈ K', τ i * k⁻¹ * c ∈ S)
    (hdisj : ∀ i j, ∀ k ∈ K', ∀ k' ∈ K', τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ S → i = j)
    (a : fixedModule A S) (ha : ∀ i, (τ i)⁻¹ • (a : A) ∈ fixedModule A (M i)) :
    (norm A K S a : A) = ∏ i, (norm A K' (M i) ⟨(τ i)⁻¹ • (a : A), ha i⟩ : A) := by
  classical
  let f : ∀ i, K' ⧸ (M i).subgroupOf K' → K ⧸ S.subgroupOf K := fun i =>
    doubleCosetMap hK'K (hτ i) (fun k hk hkM => (hM i k hk).1 hkM)
  let F : (Σ i, K' ⧸ (M i).subgroupOf K') → K ⧸ S.subgroupOf K := fun p => f p.1 p.2
  have hFmk : ∀ i (k : K'), F ⟨i, (k : K' ⧸ (M i).subgroupOf K')⟩ =
      ((⟨k * (τ i)⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem (hτ i))⟩ : K) : K ⧸ S.subgroupOf K) :=
    fun _ _ => rfl
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H k =>
      induction y using QuotientGroup.induction_on with
      | H k' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        have hxy' : τ i * (k : G)⁻¹ * k' * (τ j)⁻¹ ∈ S := by simpa [mul_assoc] using hxy
        obtain rfl := hdisj i j k k.2 k' k'.2 hxy'
        have hkk : (k : G)⁻¹ * k' ∈ M i :=
          (hM i _ (K'.mul_mem (K'.inv_mem k.2) k'.2)).2 (by simpa [mul_assoc] using hxy')
        have : ((k : K' ⧸ (M i).subgroupOf K')) = (k' : K' ⧸ (M i).subgroupOf K') := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simpa using hkk
        rw [this]
    · intro y
      induction y using QuotientGroup.induction_on with
      | H c =>
        obtain ⟨i, k, hk, hc⟩ := hcover c c.2
        refine ⟨⟨i, ((⟨k, hk⟩ : K') : K' ⧸ (M i).subgroupOf K')⟩, ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using hc
  have : ∀ i, Fintype (K' ⧸ (M i).subgroupOf K') := fun i => Fintype.ofFinite _
  let _ := Fintype.ofFinite (K ⧸ S.subgroupOf K)
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF), finprod_eq_prod_of_fintype,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype]
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk]
    exact mul_smul _ _ _
theorem conj_mem_of_normal {K L : Subgroup G} [hN : (L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) (hkL : k ∈ L) : τ * k * τ⁻¹ ∈ L := by
  have := hN.conj_mem ⟨k, hk⟩ (Subgroup.mem_subgroupOf.2 hkL) ⟨τ, hτ⟩
  simpa [Subgroup.mem_subgroupOf] using this
theorem conj_mem_iff_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) : τ * k * τ⁻¹ ∈ L ↔ k ∈ L := by
  refine ⟨fun h => ?_, conj_mem_of_normal hτ hk⟩
  have := conj_mem_of_normal (K.inv_mem hτ) (K.mul_mem (K.mul_mem hτ hk) (K.inv_mem hτ)) h
  simpa [mul_assoc] using this
end DoubleCoset
section Inclusion
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]
theorem norm_mem_range_norm_of_le {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (b : fixedModule A (L : Subgroup G)) :
    (⟨norm A (K : Subgroup G) (L : Subgroup G) b,
        fixedModule_anti hK'K (norm A (K : Subgroup G) (L : Subgroup G) b).2⟩ :
        fixedModule A (K' : Subgroup G)) ∈ (norm A (K' : Subgroup G) (L : Subgroup G)).range := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  let _ := Fintype.ofFinite ((K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K)
  let τ : (K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K → G := fun i => ((Quotient.out i : K) : G)
  have hτ : ∀ i, τ i ∈ (K : Subgroup G) := fun i => (Quotient.out i : K).2
  have ha : ∀ i, (τ i)⁻¹ • (b : A) ∈ fixedModule A (L : Subgroup G) := fun i =>
    smul_mem_fixedModule_of_normal hLK ((K : Subgroup G).inv_mem (hτ i)) b.2
  have key := coe_norm_eq_prod_norm_inf (A := A) (S := (L : Subgroup G)) hK'K τ hτ
    (fun _ => (L : Subgroup G)) (fun i k hk => (conj_mem_iff_of_normal (hτ i) (hK'K hk)).symm)
    (fun c hc => by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((K' : Subgroup G).subgroupOf K)
        (⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G))
      refine ⟨((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _), (h : G),
        Subgroup.mem_subgroupOf.1 h.2, ?_⟩
      have : τ ((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _) = c⁻¹ * (h : G) := by
        simp only [τ, hh, Subgroup.coe_mul]
      rw [this]
      simp)
    (fun i j k hk k' hk' hy => by
      rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hyK : τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ (K : Subgroup G) := hLK hy
      have hc := conj_mem_of_normal ((K : Subgroup G).inv_mem (hτ j)) ((K : Subgroup G).inv_mem hyK)
        ((L : Subgroup G).inv_mem hy)
      have hmem : k⁻¹ * k' * ((τ j)⁻¹ * (τ i * k⁻¹ * k' * (τ j)⁻¹)⁻¹ * (τ j)⁻¹⁻¹) ∈
          (K' : Subgroup G) :=
        (K' : Subgroup G).mul_mem ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk) hk')
          (hLK' hc)
      convert hmem using 1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, τ]
      group)
    b ha
  refine ⟨∏ i, ⟨(τ i)⁻¹ • (b : A), ha i⟩, Subtype.ext ?_⟩
  rw [map_prod]
  simp only [SubmonoidClass.coe_finsetProd]
  exact key.symm
noncomputable def tateZeroIncl {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] :
    tateZero A (K : Subgroup G) (L : Subgroup G) →* tateZero A (K' : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (Subgroup.inclusion (fixedModule_anti (A := A) hK'K)) (by
    rintro _ ⟨b, rfl⟩
    exact norm_mem_range_norm_of_le hLK' hK'K b)
end Inclusion
end GroundTheory.LocalField.Abstract


