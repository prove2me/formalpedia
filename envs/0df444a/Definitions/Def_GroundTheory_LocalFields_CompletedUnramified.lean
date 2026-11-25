-- Prove2me | Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
-- name    : GroundTheory_LocalFields_CompletedUnramified
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:28.732513+00:00
-- url     : https://prove2.me/theorems/82ae5a4a-945a-5a88-b75f-72b7fda8bb82
-- title:
--   Completed Unramified
-- statement:
--   Definitions and structural lemmas for Completed Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_algebraMap_integer_injective
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_frobenius_integer_sub_pow_mem_maximalIdeal
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_isAdicComplete_integer
import Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal_integer
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_eq_unit_mul_pow_adicCompletion_4e23160a211e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.maximalUnramifiedExtensionGaloisEquiv_apply
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open IsLocalRing ValuativeRel
section Lift
variable {R : Type*} [CommRing R] {I : Ideal R}
variable (I) in

theorem factorPow_evalₐ {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule R R) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)
theorem pow_le_comap_pow {θ : R →+* R} (hθ : I ≤ I.comap θ) (n : ℕ) : I ^ n ≤ (I ^ n).comap θ :=
  Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hθ) n)
def adicCompletionQuotientMap (θ : R →+* R) (hθ : I ≤ I.comap θ) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ I ^ n :=
  (Ideal.quotientMap (I ^ n) θ (pow_le_comap_pow hθ n)).comp
    (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)
theorem factorPow_comp_adicCompletionQuotientMap (θ : R →+* R) (hθ : I ≤ I.comap θ) {k n : ℕ}
    (hle : k ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (adicCompletionQuotientMap θ hθ n) =
      adicCompletionQuotientMap θ hθ k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionQuotientMap, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl
def adicCompletionMap (θ : R →+* R) (hθ : I ≤ I.comap θ) :
    AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (adicCompletionQuotientMap θ hθ)
    (factorPow_comp_adicCompletionQuotientMap θ hθ)
theorem evalₐ_adicCompletionMap (θ : R →+* R) (hθ : I ≤ I.comap θ) (n : ℕ)
    (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionMap θ hθ x) =
      Ideal.quotientMap (I ^ n) θ (pow_le_comap_pow hθ n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom I _ (factorPow_comp_adicCompletionQuotientMap θ hθ) n x
@[simp]
theorem adicCompletionMap_of (θ : R →+* R) (hθ : I ≤ I.comap θ) (r : R) :
    adicCompletionMap θ hθ (AdicCompletion.of I R r) = AdicCompletion.of I R (θ r) := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of,
    Ideal.quotientMap_mk]
theorem adicCompletionMap_id :
    adicCompletionMap (RingHom.id R) (Ideal.comap_id I).ge = RingHom.id (AdicCompletion I R) := by
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, RingHom.id_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr, Ideal.quotientMap_mk, RingHom.id_apply]
theorem adicCompletionMap_comp (θ₁ θ₂ : R →+* R) (h₁ : I ≤ I.comap θ₁) (h₂ : I ≤ I.comap θ₂) :
    (adicCompletionMap θ₁ h₁).comp (adicCompletionMap θ₂ h₂) =
      adicCompletionMap (θ₁.comp θ₂)
        (by rw [← Ideal.comap_comap]; exact h₂.trans (Ideal.comap_mono h₁)) := by
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [RingHom.comp_apply, evalₐ_adicCompletionMap, evalₐ_adicCompletionMap,
    evalₐ_adicCompletionMap]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, RingHom.comp_apply]
end Lift
section DVR
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "𝔅" => AdicCompletion (maximalIdeal R) R
variable (R) in

theorem algebraMap_adicCompletion_injective : Function.Injective (algebraMap R 𝔅) :=
  AdicCompletion.of_injective _ _
theorem maximalIdeal_adicCompletion_eq_span {ϖ : R} (hϖ : Irreducible ϖ) :
    maximalIdeal 𝔅 = Ideal.span {algebraMap R 𝔅 ϖ} := by
  rw [AdicCompletion.maximalIdeal_eq_map, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
theorem exists_eq_unit_mul_pow_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) {x : 𝔅} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : 𝔅ˣ), x = u * algebraMap R 𝔅 ϖ ^ n :=
  _root_.GroundTheory.Variant₂.N1.exists_eq_unit_mul_pow_adicCompletion hϖ hx
theorem algebraMap_pow_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    algebraMap R 𝔅 ϖ ^ n ≠ 0 := by
  rw [← map_pow, Ne, ← map_zero (algebraMap R 𝔅), (algebraMap_adicCompletion_injective R).eq_iff]
  exact pow_ne_zero n hϖ.ne_zero
instance isDomain_adicCompletion : IsDomain 𝔅 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : NoZeroDivisors 𝔅 := ⟨fun {x y} hxy ↦ by
    by_contra h
    push Not at h
    obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ h.1
    obtain ⟨n, v, rfl⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ h.2
    apply algebraMap_pow_ne_zero hϖ (m + n)
    have : ((u * v : 𝔅ˣ) : 𝔅) * algebraMap R 𝔅 ϖ ^ (m + n) = 0 := by
      rw [← hxy, Units.val_mul, pow_add]
      ring
    exact (Units.mul_right_eq_zero _).mp this⟩
  exact NoZeroDivisors.to_isDomain _
theorem irreducible_algebraMap_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap R 𝔅 ϖ) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (by simpa using algebraMap_pow_ne_zero hϖ 1) (maximalIdeal_adicCompletion_eq_span hϖ)
instance isDiscreteValuationRing_adicCompletion : IsDiscreteValuationRing 𝔅 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_algebraMap_adicCompletion hϖ, fun hx ↦ by
      obtain ⟨n, u, hu⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ hx
      exact ⟨n, u, by rw [hu, mul_comm]⟩⟩
theorem exists_sub_algebraMap_mem_pow (x : 𝔅) (n : ℕ) :
    ∃ r : R, x - algebraMap R 𝔅 r ∈ maximalIdeal 𝔅 ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm := maximalIdeal_adicCompletion_eq_span hϖ
  have hres : ∀ y : 𝔅, ∃ s : R, y - algebraMap R 𝔅 s ∈ maximalIdeal 𝔅 := by
    intro y
    obtain ⟨t, ht⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue 𝔅 y)
    obtain ⟨s, rfl⟩ := residue_surjective t
    refine ⟨s, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, ← ht, ResidueField.map_residue, sub_self]
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
    obtain ⟨c, hc⟩ := hr
    obtain ⟨s, hs⟩ := hres c
    rw [hm, Ideal.mem_span_singleton'] at hs
    obtain ⟨d, hd⟩ := hs
    refine ⟨r + ϖ ^ n * s, ?_⟩
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨d, ?_⟩
    rw [map_add, map_mul, map_pow]
    linear_combination (algebraMap R 𝔅 ϖ) ^ n * hd + hc
end DVR
section Automorphism
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "𝔅" => AdicCompletion (maximalIdeal R) R
theorem maximalIdeal_le_comap_ringEquiv (θ : R ≃+* R) :
    maximalIdeal R ≤ (maximalIdeal R).comap (θ : R →+* R) := by
  intro x hx
  rw [Ideal.mem_comap]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  simpa using hu.map θ.symm
theorem adicCompletionMap_congr {θ₁ θ₂ : R →+* R} (h : θ₁ = θ₂)
    (h₁ : maximalIdeal R ≤ (maximalIdeal R).comap θ₁) (h₂ : maximalIdeal R ≤ (maximalIdeal R).comap θ₂) :
    adicCompletionMap θ₁ h₁ = adicCompletionMap θ₂ h₂ := by
  subst h
  rfl
theorem adicCompletionMap_eq_id {θ : R →+* R} (hθ : maximalIdeal R ≤ (maximalIdeal R).comap θ)
    (h : θ = RingHom.id R) : adicCompletionMap θ hθ = RingHom.id 𝔅 := by
  subst h
  exact adicCompletionMap_id
def adicCompletionRingEquiv (θ : R ≃+* R) : 𝔅 ≃+* 𝔅 :=
  RingEquiv.ofRingHom
    (adicCompletionMap (θ : R →+* R) (maximalIdeal_le_comap_ringEquiv θ))
    (adicCompletionMap (θ.symm : R →+* R) (maximalIdeal_le_comap_ringEquiv θ.symm))
    (by
      rw [adicCompletionMap_comp]
      exact adicCompletionMap_eq_id _ (by ext; simp))
    (by
      rw [adicCompletionMap_comp]
      exact adicCompletionMap_eq_id _ (by ext; simp))
variable {S : Type*} [CommRing S] [Algebra S R]
def adicCompletionAlgEquiv : (R ≃ₐ[S] R) →* (𝔅 ≃ₐ[S] 𝔅) where
  toFun θ :=
    AlgEquiv.ofRingEquiv (f := adicCompletionRingEquiv θ.toRingEquiv) (fun s ↦ by
      change adicCompletionMap _ _ (AdicCompletion.of _ R (algebraMap S R s)) =
        AdicCompletion.of _ R (algebraMap S R s)
      rw [adicCompletionMap_of]
      simp)
  map_one' := by
    ext1 x
    change adicCompletionMap _ _ x = x
    rw [adicCompletionMap_eq_id _ (by ext; simp)]
    rfl
  map_mul' θ₁ θ₂ := by
    ext1 x
    change adicCompletionMap _ _ x = adicCompletionMap _ _ (adicCompletionMap _ _ x)
    rw [← RingHom.comp_apply (adicCompletionMap _ _), adicCompletionMap_comp]
    exact congrArg (fun f : 𝔅 →+* 𝔅 ↦ f x) (adicCompletionMap_congr (by ext; simp) _ _)
@[simp]
theorem adicCompletionAlgEquiv_algebraMap (θ : R ≃ₐ[S] R) (r : R) :
    adicCompletionAlgEquiv θ (algebraMap R 𝔅 r) = algebraMap R 𝔅 (θ r) :=
  show adicCompletionMap _ _ (AdicCompletion.of _ R r) = _ from adicCompletionMap_of _ _ r
end Automorphism
section FixedRing
open Polynomial
theorem mem_range_of_pow_card_eq_self {F k : Type*} [Field F] [Finite F] [Field k] [Algebra F k]
    {y : k} (hy : y ^ Nat.card F = y) : y ∈ (algebraMap F k).range := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at hy
  have hs : Splits (X ^ Fintype.card F - X : F[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F hq]
    exact Finset.card_univ
  refine hs.mem_range_of_isRoot (FiniteField.X_pow_card_sub_X_ne_zero F hq) ?_
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, IsRoot.def, eval_sub, eval_pow,
    eval_X, hy, sub_self]
variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
theorem isLocalHom_algebraMap_of_map_maximalIdeal
    (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha ↦ ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 h
  have := Ideal.mem_map_of_mem (algebraMap A B) hm
  rw [hunr] at this
  exact (mem_maximalIdeal _).1 this ha
variable [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
include hunr hσ
omit [IsAdicComplete (maximalIdeal A) A] in

theorem exists_sub_algebraMap_mem_of_fixed {c : B} (hc : σ c = c) :
    ∃ d : A, c - algebraMap A B d ∈ maximalIdeal B := by
  have := isLocalHom_algebraMap_of_map_maximalIdeal hunr
  have hy : residue B c ^ Nat.card (ResidueField A) = residue B c := by rw [← hσ, hc]
  obtain ⟨t, ht⟩ := mem_range_of_pow_card_eq_self hy
  obtain ⟨d, rfl⟩ := residue_surjective t
  refine ⟨d, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← ht, ResidueField.algebraMap_residue, sub_self]
theorem mem_range_algebraMap_iff_fixed (b : B) : b ∈ (algebraMap A B).range ↔ σ b = b := by
  refine ⟨fun ⟨a, ha⟩ ↦ by rw [← ha, σ.commutes], fun hb ↦ ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set ϖ := algebraMap A B π with hϖdef
  have hmB : maximalIdeal B = Ideal.span {ϖ} := by
    rw [← hunr, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field B
    rw [hmB, h0, Ideal.span_singleton_eq_bot]
  have hϖm : ϖ ∈ maximalIdeal B := hmB ▸ Ideal.mem_span_singleton_self ϖ
  have hπm : π ∈ maximalIdeal A := hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hσϖ : σ ϖ = ϖ := σ.commutes π
  have step : ∀ c : B, σ c = c → ∃ d : A, ∃ c' : B, σ c' = c' ∧ c = algebraMap A B d + ϖ * c' := by
    intro c hc
    obtain ⟨d, hd⟩ := exists_sub_algebraMap_mem_of_fixed hunr σ hσ hc
    rw [hmB, Ideal.mem_span_singleton'] at hd
    obtain ⟨c', hc'⟩ := hd
    refine ⟨d, c', ?_, by rw [mul_comm, hc']; ring⟩
    have h1 := congrArg σ hc'
    rw [map_mul, hσϖ, map_sub, hc, σ.commutes, ← hc'] at h1
    exact mul_right_cancel₀ hϖ0 h1
  choose D N hN hDN using step
  let c : ℕ → {x : B // σ x = x} := fun n ↦
    Nat.rec ⟨b, hb⟩ (fun _ x ↦ ⟨N x.1 x.2, hN x.1 x.2⟩) n
  have hc_succ : ∀ n, (c (n + 1)).1 = N (c n).1 (c n).2 := fun _ ↦ rfl
  let d : ℕ → A := fun n ↦ D (c n).1 (c n).2
  let s : ℕ → A := fun n ↦ ∑ i ∈ Finset.range n, π ^ i * d i
  have hs : ∀ n, b = algebraMap A B (s n) + ϖ ^ n * (c n).1 := by
    intro n
    induction n with
    | zero => simp [s, c]
    | succ n ih =>
      have h := hDN (c n).1 (c n).2
      rw [← hc_succ] at h
      rw [ih, h]
      simp only [s, d, Finset.sum_range_succ, map_add, map_mul, map_pow]
      ring
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → s m ≡ s n [SMOD (maximalIdeal A ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, neg_mem_iff]
    simp only [s]
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Ideal.sum_mem _ fun i hi ↦ ?_
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.mp hi).1 (Ideal.pow_mem_pow hπm i)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal A) s hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := maximalIdeal B) _ fun n ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have hLn := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hLn
  have h1 : algebraMap A B (s n - L) ∈ maximalIdeal B ^ n := by
    rw [← hunr, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hLn
  have h2 : ϖ ^ n * (c n).1 ∈ maximalIdeal B ^ n :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖm n)
  have : algebraMap A B L - b = -(algebraMap A B (s n - L) + ϖ ^ n * (c n).1) := by
    rw [hs n, map_sub]
    ring
  rw [this, neg_mem_iff]
  exact add_mem h1 h2
end FixedRing
section Completed
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
abbrev CompletedUnramifiedIntegers : Type _ :=
  AdicCompletion (maximalIdeal 𝒪[maximalUnramifiedExtension K Ω]) 𝒪[maximalUnramifiedExtension K Ω]
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
example : IsDiscreteValuationRing 𝔹 := inferInstance
instance isScalarTower_completedUnramifiedIntegers : IsScalarTower 𝒪[K] 𝒪[𝔼] 𝔹 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
theorem algebraMap_integer_completedUnramifiedIntegers_injective :
    Function.Injective (algebraMap 𝒪[𝔼] 𝔹) :=
  algebraMap_adicCompletion_injective _
theorem algebraMap_completedUnramifiedIntegers_injective :
    Function.Injective (algebraMap 𝒪[K] 𝔹) := by
  rw [IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[𝔼] 𝔹]
  exact (algebraMap_integer_completedUnramifiedIntegers_injective K Ω).comp
    (algebraMap_integer_injective K 𝔼)
theorem map_maximalIdeal_completedUnramifiedIntegers :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝔹) = maximalIdeal 𝔹 := by
  rw [IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[𝔼] 𝔹, ← Ideal.map_map, map_maximalIdeal_integer,
    AdicCompletion.maximalIdeal_eq_map]
instance isLocalHom_algebraMap_completedUnramifiedIntegers : IsLocalHom (algebraMap 𝒪[K] 𝔹) :=
  isLocalHom_algebraMap_of_map_maximalIdeal (map_maximalIdeal_completedUnramifiedIntegers K Ω)
theorem irreducible_algebraMap_completedUnramifiedIntegers_iff (π : 𝒪[K]) :
    Irreducible (algebraMap 𝒪[K] 𝔹 π) ↔ Irreducible π := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine irreducible_iff.mpr ⟨fun hu ↦ h.not_isUnit (hu.map _), fun a b hab ↦ ?_⟩
    rw [hab, map_mul] at h
    exact (h.isUnit_or_isUnit rfl).imp (isUnit_of_map_unit _ _) (isUnit_of_map_unit _ _)
  · rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[𝔼] 𝔹]
    exact irreducible_algebraMap_adicCompletion (irreducible_algebraMap_uniformizer h)
def residueFieldCompletedUnramifiedIntegersEquiv :
    ResidueField 𝒪[𝔼] ≃+* ResidueField 𝔹 :=
  RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective 𝒪[𝔼])
instance isAlgClosed_residueField_completedUnramifiedIntegers : IsAlgClosed (ResidueField 𝔹) :=
  IsAlgClosed.of_ringEquiv _ _ (residueFieldCompletedUnramifiedIntegersEquiv K Ω)
instance isAlgebraic_residueField_completedUnramifiedIntegers :
    Algebra.IsAlgebraic 𝓀[K] (ResidueField 𝔹) :=
  AlgEquiv.isAlgebraic (R := 𝓀[K]) (A := ResidueField 𝒪[𝔼])
    (AlgEquiv.ofRingEquiv (f := residueFieldCompletedUnramifiedIntegersEquiv K Ω) fun t ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective t
      change ResidueField.map (algebraMap 𝒪[𝔼] 𝔹)
        (algebraMap 𝓀[K] (ResidueField 𝒪[𝔼]) (residue 𝒪[K] a)) = _
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
        ResidueField.map_residue]
      rfl)
instance isAlgClosure_residueField_completedUnramifiedIntegers :
    letI : Module.IsTorsionFree 𝓀[K] (ResidueField 𝔹) := DivisionSemiring.to_moduleIsTorsionFree
    IsAlgClosure 𝓀[K] (ResidueField 𝔹) :=
  letI : Module.IsTorsionFree 𝓀[K] (ResidueField 𝔹) := DivisionSemiring.to_moduleIsTorsionFree
  ⟨isAlgClosed_residueField_completedUnramifiedIntegers K Ω,
    isAlgebraic_residueField_completedUnramifiedIntegers K Ω⟩
end Completed
section Frobenius
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
def completedUnramifiedAlgEquiv : (𝔼 ≃ₐ[K] 𝔼) →* (𝔹 ≃ₐ[𝒪[K]] 𝔹) :=
  adicCompletionAlgEquiv.comp (integerAlgEquivOfIsAlgebraic K 𝔼)
variable {K Ω}
@[simp]
theorem completedUnramifiedAlgEquiv_algebraMap (ρ : 𝔼 ≃ₐ[K] 𝔼) (x : 𝒪[𝔼]) :
    completedUnramifiedAlgEquiv K Ω ρ (algebraMap 𝒪[𝔼] 𝔹 x) =
      algebraMap 𝒪[𝔼] 𝔹 (integerAlgEquivOfIsAlgebraic K 𝔼 ρ x) :=
  adicCompletionAlgEquiv_algebraMap _ x
variable [IsGalois K Ω]
variable (K Ω) in

def completedFrobenius : 𝔹 ≃ₐ[𝒪[K]] 𝔹 :=
  completedUnramifiedAlgEquiv K Ω (maximalUnramifiedExtensionFrobenius K Ω)
theorem completedFrobenius_algebraMap (x : 𝒪[𝔼]) :
    completedFrobenius K Ω (algebraMap 𝒪[𝔼] 𝔹 x) = algebraMap 𝒪[𝔼] 𝔹
      (integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x) :=
  completedUnramifiedAlgEquiv_algebraMap _ x
theorem residue_completedFrobenius (x : 𝔹) :
    residue 𝔹 (completedFrobenius K Ω x) = residue 𝔹 x ^ Nat.card 𝓀[K] := by
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_pow x 1
  rw [pow_one] at hr
  set σ := completedFrobenius K Ω
  have h1 : residue 𝔹 x = residue 𝔹 (algebraMap 𝒪[𝔼] 𝔹 r) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hr
  have h2 : residue 𝔹 (σ x) = residue 𝔹 (σ (algebraMap 𝒪[𝔼] 𝔹 r)) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
    exact fun hu ↦ hr (by simpa using hu.map σ.symm)
  rw [h2, h1, completedFrobenius_algebraMap, ← map_pow, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff, ← map_pow, ← map_sub, AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (frobenius_integer_sub_pow_mem_maximalIdeal r)
theorem mem_range_algebraMap_iff_completedFrobenius (b : 𝔹) :
    b ∈ (algebraMap 𝒪[K] 𝔹).range ↔ completedFrobenius K Ω b = b :=
  have := isAdicComplete_integer K
  mem_range_algebraMap_iff_fixed (map_maximalIdeal_completedUnramifiedIntegers K Ω)
    (completedFrobenius K Ω).toAlgHom (residue_completedFrobenius) b
variable (K Ω) in

theorem completedUnramifiedIntegers_spec :
    IsDiscreteValuationRing 𝔹 ∧ IsAdicComplete (maximalIdeal 𝔹) 𝔹 ∧
      Function.Injective (algebraMap 𝒪[K] 𝔹) ∧
      (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝔹) = maximalIdeal 𝔹 ∧
      (∀ π : 𝒪[K], Irreducible (algebraMap 𝒪[K] 𝔹 π) ↔ Irreducible π) ∧
      IsAlgClosed (ResidueField 𝔹) ∧ Algebra.IsAlgebraic 𝓀[K] (ResidueField 𝔹) ∧
      (∀ x : 𝔹, residue 𝔹 (completedFrobenius K Ω x) = residue 𝔹 x ^ Nat.card 𝓀[K]) ∧
      (∀ b : 𝔹, completedFrobenius K Ω b = b ↔ b ∈ (algebraMap 𝒪[K] 𝔹).range) :=
  ⟨inferInstance, inferInstance, algebraMap_completedUnramifiedIntegers_injective K Ω,
    map_maximalIdeal_completedUnramifiedIntegers K Ω,
    irreducible_algebraMap_completedUnramifiedIntegers_iff K Ω, inferInstance, inferInstance,
    residue_completedFrobenius, fun b ↦ (mem_range_algebraMap_iff_completedFrobenius b).symm⟩
end Frobenius
section Finite
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
def integerToCompleted {L : IntermediateField K Ω} (h : L ≤ 𝔼) : 𝒪[L] →ₐ[𝒪[K]] 𝔹 :=
  (IsScalarTower.toAlgHom 𝒪[K] 𝒪[𝔼] 𝔹).comp (integerInclusion h)
variable {K Ω}
end Finite
section FiniteFrobenius
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
end FiniteFrobenius
section Check
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
example : IsAdicComplete (maximalIdeal (CompletedUnramifiedIntegers K (SeparableClosure K)))
    (CompletedUnramifiedIntegers K (SeparableClosure K)) :=
  inferInstance
example (b : CompletedUnramifiedIntegers K (SeparableClosure K)) :
    completedFrobenius K (SeparableClosure K) b = b ↔
      b ∈ (algebraMap 𝒪[K] (CompletedUnramifiedIntegers K (SeparableClosure K))).range :=
  (completedUnramifiedIntegers_spec K (SeparableClosure K)).2.2.2.2.2.2.2.2 b
example (π : 𝒪[K]) (hπ : Irreducible π) :
    IsDomain (CompletedUnramifiedIntegers K (SeparableClosure K)) ∧
      IsDiscreteValuationRing (CompletedUnramifiedIntegers K (SeparableClosure K)) ∧
      Irreducible (algebraMap 𝒪[K] (CompletedUnramifiedIntegers K (SeparableClosure K)) π) ∧
      IsAlgClosed (ResidueField (CompletedUnramifiedIntegers K (SeparableClosure K))) ∧
      ∀ x : CompletedUnramifiedIntegers K (SeparableClosure K),
        residue _ ((completedFrobenius K (SeparableClosure K)).toAlgHom x) =
          residue _ x ^ Nat.card (ResidueField 𝒪[K]) :=
  ⟨inferInstance, inferInstance,
    (irreducible_algebraMap_completedUnramifiedIntegers_iff K (SeparableClosure K) π).mpr hπ,
    inferInstance, residue_completedFrobenius⟩
end Check
end GroundTheory.LocalField


