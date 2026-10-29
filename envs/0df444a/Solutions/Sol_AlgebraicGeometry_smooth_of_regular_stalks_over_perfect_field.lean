-- Prove2me | solution 1 for AlgebraicGeometry.smooth_of_regular_stalks_over_perfect_field
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-28T22:57:42.701212+00:00
-- url     : https://prove2.me/submissions/56f36292-78da-462f-afca-f93f099b18e0

import Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular
import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain

universe u
set_option linter.style.haveILetI false


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing
namespace PhilipponRegularLocalPerfectSmooth

open Polynomial TensorProduct

theorem isUnit_add_of_mem {S : Type u} [CommRing S] [IsLocalRing S] {a b : S}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal S) : IsUnit (a + b) := by
  by_contra h
  have hab : a + b ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : a ∈ maximalIdeal S := by simpa using sub_mem hab hb
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha

theorem isUnit_aeval_of_coeff_zero_ne_zero {k : Type u} [Field k] {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra k S] {t : S} (ht : t ∈ maximalIdeal S) {q : k[X]} (hq : q.coeff 0 ≠ 0) :
    IsUnit (aeval t q) := by
  have h : aeval t q = algebraMap k S (q.coeff 0) + t * aeval t q.divX := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    simp only [map_add, map_mul, aeval_X, aeval_C]
    ring
  rw [h]
  exact isUnit_add_of_mem ((IsUnit.mk0 _ hq).map _) (Ideal.mul_mem_right _ _ ht)

theorem exists_mem_notMem_sq {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (h : maximalIdeal S ≠ ⊥) : ∃ t ∈ maximalIdeal S, t ∉ (maximalIdeal S) ^ 2 := by
  by_contra hall
  push_neg at hall
  apply h
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (maximalIdeal S) (IsNoetherian.noetherian _)
  · intro x hx
    have := hall x hx
    rwa [pow_two, ← Ideal.smul_eq_mul] at this
  · exact IsLocalRing.maximalIdeal_le_jacobson _

theorem spanFinrank_maximalIdeal_quotient_congr {S : Type u} [CommRing S] {I J : Ideal S} (h : I = J)
    [hI : IsLocalRing (S ⧸ I)] [hJ : IsLocalRing (S ⧸ J)] :
    (maximalIdeal (S ⧸ I)).spanFinrank = (maximalIdeal (S ⧸ J)).spanFinrank := by
  subst h
  rfl

theorem main (n : ℕ) : ∀ (k : Type u) [Field k] [PerfectField k] (S : Type u) [CommRing S] [IsRegularLocalRing S]
    [Algebra k S] [Algebra.EssFiniteType k S],
    (maximalIdeal S).spanFinrank = n →
    Algebra.FormallySmooth k S := by
  induction n with
  | zero =>
    intro k _ _ S _ _ _ _ h0
    have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0
    letI : Field S := ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot).toField
    exact Algebra.FormallySmooth.of_perfectField
  | succ n ih =>
    intro k _ _ S _ _ _ _ hn
    classical
    haveI : IsDomain S := IsRegularLocalRing.isDomain S
    have hne : maximalIdeal S ≠ ⊥ := fun h => by
      rw [(Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mpr h] at hn
      exact Nat.succ_ne_zero n hn.symm
    obtain ⟨t, ht, ht2⟩ := exists_mem_notMem_sq hne
    have ht0 : t ≠ 0 := fun h => ht2 (h ▸ zero_mem _)

    have htr : Function.Injective (aeval (R := k) t) := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra hp0
      obtain ⟨q, hq, hdvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
      have hq0 : q.coeff 0 ≠ 0 := by
        rw [map_zero, sub_zero, Polynomial.X_dvd_iff] at hdvd
        exact hdvd
      have hu : IsUnit (aeval t q) := isUnit_aeval_of_coeff_zero_ne_zero ht hq0
      have h1 : t ^ (rootMultiplicity 0 p) * aeval t q = 0 := by
        have h2 := congrArg (aeval t) hq
        rw [hp, map_mul, map_pow, map_sub, aeval_X, map_zero, map_zero, sub_zero] at h2
        exact h2.symm
      have htm : t ^ (rootMultiplicity 0 p) = 0 := hu.mul_left_eq_zero.mp h1
      by_cases hm : rootMultiplicity 0 p = 0
      · rw [hm, pow_zero] at htm
        exact one_ne_zero htm
      · exact ht0 ((pow_eq_zero_iff hm).mp htm)

    haveI hprime : (Ideal.span {(X : k[X])}).IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
    let K₁ : Type u := Localization.AtPrime (Ideal.span {(X : k[X])})
    haveI : IsDiscreteValuationRing K₁ :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X]
        (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_ne_zero) K₁
    have hunits : ∀ y : (Ideal.span {(X : k[X])}).primeCompl, IsUnit (aeval t (y : k[X])) := by
      rintro ⟨y, hy⟩
      apply isUnit_aeval_of_coeff_zero_ne_zero ht
      intro h0
      exact hy (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h0))
    let ψ : K₁ →ₐ[k] S := IsLocalization.liftAlgHom (M := (Ideal.span {(X : k[X])}).primeCompl) (f := aeval t) hunits
    letI : Algebra K₁ S := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower k K₁ S := IsScalarTower.of_algebraMap_eq fun a => (ψ.commutes a).symm
    have hψ : ∀ y : k[X], algebraMap K₁ S (algebraMap k[X] K₁ y) = aeval t y := fun y =>
      IsLocalization.lift_eq (M := (Ideal.span {(X : k[X])}).primeCompl) hunits y
    have hψX : algebraMap K₁ S (algebraMap k[X] K₁ X) = t := by rw [hψ, aeval_X]
    have hI : (maximalIdeal K₁).map (algebraMap K₁ S) = Ideal.span {t} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_span, Set.image_singleton,
        RingHom.comp_apply, hψX]
    haveI : IsLocalHom (algebraMap K₁ S) := by
      apply ((IsLocalRing.local_hom_TFAE (algebraMap K₁ S)).out 0 2).mpr
      rw [hI, Ideal.span_le, Set.singleton_subset_iff]
      exact ht

    have hinj : Function.Injective (algebraMap K₁ S) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(X : k[X])}).primeCompl z
      have h1 : algebraMap K₁ S (IsLocalization.mk' K₁ a s) * algebraMap K₁ S (algebraMap k[X] K₁ s) =
          aeval t a := by
        rw [← map_mul, IsLocalization.mk'_spec, hψ]
      rw [hz, zero_mul] at h1
      have ha : a = 0 := htr (by rw [map_zero]; exact h1.symm)
      subst ha
      show IsLocalization.mk' K₁ (0 : k[X]) s = 0
      exact IsLocalization.mk'_zero s
    haveI : Module.IsTorsionFree K₁ S := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
    haveI : Module.Flat K₁ S := inferInstance
    haveI : Algebra.EssFiniteType K₁ S := Algebra.EssFiniteType.of_comp k K₁ S

    haveI hlocF : IsLocalRing (S ⧸ Ideal.span {t}) := RegularQuotientEngine.isLocalRing_quotient_span_singleton S ht
    have hregF' : IsRegularLocalRing (S ⧸ Ideal.span {t}) :=
      RegularQuotientEngine.isRegularLocalRing_quotient_span_singleton S ht ht2
    have hnF' : (maximalIdeal (S ⧸ Ideal.span {t})).spanFinrank = n := by
      have := RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_succ_eq S ht ht2
      omega
    haveI hregF : IsRegularLocalRing (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S)) := by rw [hI]; exact hregF'
    have hnF : (maximalIdeal (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S))).spanFinrank = n := by
      rw [spanFinrank_maximalIdeal_quotient_congr hI]; exact hnF'
    haveI hmax : (maximalIdeal K₁).IsMaximal := IsLocalRing.maximalIdeal.isMaximal K₁
    letI : Field (K₁ ⧸ maximalIdeal K₁) := Ideal.Quotient.field (maximalIdeal K₁)
    haveI : (Ideal.span {(X : k[X])}).IsMaximal := by
      exact PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
    haveI : Algebra.FiniteType k (ResidueField K₁) :=
      Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
    haveI : Module.Finite k (ResidueField K₁) :=
      finite_of_finite_type_of_isJacobsonRing k (ResidueField K₁)
    haveI : PerfectField (K₁ ⧸ maximalIdeal K₁) :=
      Algebra.IsAlgebraic.perfectField (K := k) (L := ResidueField K₁)
    have hF : Algebra.FormallySmooth (K₁ ⧸ maximalIdeal K₁)
        (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S)) :=
      ih (K₁ ⧸ maximalIdeal K₁) (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S)) hnF
    haveI : Algebra.FormallySmooth (K₁ ⧸ maximalIdeal K₁) ((K₁ ⧸ maximalIdeal K₁) ⊗[K₁] S) :=
      Algebra.FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal K₁))
    haveI : Algebra.FormallySmooth (ResidueField K₁) ((ResidueField K₁) ⊗[K₁] S) := ‹_›
    haveI : Algebra.FinitePresentation K₁ (Algebra.EssFiniteType.subalgebra K₁ S) :=
      (Algebra.FinitePresentation.of_finiteType (R := K₁) (A := Algebra.EssFiniteType.subalgebra K₁ S)).mp inferInstance
    haveI hS : Algebra.FormallySmooth K₁ S :=
      Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := K₁) (S := S)
        (P := Algebra.EssFiniteType.subalgebra K₁ S) (Algebra.EssFiniteType.submonoid K₁ S)
    haveI : Algebra.FormallySmooth k K₁ := inferInstance
    exact Algebra.FormallySmooth.comp k K₁ S


theorem formallySmooth
    (k : Type u) [Field k] [PerfectField k] (S : Type u) [CommRing S]
    [IsRegularLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S] :
    Algebra.FormallySmooth k S :=
  main _ k S rfl

end PhilipponRegularLocalPerfectSmooth


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PhilipponNoetherianPresentation

lemma locallyOfFinitePresentation_of_locallyOfFiniteType
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f := by
  constructor
  intro U hU V hV hVU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact RingHom.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hVU)

end PhilipponNoetherianPresentation


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory

namespace PhilipponRegularSchemeSmooth

set_option backward.isDefEq.respectTransparency false in
theorem mem_smoothLocus
    (K : Type u) [Field K] [PerfectField K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) [LocallyOfFinitePresentation g]
    (y : Y) (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) :
    y ∈ g.smoothLocus := by
  have hft := LocallyOfFiniteType.stalkMap g y
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(g.stalkMap y).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (g y)
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (g y).asIdeal.primeCompl
    (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let iF : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let iF' : Field ((Spec (.of K)).presheaf.stalk (g y)) := iF
  have : PerfectField ((Spec (.of K)).presheaf.stalk (g y)) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (g y))
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hreg
  exact PhilipponRegularLocalPerfectSmooth.formallySmooth
    ((Spec (.of K)).presheaf.stalk (g y)) (Y.presheaf.stalk y)

theorem smooth
    (K : Type u) [Field K] [PerfectField K] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) :
    Smooth π := by
  have : LocallyOfFinitePresentation π :=
    PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType π
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_le_iff.mp
  intro y _
  exact mem_smoothLocus K π y (hreg y)

end PhilipponRegularSchemeSmooth


theorem solution
    (K : Type u) [Field K] [PerfectField K] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) :
    Smooth π := by
  exact PhilipponRegularSchemeSmooth.smooth K π hreg
