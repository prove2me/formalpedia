-- Prove2me | solution 1 for Algebra.FormallySmooth.residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/004bfb95-c6b8-53e0-b9c0-40f4bed58dce

import Mathlib
import Theorems.Thm_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
import Theorems.Thm_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental

set_option autoImplicit false

namespace C3M4aGen

open IsLocalRing

open IntermediateField.algebraAdjoinAdjoin in
theorem ringKrullDim_le_one_of_transcendental {L K : Type} [Field L] [Field K] [Algebra L K]
    (x : K) (hx : Transcendental L x)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set K)) K)
    (T : Subalgebra L K) (hxT : x ∈ T) :
    IsNoetherianRing ↥T ∧ ringKrullDim ↥T ≤ 1 := by
  classical
  set R : Subalgebra L K := Algebra.adjoin L ({x} : Set K) with hR
  have e : Polynomial L ≃ₐ[L] ↥R := Polynomial.algEquivOfTranscendental L x hx
  haveI : IsNoetherianRing ↥R := isNoetherianRing_of_ringEquiv (Polynomial L) e.toRingEquiv
  have hdimR : ringKrullDim ↥R ≤ 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv, Polynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    norm_num
  haveI : FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set K)) K := hfin
  have hRT : R ≤ T := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxT)
  let T' : Subalgebra ↥R K :=
    { carrier := (T : Set K)
      mul_mem' := fun ha hb => T.mul_mem ha hb
      one_mem' := T.one_mem
      add_mem' := fun ha hb => T.add_mem ha hb
      zero_mem' := T.zero_mem
      algebraMap_mem' := fun r => hRT r.2 }
  exact IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra (R := ↥R) hdimR
    ↥(IntermediateField.adjoin L ({x} : Set K)) K T'

theorem formallySmooth_fiber_of_eq_bot
    (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    (A : Type) [CommRing A] [IsDomain A] [Algebra O A] [FaithfulSMul O A] [Algebra.FiniteType O A] [IsIntegrallyClosed A]
    (L : Type) [Field L] [Algebra O L] [IsFractionRing O L]
    (K : Type) [Field K] [Algebra L K] [Algebra O K] [IsScalarTower O L K] [Algebra A K] [IsScalarTower O A K]
    (hAK : Function.Injective (algebraMap A K))
    (x : A) (hx : Transcendental L (algebraMap A K x))
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin L ({algebraMap A K x} : Set K)) K)
    (p : Ideal O) [p.IsPrime] (hp : p = ⊥) :
    Algebra.FormallySmooth p.ResidueField (p.Fiber A) := by
  classical
  subst hp

  set Rp := Localization.AtPrime (⊥ : Ideal O) with hRp
  have hmax : maximalIdeal Rp = ⊥ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (⊥ : Ideal O) Rp, Ideal.map_bot]

  have hκinj : Function.Injective (algebraMap O (⊥ : Ideal O).ResidueField) := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
  haveI : CharZero (⊥ : Ideal O).ResidueField := charZero_of_injective_ringHom hκinj

  set M : Submonoid A := Algebra.algebraMapSubmonoid A (⊥ : Ideal O).primeCompl with hM
  have hM : M ≤ nonZeroDivisors A :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ (Ideal.primeCompl_le_nonZeroDivisors _)
  set Sp := Localization M with hSp
  haveI : IsDomain Sp := IsLocalization.isDomain_localization hM
  haveI : IsIntegrallyClosed Sp := isIntegrallyClosed_of_isLocalization Sp M hM

  have eκ : (⊥ : Ideal O).ResidueField ≃ₐ[O] Rp := by
    refine (AlgEquiv.ofRingEquiv (f := ((Ideal.quotEquivOfEq hmax).trans (RingEquiv.quotientBot Rp))) ?_)
    intro o
    rfl
  let e : (⊥ : Ideal O).Fiber A ≃+* Sp :=
    ((Algebra.TensorProduct.congr eκ (AlgEquiv.refl : A ≃ₐ[O] A)).toRingEquiv).trans
      (Localization.tensorRightAlgEquiv ((⊥ : Ideal O).primeCompl) A).toRingEquiv

  have hunits : ∀ y : M, IsUnit (algebraMap A K y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro h0
    have : (y : A) = 0 := hAK (by rw [h0, map_zero])
    exact nonZeroDivisors.ne_zero (hM y.2) this
  let φ : Sp →+* K := IsLocalization.lift (M := M) hunits
  have hφinj : Function.Injective φ := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro h; rw [IsLocalization.injective Sp hM h]
    · intro h; rw [hAK h]
  have hφalg : ∀ a : A, φ (algebraMap A Sp a) = algebraMap A K a := fun a => IsLocalization.lift_eq hunits a

  have hLrange : ∀ l : L, algebraMap L K l ∈ φ.range := by
    intro l
    obtain ⟨o₁, o₂, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors O) l
    have ho₂ : (o₂ : O) ∈ (⊥ : Ideal O).primeCompl := by
      rw [Ideal.primeCompl_bot]; exact o₂.2
    refine ⟨IsLocalization.mk' Sp (algebraMap O A o₁) ⟨algebraMap O A o₂, Algebra.mem_algebraMapSubmonoid_of_mem ⟨_, ho₂⟩⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    show algebraMap A K (algebraMap O A o₁) = algebraMap A K (algebraMap O A o₂) * algebraMap L K (IsLocalization.mk' L o₁ o₂)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply O L K o₁, IsScalarTower.algebraMap_apply O L K (o₂ : O), ← map_mul,
      IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left]
  let T : Subalgebra L K :=
    { carrier := (φ.range : Set K)
      mul_mem' := fun ha hb => φ.range.mul_mem ha hb
      one_mem' := φ.range.one_mem
      add_mem' := fun ha hb => φ.range.add_mem ha hb
      zero_mem' := φ.range.zero_mem
      algebraMap_mem' := fun l => hLrange l }
  have hxT : algebraMap A K x ∈ T := ⟨algebraMap A Sp x, hφalg x⟩
  obtain ⟨-, hdimT⟩ := ringKrullDim_le_one_of_transcendental (algebraMap A K x) hx hfin T hxT
  have eT : Sp ≃+* ↥T := (RingEquiv.ofBijective (φ.rangeRestrict) ⟨fun a b h => hφinj (congrArg Subtype.val h),
    φ.rangeRestrict_surjective⟩).trans (RingEquiv.refl _)
  have hdimSp : ringKrullDim Sp ≤ 1 := by rw [ringKrullDim_eq_of_ringEquiv eT]; exact hdimT

  haveI : IsDomain ((⊥ : Ideal O).Fiber A) := e.toMulEquiv.isDomain Sp
  haveI : IsIntegrallyClosed ((⊥ : Ideal O).Fiber A) := IsIntegrallyClosed.of_equiv e.symm
  haveI : Ring.KrullDimLE 1 ((⊥ : Ideal O).Fiber A) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv e]; exact_mod_cast hdimSp
  have hs := Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField (⊥ : Ideal O).ResidueField
    ((⊥ : Ideal O).Fiber A)
  exact hs.formallySmooth

open IsLocalRing in

theorem formallySmooth_fiber_maximalIdeal
    (O : Type) [CommRing O] [IsLocalRing O]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (hκ : IsAlgClosed (ResidueField O))
    (A : Type) [CommRing A] [Algebra O A] [Algebra.FiniteType O A]
    (hdom : IsDomain (A ⧸ Ideal.span {algebraMap O A π}))
    (hnorm : IsIntegrallyClosed (A ⧸ Ideal.span {algebraMap O A π}))
    (hdim : Ring.KrullDimLE 1 (A ⧸ Ideal.span {algebraMap O A π}))
    (p : Ideal O) [p.IsPrime] (hp : p = maximalIdeal O) :
    Algebra.FormallySmooth p.ResidueField (p.Fiber A) := by
  classical
  haveI hpmax : p.IsMaximal := by rw [hp]; exact maximalIdeal.isMaximal O

  have hbij := Ideal.bijective_algebraMap_quotient_residueField p
  let e₀ : (O ⧸ p) ≃+* p.ResidueField := RingEquiv.ofBijective (algebraMap (O ⧸ p) p.ResidueField) hbij
  have e₁ : ResidueField O ≃+* (O ⧸ p) := Ideal.quotEquivOfEq hp.symm
  haveI : IsAlgClosed p.ResidueField := IsAlgClosed.of_ringEquiv (ResidueField O) p.ResidueField (e₁.trans e₀)

  have hmap : p.map (algebraMap O A) = Ideal.span {algebraMap O A π} := by
    rw [hp, hπ, Ideal.map_span, Set.image_singleton]
  let eκ : (O ⧸ p) ≃ₐ[O] p.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId (O ⧸ p) p.ResidueField |>.restrictScalars O) hbij
  let e : p.Fiber A ≃+* (A ⧸ Ideal.span {algebraMap O A π}) :=
    ((Algebra.TensorProduct.congr eκ.symm (AlgEquiv.refl : A ≃ₐ[O] A)).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A p).symm.toRingEquiv).trans
      (Ideal.quotEquivOfEq hmap)
  haveI : IsDomain (p.Fiber A) := e.toMulEquiv.isDomain _
  haveI : IsIntegrallyClosed (p.Fiber A) := IsIntegrallyClosed.of_equiv e.symm
  haveI : Ring.KrullDimLE 1 (p.Fiber A) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv e]; exact (Ring.krullDimLE_iff.mp hdim)
  exact (Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField p.ResidueField (p.Fiber A)).formallySmooth

end C3M4aGen

open IsLocalRing in
theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (π : O) (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (halg : IsAlgClosed (IsLocalRing.ResidueField O))
    (A : Type) [CommRing A] [IsDomain A] [Algebra O A] [FaithfulSMul O A] [Algebra.FiniteType O A] [IsIntegrallyClosed A]
    (L : Type) [Field L] [Algebra O L] [IsFractionRing O L]
    (K : Type) [Field K] [Algebra L K] [Algebra O K] [IsScalarTower O L K] [Algebra A K] [IsScalarTower O A K]
    (hAK : Function.Injective (algebraMap A K))
    (x : A) (hx : Transcendental L (algebraMap A K x))
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin L {algebraMap A K x}) K)
    (hdom : IsDomain (A ⧸ Ideal.span {algebraMap O A π}))
    (hnorm : IsIntegrallyClosed (A ⧸ Ideal.span {algebraMap O A π}))
    (hdim : Ring.KrullDimLE 1 (A ⧸ Ideal.span {algebraMap O A π})) :
    ∀ (𝔭 : Ideal O) [𝔭.IsPrime], Algebra.FormallySmooth 𝔭.ResidueField (𝔭.Fiber A) := by
  intro 𝔭 h𝔭
  by_cases hbot : 𝔭 = ⊥
  · exact C3M4aGen.formallySmooth_fiber_of_eq_bot O A L K hAK x hx hfin 𝔭 hbot
  · have hmax : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal h𝔭 hbot
    exact C3M4aGen.formallySmooth_fiber_maximalIdeal O π hπ halg A hdom hnorm hdim 𝔭 (IsLocalRing.eq_maximalIdeal hmax)

end S_Algebra_FormallySmooth_residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental
end P2MW
export P2MW.S_Algebra_FormallySmooth_residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental (solution)
