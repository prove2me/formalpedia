-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a4b4257c-48d3-5ae2-8997-60ad2ec82f42

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin.AlgebraicCurve.TwoChartIntegralModel Polynomial"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf TwoChartIntegralModel.isIntegrallyClosed_chartAlg TwoChartIntegralModel.isFractionRing_chartAlg"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin fibre finiteType_chartAlgFin_and_chartAlgInf isIntegrallyClosed_chartAlg isFractionRing_chartAlg"
namespace S0Aux
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable {R : Type u} [CommRing R] [IsDomain R]

theorem polynomial_prime_le_span_C (hR : UniqueFactorizationMonoid R) {ϖ : R} (hϖ : Prime ϖ)
    (I : Ideal (Polynomial R)) [I.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ Ideal.span {C ϖ}) :
    I = Ideal.span {C ϖ} := by
  haveI := hR
  refine le_antisymm hle ?_
  obtain ⟨q, hqI, hq⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hI
  have hCϖ : Prime (C ϖ) := Polynomial.prime_C_iff.mpr hϖ
  have hdvd : C ϖ ∣ q := Ideal.mem_span_singleton.mp (hle hqI)
  have hass : Associated (C ϖ) q := hCϖ.irreducible.associated_of_dvd hq.irreducible hdvd
  obtain ⟨w, hw⟩ := hass
  rw [Ideal.span_singleton_le_iff_mem]
  have : q * (↑w⁻¹ : Polynomial R) = C ϖ := by rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  rw [← this]
  exact I.mul_mem_right _ hqI

end AlgebraicCurve.TwoChartIntegralModel.S0Aux

end

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (𝔭 : Ideal ↥(chartAlgFin R F j))
    (h𝔭 : 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes) :
    ∃ V : ValuationSubring F,
      IsDiscreteValuationRing ↥V ∧
      (∀ f : ↥(chartAlgFin R F j), (f : F) ∈ V) ∧
      (∀ f : ↥(chartAlgFin R F j), f ∈ 𝔭 ↔ (f : F) ∈ V.nonunits) ∧
      algebraMap R F ϖ ∈ V.nonunits ∧
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) := by
  classical
  haveI h𝔭prime : 𝔭.IsPrime := h𝔭.1.1
  have hspan𝔭 : Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ} ≤ 𝔭 := h𝔭.1.2
  have hϖ𝔭 : algebraMap R ↥(chartAlgFin R F j) ϖ ∈ 𝔭 := hspan𝔭 (Ideal.subset_span rfl)

  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hϖF : algebraMap R F ϖ ≠ 0 := (map_ne_zero_iff _ hRF).mpr hϖ.ne_zero
  have hϖ𝒪 : algebraMap R ↥(chartAlgFin R F j) ϖ ≠ 0 := fun h => hϖF (by
    have := congrArg (fun x : ↥(chartAlgFin R F j) => (x : F)) h
    simpa only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] using this)
  have h𝔭ne : 𝔭 ≠ ⊥ := fun h => hϖ𝒪 (by rw [h] at hϖ𝔭; exact hϖ𝔭)

  have hB𝒪 : Algebra.adjoin R ({j} : Set F) ≤ chartAlgFin R F j := adjoin_le_chartAlg R F {j}
  letI : Algebra ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) :=
    (Subalgebra.inclusion hB𝒪).toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) F :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower R ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  have hBinj : Function.Injective
      (algebraMap ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j)) :=
    Subalgebra.inclusion_injective hB𝒪
  haveI : FaithfulSMul ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hBinj
  haveI hint : Algebra.IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) :=
    ⟨fun x => by
      have hx : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) (x : F) := (mem_chartAlg_iff R F).mp x.2
      exact (isIntegral_algHom_iff
        (IsScalarTower.toAlgHom ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) F)
        Subtype.val_injective).mp hx⟩
  let e : Polynomial R ≃ₐ[R] ↥(Algebra.adjoin R ({j} : Set F)) :=
    Polynomial.algEquivOfTranscendental R j htj
  haveI : UniqueFactorizationMonoid R := inferInstance
  haveI : IsIntegrallyClosed ↥(Algebra.adjoin R ({j} : Set F)) :=
    IsIntegrallyClosed.of_equiv e.toRingEquiv
  haveI : Algebra.HasGoingDown ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) :=
    inferInstance

  have heC : ∀ r : R, e (C r) = algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) r := fun r => by
    rw [Polynomial.C_eq_algebraMap, AlgEquiv.commutes]
  have hecoe : ∀ P : Polynomial R, ((e P : ↥(Algebra.adjoin R ({j} : Set F))) : F) = aeval j P :=
    fun P => by simp [e, Polynomial.algEquivOfTranscendental]

  have hmemϖB : ∀ b : ↥(Algebra.adjoin R ({j} : Set F)),
      b ∈ Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ} ↔ C ϖ ∣ e.symm b := by
    intro b
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨e.symm c, ?_⟩
      rw [map_mul, ← heC, AlgEquiv.symm_apply_apply]
    · rintro ⟨c, hc⟩
      refine ⟨e c, ?_⟩
      have := congrArg e hc
      rwa [AlgEquiv.apply_symm_apply, map_mul, heC] at this
  haveI hϖBprime : (Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ}).IsPrime := by
    have h1 : (Ideal.span {C ϖ} : Ideal (Polynomial R)).IsPrime :=
      (Ideal.span_singleton_prime (Polynomial.prime_C_iff.mpr hϖ).ne_zero).mpr
        (Polynomial.prime_C_iff.mpr hϖ)
    have h2 : Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ} =
        Ideal.comap e.symm.toRingEquiv.toRingHom (Ideal.span {C ϖ}) := by
      ext b
      rw [hmemϖB, Ideal.mem_comap, Ideal.mem_span_singleton]
      rfl
    rw [h2]
    exact Ideal.IsPrime.comap _

  have hϖB_le : Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ} ≤
      𝔭.under ↥(Algebra.adjoin R ({j} : Set F)) := by
    rw [Ideal.span_singleton_le_iff_mem]
    change algebraMap ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j)
      (algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ) ∈ 𝔭
    rw [← IsScalarTower.algebraMap_apply]
    exact hϖ𝔭
  haveI : 𝔭.LiesOver (𝔭.under ↥(Algebra.adjoin R ({j} : Set F))) := ⟨rfl⟩
  have h𝔮 : 𝔭.under ↥(Algebra.adjoin R ({j} : Set F)) =
      Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ} := by
    by_contra hne
    have hlt : Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ} <
        𝔭.under ↥(Algebra.adjoin R ({j} : Set F)) := lt_of_le_of_ne hϖB_le (Ne.symm hne)
    obtain ⟨P, hP𝔭, hPprime, hPover⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt
        (p := Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ})
        (q := 𝔭.under ↥(Algebra.adjoin R ({j} : Set F))) 𝔭 hlt
    have hϖP : algebraMap R ↥(chartAlgFin R F j) ϖ ∈ P := by
      have : algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ ∈
          P.under ↥(Algebra.adjoin R ({j} : Set F)) := by
        rw [← hPover.over]
        exact Ideal.subset_span rfl
      rw [IsScalarTower.algebraMap_apply R ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j)]
      exact this
    have hle : 𝔭 ≤ P := h𝔭.2 ⟨hPprime, (Ideal.span_singleton_le_iff_mem _).mpr hϖP⟩ hP𝔭.le
    exact (lt_irrefl _) (lt_of_lt_of_le hP𝔭 hle)

  have hgen : ∀ P : Polynomial R, ¬ (C ϖ ∣ P) →
      (⟨aeval j P, hecoe P ▸ hB𝒪 (e P).2⟩ : ↥(chartAlgFin R F j)) ∉ 𝔭 := by
    intro P hP hmem
    have h1 : (e P : ↥(Algebra.adjoin R ({j} : Set F))) ∈
        𝔭.under ↥(Algebra.adjoin R ({j} : Set F)) := by
      change algebraMap _ ↥(chartAlgFin R F j) (e P) ∈ 𝔭
      convert hmem using 1
      exact Subtype.ext (hecoe P)
    rw [h𝔮, hmemϖB, AlgEquiv.symm_apply_apply] at h1
    exact hP h1

  obtain ⟨hFT, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep
  haveI := hFT
  haveI : IsNoetherianRing ↥(chartAlgFin R F j) :=
    Algebra.FiniteType.isNoetherianRing R ↥(chartAlgFin R F j)
  haveI : IsIntegrallyClosed ↥(chartAlgFin R F j) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg R F {j}
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ F
  haveI : IsFractionRing ↥(chartAlgFin R F j) F :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg R K₀ F {j}

  set S := Localization.AtPrime 𝔭 with hSdef
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔭.primeCompl S inferInstance
  haveI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S 𝔭.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  have hmaxne : IsLocalRing.maximalIdeal S ≠ ⊥ := by
    intro h
    have h1 : algebraMap ↥(chartAlgFin R F j) S (algebraMap R _ ϖ) ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔭 _).mpr hϖ𝔭
    rw [h, Ideal.mem_bot] at h1
    exact hϖ𝒪 ((IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors 𝔭)) (by
      rw [h1, map_zero]))
  have hnotfield : ¬ IsField S := fun hf =>
    hmaxne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hf)

  have huniq : ∃! Q : Ideal S, Q ≠ ⊥ ∧ Q.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal S, ⟨hmaxne, inferInstance⟩, ?_⟩
    rintro Q ⟨hQne, hQprime⟩

    set Q' := Q.comap (algebraMap ↥(chartAlgFin R F j) S) with hQ'def
    haveI : Q'.IsPrime := Ideal.IsPrime.comap _
    have hQ'le : Q' ≤ 𝔭 := by
      rw [← IsLocalization.AtPrime.comap_maximalIdeal S 𝔭]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQprime.ne_top)
    have hmapQ' : Ideal.map (algebraMap ↥(chartAlgFin R F j) S) Q' = Q :=
      IsLocalization.map_comap 𝔭.primeCompl S Q
    have hQ'ne : Q' ≠ ⊥ := by
      intro h
      apply hQne
      rw [← hmapQ', h, Ideal.map_bot]

    have hQ'eq : Q' = 𝔭 := by
      by_contra hne
      have hlt : Q' < 𝔭 := lt_of_le_of_ne hQ'le hne
      obtain ⟨x, hx𝔭, hxQ⟩ := Set.exists_of_ssubset hlt
      have hlt' : Q'.under ↥(Algebra.adjoin R ({j} : Set F)) <
          𝔭.under ↥(Algebra.adjoin R ({j} : Set F)) :=
        Ideal.comap_lt_comap_of_integral_mem_sdiff hQ'le ⟨hx𝔭, hxQ⟩
          (Algebra.IsIntegral.isIntegral x)
      have hne' : Q'.under ↥(Algebra.adjoin R ({j} : Set F)) ≠ ⊥ := fun h =>
        hQ'ne (Ideal.eq_bot_of_comap_eq_bot h)
      rw [h𝔮] at hlt'

      set I := (Q'.under ↥(Algebra.adjoin R ({j} : Set F))).comap e.toRingEquiv.toRingHom with hIdef
      haveI : I.IsPrime := Ideal.IsPrime.comap _
      have hImem : ∀ q : Polynomial R, q ∈ I ↔ e q ∈ Q'.under ↥(Algebra.adjoin R ({j} : Set F)) :=
        fun q => Iff.rfl
      have hIne : I ≠ ⊥ := by
        intro h
        apply hne'
        rw [eq_bot_iff]
        intro b hb
        have : e.symm b ∈ I := by
          rw [hImem, AlgEquiv.apply_symm_apply]; exact hb
        rw [h, Ideal.mem_bot] at this
        have := congrArg e this
        rwa [AlgEquiv.apply_symm_apply, map_zero] at this
      have hIle : I ≤ Ideal.span {C ϖ} := by
        intro q hq
        have hq' : e q ∈ Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ} :=
          hlt'.le hq
        rw [hmemϖB, AlgEquiv.symm_apply_apply] at hq'
        exact Ideal.mem_span_singleton.mpr hq'
      have hIeq := AlgebraicCurve.TwoChartIntegralModel.S0Aux.polynomial_prime_le_span_C
        inferInstance hϖ I hIne hIle

      apply (lt_irrefl _) (lt_of_lt_of_le hlt' ?_)
      intro b hb
      rw [hmemϖB] at hb
      have : e.symm b ∈ I := by rw [hIeq]; exact Ideal.mem_span_singleton.mpr hb
      rw [hImem, AlgEquiv.apply_symm_apply] at this
      exact this
    rw [← hmapQ', hQ'eq]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have h03 : IsDiscreteValuationRing S ↔
      (IsIntegrallyClosed S ∧ ∃! Q : Ideal S, Q ≠ ⊥ ∧ Q.IsPrime) :=
    (IsDiscreteValuationRing.TFAE S hnotfield).out 0 3
  haveI hDVR : IsDiscreteValuationRing S := h03.mpr ⟨inferInstance, huniq⟩

  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap ↥(chartAlgFin R F j) F y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h => y.2 ?_
    have h' : ((y : ↥(chartAlgFin R F j)) : F) = 0 := h
    have : (y : ↥(chartAlgFin R F j)) = 0 := Subtype.ext h'
    change (y : ↥(chartAlgFin R F j)) ∈ 𝔭
    rw [this]; exact 𝔭.zero_mem
  letI : Algebra S F := (IsLocalization.lift (M := 𝔭.primeCompl) (S := S) hunit).toAlgebra
  haveI : IsScalarTower ↥(chartAlgFin R F j) S F :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  haveI : IsFractionRing S F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl S F
  let V : ValuationSubring F := (ValuationRing.valuation S F).valuationSubring
  have hVmem : ∀ x : F, x ∈ V ↔ ∃ a : S, algebraMap S F a = x := fun x =>
    (Valuation.mem_valuationSubring_iff _ x).trans
      ((Valuation.mem_integer_iff _ x).symm.trans (ValuationRing.mem_integer_iff S F x))
  have hSF : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  let toV : S →+* ↥V := (algebraMap S F).codRestrict V.toSubring fun a => (hVmem _).mpr ⟨a, rfl⟩
  have htoVcoe : ∀ a : S, ((toV a : ↥V) : F) = algebraMap S F a := fun a => rfl
  have htoV : Function.Bijective toV := by
    refine ⟨fun a b h => hSF ?_, fun x => ?_⟩
    · have := congrArg (fun z : ↥V => (z : F)) h
      simpa only [htoVcoe] using this
    · obtain ⟨a, ha⟩ := (hVmem x).mp x.2
      exact ⟨a, Subtype.ext ha⟩
  let eV : S ≃+* ↥V := RingEquiv.ofBijective toV htoV
  have heVcoe : ∀ a : S, ((eV a : ↥V) : F) = algebraMap S F a := fun a => rfl

  have hOS : ∀ f : ↥(chartAlgFin R F j), ((eV (algebraMap _ S f) : ↥V) : F) = (f : F) := fun f => by
    rw [heVcoe, ← IsScalarTower.algebraMap_apply]; rfl
  have hcentre : ∀ f : ↥(chartAlgFin R F j), f ∈ 𝔭 ↔ (f : F) ∈ V.nonunits := by
    intro f
    have hu : IsUnit (eV (algebraMap _ S f)) ↔ IsUnit (algebraMap ↥(chartAlgFin R F j) S f) :=
      ⟨fun h => by simpa using h.map eV.symm, fun h => h.map eV⟩
    rw [← hOS f, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      hu, ← IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔭 f,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

  refine ⟨V, ?_, ?_, hcentre, ?_, ?_⟩
  ·
    haveI : IsPrincipalIdealRing ↥V :=
      IsPrincipalIdealRing.of_surjective eV.toRingHom eV.surjective
    refine IsDiscreteValuationRing.mk ?_
    intro hbot
    have h1 : (eV (algebraMap _ S (algebraMap R ↥(chartAlgFin R F j) ϖ)) : ↥V) ∈
        IsLocalRing.maximalIdeal ↥V := by
      rw [← ValuationSubring.coe_mem_nonunits_iff, hOS]
      exact (hcentre _).mp hϖ𝔭
    rw [hbot, Ideal.mem_bot, map_eq_zero_iff eV eV.injective] at h1
    exact hϖ𝒪 ((IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors 𝔭)) (by
      rw [h1, map_zero]))
  · intro f
    rw [← hOS f]
    exact (eV (algebraMap _ S f)).2
  · have := (hcentre _).mp hϖ𝔭
    simpa only [Subalgebra.coe_algebraMap] using this
  · intro P hP
    have hunitP : IsUnit (algebraMap ↥(chartAlgFin R F j) S ⟨aeval j P, hecoe P ▸ hB𝒪 (e P).2⟩) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff S 𝔭 _).mpr (hgen P hP)
    obtain ⟨u, hu⟩ := hunitP
    have hval : algebraMap S F (u : S) = aeval j P := by
      rw [hu, ← IsScalarTower.algebraMap_apply]; rfl
    refine ⟨(hVmem _).mpr ⟨u, hval⟩, (hVmem _).mpr ⟨(↑u⁻¹ : S), ?_⟩⟩
    rw [← hval]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

end S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin (solution)
