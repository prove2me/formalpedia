-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/84da97bb-b2e7-59c8-af14-96805f60da96

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

open AlgebraicCurve.TwoChartIntegralModel Polynomial

noncomputable section

namespace BCBody

variable {R : Type u} [CommRing R] [IsDomain R]

private theorem polynomial_prime_le_span_C (hR : UniqueFactorizationMonoid R) {ϖ : R} (hϖ : Prime ϖ)
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

private theorem C_dvd_of_map_residue_eq_zero [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    (P : Polynomial R) (hP : P.map (IsLocalRing.residue R) = 0) : C ϖ ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  have h1 : IsLocalRing.residue R (P.coeff i) = 0 := by
    have := congrArg (fun Q => Q.coeff i) hP
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using this
  have h2 : P.coeff i ∈ IsLocalRing.maximalIdeal R := by
    rwa [← IsLocalRing.residue_eq_zero_iff]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at h2
  exact Ideal.mem_span_singleton.mp h2

end BCBody

end

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (V : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) :

    (∀ b : ↥(chartAlgFin R F j), (b : F) ∈ V) ∧

    (∃ 𝔓 : Ideal ↥(chartAlgFin R F j), 𝔓.IsPrime ∧ 𝔓.height = 1 ∧
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 ↔ (b : F) ∈ V.nonunits) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) a ∈ 𝔓) ∧

      (∀ f : F, f ∈ V ↔ ∃ a b : ↥(chartAlgFin R F j), b ∉ 𝔓 ∧ f * (b : F) = (a : F))) ∧

    (∀ V' : ValuationSubring F,
      (∀ a : R, algebraMap R F a ∈ V') →
      (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits) →
      (∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') →
      V ≠ V' →
      ∃ b : ↥(chartAlgFin R F j), (b : F) ∈ V'.nonunits ∧ (b : F) ∉ V.nonunits) := by
  classical

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : Prime ϖ := hϖirr.prime
  have hmaxR : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal R := by rw [hmaxR]; exact Ideal.mem_span_singleton_self ϖ

  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hϖF : algebraMap R F ϖ ≠ 0 := (map_ne_zero_iff _ hRF).mpr hϖ.ne_zero
  have hϖ𝒪 : algebraMap R ↥(chartAlgFin R F j) ϖ ≠ 0 := fun h => hϖF (by
    have := congrArg (fun x : ↥(chartAlgFin R F j) => (x : F)) h
    simpa only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] using this)

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

  have key : ∀ (W : ValuationSubring F),
      (∀ a : R, algebraMap R F a ∈ W) →
      (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ W.nonunits) →
      (∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        Polynomial.aeval j P ∈ W ∧ (Polynomial.aeval j P)⁻¹ ∈ W) →
      (∀ b : ↥(chartAlgFin R F j), (b : F) ∈ W) ∧
      ∃ 𝔓 : Ideal ↥(chartAlgFin R F j), 𝔓.IsPrime ∧ 𝔓.height = 1 ∧
        (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 ↔ (b : F) ∈ W.nonunits) ∧
        (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) a ∈ 𝔓) ∧
        (∀ f : F, f ∈ W ↔ ∃ a b : ↥(chartAlgFin R F j), b ∉ 𝔓 ∧ f * (b : F) = (a : F)) := by
    intro W hWA hWm hWj

    have hjW : j ∈ W := by
      have := (hWj X (by rw [Polynomial.map_X]; exact X_ne_zero)).1
      rwa [aeval_X] at this
    let SW : Subalgebra R F :=
      { W.toSubring with
        algebraMap_mem' := fun a => hWA a }
    have hBW : Algebra.adjoin R ({j} : Set F) ≤ SW := Algebra.adjoin_le (Set.singleton_subset_iff.2 hjW)
    have hAW : ∀ b : ↥(chartAlgFin R F j), (b : F) ∈ W := by
      intro b
      have hb : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) (b : F) := (mem_chartAlg_iff R F).mp b.2

      letI : Algebra ↥(Algebra.adjoin R ({j} : Set F)) ↥W :=
        ((Subalgebra.inclusion hBW).toRingHom.comp (RingHom.id _)).toAlgebra
      haveI : IsScalarTower ↥(Algebra.adjoin R ({j} : Set F)) ↥W F :=
        IsScalarTower.of_algebraMap_eq fun x => rfl
      have hbW : IsIntegral ↥W (b : F) := hb.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W) (K := F)).mp hbW
      rw [← hy]
      exact y.2
    refine ⟨hAW, ?_⟩

    let toW : ↥(chartAlgFin R F j) →+* ↥W :=
      (chartAlgFin R F j).val.toRingHom.codRestrict W.toSubring hAW
    have htoW : ∀ b : ↥(chartAlgFin R F j), ((toW b : ↥W) : F) = (b : F) := fun b => rfl
    let 𝔓 : Ideal ↥(chartAlgFin R F j) := (IsLocalRing.maximalIdeal ↥W).comap toW
    haveI h𝔓prime : 𝔓.IsPrime := Ideal.IsPrime.comap toW
    have hPmem : ∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 ↔ (b : F) ∈ W.nonunits := by
      intro b
      rw [← htoW b, ValuationSubring.coe_mem_nonunits_iff]
      rfl
    have hPR : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) a ∈ 𝔓 := by
      intro a ha
      rw [hPmem, Subalgebra.coe_algebraMap]
      exact hWm a ha
    have hϖ𝔓 : algebraMap R ↥(chartAlgFin R F j) ϖ ∈ 𝔓 := hPR ϖ hϖmax
    have h𝔓ne : 𝔓 ≠ ⊥ := fun h => hϖ𝒪 (by rw [h] at hϖ𝔓; exact hϖ𝔓)

    have hgen : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        (⟨aeval j P, hecoe P ▸ hB𝒪 (e P).2⟩ : ↥(chartAlgFin R F j)) ∉ 𝔓 := by
      intro P hP hmem0
      have hmem : (aeval j P : F) ∈ W.nonunits := (hPmem _).mp hmem0
      obtain ⟨h1, h2⟩ := hWj P hP
      rw [ValuationSubring.mem_nonunits_iff] at hmem
      have h3 : W.valuation (aeval j P)⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr h2
      have h0 : aeval j P ≠ 0 := by
        intro h0
        refine htj ⟨P, ?_, h0⟩
        rintro rfl
        exact hP (Polynomial.map_zero _)
      rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact h0)] at h3
      exact not_lt.mpr h3 hmem

    have h𝔮 : 𝔓.under ↥(Algebra.adjoin R ({j} : Set F)) =
        Ideal.span {algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ} := by
      apply le_antisymm
      · intro b hb
        rw [hmemϖB]
        by_contra hndvd
        have hP : (e.symm b).map (IsLocalRing.residue R) ≠ 0 := fun h0 =>
          hndvd (BCBody.C_dvd_of_map_residue_eq_zero hϖirr _ h0)
        apply hgen (e.symm b) hP
        have : (⟨aeval j (e.symm b), hecoe (e.symm b) ▸ hB𝒪 (e (e.symm b)).2⟩ : ↥(chartAlgFin R F j)) =
            algebraMap ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) b := by
          apply Subtype.ext
          show aeval j (e.symm b) = (b : F)
          rw [← hecoe, AlgEquiv.apply_symm_apply]
        rw [this]
        exact hb
      · rw [Ideal.span_singleton_le_iff_mem]
        change algebraMap ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j)
          (algebraMap R ↥(Algebra.adjoin R ({j} : Set F)) ϖ) ∈ 𝔓
        rw [← IsScalarTower.algebraMap_apply]
        exact hϖ𝔓

    have hbelow : ∀ Q : Ideal ↥(chartAlgFin R F j), Q.IsPrime → Q < 𝔓 → Q = ⊥ := by
      intro Q hQ hlt
      by_contra hQne
      obtain ⟨x, hx𝔓, hxQ⟩ := Set.exists_of_ssubset hlt
      have hlt' : Q.under ↥(Algebra.adjoin R ({j} : Set F)) <
          𝔓.under ↥(Algebra.adjoin R ({j} : Set F)) :=
        Ideal.comap_lt_comap_of_integral_mem_sdiff hlt.le ⟨hx𝔓, hxQ⟩ (Algebra.IsIntegral.isIntegral x)
      have hne' : Q.under ↥(Algebra.adjoin R ({j} : Set F)) ≠ ⊥ := fun h =>
        hQne (Ideal.eq_bot_of_comap_eq_bot h)
      rw [h𝔮] at hlt'
      set I := (Q.under ↥(Algebra.adjoin R ({j} : Set F))).comap e.toRingEquiv.toRingHom with hIdef
      haveI : I.IsPrime := Ideal.IsPrime.comap _
      have hImem : ∀ q : Polynomial R, q ∈ I ↔ e q ∈ Q.under ↥(Algebra.adjoin R ({j} : Set F)) :=
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
      have hIeq := BCBody.polynomial_prime_le_span_C inferInstance hϖ I hIne hIle
      apply (lt_irrefl _) (lt_of_lt_of_le hlt' ?_)
      intro b hb
      rw [hmemϖB] at hb
      have : e.symm b ∈ I := by rw [hIeq]; exact Ideal.mem_span_singleton.mpr hb
      rw [hImem, AlgEquiv.apply_symm_apply] at this
      exact this
    have hheight : 𝔓.height = 1 := by
      apply le_antisymm
      · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
        intro Q hQ hlt
        rw [hbelow Q hQ hlt, Ideal.height_bot]
        exact zero_lt_one
      · rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
          Set.mem_singleton_iff]
        exact h𝔓ne

    set S := Localization.AtPrime 𝔓 with hSdef
    haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔓.primeCompl S inferInstance
    haveI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S 𝔓.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔓)
    have hmaxne : IsLocalRing.maximalIdeal S ≠ ⊥ := by
      intro h
      have h1 : algebraMap ↥(chartAlgFin R F j) S (algebraMap R _ ϖ) ∈ IsLocalRing.maximalIdeal S :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔓 _).mpr hϖ𝔓
      rw [h, Ideal.mem_bot] at h1
      exact hϖ𝒪 ((IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors 𝔓)) (by
        rw [h1, map_zero]))
    have hnotfield : ¬ IsField S := fun hf => hmaxne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hf)
    have huniq : ∃! Q : Ideal S, Q ≠ ⊥ ∧ Q.IsPrime := by
      refine ⟨IsLocalRing.maximalIdeal S, ⟨hmaxne, inferInstance⟩, ?_⟩
      rintro Q ⟨hQne, hQprime⟩
      set Q' := Q.comap (algebraMap ↥(chartAlgFin R F j) S) with hQ'def
      haveI : Q'.IsPrime := Ideal.IsPrime.comap _
      have hQ'le : Q' ≤ 𝔓 := by
        rw [← IsLocalization.AtPrime.comap_maximalIdeal S 𝔓]
        exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQprime.ne_top)
      have hmapQ' : Ideal.map (algebraMap ↥(chartAlgFin R F j) S) Q' = Q :=
        IsLocalization.map_comap 𝔓.primeCompl S Q
      have hQ'ne : Q' ≠ ⊥ := by
        intro h
        apply hQne
        rw [← hmapQ', h, Ideal.map_bot]
      have hQ'eq : Q' = 𝔓 := by
        by_contra hne
        exact hQ'ne (hbelow Q' inferInstance (lt_of_le_of_ne hQ'le hne))
      rw [← hmapQ', hQ'eq]
      exact Localization.AtPrime.map_eq_maximalIdeal
    have h03 : IsDiscreteValuationRing S ↔
        (IsIntegrallyClosed S ∧ ∃! Q : Ideal S, Q ≠ ⊥ ∧ Q.IsPrime) :=
      (IsDiscreteValuationRing.TFAE S hnotfield).out 0 3
    haveI hDVR : IsDiscreteValuationRing S := h03.mpr ⟨inferInstance, huniq⟩

    have hunit : ∀ y : 𝔓.primeCompl, IsUnit (algebraMap ↥(chartAlgFin R F j) F y) := by
      intro y
      refine isUnit_iff_ne_zero.mpr fun h => y.2 ?_
      have h' : ((y : ↥(chartAlgFin R F j)) : F) = 0 := h
      have : (y : ↥(chartAlgFin R F j)) = 0 := Subtype.ext h'
      change (y : ↥(chartAlgFin R F j)) ∈ 𝔓
      rw [this]; exact 𝔓.zero_mem
    letI : Algebra S F := (IsLocalization.lift (M := 𝔓.primeCompl) (S := S) hunit).toAlgebra
    haveI : IsScalarTower ↥(chartAlgFin R F j) S F :=
      IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
    haveI : IsFractionRing S F :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔓.primeCompl S F

    have hSmem : ∀ f : F, (∃ s : S, algebraMap S F s = f) ↔
        ∃ a b : ↥(chartAlgFin R F j), b ∉ 𝔓 ∧ f * (b : F) = (a : F) := by
      intro f
      constructor
      · rintro ⟨s, rfl⟩
        obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl s
        refine ⟨a, b, b.2, ?_⟩
        have h1 := (IsLocalization.lift_mk'_spec (M := 𝔓.primeCompl) (hg := hunit) a
          ((IsLocalization.lift (M := 𝔓.primeCompl) (S := S) hunit) (IsLocalization.mk' S a b)) b).mp rfl

        show (IsLocalization.lift (M := 𝔓.primeCompl) (S := S) hunit) (IsLocalization.mk' S a b) * (b : F) = (a : F)
        rw [mul_comm]
        exact h1.symm
      · rintro ⟨a, b, hb, hf⟩
        refine ⟨IsLocalization.mk' S a (⟨b, hb⟩ : 𝔓.primeCompl), ?_⟩
        show (IsLocalization.lift (M := 𝔓.primeCompl) (S := S) hunit) (IsLocalization.mk' S a ⟨b, hb⟩) = f
        rw [IsLocalization.lift_mk'_spec]
        show algebraMap _ F a = algebraMap _ F b * f
        rw [mul_comm]
        exact hf.symm

    have hval_le : ∀ b : ↥(chartAlgFin R F j), W.valuation (b : F) ≤ 1 := fun b =>
      (W.valuation_le_one_iff _).mpr (hAW b)
    have hval_eq : ∀ b : ↥(chartAlgFin R F j), b ∉ 𝔓 → W.valuation (b : F) = 1 := by
      intro b hb
      rw [hPmem, ValuationSubring.mem_nonunits_iff, not_lt] at hb
      exact le_antisymm (hval_le b) hb
    have hval_lt : ∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 → W.valuation (b : F) < 1 := by
      intro b hb
      rwa [hPmem, ValuationSubring.mem_nonunits_iff] at hb
    have hloc : ∀ f : F, f ∈ W ↔ ∃ a b : ↥(chartAlgFin R F j), b ∉ 𝔓 ∧ f * (b : F) = (a : F) := by
      intro f
      constructor
      · intro hfW
        rw [← hSmem]
        rcases eq_or_ne f 0 with rfl | hf0
        · exact ⟨0, map_zero _⟩

        rcases ValuationRing.isInteger_or_isInteger S f with ⟨s, hs⟩ | ⟨s, hs⟩
        · exact ⟨s, hs⟩
        · by_cases hsu : IsUnit s
          · obtain ⟨t, rfl⟩ := hsu
            refine ⟨(↑t⁻¹ : S), ?_⟩
            have : algebraMap S F (↑t⁻¹ : S) * algebraMap S F (t : S) = 1 := by
              rw [← map_mul, Units.inv_mul, map_one]
            rw [hs] at this
            exact (eq_inv_of_mul_eq_one_left this).trans (inv_inv f)
          · exfalso
            have hsmax : s ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal s).mpr hsu
            obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl s
            have ha : a ∈ 𝔓 := (IsLocalization.AtPrime.mk'_mem_maximal_iff S 𝔓 a b).mp hsmax
            have hrel : algebraMap _ F a = algebraMap _ F (b : ↥(chartAlgFin R F j)) * f⁻¹ :=
              (IsLocalization.lift_mk'_spec (M := 𝔓.primeCompl) (hg := hunit) a f⁻¹ b).mp hs
            have h1 : W.valuation ((b : ↥(chartAlgFin R F j)) : F) * W.valuation f⁻¹ = W.valuation (a : F) := by
              rw [← map_mul]; exact congrArg _ hrel.symm
            rw [hval_eq _ b.2, one_mul, map_inv₀] at h1
            have h2 : W.valuation (a : F) < 1 := hval_lt a ha
            rw [← h1, inv_lt_one₀ (by rw [Valuation.pos_iff]; exact hf0)] at h2
            exact not_le.mpr h2 ((W.valuation_le_one_iff f).mpr hfW)
      · rintro ⟨a, b, hb, hf⟩
        apply (W.valuation_le_one_iff f).mp
        have hb1 := hval_eq b hb
        have h1 : W.valuation f * W.valuation ((b : ↥(chartAlgFin R F j)) : F) = W.valuation (a : F) := by
          rw [← map_mul, hf]
        rw [hb1, mul_one] at h1
        rw [h1]
        exact hval_le a
    exact ⟨𝔓, h𝔓prime, hheight, hPmem, hPR, hloc⟩

  obtain ⟨hAV, 𝔓, h𝔓prime, hheight, hPmem, hPR, hloc⟩ := key V hVA hVm hVj
  refine ⟨hAV, ⟨𝔓, h𝔓prime, hheight, hPmem, hPR, hloc⟩, ?_⟩
  intro V' hV'A hV'm hV'j hne
  obtain ⟨hAV', 𝔓', h𝔓'prime, hheight', hPmem', hPR', hloc'⟩ := key V' hV'A hV'm hV'j
  by_contra hno
  push_neg at hno

  have hle : 𝔓' ≤ 𝔓 := by
    intro b hb
    have h1 : (b : F) ∈ V'.nonunits := (hPmem' b).mp hb
    by_contra hb𝔓
    exact hb𝔓 ((hPmem b).mpr (hno b h1))

  have heq : 𝔓' = 𝔓 := by
    haveI := h𝔓prime; haveI := h𝔓'prime
    by_contra hne'
    have hlt : 𝔓' < 𝔓 := lt_of_le_of_ne hle hne'
    have h1 : 𝔓'.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp (le_of_eq hheight)) 𝔓' h𝔓'prime hlt
    rw [hheight'] at h1
    exact lt_irrefl _ h1

  apply hne
  ext f
  rw [hloc, hloc', heq]

end S_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental (solution)
