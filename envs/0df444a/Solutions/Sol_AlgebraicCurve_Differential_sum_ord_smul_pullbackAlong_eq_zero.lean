-- Prove2me | solution 1 for AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6968fb8e-1a03-5681-89b7-7c2e9d89199c

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_residueTheorem_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_hasCanonicalLocalResidueK
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Theorems.Thm_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

namespace W11AbelDiff

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem one_le_ord_of_mem_of_inv_not_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∉ v.toValuationSubring) : 1 ≤ v.ord f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have h0 := ord_nonneg_of_mem v h1
  by_contra hlt
  have hz : v.ord f = 0 := by omega
  apply h2
  have hmul : ((u : v.toValuationSubring) : F) *
      (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [hu, hz, zpow_zero, mul_one, ← eq_inv_of_mul_eq_one_right hmul]
  exact SetLike.coe_mem _

theorem mem_iff_ord_nonneg (f : F) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  refine ⟨ord_nonneg_of_mem v, fun h => ?_⟩
  by_contra hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
  have := one_le_ord_of_mem_of_inv_not_mem v hinv (by simpa using hmem)
  rw [v.ord_inv] at this
  omega

theorem irreducible_unifElt :
    Irreducible (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

theorem coe_unifElt :
    ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)
      = v.uniformizer := rfl

theorem uniformizer_mem : v.uniformizer ∈ v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose.2

theorem ord_eq_zero_of_isUnit {a : v.toValuationSubring} (ha : IsUnit a) : v.ord (a : F) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  exact v.ord_coe_unit u

theorem mem_maximalIdeal_of_not_isUnit {a : v.toValuationSubring} (ha : ¬IsUnit a) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem exists_unit_mul_uniformizer_zpow {g : F} (hg : g ≠ 0) :
    ∃ u : v.toValuationSubringˣ,
      g = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord g := by
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hg (irreducible_unifElt v)
  exact ⟨u, hu⟩

theorem exists_mem_eq_uniformizer_mul {z : F}
    (hz : v.toValuationSubring.valuation z < 1) :
    ∃ s ∈ v.toValuationSubring, z = v.uniformizer * s := by
  have hzO : z ∈ v.toValuationSubring :=
    (v.toValuationSubring.valuation_le_one_iff z).1 hz.le
  have hmax : (⟨z, hzO⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring :=
    (ValuationSubring.valuation_lt_one_iff _ _).2 hz
  rw [(irreducible_unifElt v).maximalIdeal_eq, Ideal.mem_span_singleton'] at hmax
  obtain ⟨s, hs⟩ := hmax
  refine ⟨s, s.2, ?_⟩
  have h := congrArg Subtype.val hs
  simp only [MulMemClass.coe_mul] at h
  rw [← h, coe_unifElt, mul_comm]

end Toolkit

section LogDer

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] (Θ : Derivation R L L)

theorem logDer_mul {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    Θ (a * b) / (a * b) = Θ a / a + Θ b / b := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, div_add_div _ _ ha hb,
    div_eq_div_iff (mul_ne_zero ha hb) (mul_ne_zero ha hb)]
  ring

theorem logDer_zpow {a : L} (ha : a ≠ 0) (n : ℤ) :
    Θ (a ^ n) / a ^ n = (n : L) * (Θ a / a) := by
  rw [Derivation.leibniz_zpow, zpow_sub_one₀ ha, smul_eq_mul, zsmul_eq_mul,
    div_eq_iff (zpow_ne_zero n ha), div_eq_mul_inv]
  ring

variable {K : Type*} [Field K] [Algebra K L] (v : Place K L)

theorem logDer_mem_of_ord_eq_zero
    (hΘ : ∀ z ∈ v.toValuationSubring, Θ z ∈ v.toValuationSubring) {f : L} (hf : v.ord f = 0) :
    Θ f / f ∈ v.toValuationSubring := by
  rw [div_eq_mul_inv]
  refine mul_mem (hΘ _ ((mem_iff_ord_nonneg v f).2 hf.ge)) ((mem_iff_ord_nonneg v _).2 ?_)
  rw [v.ord_inv, hf, neg_zero]

theorem logDer_eq (hΘ : ∀ z ∈ v.toValuationSubring, Θ z ∈ v.toValuationSubring)
    {g : L} (hg : g ≠ 0) :
    ∃ ℓ ∈ v.toValuationSubring,
      Θ g / g = ℓ + (v.ord g : L) * (Θ v.uniformizer / v.uniformizer) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_zpow v hg
  have hU0 : ((u : v.toValuationSubring) : L) ≠ 0 := by
    intro h0
    apply hg
    rw [hu, h0, zero_mul]
  refine ⟨Θ (u : L) / (u : L), logDer_mem_of_ord_eq_zero Θ v hΘ (v.ord_coe_unit u), ?_⟩
  conv_lhs => rw [hu]
  rw [logDer_mul Θ hU0 (zpow_ne_zero _ v.uniformizer_ne_zero),
    logDer_zpow Θ v.uniformizer_ne_zero]

theorem logDer_uniformizer_mem (hΘ : ∀ z ∈ v.toValuationSubring, Θ z ∈ v.toValuationSubring)
    {p : L} (hp1 : v.ord p = 1) (hΘp : Θ p = 0) :
    Θ v.uniformizer / v.uniformizer ∈ v.toValuationSubring := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp1
  obtain ⟨w, hw⟩ := exists_unit_mul_uniformizer_zpow v hp0
  rw [hp1, zpow_one] at hw
  have hW0 : ((w : v.toValuationSubring) : L) ≠ 0 := by
    intro h0
    apply hp0
    rw [hw, h0, zero_mul]
  have h0 : Θ p / p = 0 := by rw [hΘp, zero_div]
  rw [hw, logDer_mul Θ hW0 v.uniformizer_ne_zero] at h0
  have h1 : Θ v.uniformizer / v.uniformizer
      = -(Θ (w : L) / (w : L)) := by
    linear_combination h0
  rw [h1]
  exact neg_mem (logDer_mem_of_ord_eq_zero Θ v hΘ (v.ord_coe_unit w))

end LogDer

section BasisD

open scoped Polynomial
open KaehlerDifferential TensorProduct IntermediateField

variable (K : Type*) [Field K]

noncomputable def polyBasis : Module.Basis (Fin 1) K[X] Ω[K[X]⁄K] :=
  (Module.Basis.singleton (Fin 1) K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

theorem polyBasis_zero : polyBasis K 0 = D K K[X] Polynomial.X := by
  simp [polyBasis]

noncomputable def ratFuncBasis : Module.Basis (Fin 1) (RatFunc K) Ω[(RatFunc K)⁄K] :=
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  ((polyBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem ratFuncBasis_zero : ratFuncBasis K 0 = D K (RatFunc K) RatFunc.X := by
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  simp only [ratFuncBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, polyBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
    RatFunc.algebraMap_X]

variable {F : Type*} [Field F] [Algebra K F]

noncomputable def towerBasis [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Module.Basis (Fin 1) F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  ((ratFuncBasis K).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) F)

theorem towerBasis_zero [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] :
    towerBasis K (F := F) 0 = D K F (algebraMap (RatFunc K) F RatFunc.X) := by
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  simp only [towerBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, ratFuncBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

theorem exists_basis_D (F : Type*) [Field F] [Algebra K F] [CharZero K]
    {t : F} (ht : Transcendental K t) (hfin : FiniteDimensional K⟮t⟯ F) :
    ∃ b : Module.Basis (Fin 1) F (Ω[F⁄K]), b 0 = D K F t := by
  haveI := hfin
  haveI : CharZero K⟮t⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮t⟯).injective
  haveI : Algebra.IsSeparable K⟮t⟯ F := Algebra.IsSeparable.of_integral K⟮t⟯ F
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  refine ⟨towerBasis K, ?_⟩
  rw [towerBasis_zero]
  show D K F (algebraMap K⟮t⟯ F (e RatFunc.X)) = D K F t
  congr 1
  exact RatFunc.algEquivOfTranscendental_X t ht

end BasisD

section Coeff

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def coeffLin (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    Ω[F⁄K] →ₗ[F] F where
  toFun := w.differentialCoeff
  map_add' ω₁ ω₂ := w.differentialCoeff_unique
    (by rw [add_smul, w.differentialCoeff_smul_dCoord, w.differentialCoeff_smul_dCoord])
  map_smul' c ω := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact w.differentialCoeff_smul c ω

@[scoped simp]
theorem coeffLin_apply (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] (ω : Ω[F⁄K]) :
    coeffLin w ω = w.differentialCoeff ω := rfl

noncomputable def coeffDer (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    Derivation K F F :=
  (coeffLin w).compDer (D K F)

@[scoped simp]
theorem coeffDer_apply (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] (f : F) :
    coeffDer w f = w.differentialCoeff (D K F f) := rfl

theorem coeffDer_uniformizer (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    coeffDer w w.uniformizer = 1 := by
  rw [coeffDer_apply, ← Place.dCoord_eq, w.differentialCoeff_dCoord]

theorem differentialCoeff_D_mem [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ w : Place K F, w.DCoordGenerates] (w : Place K F) {z : F}
    (hz : z ∈ w.toValuationSubring) :
    w.differentialCoeff (D K F z) ∈ w.toValuationSubring := by

  have hunit : ∀ u : F, u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (D K F u) ∈ w.toValuationSubring := by
    intro u hu0 hu
    rcases localUnitDerivativeRegular_of_isCurveOver w u hu0 hu with h | h
    · rw [h]; exact zero_mem _
    · exact (mem_iff_ord_nonneg w _).2 h
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [← coeffDer_apply, map_zero]; exact zero_mem _
  by_cases hzu : w.ord z = 0
  · exact hunit z hz0 hzu
  have h1 : 1 ≤ w.ord z := by have := ord_nonneg_of_mem w hz; omega
  have hzmax : (⟨z, hz⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    mem_maximalIdeal_of_not_isUnit w fun hu => by
      have := ord_eq_zero_of_isUnit w hu; simp only at this; omega
  have hu : IsUnit (1 - (⟨z, hz⟩ : w.toValuationSubring)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hzmax
  have hu0 : (1 - z : F) ≠ 0 := by
    intro h
    apply hu.ne_zero
    exact Subtype.ext h
  have huord : w.ord (1 - z) = 0 := ord_eq_zero_of_isUnit w hu
  have key : w.differentialCoeff (D K F z) = -w.differentialCoeff (D K F (1 - z)) := by
    rw [← coeffDer_apply, ← coeffDer_apply, map_sub, Derivation.map_one_eq_zero, zero_sub,
      neg_neg]
  rw [key]
  exact neg_mem (hunit _ hu0 huord)

end Coeff

section Residue

open KaehlerDifferential IntermediateField
open scoped Polynomial

variable {E FE : Type*} [Field E] [Field FE] [Algebra E FE]

theorem trace_localResidue_eq [IsAlgClosed E] [IsCurveOver E FE]
    [HasCanonicalLocalResidueKStar E FE] (v : Place E FE) (r : E) {f : FE}
    (h : f - algebraMap E FE r * v.uniformizer⁻¹ ∈ v.toValuationSubring) :
    Algebra.trace E v.ResidueField (v.localResidue f) = r := by
  have hf : f = (f - algebraMap E FE r * v.uniformizer⁻¹) + r • v.uniformizer⁻¹ := by
    rw [Algebra.smul_def]; ring
  rw [hf, map_add, v.localResidue_of_mem h, zero_add, LinearMap.map_smul,
    v.gate_localResidue_uniformizer_inv, ← Algebra.algebraMap_eq_smul_one,
    Algebra.trace_algebraMap,
    show Module.finrank E v.ResidueField = 1 from IsCurveOver.deg_eq_one_of_isAlgClosed v,
    one_smul]

theorem trace_localResidue_eq_zero [HasCanonicalLocalResidueKStar E FE] (v : Place E FE)
    {f : FE} (h : f ∈ v.toValuationSubring) :
    Algebra.trace E v.ResidueField (v.localResidue f) = 0 := by
  rw [v.localResidue_of_mem h, map_zero]

theorem residueTheorem_of_curve [IsAlgClosed E] [CharZero E] [IsCurveOver E FE]
    [HasCanonicalLocalResidueKStar E FE] [HasCanonicalDivisor (K := E) (F := FE)]
    [∀ v : Place E FE, v.DCoordGenerates]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE) :
    ResidueTheorem E FE := by
  classical
  obtain ⟨t, ht, hfin⟩ := hfgE
  haveI := hfin
  haveI : PerfectField E := inferInstance
  haveI : Algebra.EssFiniteType E FE := essFiniteType_of_transcendental_of_finiteDimensional ht hfin
  let e : RatFunc E ≃ₐ[E] E⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc E) FE :=
    ((algebraMap E⟮t⟯ FE).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc E) FE)
        (e.symm.toRingEquiv : E⟮t⟯ →+* RatFunc E)
      = RingHom.comp (RingEquiv.refl FE : FE →+* FE) (algebraMap E⟮t⟯ FE) := by
    refine RingHom.ext fun a => ?_
    show algebraMap E⟮t⟯ FE (e (e.symm a)) = algebraMap E⟮t⟯ FE a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower E (RatFunc E) FE :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap E FE a = algebraMap E⟮t⟯ FE (e (algebraMap E (RatFunc E) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Module.Finite (RatFunc E) FE :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl FE) hsq
  haveI : Algebra.IsIntegral (RatFunc E) FE := Algebra.IsIntegral.of_finite _ _
  haveI : CharZero (RatFunc E) :=
    charZero_of_injective_algebraMap (algebraMap E (RatFunc E)).injective
  haveI : PerfectField (RatFunc E) := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable (RatFunc E) FE := Algebra.IsSeparable.of_integral _ _
  haveI : IsCurveOver E (RatFunc E) := isCurveOver_ratFunc E
  haveI : Algebra.EssFiniteType E (RatFunc E) := by
    haveI : Algebra.EssFiniteType E[X] (RatFunc E) :=
      Algebra.EssFiniteType.of_isLocalization (RatFunc E) (nonZeroDivisors E[X])
    exact Algebra.EssFiniteType.comp E E[X] (RatFunc E)
  haveI : ∀ v : Place E (RatFunc E), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  intro hPD ω hω f
  exact residueTheorem_of_isAlgClosed hω f

end Residue

section Main

open KaehlerDifferential IntermediateField

theorem main
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (g : FE) (hg : g ≠ 0)
    (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E))
    (hS : ∀ P ∈ S, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1)
    (hrat : ∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
      ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring)
    (ω : Ω[F⁄K]) (hω : ω ∈ regularDifferentials K F) :
    ∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P) ω = 0 := by
  classical

  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : PerfectField E := inferInstance
  obtain ⟨x, hx, hxfin⟩ := hfg
  haveI := hxfin
  obtain ⟨t, ht, htfin⟩ := hfgE
  haveI : Algebra.EssFiniteType E FE :=
    essFiniteType_of_transcendental_of_finiteDimensional ht htfin
  haveI hDC : ∀ w : Place E FE, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI : HasCanonicalDivisor (K := E) (F := FE) := hasCanonicalDivisor_of_isCurveOver
  haveI hK : HasCanonicalLocalResidueK E FE := hasCanonicalLocalResidueK E FE
  letI : HasCanonicalLocalResidueKStar E FE :=
    ⟨fun v => (HasCanonicalLocalResidueK.exists_data v).some⟩

  obtain ⟨a, hωa⟩ : ∃ a : F, ω = a • D K F x := by
    obtain ⟨bF, hbF⟩ := exists_basis_D K F hx hxfin
    refine ⟨bF.repr ω 0, ?_⟩
    have h := bF.sum_repr ω
    rw [Fin.sum_univ_one, hbF] at h
    exact h.symm

  refine (Module.forall_dual_apply_eq_zero_iff E _).1 fun lam => ?_
  let δ : Derivation K E E := lam.compDer (D K E)
  have hδ : ∀ e : E, δ e = lam (D K E e) := fun e => rfl
  have hlam : lam (∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P) ω)
      = ∑ P ∈ S, ((P.ord g : ℤ) : E) * ((y P a) * δ (y P x)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [map_zsmul, hωa, Differential.pullbackAlong_smul, Differential.pullbackAlong_D,
      LinearMap.map_smul, smul_eq_mul, zsmul_eq_mul, hδ]
  rw [hlam]

  obtain ⟨Θ, hΘF, hΘE, hΘO⟩ :=
    exists_derivation_constantFieldExtension_map_mem K F E FE ⟨x, hx, hxfin⟩ ⟨t, ht, htfin⟩
      hgen δ

  obtain ⟨bE, -⟩ := exists_basis_D E FE ht htfin
  have hω₀ : bE 0 ≠ 0 := bE.ne_zero 0
  obtain ⟨h, hDx⟩ : ∃ h : FE, D E FE (algebraMap F FE x) = h • bE 0 := by
    refine ⟨bE.repr (D E FE (algebraMap F FE x)) 0, ?_⟩
    have h := bE.sum_repr (D E FE (algebraMap F FE x))
    rw [Fin.sum_univ_one] at h
    exact h.symm
  have hcoef : ∀ v : Place E FE,
      h * v.differentialCoeff (bE 0) = coeffDer v (algebraMap F FE x) := by
    intro v
    rw [coeffDer_apply, hDx, Place.differentialCoeff_smul]

  have RT : ResidueTheorem E FE := residueTheorem_of_curve ⟨t, ht, htfin⟩
  have hRT := RT hω₀ (Θ g / g * algebraMap F FE a * h)
  rw [weilOfKaehler_apply] at hRT
  have hRT' : ∑ᶠ v, kaehlerResidueTerm (bE 0)
      (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v = 0 := hRT
  have hTv : ∀ v : Place E FE,
      kaehlerResidueTerm (bE 0) (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v
        = Algebra.trace E v.ResidueField (v.localResidue
            (Θ g / g * (algebraMap F FE a * coeffDer v (algebraMap F FE x)))) := by
    intro v
    show Algebra.trace E v.ResidueField (v.localResidue
      (Θ g / g * algebraMap F FE a * h * v.differentialCoeff (bE 0))) = _
    rw [mul_assoc, mul_assoc, hcoef v]

  have hEmem : ∀ (v : Place E FE) (e : E), algebraMap E FE e ∈ v.toValuationSubring :=
    fun v e => v.algebraMap_mem' e

  have hT_on : ∀ v ∈ S,
      kaehlerResidueTerm (bE 0) (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v
        = -(((v.ord g : ℤ) : E) * ((y v a) * δ (y v x))) := by
    intro v hv
    rw [hTv]
    refine trace_localResidue_eq v _ ?_

    obtain ⟨s₁, hs₁, hs₁e⟩ := exists_mem_eq_uniformizer_mul v (hS v hv a)
    obtain ⟨s₂, hs₂, hs₂e⟩ := exists_mem_eq_uniformizer_mul v (hS v hv x)
    obtain ⟨ℓ, hℓ, hL⟩ := logDer_eq Θ v (hΘO v) hg
    have hπ : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
    have hπi : v.uniformizer * v.uniformizer⁻¹ = 1 := mul_inv_cancel₀ hπ
    have ha' : algebraMap F FE a = algebraMap E FE (y v a) + v.uniformizer * s₁ := by
      linear_combination hs₁e
    have hx' : algebraMap F FE x = algebraMap E FE (y v x) + v.uniformizer * s₂ := by
      linear_combination hs₂e

    have hc : coeffDer v (algebraMap F FE x)
        = v.uniformizer * coeffDer v s₂ + s₂ := by
      rw [hx', map_add, Derivation.map_algebraMap, Derivation.leibniz, coeffDer_uniformizer,
        smul_eq_mul, smul_eq_mul, mul_one, zero_add]

    have h3 : Θ v.uniformizer * s₂ + v.uniformizer * Θ s₂
        + algebraMap E FE (δ (y v x)) = 0 := by
      have h0 := hΘF x
      rw [hx', map_add, hΘE, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h0
      linear_combination h0
    have hr : algebraMap E FE (-(((v.ord g : ℤ) : E) * ((y v a) * δ (y v x))))
        = -((v.ord g : FE) * (algebraMap E FE (y v a) * algebraMap E FE (δ (y v x)))) := by
      rw [map_neg, map_mul, map_mul, map_intCast]
    rw [hr, hL, ha', hc, div_eq_mul_inv]
    have key :
        (ℓ + (v.ord g : FE) * (Θ v.uniformizer * v.uniformizer⁻¹)) *
            ((algebraMap E FE (y v a) + v.uniformizer * s₁) *
              (v.uniformizer * coeffDer v s₂ + s₂)) -
          -((v.ord g : FE) * (algebraMap E FE (y v a) * algebraMap E FE (δ (y v x)))) *
            v.uniformizer⁻¹
        = ℓ * ((algebraMap E FE (y v a) + v.uniformizer * s₁) *
              (v.uniformizer * coeffDer v s₂ + s₂))
          + (v.ord g : FE) * (Θ v.uniformizer * (algebraMap E FE (y v a) * coeffDer v s₂
              + v.uniformizer * s₁ * coeffDer v s₂ + s₁ * s₂)
              - algebraMap E FE (y v a) * Θ s₂) := by
      linear_combination
        ((v.ord g : FE) * (Θ v.uniformizer * (algebraMap E FE (y v a) * coeffDer v s₂
              + v.uniformizer * s₁ * coeffDer v s₂ + s₁ * s₂)
              - algebraMap E FE (y v a) * Θ s₂)) * hπi
        + ((v.ord g : FE) * algebraMap E FE (y v a) * v.uniformizer⁻¹) * h3
    rw [key]
    have hcs : coeffDer v s₂ ∈ v.toValuationSubring := by
      rw [coeffDer_apply]; exact differentialCoeff_D_mem v hs₂
    have hπm : v.uniformizer ∈ v.toValuationSubring := uniformizer_mem v
    have hA : algebraMap E FE (y v a) ∈ v.toValuationSubring := hEmem v _
    have hm : ((v.ord g : ℤ) : FE) ∈ v.toValuationSubring := intCast_mem _ _
    refine add_mem (mul_mem hℓ (mul_mem (add_mem hA (mul_mem hπm hs₁))
      (add_mem (mul_mem hπm hcs) hs₂))) (mul_mem hm (sub_mem (mul_mem (hΘO v _ hπm)
        (add_mem (add_mem (mul_mem hA hcs) (mul_mem (mul_mem hπm hs₁) hcs)) (mul_mem hs₁ hs₂)))
        (mul_mem hA (hΘO v _ hs₂))))

  have hT_off : ∀ v ∉ S,
      kaehlerResidueTerm (bE 0) (diagonalHom E FE (Θ g / g * algebraMap F FE a * h)) v = 0 := by
    intro v hv
    rw [hTv]
    refine trace_localResidue_eq_zero v ?_
    by_cases hnew : ∀ f : F, algebraMap F FE f ∈ v.toValuationSubring
    ·
      have hord : v.ord g = 0 := by
        by_contra hne
        obtain ⟨f, hf⟩ := hrat v hv hne
        exact hf (hnew f)
      refine mul_mem (logDer_mem_of_ord_eq_zero Θ v (hΘO v) hord) (mul_mem (hnew a) ?_)
      rw [coeffDer_apply]
      exact differentialCoeff_D_mem v (hnew x)
    ·
      push Not at hnew
      obtain ⟨f₀, hf₀⟩ := hnew
      have hwK : ∀ k : K, (algebraMap F FE : F →+* FE) (algebraMap K F k)
          ∈ v.toValuationSubring := by
        intro k
        have : (algebraMap F FE : F →+* FE) (algebraMap K F k)
            = algebraMap E FE (algebraMap K E k) := by
          show algebraMap F FE (algebraMap K F k) = _
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [this]
        exact hEmem v _
      obtain ⟨u, hu⟩ := Place.exists_toValuationSubring_eq_comap_ringHom (K := K) x
        (algebraMap F FE : F →+* FE) v.toValuationSubring hwK ⟨f₀, hf₀⟩
      have hmemF : ∀ f : F, f ∈ u.toValuationSubring ↔
          algebraMap F FE f ∈ v.toValuationSubring := by
        intro f
        rw [hu, ValuationSubring.mem_comap]
      obtain ⟨P', -, hP'ord, hP'uniq⟩ :=
        Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE ⟨x, hx, hxfin⟩
          ⟨t, ht, htfin⟩ hgen u
      have hvP' : v = P' := hP'uniq v hu.symm
      have hordF : ∀ f : F, v.ord (algebraMap F FE f) = u.ord f := by
        intro f; rw [hvP']; exact hP'ord f

      have hLg : Θ g / g ∈ v.toValuationSubring := by
        obtain ⟨ℓ, hℓ, hL⟩ := logDer_eq Θ v (hΘO v) hg
        rw [hL]
        refine add_mem hℓ (mul_mem (intCast_mem _ _) ?_)
        refine logDer_uniformizer_mem Θ v (hΘO v) (p := algebraMap F FE u.uniformizer) ?_ (hΘF _)
        rw [hordF, u.ord_uniformizer]

      obtain ⟨fu, hfu, hωu⟩ := (mem_regularDifferentials_iff).1 hω u
      have h1 : ∀ (c z : F), KaehlerDifferential.map K E F FE (c • D K F z)
          = algebraMap F FE c • D E FE (algebraMap F FE z) := by
        intro c z
        rw [LinearMap.map_smul, KaehlerDifferential.map_D, algebraMap_smul]
      have hmap : algebraMap F FE a • D E FE (algebraMap F FE x)
          = algebraMap F FE fu • D E FE (algebraMap F FE u.uniformizer) := by
        rw [← h1, ← h1, ← hωa, ← Place.dCoord_eq, ← hωu]
      have hreg : algebraMap F FE a * coeffDer v (algebraMap F FE x)
          = algebraMap F FE fu * coeffDer v (algebraMap F FE u.uniformizer) := by
        have h2 := congrArg v.differentialCoeff hmap
        rwa [Place.differentialCoeff_smul, Place.differentialCoeff_smul] at h2
      refine mul_mem hLg ?_
      rw [hreg]
      refine mul_mem ((hmemF fu).1 hfu) ?_
      rw [coeffDer_apply]
      exact differentialCoeff_D_mem v ((hmemF _).1 (uniformizer_mem u))

  have hsupp : Function.support (kaehlerResidueTerm (bE 0)
      (diagonalHom E FE (Θ g / g * algebraMap F FE a * h))) ⊆ ↑S := by
    intro v hv
    by_contra hvS
    exact hv (hT_off v (by simpa using hvS))
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_congr rfl hT_on,
    Finset.sum_neg_distrib, neg_eq_zero] at hRT'
  exact hRT'

end Main

end W11AbelDiff
p2m_reactivate "P2MW.S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.W11AbelDiff"

open AlgebraicCurve in
theorem solution
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (g : FE) (hg : g ≠ 0)
    (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E))
    (hS : ∀ P ∈ S, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1)
    (hrat : ∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
      ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring)
    (ω : Ω[F⁄K]) (hω : ω ∈ regularDifferentials K F) :
    ∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P) ω = 0 :=
  W11AbelDiff.main K F E FE hfg hfgE hgen g hg S y hS hrat ω hω

end S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero (solution)
