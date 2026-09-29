-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_weilPairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1385c85d-4381-5857-96db-6eac83489eef

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational
import Theorems.Thm_AlgebraicCurve_weilReciprocity
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible
import Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_weilPairing
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_exists_weilPairing.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "FundamentalIdentityAlong FiniteAlong NormFormulaAlong Pic0.correspondence Place Divisor HasPrincipalDivisors Pic0 Pic0.mk Pic0.torsion Pic0.mem_torsion SemilinearAut SemilinearAut.baseAut SemilinearAut.smulValuationSubringEquiv SemilinearAut.smul_toValuationSubring SemilinearAut.ord_smul SemilinearAut.smulResidueRingEquiv SemilinearAut.smulResidueRingEquiv_algebraMap SemilinearAut.divisor_smul_def SemilinearAut.divisor_smul_apply_smul SemilinearAut.divisor_smul_apply SemilinearAut.pic0_smul_mk SemilinearAut.smul_mem_torsion IsCurveOver WeilDatum.coe_classLeft WeilDatum.coe_classRight DivisorialWeilPairingData DivisorialWeilPairingData.pair_pow_eq_one WeilDatum Place.IsRational Divisor.evalFun Divisor.evalFun_def WeilReciprocity Divisor.evalFun_natCast_smul_divisor Pic0.exists_nsmul_eq weilReciprocity DivisorialWeilPairingData.toHom_injective_of_divisible FunctionField.exists_ratFuncAlgHom_apply_X_eq isCurveOver_of_transcendental Pic0.nonempty_divisorialWeilPairingData DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence"
namespace WC7E
p2m_open "AlgebraicCurve"

private theorem transcendental_not_mem_range {K F : Type*} [Field K] [Field F] [Algebra K F]
    {j : F} (hj : Transcendental K j) : j ∉ Set.range (algebraMap K F) := by
  rintro ⟨c, rfl⟩
  exact hj (isAlgebraic_algebraMap c)

private theorem transcendental_algHom {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (ψ : A →ₐ[K] B) (hinj : Function.Injective ψ)
    {a : A} (ha : Transcendental K a) : Transcendental K (ψ a) := by
  rintro ⟨p, hp0, hpe⟩
  refine ha ⟨p, hp0, hinj ?_⟩
  rw [← Polynomial.aeval_algHom_apply, hpe, map_zero]

private theorem transcendental_ratFunc_X {K : Type*} [Field K] :
    Transcendental K (RatFunc.X : RatFunc K) := by
  have h := transcendental_algHom (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
    (IsFractionRing.injective (Polynomial K) (RatFunc K)) (Polynomial.transcendental_X K)
  simpa [RatFunc.algebraMap_X] using h

private theorem ratFuncAlgHom_fieldRange_eq_adjoin {K F : Type*} [Field K] [Field F]
    [Algebra K F] (φ : RatFunc K →ₐ[K] F) :
    φ.fieldRange = IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
  have key : ∀ p : Polynomial K,
      φ (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (φ RatFunc.X) p := by
    intro p
    have h2 : φ.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
        = Polynomial.aeval (φ RatFunc.X) := by
      apply Polynomial.algHom_ext
      simp [RatFunc.algebraMap_X]
    exact DFunLike.congr_fun h2 p
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply RatFunc.induction_on z
    intro p q hq
    show φ (algebraMap (Polynomial K) (RatFunc K) p
        / algebraMap (Polynomial K) (RatFunc K) q)
      ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F)
    rw [map_div₀, key, key]
    have hmem : ∀ r : Polynomial K,
        Polynomial.aeval (φ RatFunc.X) r
          ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
      intro r
      exact IntermediateField.algebra_adjoin_le_adjoin K _
        (Polynomial.aeval_mem_adjoin_singleton K _)
    exact div_mem (hmem p) (hmem q)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨RatFunc.X, rfl⟩

private theorem finite_ratFunc_of_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : RatFunc K →ₐ[K] F) {j : F} (hX : φ RatFunc.X = j)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F) :
    @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule := by
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  show FiniteDimensional (RatFunc K) F
  have hE : φ.fieldRange = IntermediateField.adjoin K ({j} : Set F) := by
    rw [ratFuncAlgHom_fieldRange_eq_adjoin, hX]
  haveI hfdE : FiniteDimensional φ.fieldRange F := by rw [hE]; exact hfd
  let ε : RatFunc K ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  letI : Algebra (RatFunc K) φ.fieldRange := ε.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) φ.fieldRange F :=
    IsScalarTower.of_algebraMap_eq fun z => rfl
  haveI : Module.Finite (RatFunc K) φ.fieldRange :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) φ.fieldRange) ε.surjective
  exact Module.Finite.trans (↥φ.fieldRange) F

private theorem hdiv_engine {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (L' : Type*) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
    [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'] :
    ∀ m : ℤ, m ≠ 0 → ∀ x : Pic0 K L', ∃ y, m • y = x := by
  intro m hm x

  set ψ : RatFunc K →ₐ[K] L' := IsScalarTower.toAlgHom K (RatFunc K) L' with hψ
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  set x₀ : L' := ψ RatFunc.X with hx₀
  have hx₀tr : Transcendental K x₀ := transcendental_algHom ψ hψinj transcendental_ratFunc_X

  have hE : ψ.fieldRange = IntermediateField.adjoin K ({x₀} : Set L') :=
    ratFuncAlgHom_fieldRange_eq_adjoin ψ

  haveI hfdE : FiniteDimensional (↥ψ.fieldRange) L' := by
    let ε : RatFunc K ≃ₐ[K] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
    letI : Algebra (RatFunc K) ψ.fieldRange := ε.toAlgHom.toRingHom.toAlgebra
    haveI : IsScalarTower (RatFunc K) ψ.fieldRange L' :=
      IsScalarTower.of_algebraMap_eq fun z => rfl
    exact Module.Finite.of_restrictScalars_finite (RatFunc K) (↥ψ.fieldRange) L'
  haveI hfd : FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set L')) L' := by
    rw [← hE]; exact hfdE

  haveI : CharZero (IntermediateField.adjoin K ({x₀} : Set L')) :=
    charZero_of_injective_algebraMap
      (algebraMap K (IntermediateField.adjoin K ({x₀} : Set L'))).injective
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x₀} : Set L')) L' :=
    inferInstance

  haveI : IsCurveOver K L' := isCurveOver_of_transcendental hx₀tr hfd hsep
  obtain ⟨y, hy⟩ := Pic0.exists_nsmul_eq K L' ⟨x₀, hx₀tr, hfd⟩ m.natAbs
    (Int.natAbs_ne_zero.mpr hm) x
  rcases Int.natAbs_eq m with h | h
  · exact ⟨y, by rw [h, natCast_zsmul, hy]⟩
  · refine ⟨-y, ?_⟩
    rw [h, neg_zsmul, zsmul_neg, neg_neg, natCast_zsmul, hy]

section Equivariance

open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mem_smul_toValuationSubring_iff (g : SemilinearAut K F) (v : Place K F)
    (f : F) : g • f ∈ (g • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  constructor
  · intro h
    have h1 := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      (g := g) (S := v.toValuationSubring) (x := g • f)).mp h
    rwa [inv_smul_smul] at h1
  · intro h
    exact ValuationSubring.smul_mem_pointwise_smul g f v.toValuationSubring h

private theorem isRational_smul (g : SemilinearAut K F) (v : Place K F)
    (hv : v.IsRational) : (g • v).IsRational := by
  intro x
  obtain ⟨a, ha⟩ := hv ((SemilinearAut.smulResidueRingEquiv g v).symm x)
  exact ⟨SemilinearAut.baseAut g a, by
    rw [← SemilinearAut.smulResidueRingEquiv_algebraMap g v a, ha,
      RingEquiv.apply_symm_apply]⟩

private theorem residue_smul (g : SemilinearAut K F) (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    IsLocalRing.residue (g • v).toValuationSubring
        (⟨g • f, (mem_smul_toValuationSubring_iff g v f).mpr hf⟩ :
          (g • v).toValuationSubring)
      = SemilinearAut.smulResidueRingEquiv g v
          (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩) := by
  show _ = IsLocalRing.ResidueField.mapEquiv
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring)
      (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ (Subtype.ext rfl)

private theorem evalAt_smul (g : SemilinearAut K F) (v : Place K F) (hv : v.IsRational)
    {f : F} (hf : f ∈ v.toValuationSubring) :
    (g • v).evalAt (g • f) = SemilinearAut.baseAut g (v.evalAt f) := by
  have hv' : (g • v).IsRational := isRational_smul g v hv
  have hmem : g • f ∈ (g • v).toValuationSubring :=
    (mem_smul_toValuationSubring_iff g v f).mpr hf
  apply (g • v).algebraMap_residueField_injective
  rw [(g • v).algebraMap_evalAt hv' hmem, residue_smul g v hf, ← v.algebraMap_evalAt hv hf]
  exact SemilinearAut.smulResidueRingEquiv_algebraMap g v (v.evalAt f)

private theorem evalFun_smul (g : SemilinearAut K F) {f : F} (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hmem : ∀ v ∈ D.support, f ∈ v.toValuationSubring) :
    Divisor.evalFun (g • f) (g • D) = SemilinearAut.baseAut g (Divisor.evalFun f D) := by
  classical
  have hL : Divisor.evalFun (g • f) (g • D)
      = ∏ w ∈ D.support, (g • w).evalAt (g • f) ^ D w := by
    rw [show Divisor.evalFun (g • f) (g • D)
        = (g • D).prod (fun w n => w.evalAt (g • f) ^ n) from rfl,
      SemilinearAut.divisor_smul_def, Finsupp.prod_mapDomain_index_inj (MulAction.injective g)]
    rfl
  have hR : SemilinearAut.baseAut g (Divisor.evalFun f D)
      = ∏ w ∈ D.support, SemilinearAut.baseAut g (w.evalAt f ^ D w) := by
    rw [Divisor.evalFun_def, map_prod]
  rw [hL, hR]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [evalAt_smul g w (hrat w hw) (hmem w hw), map_zpow₀]

private def semilinearSmul {n : ℕ} (g : SemilinearAut K F) (d : WeilDatum K F n) :
    WeilDatum K F n where
  D₁ := g • d.D₁
  D₂ := g • d.D₂
  f₁ := g • d.f₁
  f₂ := g • d.f₂
  f₁_ne_zero := fun h0 => d.f₁_ne_zero (by
    have h1 : g⁻¹ • (g • d.f₁) = g⁻¹ • (0 : F) := congrArg (g⁻¹ • ·) h0
    rwa [inv_smul_smul, smul_zero] at h1)
  f₂_ne_zero := fun h0 => d.f₂_ne_zero (by
    have h1 : g⁻¹ • (g • d.f₂) = g⁻¹ • (0 : F) := congrArg (g⁻¹ • ·) h0
    rwa [inv_smul_smul, smul_zero] at h1)
  ord_f₁ := by
    intro v
    rw [show v = g • (g⁻¹ • v) from (smul_inv_smul g v).symm, SemilinearAut.ord_smul,
      SemilinearAut.divisor_smul_apply_smul]
    exact d.ord_f₁ (g⁻¹ • v)
  ord_f₂ := by
    intro v
    rw [show v = g • (g⁻¹ • v) from (smul_inv_smul g v).symm, SemilinearAut.ord_smul,
      SemilinearAut.divisor_smul_apply_smul]
    exact d.ord_f₂ (g⁻¹ • v)
  disjoint := by
    intro v
    rw [SemilinearAut.divisor_smul_apply, SemilinearAut.divisor_smul_apply]
    exact d.disjoint (g⁻¹ • v)
  rational := by
    intro v hv
    rw [SemilinearAut.divisor_smul_apply, SemilinearAut.divisor_smul_apply] at hv
    have h1 : (g⁻¹ • v).IsRational := d.rational (g⁻¹ • v) hv
    have h2 := isRational_smul g (g⁻¹ • v) h1
    rwa [smul_inv_smul] at h2

private theorem semilinearSmul_pairing {n : ℕ} (g : SemilinearAut K F)
    (d : WeilDatum K F n) :
    (semilinearSmul g d).pairing = SemilinearAut.baseAut g d.pairing := by
  show Divisor.evalFun (g • d.f₁) (g • d.D₂) / Divisor.evalFun (g • d.f₂) (g • d.D₁)
      = SemilinearAut.baseAut g d.pairing
  rw [evalFun_smul g d.D₂ (fun v hv => d.rational_of_mem_support_right hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₁_ne_zero
        (d.ord_f₁_eq_zero_of_mem_support hv).ge),
    evalFun_smul g d.D₁ (fun v hv => d.rational_of_mem_support_left hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₂_ne_zero
        (d.ord_f₂_eq_zero_of_mem_support hv).ge),
    ← map_div₀]
  rfl

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

private theorem coe_classLeft_semilinearSmul (g : SemilinearAut K F) (d : WeilDatum K F n) :
    ((semilinearSmul g d).classLeft : Pic0 K F) = g • (d.classLeft : Pic0 K F) := by
  rw [WeilDatum.coe_classLeft, WeilDatum.coe_classLeft, SemilinearAut.pic0_smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

private theorem coe_classRight_semilinearSmul (g : SemilinearAut K F) (d : WeilDatum K F n) :
    ((semilinearSmul g d).classRight : Pic0 K F) = g • (d.classRight : Pic0 K F) := by
  rw [WeilDatum.coe_classRight, WeilDatum.coe_classRight, SemilinearAut.pic0_smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

private theorem pair_semilinearSmul (e : DivisorialWeilPairingData K F n)
    (g : SemilinearAut K F) (x y : Pic0.torsion K F n) :
    e.pair ⟨g • (x : Pic0 K F), SemilinearAut.smul_mem_torsion g x.2⟩
        ⟨g • (y : Pic0 K F), SemilinearAut.smul_mem_torsion g y.2⟩
      = SemilinearAut.baseAut g (e.pair x y) := by
  obtain ⟨d, hx, hy⟩ := e.exists_datum x y
  have h1 := e.compatible (semilinearSmul g d)
  have hL : (semilinearSmul g d).classLeft
      = (⟨g • (x : Pic0 K F), SemilinearAut.smul_mem_torsion g x.2⟩ :
          Pic0.torsion K F n) := by
    refine Subtype.ext ?_
    rw [coe_classLeft_semilinearSmul, hx]
  have hR : (semilinearSmul g d).classRight
      = (⟨g • (y : Pic0 K F), SemilinearAut.smul_mem_torsion g y.2⟩ :
          Pic0.torsion K F n) := by
    refine Subtype.ext ?_
    rw [coe_classRight_semilinearSmul, hy]
  rw [hL, hR, semilinearSmul_pairing] at h1
  rw [h1, ← e.compatible d, hx, hy]

end Equivariance

section Compat

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def smulDatum {n m : ℕ} (d : WeilDatum K F (n * m)) : WeilDatum K F n where
  D₁ := (m : ℤ) • d.D₁
  D₂ := (m : ℤ) • d.D₂
  f₁ := d.f₁
  f₂ := d.f₂
  f₁_ne_zero := d.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ := fun v => by
    rw [d.ord_f₁ v, Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  ord_f₂ := fun v => by
    rw [d.ord_f₂ v, Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  disjoint := fun v => (d.disjoint v).imp
    (fun h => by rw [Finsupp.smul_apply, h, smul_zero])
    (fun h => by rw [Finsupp.smul_apply, h, smul_zero])
  rational := fun v hv => d.rational v (hv.imp
    (fun h hc => h (by rw [Finsupp.smul_apply, hc, smul_zero]))
    (fun h hc => h (by rw [Finsupp.smul_apply, hc, smul_zero])))

private theorem smulDatum_pairing {n m : ℕ} (d : WeilDatum K F (n * m)) :
    (smulDatum (n := n) d).pairing = d.pairing ^ m := by
  show Divisor.evalFun d.f₁ ((m : ℤ) • d.D₂) / Divisor.evalFun d.f₂ ((m : ℤ) • d.D₁)
      = (Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁) ^ m
  rw [Divisor.evalFun_natCast_smul_divisor, Divisor.evalFun_natCast_smul_divisor, div_pow]

variable {n m : ℕ} [NeZero n] [NeZero (n * m)] [HasPrincipalDivisors K F]

private theorem coe_classLeft_smulDatum (d : WeilDatum K F (n * m)) :
    ((smulDatum (n := n) d).classLeft : Pic0 K F)
      = (m : ℤ) • (d.classLeft : Pic0 K F) := by
  rw [WeilDatum.coe_classLeft, WeilDatum.coe_classLeft]
  show QuotientAddGroup.mk _ = (m : ℤ) • (QuotientAddGroup.mk _)
  rw [← QuotientAddGroup.mk_zsmul]
  exact congrArg QuotientAddGroup.mk (Subtype.ext rfl)

private theorem coe_classRight_smulDatum (d : WeilDatum K F (n * m)) :
    ((smulDatum (n := n) d).classRight : Pic0 K F)
      = (m : ℤ) • (d.classRight : Pic0 K F) := by
  rw [WeilDatum.coe_classRight, WeilDatum.coe_classRight]
  show QuotientAddGroup.mk _ = (m : ℤ) • (QuotientAddGroup.mk _)
  rw [← QuotientAddGroup.mk_zsmul]
  exact congrArg QuotientAddGroup.mk (Subtype.ext rfl)

end Compat

section Corr

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem correspondence_mem_torsion {F' : Type*} [Field F'] [Algebra K F']
    [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F]
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ) {n : ℕ} {x : Pic0 K F}
    (hx : (n : ℤ) • x = 0) :
    (n : ℤ) • Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x = 0 := by
  rw [← map_zsmul, hx, map_zero]

end Corr

end AlgebraicCurve.WC7E

open AlgebraicCurve.WC7E in
theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] :
    ∃ e : ℕ → Pic0 K F → Pic0 K F → K,
      (∀ (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n x y ^ n = 1) ∧
      (∀ (n : ℕ) (x x' y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • x' = 0 → (n : ℤ) • y = 0 →
        e n (x + x') y = e n x y * e n x' y) ∧
      (∀ (n : ℕ) (x y y' : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → (n : ℤ) • y' = 0 →
        e n x (y + y') = e n x y * e n x y') ∧
      (∀ (n : ℕ) (x : Pic0 K F), 0 < n → (n : ℤ) • x = 0 →
        (∀ y : Pic0 K F, (n : ℤ) • y = 0 → e n x y = 1) → x = 0) ∧
      (∀ (n : ℕ) (y : Pic0 K F), 0 < n → (n : ℤ) • y = 0 →
        (∀ x : Pic0 K F, (n : ℤ) • x = 0 → e n x y = 1) → y = 0) ∧
      (∀ (n m : ℕ) (x y : Pic0 K F), 0 < n → 0 < m →
        ((n * m : ℕ) : ℤ) • x = 0 → ((n * m : ℕ) : ℤ) • y = 0 →
        e n ((m : ℤ) • x) ((m : ℤ) • y) = e (n * m) x y ^ m) ∧
      (∀ (n : ℕ) (g : SemilinearAut K F) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (g • x) (g • y) = SemilinearAut.baseAut g (e n x y)) ∧
      (∀ (F' : Type*) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
        (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
        (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
        (hNψ : NormFormulaAlong K ψ hfinψ)
        (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
        (hNφ : NormFormulaAlong K φ hfinφ)
        (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x) y
          = e n x (Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y)) := by
  classical

  obtain ⟨j, hjtr, hjfd⟩ := hfg
  haveI : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F := hjfd

  obtain ⟨φ, hφX⟩ :=
    FunctionField.exists_ratFuncAlgHom_apply_X_eq (transcendental_not_mem_range hjtr)
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI : FiniteDimensional (RatFunc K) F := finite_ratFunc_of_adjoin φ hφX hjfd
  have hrec : WeilReciprocity K F := weilReciprocity K F

  have hne : ∀ (n : ℕ) [NeZero n], Nonempty (DivisorialWeilPairingData K F n) :=
    fun n _ => Pic0.nonempty_divisorialWeilPairingData K F ⟨j, hjtr, hjfd⟩ n

  refine ⟨fun n x y =>
    if h : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • y = 0 then
      haveI : NeZero n := ⟨h.1.ne'⟩
      ((hne n).some).pair ⟨x, Pic0.mem_torsion.mpr h.2.1⟩
        ⟨y, Pic0.mem_torsion.mpr h.2.2⟩
    else 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro n x y hn hx hy
    haveI : NeZero n := ⟨hn.ne'⟩
    have hc : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • y = 0 := ⟨hn, hx, hy⟩
    simp only [dif_pos hc]
    exact DivisorialWeilPairingData.pair_pow_eq_one _ hrec _ _

  · intro n x x' y hn hx hx' hy
    haveI : NeZero n := ⟨hn.ne'⟩
    have hxx' : (n : ℤ) • (x + x') = 0 := by rw [zsmul_add, hx, hx', add_zero]
    have hc1 : 0 < n ∧ (n : ℤ) • (x + x') = 0 ∧ (n : ℤ) • y = 0 := ⟨hn, hxx', hy⟩
    have hc2 : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • y = 0 := ⟨hn, hx, hy⟩
    have hc3 : 0 < n ∧ (n : ℤ) • x' = 0 ∧ (n : ℤ) • y = 0 := ⟨hn, hx', hy⟩
    simp only [dif_pos hc1, dif_pos hc2, dif_pos hc3]
    have h := ((hne n).some).pair_add_left
      ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨x', Pic0.mem_torsion.mpr hx'⟩
      ⟨y, Pic0.mem_torsion.mpr hy⟩
    exact h

  · intro n x y y' hn hx hy hy'
    haveI : NeZero n := ⟨hn.ne'⟩
    have hyy' : (n : ℤ) • (y + y') = 0 := by rw [zsmul_add, hy, hy', add_zero]
    have hc1 : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • (y + y') = 0 := ⟨hn, hx, hyy'⟩
    have hc2 : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • y = 0 := ⟨hn, hx, hy⟩
    have hc3 : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • y' = 0 := ⟨hn, hx, hy'⟩
    simp only [dif_pos hc1, dif_pos hc2, dif_pos hc3]
    have h := ((hne n).some).pair_add_right
      ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩
      ⟨y', Pic0.mem_torsion.mpr hy'⟩
    exact h

  · intro n x hn hx hall
    haveI : NeZero n := ⟨hn.ne'⟩
    set e0 := (hne n).some with he0
    have hdiv : ∀ (L' : Type _) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
        [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
        ∀ m : ℤ, m ≠ 0 → ∀ z : Pic0 K L', ∃ w, m • w = z :=
      fun L' _ _ _ _ _ => hdiv_engine L'
    have hinj : Function.Injective e0.toHom :=
      DivisorialWeilPairingData.toHom_injective_of_divisible hdiv e0
    have h0 : e0.toHom ⟨x, Pic0.mem_torsion.mpr hx⟩ = e0.toHom 0 := by
      rw [map_zero]
      show Additive.ofMul (e0.toChar ⟨x, Pic0.mem_torsion.mpr hx⟩) = 0
      rw [ofMul_eq_zero]
      apply AddChar.ext
      intro y'
      have h1 : e0.pair ⟨x, Pic0.mem_torsion.mpr hx⟩ y' = 1 := by
        have hcy : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • (y' : Pic0 K F) = 0 :=
          ⟨hn, hx, Pic0.mem_torsion.mp y'.2⟩
        have h2 := hall (y' : Pic0 K F) (Pic0.mem_torsion.mp y'.2)
        simp only [dif_pos hcy] at h2
        exact h2
      rw [AddChar.one_apply]
      exact h1
    have h3 := hinj h0
    have h4 : x = ((0 : Pic0.torsion K F n) : Pic0 K F) := congrArg Subtype.val h3
    simpa using h4

  · intro n y hn hy hall
    haveI : NeZero n := ⟨hn.ne'⟩
    set e0 := (hne n).some with he0
    have hdiv : ∀ (L' : Type _) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
        [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
        ∀ m : ℤ, m ≠ 0 → ∀ z : Pic0 K L', ∃ w, m • w = z :=
      fun L' _ _ _ _ _ => hdiv_engine L'
    have hinj : Function.Injective e0.toHom :=
      DivisorialWeilPairingData.toHom_injective_of_divisible hdiv e0
    have h0 : e0.toHom ⟨y, Pic0.mem_torsion.mpr hy⟩ = e0.toHom 0 := by
      rw [map_zero]
      show Additive.ofMul (e0.toChar ⟨y, Pic0.mem_torsion.mpr hy⟩) = 0
      rw [ofMul_eq_zero]
      apply AddChar.ext
      intro x'
      have h1 : e0.pair ⟨y, Pic0.mem_torsion.mpr hy⟩ x' = 1 := by
        have hswap := e0.pair_swap_eq_inv x' ⟨y, Pic0.mem_torsion.mpr hy⟩
        have hcx : 0 < n ∧ (n : ℤ) • (x' : Pic0 K F) = 0 ∧ (n : ℤ) • y = 0 :=
          ⟨hn, Pic0.mem_torsion.mp x'.2, hy⟩
        have h2 := hall (x' : Pic0 K F) (Pic0.mem_torsion.mp x'.2)
        simp only [dif_pos hcx] at h2
        have h2' : e0.pair x' ⟨y, Pic0.mem_torsion.mpr hy⟩ = 1 := h2
        rw [hswap, h2', inv_one]
      rw [AddChar.one_apply]
      exact h1
    have h3 := hinj h0
    have h4 : y = ((0 : Pic0.torsion K F n) : Pic0 K F) := congrArg Subtype.val h3
    simpa using h4

  · intro n m x y hn hm hx hy
    haveI : NeZero n := ⟨hn.ne'⟩
    haveI : NeZero (n * m) := ⟨(Nat.mul_pos hn hm).ne'⟩
    have hnm : 0 < n * m := Nat.mul_pos hn hm
    have hmx : (n : ℤ) • ((m : ℤ) • x) = 0 := by
      rw [← mul_zsmul, ← Int.natCast_mul, hx]
    have hmy : (n : ℤ) • ((m : ℤ) • y) = 0 := by
      rw [← mul_zsmul, ← Int.natCast_mul, hy]
    have hcL : 0 < n ∧ (n : ℤ) • ((m : ℤ) • x) = 0 ∧ (n : ℤ) • ((m : ℤ) • y) = 0 :=
      ⟨hn, hmx, hmy⟩
    have hcR : 0 < n * m ∧ ((n * m : ℕ) : ℤ) • x = 0 ∧ ((n * m : ℕ) : ℤ) • y = 0 :=
      ⟨hnm, hx, hy⟩
    simp only [dif_pos hcL, dif_pos hcR]
    obtain ⟨d, hdL, hdR⟩ := ((hne (n * m)).some).exists_datum
      ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩
    have h1 : ((hne (n * m)).some).pair
        ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩ = d.pairing := by
      rw [← hdL, ← hdR]
      exact ((hne (n * m)).some).compatible d
    have h2 := ((hne n).some).compatible (smulDatum (n := n) d)
    have hL : (smulDatum (n := n) d).classLeft
        = (⟨(m : ℤ) • x, Pic0.mem_torsion.mpr hmx⟩ : Pic0.torsion K F n) := by
      refine Subtype.ext ?_
      rw [coe_classLeft_smulDatum, show (d.classLeft : Pic0 K F) = x from
        congrArg Subtype.val hdL]
    have hR : (smulDatum (n := n) d).classRight
        = (⟨(m : ℤ) • y, Pic0.mem_torsion.mpr hmy⟩ : Pic0.torsion K F n) := by
      refine Subtype.ext ?_
      rw [coe_classRight_smulDatum, show (d.classRight : Pic0 K F) = y from
        congrArg Subtype.val hdR]
    rw [hL, hR] at h2
    rw [h2, smulDatum_pairing, h1]

  · intro n g x y hn hx hy
    haveI : NeZero n := ⟨hn.ne'⟩
    have hgx : (n : ℤ) • (g • x) = 0 :=
      Pic0.mem_torsion.mp (SemilinearAut.smul_mem_torsion g (Pic0.mem_torsion.mpr hx))
    have hgy : (n : ℤ) • (g • y) = 0 :=
      Pic0.mem_torsion.mp (SemilinearAut.smul_mem_torsion g (Pic0.mem_torsion.mpr hy))
    have hcL : 0 < n ∧ (n : ℤ) • (g • x) = 0 ∧ (n : ℤ) • (g • y) = 0 := ⟨hn, hgx, hgy⟩
    have hcR : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • y = 0 := ⟨hn, hx, hy⟩
    simp only [dif_pos hcL, dif_pos hcR]
    have h := pair_semilinearSmul ((hne n).some) g
      ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩
    exact h

  · intro F' _ _ _ φ' ψ' hφ' hψ' hFIφ hfinψ hNψ hFIψ hfinφ hNφ n x y hn hx hy
    haveI : NeZero n := ⟨hn.ne'⟩
    have hcx : (n : ℤ) • Pic0.correspondence φ' ψ' hφ' hψ' hFIφ hfinψ hNψ x = 0 :=
      correspondence_mem_torsion φ' ψ' hφ' hψ' hFIφ hfinψ hNψ hx
    have hcy : (n : ℤ) • Pic0.correspondence ψ' φ' hψ' hφ' hFIψ hfinφ hNφ y = 0 :=
      correspondence_mem_torsion ψ' φ' hψ' hφ' hFIψ hfinφ hNφ hy
    have hcL : 0 < n ∧ (n : ℤ) • Pic0.correspondence φ' ψ' hφ' hψ' hFIφ hfinψ hNψ x = 0
        ∧ (n : ℤ) • y = 0 := ⟨hn, hcx, hy⟩
    have hcR : 0 < n ∧ (n : ℤ) • x = 0
        ∧ (n : ℤ) • Pic0.correspondence ψ' φ' hψ' hφ' hFIψ hfinφ hNφ y = 0 := ⟨hn, hx, hcy⟩
    simp only [dif_pos hcL, dif_pos hcR]
    have h := DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence
      φ' ψ' hφ' hψ' hFIφ hfinψ hNψ hFIψ hfinφ hNφ ((hne n).some) x y hx hy hcx hcy
    exact h

end

end S_AlgebraicCurve_Pic0_exists_weilPairing
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_weilPairing (solution)
