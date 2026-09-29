-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/73364bd0-d770-5f5e-8c01-4db159dbe32e

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_KummerCover_finrank_eq
import Theorems.Thm_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve~genus P2MW.S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one.AlgebraicCurve IsLocalRing Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place genusFF KummerCover.finrank_eq genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord RegularProlongation.exists_prolongation_of_card_roots_eq RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "integers residue exists_prolongation_of_card_roots_eq sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one"
namespace W10C1
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve~genus"

section Residue

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem mem_of_isRoot_monic {P : A[X]} (hP : P.Monic) {x : L}
    (hx : (P.map (algebraMap A L)).IsRoot x) : x ∈ A := by
  have hint : IsIntegral A x := ⟨P, hP, by rwa [← eval_map, ← IsRoot.def]⟩
  have : IsIntegrallyClosed A := inferInstance
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).mp this hint
  rw [← hy]
  exact y.2

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
  obtain ⟨P, hPp, hPdeg, hPmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (mem_lifts_of_surjective hsurj p) hp
  have hdeg : (P.map (algebraMap A L)).degree ≠ 0 := by
    rw [hPmon.degree_map, hPdeg]
    exact fun h0 => hirr.not_isUnit (isUnit_iff_degree_eq_zero.mpr h0) |>.elim
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  have hxA : x ∈ A := mem_of_isRoot_monic hPmon hx
  refine ⟨IsLocalRing.residue A ⟨x, hxA⟩, ?_⟩
  have hPx : P.eval ⟨x, hxA⟩ = 0 := by
    have h1 : (P.map (algebraMap A L)).eval x = 0 := hx
    rw [eval_map] at h1
    have h2 : algebraMap A L (P.eval ⟨x, hxA⟩) = 0 := by
      rw [← eval₂_at_apply]; exact h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective A L)).mp h2
  rw [← hPp, eval_map, eval₂_at_apply, hPx, map_zero]

end Residue

theorem exists_isPrimitiveRoot_algebraMap {K E : Type*} [Field K] [IsAlgClosed K] [Field E]
    [Algebra K E] {q : ℕ} (hq : (q : K) ≠ 0) : ∃ ξ : E, IsPrimitiveRoot ξ q := by
  haveI : NeZero (q : K) := ⟨hq⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K q
  exact ⟨algebraMap K E ζ, hζ.map_of_injective (algebraMap K E).injective⟩

theorem exists_finset_roots {E : Type*} [Field E] {q : ℕ} {ξ : E}
    (hξ : IsPrimitiveRoot ξ q) {w : E} (hw : w ≠ 0) :
    ∃ S : Finset E, S.card = q ∧ ∀ s ∈ S, s ^ q = w ^ q := by
  classical
  refine ⟨(Finset.range q).image fun i => ξ ^ i * w, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hij' : ξ ^ i = ξ ^ j := mul_right_cancel₀ hw hij
    exact hξ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij'
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    rw [mul_pow, ← pow_mul, mul_comm i q, pow_mul, hξ.pow_eq_one, one_pow, one_mul]

theorem exists_transcendental_of_finiteDimensional {L F F' : Type*} [Field L] [Field F] [Field F']
    [Algebra L F] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F'] [FiniteDimensional F F']
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F) :
    ∃ y : F', Transcendental L y ∧
      FiniteDimensional (IntermediateField.adjoin L ({y} : Set F')) F' := by
  obtain ⟨x, hx, hfin⟩ := hF
  set φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F' with hφ
  refine ⟨φ x, (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx, ?_⟩
  set E : IntermediateField L F := IntermediateField.adjoin L ({x} : Set F) with hE
  set E' : IntermediateField L F' := IntermediateField.adjoin L ({φ x} : Set F') with hE'
  have hmap : E.map φ = E' := by
    rw [hE, IntermediateField.adjoin_map, Set.image_singleton]
  have hle : ∀ e : E, φ (e : F) ∈ E' := fun e => by
    rw [← hmap]
    exact ⟨e, e.2, rfl⟩
  let ψ : E →+* E' :=
    { toFun := fun e => ⟨φ e, hle e⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI : Algebra E E' := ψ.toAlgebra
  haveI : IsScalarTower E E' F' := IsScalarTower.of_algebraMap_eq (fun e => by
    rw [IsScalarTower.algebraMap_apply E F F' e]
    rfl)
  haveI : Module.Finite E F' := Module.Finite.trans F F'
  exact Module.Finite.of_restrictScalars_finite E E' F'

theorem finrank_adjoin_algebraMap_mul {L F F' : Type*} [Field L] [Field F] [Field F']
    [Algebra L F] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F'] (x : F) :
    Module.finrank (IntermediateField.adjoin L ({algebraMap F F' x} : Set F')) F' =
      Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F * Module.finrank F F' := by
  set φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F' with hφ
  set E : IntermediateField L F := IntermediateField.adjoin L ({x} : Set F) with hE
  set E' : IntermediateField L F' := IntermediateField.adjoin L ({algebraMap F F' x} : Set F')
    with hE'
  have hmap : E.map φ = E' := by
    rw [hE, IntermediateField.adjoin_map, Set.image_singleton]; rfl
  let e : E ≃ₐ[L] E' := (IntermediateField.equivMap E φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ y : E, ((e y : E') : F') = algebraMap F F' (y : F) := fun y => rfl
  have h1 : Module.finrank E F' = Module.finrank E' F' :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F')
      (RingHom.ext fun y => (he y).symm)
  rw [← h1, Module.finrank_mul_finrank]

theorem finiteDimensional_adjoin_algebraMap {L F F' : Type*} [Field L] [Field F] [Field F']
    [Algebra L F] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F'] [FiniteDimensional F F']
    (x : F) (h : 0 < Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F) :
    FiniteDimensional (IntermediateField.adjoin L ({algebraMap F F' x} : Set F')) F' := by
  apply Module.finite_of_finrank_pos
  rw [finrank_adjoin_algebraMap_mul]
  exact Nat.mul_pos h Module.finrank_pos

theorem transcendental_of_finrank_pos {L F : Type*} [Field L] [Field F] [Algebra L F]
    (hF : ∃ y : F, Transcendental L y ∧
      FiniteDimensional (IntermediateField.adjoin L ({y} : Set F)) F)
    (x : F) (h : 0 < Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F) :
    Transcendental L x := by
  intro hx
  obtain ⟨y, hy, -⟩ := hF
  haveI : FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F :=
    Module.finite_of_finrank_pos h
  haveI : FiniteDimensional L (IntermediateField.adjoin L ({x} : Set F)) :=
    IntermediateField.adjoin.finiteDimensional hx.isIntegral
  haveI : FiniteDimensional L F :=
    FiniteDimensional.trans L (IntermediateField.adjoin L ({x} : Set F)) F
  exact hy (Algebra.IsAlgebraic.isAlgebraic y)

theorem main {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (hreg : ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {q : ℕ} [hqp : Fact q.Prime] (hq : (q : IsLocalRing.ResidueField A) ≠ 0)
    (f : R.integers) (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F))
    (w : Fbar) (hw0 : w ≠ 0) (hw : w ^ q = R.residue f) :
    ∃ h : F, h ^ q = (f : F) := by
  classical
  have hq0 : q ≠ 0 := hqp.out.ne_zero
  have hqpos : 0 < q := hqp.out.pos
  by_contra hpow
  have hf' : ∀ h : F, h ^ q ≠ (f : F) := fun h hh => hpow ⟨h, hh⟩

  let F' := (X ^ q - C (f : F)).SplittingField

  obtain ⟨ξF, hξF⟩ := exists_isPrimitiveRoot_algebraMap (K := L) (E := F) (q := q)
    (Nat.cast_ne_zero.mpr hq0)
  have hζ : (primitiveRoots q F).Nonempty := ⟨ξF, (mem_primitiveRoots hqpos).mpr hξF⟩
  have hdeg : Module.finrank F F' = q := KummerCover.finrank_eq (L := F') hζ hf'
  haveI : FiniteDimensional F F' :=
    Polynomial.IsSplittingField.finiteDimensional F' (X ^ q - C (f : F))

  have hRH := genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord hF hf' hdvd F'

  haveI : IsAlgClosed (ResidueField A) := isAlgClosed_residueField (A := A)
  obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_algebraMap (K := ResidueField A) (E := Fbar) hq
  obtain ⟨S, hS, hSw⟩ := exists_finset_roots hξ hw0
  have hSf : ∀ s ∈ S, s ^ q = R.residue f := fun s hs => by rw [hSw s hs, hw]
  obtain ⟨R', hinj, hR'⟩ :=
    RegularProlongation.exists_prolongation_of_card_roots_eq A R f S hS hSf F' hdeg

  obtain ⟨x, hxk, hpos, hfinrk⟩ := hreg
  have hposL : 0 < Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F := by
    rw [hfinrk]; exact hpos
  have hxL : Transcendental L (x : F) := transcendental_of_finrank_pos hF (x : F) hposL
  have hxO : ∀ i, algebraMap F F' (x : F) ∈ (R' i).integers := fun i => by
    rw [← ValuationSubring.mem_comap, (hR' i).1]; exact x.2
  have hres : ∀ i, (R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩ = R.residue x := fun i =>
    (hR' i).2 ⟨algebraMap F F' (x : F), hxO i⟩ x rfl
  have htrL : Transcendental L (algebraMap F F' (x : F)) :=
    (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hxL
  have hfd : FiniteDimensional
      (IntermediateField.adjoin L ({algebraMap F F' (x : F)} : Set F')) F' :=
    finiteDimensional_adjoin_algebraMap (x : F) hposL
  have htr : ∀ i, Transcendental (ResidueField A)
      ((R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩) := fun i => by
    rw [hres i]; exact hxk
  have hfi : ∀ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({R.residue x} : Set Fbar)) Fbar := fun i => by rw [hres i]
  have heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R' i).residue ⟨algebraMap F F' (x : F), hxO i⟩} : Set Fbar)) Fbar
      = Module.finrank (IntermediateField.adjoin L ({algebraMap F F' (x : F)} : Set F')) F' := by
    rw [Finset.sum_congr rfl fun i _ => hfi i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, finrank_adjoin_algebraMap_mul, hdeg, hfinrk, mul_comm]
  have hsum := RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one A (fun _ : Fin q => Fbar) R'
    hinj (algebraMap F F' (x : F)) hxO htrL hfd htr heq
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hgood] at hsum

  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hqp.out.two_le
  have hsum' : (q : ℤ) * (genusFF L F : ℤ) ≤ (genusFF L F' : ℤ) := by exact_mod_cast hsum
  nlinarith [hsum', hRH, h2, (Int.natCast_nonneg (genusFF L F))]

end AlgebraicCurve.RegularProlongation.W10C1

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (hreg : ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {q : ℕ} [Fact q.Prime] (hq : (q : IsLocalRing.ResidueField A) ≠ 0)
    (f : R.integers) (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F))
    (w : Fbar) (hw0 : w ≠ 0) (hw : w ^ q = R.residue f) :
    ∃ h : F, h ^ q = (f : F) :=
  AlgebraicCurve.RegularProlongation.W10C1.main A hF R hgood hreg hq f hdvd w hw0 hw

end

end S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one (solution)
