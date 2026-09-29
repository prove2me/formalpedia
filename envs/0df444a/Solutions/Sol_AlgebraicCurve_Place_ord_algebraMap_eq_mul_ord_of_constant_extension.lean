-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_algebraMap_eq_mul_ord_of_constant_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6c6c68dd-91eb-5bd3-b6f8-bb0b12550e47

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_algebraMap_eq_mul_ord_of_constant_extension
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {k K E F E' F' : Type*} [Field k] [Field K] [Field E] [Field F] [Field E'] [Field F']
    [Algebra k K] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K]

    [Algebra k E] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
    [Algebra K E'] [Algebra K F'] [Algebra E' F'] [IsScalarTower K E' F']

    [Algebra E E'] [Algebra F F'] [Algebra k E'] [Algebra k F']
    [IsScalarTower k K E'] [IsScalarTower k E E'] [IsScalarTower k K F'] [IsScalarTower k F F']
    (hsq : ∀ e : E, algebraMap F F' (algebraMap E F e) = algebraMap E' F' (algebraMap E E' e))
    (hgenE : Algebra.adjoin E (Set.range (algebraMap K E')) = ⊤)
    (hgenF : Algebra.adjoin F (Set.range (algebraMap K F')) = ⊤)

    (x : Place k F) (y : Place k E) (x' : Place K F') (y' : Place K E')
    (hx : x'.toValuationSubring.comap (algebraMap F F') = x.toValuationSubring)
    (hy : y'.toValuationSubring.comap (algebraMap E E') = y.toValuationSubring)
    (hx'y' : x'.toValuationSubring.comap (algebraMap E' F') = y'.toValuationSubring)

    (n : ℕ) (u : E) (hu : y.ord u = 1) (hn : x.ord (algebraMap E F u) = n) :
    ∀ f : E', x'.ord (algebraMap E' F' f) = n * y'.ord f := by
  classical

  have hF : ∀ g : F, x'.ord (algebraMap F F' g) = x.ord g :=
    AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top hgenF x x' hx
  have hE : ∀ e : E, y'.ord (algebraMap E E' e) = y.ord e :=
    AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top hgenE y y' hy

  set u' : E' := algebraMap E E' u with hu'
  have hu'1 : y'.ord u' = 1 := by rw [hu', hE, hu]
  have hu'n : x'.ord (algebraMap E' F' u') = n := by rw [hu', ← hsq, hF, hn]
  have hu'0 : u' ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hu'1; exact zero_ne_one hu'1

  have hmem : ∀ e : E', e ∈ y'.toValuationSubring → algebraMap E' F' e ∈ x'.toValuationSubring := by
    intro e he
    rw [← hx'y'] at he
    exact he

  let φ : y'.toValuationSubring →+* x'.toValuationSubring :=
    { toFun := fun e => ⟨algebraMap E' F' (e : E'), hmem _ e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hunit : ∀ w : y'.toValuationSubringˣ, x'.ord (algebraMap E' F' ((w : y'.toValuationSubring) : E')) = 0 := by
    intro w
    have := x'.ord_coe_unit (Units.map (φ : y'.toValuationSubring →* x'.toValuationSubring) w)
    exact this

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible y'.toValuationSubring
  have hπ0 : (π : E') ≠ 0 := by
    intro h; exact hπ.ne_zero (Subtype.ext h)
  have hπF0 : algebraMap E' F' (π : E') ≠ 0 := (map_ne_zero _).mpr hπ0
  obtain ⟨w₀, hw₀⟩ := y'.exists_unit_mul_zpow hu'0 hπ
  rw [hu'1, zpow_one] at hw₀

  have hπn : x'.ord (algebraMap E' F' (π : E')) = n := by
    have h1 : x'.ord (algebraMap E' F' u') =
        x'.ord (algebraMap E' F' ((w₀ : y'.toValuationSubring) : E')) + x'.ord (algebraMap E' F' (π : E')) := by
      rw [hw₀, map_mul]
      exact x'.ord_mul ((map_ne_zero _).mpr (by simp)) hπF0
    rw [hunit w₀, zero_add, hu'n] at h1
    exact h1.symm

  intro f
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨w, hw⟩ := y'.exists_unit_mul_zpow hf hπ
  have hwF0 : algebraMap E' F' ((w : y'.toValuationSubring) : E') ≠ 0 := (map_ne_zero _).mpr (by simp)
  calc x'.ord (algebraMap E' F' f)
      = x'.ord (algebraMap E' F' ((w : y'.toValuationSubring) : E') * (algebraMap E' F' (π : E')) ^ (y'.ord f)) := by
        conv_lhs => rw [hw]
        rw [map_mul, map_zpow₀]
    _ = x'.ord (algebraMap E' F' ((w : y'.toValuationSubring) : E')) + x'.ord ((algebraMap E' F' (π : E')) ^ (y'.ord f)) :=
        x'.ord_mul hwF0 (zpow_ne_zero _ hπF0)
    _ = (y'.ord f) * x'.ord (algebraMap E' F' (π : E')) := by rw [hunit w, zero_add, x'.ord_zpow]
    _ = n * y'.ord f := by rw [hπn, mul_comm]

end S_AlgebraicCurve_Place_ord_algebraMap_eq_mul_ord_of_constant_extension
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_algebraMap_eq_mul_ord_of_constant_extension (solution)
