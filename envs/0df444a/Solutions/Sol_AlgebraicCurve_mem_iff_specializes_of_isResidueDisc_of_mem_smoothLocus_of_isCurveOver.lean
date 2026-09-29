-- Prove2me | solution 1 for AlgebraicCurve.mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4e1ae962-898f-5b9b-9f12-c2d8113eb220

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Theorems.Thm_AlgebraicCurve_exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper
import Theorems.Thm_AlgebraicCurve_RegularProlongation_subset_packageDisc_of_isResidueDisc
import Theorems.Thm_AlgebraicCurve_RegularProlongation_packageDisc_subset_of_isResidueDisc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 6400000 in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    [IsCurveOver (ResidueField ↥A) Fbar] [Algebra.EssFiniteType (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (Q : Place (ResidueField ↥A) Fbar)
    (hQ : ∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring)

    (D : Set (Place L F)) (z : F) (hD : R.IsResidueDisc Q D z) :
    ∀ P : Place L F, P ∈ D ↔
      ∀ f : F, f ∈ SemistableModel.localRing X φ x →
        f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1) := by
  classical

  obtain ⟨Q', φT, χ₀, Dx, hQ'rat, hQ'uniq, hAS, hφs, hφu, hφC, hχ₀C, hχ₀t, hchart, hres, hord, hDx, hsec, hval, hloc, hloc'⟩ :=
    AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper A hrk hA X toBase φ hφ
      x hx hxc hxs η hηx hne hη R hR

  have hQQ : Q = Q' := hQ'uniq Q (fun f => by
    obtain ⟨hRf, -⟩ := hres f
    exact ⟨hRf, hQ (f : F) hRf f.2⟩)
  subst hQQ

  have hpk := And.intro hAS (And.intro hφs (And.intro hφu (And.intro hφC (And.intro hχ₀C (And.intro hχ₀t (And.intro hchart
    (And.intro hres (And.intro hord (And.intro hDx (And.intro hsec (And.intro hval (And.intro hloc hloc'))))))))))))
  have hsub : D ⊆ Dx :=
    AlgebraicCurve.RegularProlongation.subset_packageDisc_of_isResidueDisc A hrk hA R Q D z hD _ φT χ₀ Dx hpk
  have hsup : Dx ⊆ D :=
    AlgebraicCurve.RegularProlongation.packageDisc_subset_of_isResidueDisc A hrk hA R Q D z hD _ φT χ₀ Dx hpk
  have hDeq : ∀ P, P ∈ D ↔ P ∈ Dx := fun P => ⟨fun h => hsub h, fun h => hsup h⟩

  have hrat : ∀ P : Place L F, P.IsRational := by
    intro P
    haveI : Module.Finite L P.ResidueField := IsCurveOver.finiteResidue P
    haveI : Algebra.IsIntegral L P.ResidueField := Algebra.IsIntegral.of_finite L P.ResidueField
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := P.ResidueField)).2

  have hker : ∀ f : ↥(SemistableModel.localRing X φ x), χ₀ f = 0 ↔ ¬ ∃ g ∈ SemistableModel.localRing X φ x, (f : F) * g = 1 := by

    let θ : ↑(X.presheaf.stalk x) →+* F := φ.symm.toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
    have hθmem : ∀ s, θ s ∈ SemistableModel.localRing X φ x := fun s => ⟨s, rfl⟩
    let θR : ↑(X.presheaf.stalk x) →+* ↥(SemistableModel.localRing X φ x) :=
      { toFun := fun s => ⟨θ s, hθmem s⟩
        map_one' := Subtype.ext (map_one θ)
        map_mul' := fun a b => Subtype.ext (map_mul θ a b)
        map_zero' := Subtype.ext (map_zero θ)
        map_add' := fun a b => Subtype.ext (map_add θ a b) }
    have hθRsurj : Function.Surjective θR := fun f => by
      obtain ⟨s, hs⟩ := f.2
      exact ⟨s, Subtype.ext hs⟩
    haveI : IsLocalRing ↥(SemistableModel.localRing X φ x) := IsLocalRing.of_surjective' θR hθRsurj
    have hχsurj : Function.Surjective χ₀ := fun k => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
      exact ⟨φT (Polynomial.C a), hχ₀C a⟩
    have hkermax : (RingHom.ker χ₀) = maximalIdeal ↥(SemistableModel.localRing X φ x) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ₀ hχsurj)
    intro f
    constructor
    · rintro h0 ⟨g, hg, hfg⟩
      have h1 : f * ⟨g, hg⟩ = 1 := Subtype.ext hfg
      have := congrArg χ₀ h1
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    · intro hn
      have hnu : ¬ IsUnit f := by
        rintro ⟨u, rfl⟩
        exact hn ⟨((u⁻¹ : (↥(SemistableModel.localRing X φ x))ˣ) : ↥(SemistableModel.localRing X φ x)), ((u⁻¹ : (↥(SemistableModel.localRing X φ x))ˣ) : ↥(SemistableModel.localRing X φ x)).2, by
          rw [← Subring.coe_mul, Units.mul_inv]; rfl⟩
      have : f ∈ maximalIdeal ↥(SemistableModel.localRing X φ x) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [← hkermax] at this
      exact this

  intro P
  rw [hDeq, hDx]
  constructor
  · rintro ⟨hPr, hreg, hval1⟩ f hf
    refine ⟨(hreg ⟨f, hf⟩).1, (hreg ⟨f, hf⟩).2, ?_⟩
    have e1 : (⟨P.evalAt f, (hreg ⟨f, hf⟩).2⟩ : ↥A) ∈ maximalIdeal ↥A ↔ A.valuation (P.evalAt f) < 1 :=
      A.valuation_lt_one_iff _
    have e2 := hval1 ⟨f, hf⟩
    have e3 := hker ⟨f, hf⟩
    have e4 : (⟨P.evalAt f, (hreg ⟨f, hf⟩).2⟩ : ↥A) ∈ maximalIdeal ↥A ↔ ¬ IsUnit (⟨P.evalAt f, (hreg ⟨f, hf⟩).2⟩ : ↥A) :=
      IsLocalRing.mem_maximalIdeal _
    constructor
    · intro hu
      by_contra hng
      exact (e4.mp (e1.mpr (e2.mpr (e3.mpr hng)))) hu
    · intro hg
      by_contra hnu
      exact (e3.mp (e2.mp (e1.mp (e4.mpr hnu)))) hg
  · intro h
    refine ⟨hrat P, fun f => ⟨(h f f.2).1, (h f f.2).2.1⟩, fun f => ?_⟩
    obtain ⟨hfA, hiff⟩ := (h f f.2).2
    have e1 : (⟨P.evalAt (f : F), hfA⟩ : ↥A) ∈ maximalIdeal ↥A ↔ A.valuation (P.evalAt (f : F)) < 1 :=
      A.valuation_lt_one_iff _
    have e4 : (⟨P.evalAt (f : F), hfA⟩ : ↥A) ∈ maximalIdeal ↥A ↔ ¬ IsUnit (⟨P.evalAt (f : F), hfA⟩ : ↥A) :=
      IsLocalRing.mem_maximalIdeal _
    exact e1.symm.trans (e4.trans ((not_congr hiff).trans (hker f).symm))

end S_AlgebraicCurve_mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver (solution)
