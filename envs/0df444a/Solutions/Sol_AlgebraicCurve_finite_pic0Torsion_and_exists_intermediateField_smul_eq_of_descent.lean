-- Prove2me | solution 1 for AlgebraicCurve.finite_pic0Torsion_and_exists_intermediateField_smul_eq_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1b35a226-14d0-505f-8c39-3a4611760439

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_of_isAlgClosed_of_charZero
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_intermediateField_finiteDimensional_forall_smul_eq_of_descent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finite_pic0Torsion_and_exists_intermediateField_smul_eq_of_descent
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_finite_pic0Torsion_and_exists_intermediateField_smul_eq_of_descent.AlgebraicCurve IntermediateField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degZero Pic Pic0 Pic0.mk Pic0.mk_surjective Pic0.torsion Pic0.mem_torsion SemilinearAut SemilinearAut.baseAut SemilinearAut.smul_single SemilinearAut.coe_degZeroSMulHom SemilinearAut.pic0_smul_mk IsCurveOver IsCurveOver.finrank_kaehler Pic0.finite_torsion_of_isAlgClosed_of_charZero exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one Place.exists_intermediateField_finiteDimensional_forall_smul_eq_of_descent"
namespace C3Tors
p2m_open "AlgebraicCurve"

theorem transcendental_of_isCurveOver (K F : Type) [Field K] [Field F] [Algebra K F] [CharZero K]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] : Algebra.Transcendental K F := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  have hs : Subsingleton Ω[F⁄K] := Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have h1 := IsCurveOver.finrank_kaehler (K := K) (F := F)
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

theorem exists_transcendental_finiteDimensional (K F : Type) [Field K] [Field F] [Algebra K F] [CharZero K]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F := by
  haveI := transcendental_of_isCurveOver K F
  obtain ⟨t, ht, hfd, -⟩ := AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
    (K := K) (F := F) (IsCurveOver.finrank_kaehler (K := K) (F := F))
  exact ⟨t, ht, hfd⟩

theorem finite_torsion (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (n : ℕ) (hn : 0 < n) : Finite (Pic0.torsion (AlgebraicClosure ℚ) Fbar n) := by
  have hf := AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero (AlgebraicClosure ℚ) Fbar
    (exists_transcendental_finiteDimensional (AlgebraicClosure ℚ) Fbar) n hn.ne'
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun c : Pic0 (AlgebraicClosure ℚ) Fbar => n • c = 0)
    (q := fun c => c ∈ Pic0.torsion (AlgebraicClosure ℚ) Fbar n) (fun c => by show n • c = 0 ↔ c ∈ Pic0.torsion (AlgebraicClosure ℚ) Fbar n; rw [Pic0.mem_torsion, natCast_zsmul]))

end AlgebraicCurve.C3Tors

theorem solution
    (F : Type) [Field F] [Algebra ℚ F] [IsCurveOver ℚ F] [Algebra.EssFiniteType ℚ F]
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (toBar : F →+* Fbar)
    (toBar_algebraMap : ∀ r : ℚ,
      toBar (algebraMap ℚ F r) = algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap ℚ (AlgebraicClosure ℚ) r))
    (closure_toBar : Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤)
    (linearIndependent_toBar : ∀ s : Finset F,
      LinearIndependent ℚ (fun x : s => (x : F)) →
        LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : F)))
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (baseAut_gal : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (gal_smul_toBar : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F), gal σ • toBar x = toBar x) :
    (∀ n : ℕ, 0 < n → Finite (Pic0.torsion (AlgebraicClosure ℚ) Fbar n)) ∧
    (∀ n : ℕ, 0 < n →
      ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) →
          ∀ c : Pic0 (AlgebraicClosure ℚ) Fbar, c ∈ Pic0.torsion (AlgebraicClosure ℚ) Fbar n → gal σ • c = c) := by
  classical
  refine ⟨fun n hn => AlgebraicCurve.C3Tors.finite_torsion Fbar n hn, fun n hn => ?_⟩
  haveI hfinT := AlgebraicCurve.C3Tors.finite_torsion Fbar n hn
  haveI : Fintype ↥(Pic0.torsion (AlgebraicClosure ℚ) Fbar n) := Fintype.ofFinite _

  have hPOS := fun P : Place (AlgebraicClosure ℚ) Fbar =>
    AlgebraicCurve.Place.exists_intermediateField_finiteDimensional_forall_smul_eq_of_descent F Fbar toBar toBar_algebraMap
      closure_toBar linearIndependent_toBar gal baseAut_gal gal_smul_toBar P
  choose LP hLPfin hLP using hPOS

  choose rep hrep using fun c : ↥(Pic0.torsion (AlgebraicClosure ℚ) Fbar n) => Pic0.mk_surjective (c : Pic0 (AlgebraicClosure ℚ) Fbar)
  let S : Finset (Place (AlgebraicClosure ℚ) Fbar) :=
    Finset.univ.biUnion fun c => ((rep c : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fbar))) : Divisor (AlgebraicClosure ℚ) Fbar).support
  refine ⟨⨆ P ∈ S, LP P, ?_, ?_⟩
  · haveI : ∀ P, FiniteDimensional ℚ ↥(LP P) := hLPfin
    exact IntermediateField.finiteDimensional_iSup_of_finset
  · intro σ hσ c hc
    have hfixP : ∀ P ∈ S, gal σ • P = P := fun P hP =>
      hLP P σ (fun y hy => hσ y ((le_iSup₂ (f := fun P (_ : P ∈ S) => LP P) P hP : LP P ≤ ⨆ P ∈ S, LP P) hy))
    obtain ⟨D, hD⟩ : ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fbar)), D = rep ⟨c, hc⟩ := ⟨_, rfl⟩
    have hsupp : ∀ P ∈ (D : Divisor (AlgebraicClosure ℚ) Fbar).support, gal σ • P = P := fun P hP =>
      hfixP P (Finset.mem_biUnion.mpr ⟨⟨c, hc⟩, Finset.mem_univ _, hD ▸ hP⟩)
    have hDfix : gal σ • (D : Divisor (AlgebraicClosure ℚ) Fbar) = (D : Divisor (AlgebraicClosure ℚ) Fbar) := by
      conv_lhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) Fbar)]
      rw [Finsupp.sum, Finset.smul_sum]
      conv_rhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) Fbar), Finsupp.sum]
      refine Finset.sum_congr rfl fun P hP => ?_
      rw [SemilinearAut.smul_single, hsupp P hP]
    have hc' : Pic0.mk (rep ⟨c, hc⟩) = c := hrep ⟨c, hc⟩
    rw [← hc', ← hD, SemilinearAut.pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [SemilinearAut.coe_degZeroSMulHom]; exact hDfix))

end S_AlgebraicCurve_finite_pic0Torsion_and_exists_intermediateField_smul_eq_of_descent
end P2MW
export P2MW.S_AlgebraicCurve_finite_pic0Torsion_and_exists_intermediateField_smul_eq_of_descent (solution)
