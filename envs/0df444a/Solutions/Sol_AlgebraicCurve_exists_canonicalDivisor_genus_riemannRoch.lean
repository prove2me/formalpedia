-- Prove2me | solution 1 for AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e2011d77-f3c2-5c81-bee1-0250b3844577

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

universe u v

open IntermediateField Polynomial

namespace S18RR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_and_isSeparable_of_ratFuncAlgHom (t : F)
    (hfd : FiniteDimensional K⟮t⟯ F) (hsep : Algebra.IsSeparable K⟮t⟯ F)
    (φ : RatFunc K →ₐ[K] F) (hφ : φ RatFunc.X = t) :
    letI := φ.toRingHom.toAlgebra
    Module.Finite (RatFunc K) F ∧ Algebra.IsSeparable (RatFunc K) F := by
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let E : IntermediateField K F := φ.fieldRange
  have htE : t ∈ E := ⟨RatFunc.X, hφ⟩
  have hle : K⟮t⟯ ≤ E := adjoin_simple_le_iff.mpr htE
  letI : Algebra K⟮t⟯ E := (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower K⟮t⟯ E F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Module.Finite E F := Module.Finite.of_restrictScalars_finite K⟮t⟯ E F
  haveI : Algebra.IsSeparable E F := Algebra.isSeparable_tower_top_of_isSeparable K⟮t⟯ E F
  let e : RatFunc K ≃ₐ[K] E := AlgEquiv.ofInjectiveField φ
  have key : ∀ x : E, φ (e.symm x) = (x : F) := fun x => by
    have h2 : ((e (e.symm x) : E) : F) = φ (e.symm x) := AlgEquiv.ofInjective_apply _ _ _
    rw [e.apply_symm_apply] at h2
    exact h2.symm
  have he : (algebraMap (RatFunc K) F).comp (e.symm.toRingEquiv : E ≃+* RatFunc K).toRingHom
      = (RingEquiv.refl F).toRingHom.comp (algebraMap E F) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    exact key x
  refine ⟨?_, ?_⟩
  · exact Module.Finite.of_equiv_equiv (e.symm.toRingEquiv : E ≃+* RatFunc K) (RingEquiv.refl F) he
  · exact Algebra.IsSeparable.of_equiv_equiv (e.symm.toRingEquiv : E ≃+* RatFunc K) (RingEquiv.refl F) he

theorem essFiniteType_ratFunc (K : Type*) [Field K] : Algebra.EssFiniteType K (RatFunc K) := by
  haveI : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  exact Algebra.EssFiniteType.comp K K[X] (RatFunc K)

end S18RR

open AlgebraicCurve

theorem solution (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ (Kc : Divisor K F) (g : ℕ), ∀ D : Divisor K F,
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by
  classical
  obtain ⟨t, htr, hfd, hsep⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have ht : t ∉ Set.range (algebraMap K F) := by
    rintro ⟨k, rfl⟩
    exact htr (isAlgebraic_algebraMap k)
  obtain ⟨φ, hφ⟩ := AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq (K := K) (F := F) ht
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq (fun k => (φ.commutes k).symm)
  obtain ⟨hfin, hsepR⟩ := S18RR.finite_and_isSeparable_of_ratFuncAlgHom t hfd hsep φ hφ
  haveI : Module.Finite (RatFunc K) F := hfin
  haveI : Algebra.IsSeparable (RatFunc K) F := hsepR
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _
  haveI : AlgebraicCurve.IsCurveOver K (RatFunc K) := AlgebraicCurve.instIsCurveOverRatFunc K
  haveI : Algebra.EssFiniteType K (RatFunc K) := S18RR.essFiniteType_ratFunc K
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  haveI : ∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
  obtain ⟨ω, hω⟩ := exists_ne (0 : KaehlerDifferential K F)
  exact ⟨AlgebraicCurve.canonicalDivisorOf hω, AlgebraicCurve.genus K F, fun D => hRR hω D⟩

end S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
end P2MW
export P2MW.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch (solution)
