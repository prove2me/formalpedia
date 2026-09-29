-- Prove2me | solution 1 for AutomorphicForm.exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2febb621-87bd-5ece-95a8-27e0f25e839a

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_NumberField_StandardGlobalAddChar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self
import Mathlib.Analysis.Meromorphic.Order
import Theorems.Thm_AutomorphicForm_exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.formalBaseChange_b LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology
open AutomorphicForm.CuspidalConstituent
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS10P

variable {K : Type} [Field K] [NumberField K]

theorem modulus_pos (t : (AdeleRing (𝓞 K) K)ˣ) :
    0 < ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits t : ℝˣ) : ℝ) := by
  show 0 < ((distribHaarChar (AdeleRing (𝓞 K) K) t : ℝ≥0) : ℝ)
  exact NNReal.coe_pos.2 (distribHaarChar_pos)

end RS10P

theorem RS40S_rsRep_simple
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
    (hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet) ∧
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
        meromorphicOrderAt Λ 1 = -1 ∧
        (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
        ∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
                (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by
  obtain ⟨S, f, φ, w, e₁, e₂, a, σ₀, C, 𝓕, A, L, ζi, hS, -, -, -, -, -, -, -, -, -, ha, hσ₀, hC,
    hA, hAI, hA0, hJ, hJpos, hζ, hζne, hζpos, hL, hprod⟩ :=
    AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self K RS10P.modulus_pos c u d₁ d₂ T hc hd₁ hd hcov Θ R hR tys V hV hRV

  set J : ℂ → ℂ := fun s : ℂ => RankinSelberg.sPartIntegral K S
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂
    with hJdef
  set U : Set ℂ := {z : ℂ | a + 1 / 2 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hshift : ∀ z ∈ U, z - 1 / 2 ∈ {s : ℂ | a < s.re} := by
    intro z hz
    have hz' : a + 1 / 2 < z.re := hz
    show a < (z - 1 / 2).re
    have : (z - 1 / 2 : ℂ).re = z.re - 1 / 2 := by simp
    rw [this]; linarith
  have hmaps : Set.MapsTo (fun z : ℂ => z - 1 / 2) U {s : ℂ | a < s.re} := fun z hz => hshift z hz
  have hsub : AnalyticOnNhd ℂ (fun z : ℂ => z - 1 / 2) Set.univ :=
    (analyticOnNhd_id).sub analyticOnNhd_const

  set g : ℂ → ℂ := fun z => A (z - 1 / 2) with hg
  set k : ℂ → ℂ := fun z => C * J (z - 1 / 2) * ζi (z - 1 / 2) with hk
  set h : ℂ → ℂ := fun z => (z - 1) * k z with hh
  have hAsh : AnalyticOnNhd ℂ (fun z : ℂ => A (z - 1 / 2)) U := hA.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hJsh : AnalyticOnNhd ℂ (fun z : ℂ => J (z - 1 / 2)) U := hJ.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hζsh : AnalyticOnNhd ℂ (fun z : ℂ => ζi (z - 1 / 2)) U := hζ.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hgan : AnalyticOnNhd ℂ g U := hAsh
  have hkan : AnalyticOnNhd ℂ k U := fun z hz =>
    (analyticAt_const.mul (hJsh z hz)).mul (hζsh z hz)
  have hhan : AnalyticOnNhd ℂ h U := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).mul (hkan z hz))

  have hkreal : ∀ σ : ℝ, a + 1 / 2 < σ → k σ ≠ 0 := by
    intro σ hσ
    have h1 : a < σ - 1 / 2 := by linarith
    have e : ((σ - 1 / 2 : ℝ) : ℂ) = (σ : ℂ) - 1 / 2 := by push_cast; ring
    obtain ⟨-, hJre⟩ := hJpos (σ - 1 / 2) h1
    obtain ⟨-, hζre⟩ := hζpos (σ - 1 / 2) h1
    rw [e] at hJre hζre
    have hJne : J ((σ : ℂ) - 1 / 2) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [Complex.zero_re] at this
      exact hJre.ne' this
    have hζne' : ζi ((σ : ℂ) - 1 / 2) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [Complex.zero_re] at this
      exact hζre.ne' this
    simp only [hk]
    exact mul_ne_zero (mul_ne_zero hC hJne) hζne'

  set M : ℂ → ℂ := fun z => g z / h z with hM
  have hMmero : MeromorphicOn M U := fun z hz => ((hgan z hz).meromorphicAt).div ((hhan z hz).meromorphicAt)
  set Λ : ℂ → ℂ := toMeromorphicNFOn M U with hΛ
  have hΛNF : MeromorphicNFOn Λ U := meromorphicNFOn_toMeromorphicNFOn M U
  have hΛmero : MeromorphicOn Λ U := hΛNF.meromorphicOn
  have hΛM : ∀ z ∈ U, Λ =ᶠ[𝓝[≠] z] M := fun z hz =>
    (hMmero.toMeromorphicNFOn_eq_self_on_nhdsNE hz)

  have hone : (1 : ℂ) ∈ U := by
    show a + 1 / 2 < (1 : ℂ).re
    simp only [Complex.one_re]; linarith
  have htwo : (2 : ℂ) ∈ U := by
    show a + 1 / 2 < (2 : ℂ).re
    norm_num; linarith
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt (a + 1 / 2)).isPreconnected
  have hk1 : k 1 ≠ 0 := by
    have := hkreal 1 (by linarith)
    simpa using this
  have hh2 : h 2 ≠ 0 := by
    have hk2 := hkreal 2 (by linarith)
    have : h 2 = (2 - 1) * k ((2 : ℝ) : ℂ) := by simp [hh]
    rw [this]
    exact mul_ne_zero (by norm_num) hk2

  have hh_ne : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, h w ≠ 0 := by
    intro z hz
    rcases (hhan z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      have hzero := hhan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hz h0
      exact hh2 (hzero htwo)
    · exact hne

  have hMeq : M = g * h⁻¹ := by
    funext z; simp [hM, div_eq_mul_inv]
  have hordM : ∀ z ∈ U, meromorphicOrderAt M z = meromorphicOrderAt g z - meromorphicOrderAt h z := by
    intro z hz
    rw [hMeq, meromorphicOrderAt_mul (hgan z hz).meromorphicAt (hhan z hz).meromorphicAt.inv,
      meromorphicOrderAt_inv, sub_eq_add_neg]
  have hordΛ : ∀ z ∈ U, meromorphicOrderAt Λ z = meromorphicOrderAt M z := fun z hz =>
    meromorphicOrderAt_congr (hΛM z hz)

  have ord0 : ∀ {F : ℂ → ℂ} {z : ℂ}, AnalyticAt ℂ F z → F z ≠ 0 → meromorphicOrderAt F z = 0 := by
    intro F z hF hFz
    rw [hF.meromorphicOrderAt_eq, hF.analyticOrderAt_eq_zero.mpr hFz]
    rfl

  have hg1 : g 1 ≠ 0 := by
    have : g 1 = A (1 / 2) := by simp [hg]; norm_num
    rw [this]
    exact hA0
  have hl1 : ∀ z : ℂ, AnalyticAt ℂ (fun z : ℂ => z - 1) z := fun z => by
    exact ((analyticAt_id (𝕜 := ℂ) (z := z)).sub (analyticAt_const (v := (1 : ℂ))))
  have hordh1 : meromorphicOrderAt h 1 = 1 := by
    have hlin : meromorphicOrderAt (fun z : ℂ => z - 1) 1 = (1 : ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff (hl1 1).meromorphicAt]
      exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun z => by simp⟩
    show meromorphicOrderAt ((fun z : ℂ => z - 1) * k) 1 = 1
    rw [meromorphicOrderAt_mul (hl1 1).meromorphicAt (hkan 1 hone).meromorphicAt,
      hlin, ord0 (hkan 1 hone) hk1, add_zero]
    rfl
  have hord : meromorphicOrderAt Λ 1 = -1 := by
    rw [hordΛ 1 hone, hordM 1 hone, ord0 (hgan 1 hone) hg1, hordh1]
    decide

  have han : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ) := by
    intro σ hσ
    have hσU : (σ : ℂ) ∈ U := by
      show a + 1 / 2 < (σ : ℂ).re
      simp; linarith
    have hhσ : h σ ≠ 0 := by
      have hkσ := hkreal σ (by linarith)
      show ((σ : ℂ) - 1) * k σ ≠ 0
      refine mul_ne_zero ?_ hkσ
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith

    have hordσ : 0 ≤ meromorphicOrderAt Λ σ := by
      rw [hordΛ σ hσU, hordM σ hσU, ord0 (hhan σ hσU) hhσ, sub_zero]
      exact (hgan σ hσU).meromorphicOrderAt_nonneg
    exact ((hΛNF hσU).meromorphicOrderAt_nonneg_iff_analyticAt).mp hordσ

  have hprodΛ : ∀ z : ℂ, σ₀ + 1 / 2 < z.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
            (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) (Λ z) := by
    intro z hz
    have hzU : z ∈ U := by
      show a + 1 / 2 < z.re
      linarith

    have hV : ∀ᶠ w in 𝓝 z, σ₀ + 1 / 2 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    have key : ∀ w : ℂ, σ₀ + 1 / 2 < w.re → h w ≠ 0 → M w = L (w - 1 / 2) := by
      intro w hw hhw
      have hws : σ₀ < (w - 1 / 2).re := by
        have : (w - 1 / 2 : ℂ).re = w.re - 1 / 2 := by simp
        rw [this]; linarith
      have hws' : 1 / 2 < (w - 1 / 2).re := lt_trans hσ₀ hws
      obtain ⟨-, hI⟩ := hprod (w - 1 / 2) hws
      have hAw := hAI (w - 1 / 2) hws'
      have hgw : g w = h w * L (w - 1 / 2) := by
        show A (w - 1 / 2) = (w - 1) * (C * J (w - 1 / 2) * ζi (w - 1 / 2)) * L (w - 1 / 2)
        rw [hAw, hI]
        simp only [hJdef]
        ring
      show g w / h w = L (w - 1 / 2)
      rw [hgw, mul_div_cancel_left₀ _ hhw]
    have hMG : M =ᶠ[𝓝[≠] z] fun w => L (w - 1 / 2) := by
      filter_upwards [hh_ne z hzU, hV.filter_mono nhdsWithin_le_nhds] with w h1 h2
      exact key w h2 h1
    have hGan : AnalyticAt ℂ (fun w => L (w - 1 / 2)) z := by
      refine (hL _ ?_).comp (hsub z trivial)
      show σ₀ < (z - 1 / 2).re
      have : (z - 1 / 2 : ℂ).re = z.re - 1 / 2 := by simp
      rw [this]; linarith
    have hΛG : Λ =ᶠ[𝓝[≠] z] fun w => L (w - 1 / 2) := (hΛM z hzU).trans hMG
    have hΛz : Λ z = L (z - 1 / 2) :=
      (((hΛNF hzU).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hGan.meromorphicNFAt).mp hΛG).eq_of_nhds
    obtain ⟨hP, -⟩ := hprod (z - 1 / 2) (by
      have : (z - 1 / 2 : ℂ).re = z.re - 1 / 2 := by simp
      rw [this]; linarith)
    simp only [sub_add_cancel] at hP
    rw [hΛz]
    exact hP
  refine ⟨S, hS, σ₀ + 1 / 2, Λ, ⟨a + 1 / 2, by linarith, hΛmero⟩, hord, han, hprodΛ⟩

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS10B

open Polynomial

theorem eval_rsEulerPoly_self_inv_mul (a b N : ℂ) (hb : b ≠ 0) (hN : N ≠ 0) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (a / b) b⁻¹ a b 0).eval N⁻¹ * (b * N ^ 4) =
      (N - 1) ^ 2 * (b * N ^ 2 - (a ^ 2 - 2 * b) * N + b) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp
  ring

theorem eval_rsEulerPoly_self_inv_ne_zero (a b N : ℂ) (hN : N ≠ 0) (hN1 : N ≠ 1)
    (hgen : a ^ 2 ≠ b * (N + 2 + N⁻¹)) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (a / b) b⁻¹ a b 0).eval N⁻¹ ≠ 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [LanglandsTunnell.RankinSelberg.rsEulerPoly]
  intro h
  have key := eval_rsEulerPoly_self_inv_mul a b N hb hN
  rw [h, zero_mul] at key
  have h2 : (N - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hN1)
  have h3 : b * N ^ 2 - (a ^ 2 - 2 * b) * N + b = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact absurd h h2
    · exact h
  apply hgen
  field_simp
  linear_combination -h3

theorem pole0_of_rsrep_gen
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        (LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval
          ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹) ≠ 0 := by
  obtain ⟨ξ, S₀, tys, V, φ, hV, hφV, hφ0, hiso, hφt⟩ :=
    AutomorphicForm.exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
  set R := hiso.toRealization hφ0 with hRdef
  have hR : IsGenuineCuspRealizationAt K _ Θ.toRawCentral R := hiso.continuous
  have hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K _ Θ.level ⊓ archCutSubmodule K tys :=
    ⟨⟨hφV, hiso.level_invariant⟩, hφt⟩
  obtain ⟨S, hgood, σ₀, Λ, hmero, hord, han, hprod⟩ :=
    RS40S_rsRep_simple K c u d₁ d₂ T hc hd₁ hd hcov Θ R hR tys V hV hRV
  refine ⟨S, σ₀, Λ, hmero, hord, han, hprod, fun v hv => ?_⟩
  obtain ⟨hlv, hex⟩ := hgood v hv
  have hgen := AutomorphicForm.SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet K c u d₁ d₂ T hc hd₁ hd hcov Θ R hR v hlv hex
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hN1 : Ideal.absNorm v.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  exact eval_rsEulerPoly_self_inv_ne_zero _ _ _ (Nat.cast_ne_zero.mpr hN0) (by exact_mod_cast hN1) hgen

end RS10B

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        (LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval
          ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹) ≠ 0 :=
  RS10B.pole0_of_rsrep_gen K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ

end
end
end S_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self (solution)
