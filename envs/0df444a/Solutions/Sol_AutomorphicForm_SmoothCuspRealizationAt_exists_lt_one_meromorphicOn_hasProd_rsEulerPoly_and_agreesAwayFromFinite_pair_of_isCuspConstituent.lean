-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_pair_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/58ea7ce2-e354-5931-87ca-3dc47eda66ff

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_agreesAwayFromFinite_of_projInvariant_sesqForm_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_pair_of_isCuspConstituent
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul"
p2m_attr_erase "simp" "M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open Deep.NTSupply
open Filter Topology
open scoped Classical NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace RS12M

variable {K : Type} [Field K] [NumberField K]

theorem modulus_pos (t : (AdeleRing (𝓞 K) K)ˣ) :
    0 < ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits t : ℝˣ) : ℝ) := by
  show 0 < ((distribHaarChar (AdeleRing (𝓞 K) K) t : ℝ≥0) : ℝ)
  exact NNReal.coe_pos.2 (distribHaarChar_pos)

theorem peterssonIntegral_swap (s : ℝ) (S : Set (AdelicGL2 (𝓞 K) K)) (x y : AdelicGL2 (𝓞 K) K → ℂ) :
    peterssonIntegral K s S y x = (starRingEnd ℂ) (peterssonIntegral K s S x y) := by
  simp only [peterssonIntegral]
  rw [← integral_conj]
  congr 1
  funext g
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

end RS12M

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (σ τ : HeckeEigensystem K ℂ)
    (Rσ : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.toRawCentral)
    (hRσ : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.toRawCentral Rσ)
    (Rτ : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.toRawCentral)
    (hRτ : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.toRawCentral Rτ)
    (tysσ : AutomorphicForm.ArchTypeFamily K)
    (Vσ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hVσ : IsCuspConstituent K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) Rσ.centralChar Vσ)
    (hRσV : Rσ.toFun ∈ Vσ ⊓ levelInvariantSubmodule K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) σ.level ⊓ archCutSubmodule K tysσ)
    (tysτ : AutomorphicForm.ArchTypeFamily K)
    (Vτ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hVτ : IsCuspConstituent K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) Rτ.centralChar Vτ)
    (hRτV : Rτ.toFun ∈ Vτ ⊓ levelInvariantSubmodule K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) τ.level ⊓ archCutSubmodule K tysτ)
    (hw : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S, ‖σ.b v‖ = ‖τ.b v‖) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ¬ v.asIdeal ∣ σ.level ∧ ¬ v.asIdeal ∣ τ.level ∧ v ∉ Rσ.exceptionalSet ∧ v ∉ Rτ.exceptionalSet) ∧
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
        (∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹
                (τ.a v.1) (τ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
        (meromorphicOrderAt Λ 1 < 0 → HeckeEigensystem.AgreesAwayFromFinite τ σ) := by
  obtain ⟨S, fx, fy, ν, φ, w, e₁, e₂, a, σ₀, s₀, C, 𝓕, A, L, ζi, hS, -, -, -, -, -, -, hωτ, -, -, -, -, -,
    he₁, he₁₂, h𝓕slab, h𝓕, ha, hσ₀, hC, hA, hAI, hdich1, hdich2, hJ, hJ0, hζ, hζne, hL, hprod⟩ :=
    AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
      K RS12M.modulus_pos c u d₁ d₂ T hc hd₁ hd hcov σ τ Rσ hRσ Rτ hRτ tysσ Vσ hVσ hRσV tysτ Vτ hVτ hRτV hw
  set J : ℂ → ℂ := fun s : ℂ => RankinSelberg.sPartIntegral K S
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ s) w e₁ e₂
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
  set lin : ℂ → ℂ := fun z => z - 1 / 2 - s₀ with hlin
  set h : ℂ → ℂ := fun z => lin z * k z with hh
  have hAsh : AnalyticOnNhd ℂ (fun z : ℂ => A (z - 1 / 2)) U := hA.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hJsh : AnalyticOnNhd ℂ (fun z : ℂ => J (z - 1 / 2)) U := hJ.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hζsh : AnalyticOnNhd ℂ (fun z : ℂ => ζi (z - 1 / 2)) U := hζ.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hgan : AnalyticOnNhd ℂ g U := hAsh
  have hkan : AnalyticOnNhd ℂ k U := fun z hz =>
    (analyticAt_const.mul (hJsh z hz)).mul (hζsh z hz)
  have hlinan : ∀ z : ℂ, AnalyticAt ℂ lin z := fun z => by
    have h__af := (((analyticAt_id (𝕜 := ℂ) (z := z)).sub (analyticAt_const (v := (1 / 2 : ℂ)))).sub
      (analyticAt_const (v := s₀)))
    simp [hlin] at h__af ⊢
    exact h__af
  have hhan : AnalyticOnNhd ℂ h U := fun z hz => (hlinan z).mul (hkan z hz)

  have hone : (1 : ℂ) ∈ U := by
    show a + 1 / 2 < (1 : ℂ).re
    simp only [Complex.one_re]; linarith
  have hhalf : a < (1 - 1 / 2 : ℂ).re := by
    have : (1 - 1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [this]; linarith
  have hk1 : k 1 ≠ 0 := by
    have hJ1 : J (1 - 1 / 2) ≠ 0 := by
      have : (1 - 1 / 2 : ℂ) = 1 / 2 := by norm_num
      rw [this]; simpa [hJdef] using hJ0
    have hζ1 : ζi (1 - 1 / 2) ≠ 0 := (hζne _ hhalf).1
    simp only [hk]
    exact mul_ne_zero (mul_ne_zero hC hJ1) hζ1
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt (a + 1 / 2)).isPreconnected

  have hh_ne1 : ∀ᶠ w in 𝓝[≠] (1 : ℂ), h w ≠ 0 := by
    have hk_ne : ∀ᶠ w in 𝓝 (1 : ℂ), k w ≠ 0 :=
      (hkan 1 hone).continuousAt.eventually_ne hk1

    rcases (hlinan 1).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso

      have h2 : ∀ᶠ w in 𝓝 (1 : ℂ), lin w = 0 := h0
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h2
      have hA1 : lin 1 = 0 := hball (by simpa using hε)
      have hB : lin (1 + ε / 2) = 0 := hball (by
        simp [dist_eq_norm, abs_of_pos hε]; linarith)
      have : (ε / 2 : ℂ) = 0 := by
        have := congrArg₂ (· - ·) hB hA1
        simpa [hlin] using this
      have : (ε : ℝ) / 2 = 0 := by exact_mod_cast this
      linarith
    · filter_upwards [hne, hk_ne.filter_mono nhdsWithin_le_nhds] with w h1 h2
      exact mul_ne_zero h1 h2
  have hh_ne : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, h w ≠ 0 := by
    intro z hz
    rcases (hhan z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      have hzero := hhan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hz h0

      have : ∀ᶠ w in 𝓝[≠] (1 : ℂ), False := by
        have hUn : ∀ᶠ w in 𝓝[≠] (1 : ℂ), w ∈ U := nhdsWithin_le_nhds (hUopen.mem_nhds hone)
        filter_upwards [hh_ne1, hUn] with w h1 h2
        exact h1 (hzero h2)
      exact (this.exists).elim fun _ hf => hf
    · exact hne

  set M : ℂ → ℂ := fun z => g z / h z with hM
  have hMmero : MeromorphicOn M U := fun z hz => ((hgan z hz).meromorphicAt).div ((hhan z hz).meromorphicAt)
  set Λ : ℂ → ℂ := toMeromorphicNFOn M U with hΛ
  have hΛNF : MeromorphicNFOn Λ U := meromorphicNFOn_toMeromorphicNFOn M U
  have hΛmero : MeromorphicOn Λ U := hΛNF.meromorphicOn
  have hΛM : ∀ z ∈ U, Λ =ᶠ[𝓝[≠] z] M := fun z hz =>
    (hMmero.toMeromorphicNFOn_eq_self_on_nhdsNE hz)
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

  have hprodΛ : ∀ z : ℂ, σ₀ + 1 / 2 < z.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹
            (τ.a v.1) (τ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) (Λ z) := by
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
        show A (w - 1 / 2) = (w - 1 / 2 - s₀) * (C * J (w - 1 / 2) * ζi (w - 1 / 2)) * L (w - 1 / 2)
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

  have himp : meromorphicOrderAt Λ 1 < 0 → HeckeEigensystem.AgreesAwayFromFinite τ σ := by
    intro hpole
    rw [hordΛ 1 hone, hordM 1 hone] at hpole
    have hordh : meromorphicOrderAt h 1 = meromorphicOrderAt lin 1 + meromorphicOrderAt k 1 := by
      show meromorphicOrderAt (fun z => lin z * k z) 1 = _
      exact meromorphicOrderAt_mul (hlinan 1).meromorphicAt (hkan 1 hone).meromorphicAt
    rw [hordh, ord0 (hkan 1 hone) hk1, add_zero] at hpole

    by_cases hν : ν = 1
    · obtain ⟨hs₀, hχ, hres⟩ := hdich2 hν

      have hlin1 : meromorphicOrderAt lin 1 = (1 : ℤ) := by
        rw [meromorphicOrderAt_eq_int_iff (hlinan 1).meromorphicAt]
        refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun z => ?_⟩
        simp [hlin, hs₀]
        ring
      rw [hlin1] at hpole
      have hg1 : g 1 ≠ 0 := by
        by_contra h0

        have hge : (1 : WithTop ℤ) ≤ meromorphicOrderAt g 1 := by
          rw [(hgan 1 hone).meromorphicOrderAt_eq]
          have h1 : (1 : ℕ∞) ≤ analyticOrderAt g 1 := by
            rw [ENat.one_le_iff_ne_zero]
            intro hz
            exact ((hgan 1 hone).analyticOrderAt_eq_zero.mp hz) h0

          cases hn : analyticOrderAt g 1 with
          | top => simp
          | coe n =>
            rw [hn] at h1
            have : (1 : ℕ) ≤ n := by exact_mod_cast h1
            show (1 : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ)
            exact_mod_cast this

        revert hpole hge
        cases meromorphicOrderAt g 1 with
        | top => intro h _; exact absurd h (by decide)
        | coe m =>
          intro h hge
          have h' : (m : ℤ) - 1 < 0 := by exact_mod_cast h
          have hge' : (1 : ℤ) ≤ m := by exact_mod_cast hge
          omega
      have hA0 : A (1 / 2) ≠ 0 := by
        have : g 1 = A (1 / 2) := by simp [hg]; norm_num
        rwa [this] at hg1
      obtain ⟨g₁, g₂, hP0⟩ := hres hA0

      obtain ⟨-, -, htail⟩ :=
        AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
          K c u d₁ d₂ T hd hcov σ τ Rσ Rτ hRτ w hωτ e₁ e₂ he₁ he₁₂ 𝓕 h𝓕slab h𝓕
      obtain ⟨hcov', P, hPcov, hPself, hPeq⟩ := htail hχ.symm

      have memτ : ∀ g₀ : AdelicGL2 (𝓞 K) K, (fun z => Rτ.toFun (z * g₀)) ∈
          Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rτ.toFun (z * hh)) :=
        fun g₀ => Submodule.subset_span ⟨g₀, rfl⟩
      have memσ : Rσ.toFun ∈
          Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rσ.toFun (z * hh)) ⊔
            Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rτ.toFun (z * hh)) := by
        refine Submodule.mem_sup_left (Submodule.subset_span ⟨1, ?_⟩)
        funext z; simp
      have memσ' : ∀ g₀ : AdelicGL2 (𝓞 K) K, (fun z => Rσ.toFun (z * g₀)) ∈
          Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rσ.toFun (z * hh)) ⊔
            Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rτ.toFun (z * hh)) :=
        fun g₀ => Submodule.mem_sup_left (Submodule.subset_span ⟨g₀, rfl⟩)

      have hP1 : peterssonIntegral K w 𝓕 (fun z => Rσ.toFun (z * g₂)) (fun z => Rτ.toFun (z * g₁)) ≠ 0 := by
        rw [RS12M.peterssonIntegral_swap]
        exact (map_ne_zero _).mpr hP0

      have hcov2 := hcov' g₂⁻¹ (fun z => Rσ.toFun (z * g₂)) (fun z => Rτ.toFun (z * g₁)) (memσ' g₂) (memτ g₁)
      have hx : (fun z => (fun z => Rσ.toFun (z * g₂)) (z * g₂⁻¹)) = Rσ.toFun := by
        funext z; simp [mul_assoc]
      have hy : (fun z => (fun z => Rτ.toFun (z * g₁)) (z * g₂⁻¹)) = fun z => Rτ.toFun (z * (g₂⁻¹ * g₁)) := by
        funext z; simp [mul_assoc]
      rw [hx, hy] at hcov2
      have hnorm : ((ideleNorm K (Matrix.GeneralLinearGroup.det g₂⁻¹) ^ w : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.rpow_pos_of_pos (ideleNorm_pos _) w).ne'
      have hP2 : peterssonIntegral K w 𝓕 Rσ.toFun (fun z => Rτ.toFun (z * (g₂⁻¹ * g₁))) ≠ 0 := by
        rw [hcov2]
        exact mul_ne_zero hnorm hP1
      have hcross : ∃ y ∈ Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rτ.toFun (z * hh)),
          P Rσ.toFun y ≠ 0 := by
        refine ⟨fun z => Rτ.toFun (z * (g₂⁻¹ * g₁)), memτ _, ?_⟩
        rw [hPeq _ _ memσ (memτ _)]
        exact hP2
      have hP' : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ cst : ℂ, ∀ x y : AdelicGL2 (𝓞 K) K → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rσ.toFun (z * hh)) ⊔
              Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rτ.toFun (z * hh)) →
          y ∈ Submodule.span ℂ (Set.range fun hh : AdelicGL2 (𝓞 K) K => fun z => Rτ.toFun (z * hh)) →
          P (fun z => x (z * g₀)) (fun z => y (z * g₀)) = cst * P x y :=
        fun g₀ => ⟨_, fun x y hx hy => hPcov g₀ x y hx hy⟩
      exact AutomorphicForm.agreesAwayFromFinite_of_projInvariant_sesqForm_ne_zero K
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) σ τ Rσ Rτ P hP' hPself hcross
    ·
      exfalso
      have hs₀ : s₀ ≠ 1 / 2 := hdich1 hν
      have hlin1 : lin 1 ≠ 0 := by
        simp only [hlin]
        intro h0
        apply hs₀
        have : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
        rw [this] at h0
        exact (sub_eq_zero.mp h0).symm
      rw [ord0 (hlinan 1) hlin1, sub_zero] at hpole
      exact absurd hpole (not_lt.mpr (hgan 1 hone).meromorphicOrderAt_nonneg)
  refine ⟨S, hS, σ₀ + 1 / 2, Λ, ⟨a + 1 / 2, by linarith, hΛmero⟩, hprodΛ, himp⟩

end
end S_AutomorphicForm_SmoothCuspRealizationAt_exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_pair_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_pair_of_isCuspConstituent (solution)
