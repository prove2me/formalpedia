-- Prove2me | solution 1 for AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f758905e-0e1c-5aea-ab12-a50233293755

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_continuousOn_normalisedIntertwining_of_isInducedSection_family
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace"
p2m_attr_erase "instance" "NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport"
p2m_attr_erase "simp" "RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"

set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain Topology
open scoped NNReal

noncomputable section

namespace Ws31
namespace E7

theorem extend_from_maximalCompact (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hχ₁c : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ₁ x : ℂˣ) : ℂ))
      (_hχ₂c : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ₂ x : ℂˣ) : ℂ))
      (U : Set ℂ) (_hUo : IsOpen U) (_hUc : IsPreconnected U) (_hU : {s : ℂ | (1 / 2 : ℝ) < s.re} ⊆ U)
      (f : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → IsInducedSection (𝓞 F) F (etaFst χ₁ α hα (-s)) (etaSnd χ₂ α hα (-s)) (f s))
      (h : ℂ → adelicMaximalCompact F → ℂ)
      (_hh_an : ∀ k : adelicMaximalCompact F, AnalyticOnNhd ℂ (fun s : ℂ => h s k) U)
      (_hh_co : ContinuousOn (fun p : ℂ × adelicMaximalCompact F => h p.1 p.2) (U ×ˢ Set.univ))
      (_hh_eq : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ k : adelicMaximalCompact F, h s k = f s (k : AdelicGL2 (𝓞 F) F)),
    ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) (U ×ˢ Set.univ) ∧
      ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F, H s g = f s g := by
  intro α hα χ₁ χ₂ hχ₁c hχ₂c U hUo hUc hU f hf h hh_an hh_co hh_eq
  classical

  let χsw : ℂ → ↥(adelicBorel (𝓞 F) F) → ℂ := fun s b =>
    ((etaFst χ₁ α hα (-s) (borelDiagFst b) : ℂˣ) : ℂ) * ((etaSnd χ₂ α hα (-s) (borelDiagSnd b) : ℂˣ) : ℂ)
  have hχsw_eq : ∀ (s : ℂ) (b : ↥(adelicBorel (𝓞 F) F)), χsw s b =
      (((χ₁ (borelDiagFst b) : ℂˣ) : ℂ) * ((((α (borelDiagFst b) : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2))) *
        (((χ₂ (borelDiagSnd b) : ℂˣ) : ℂ) * ((((α (borelDiagSnd b) : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2)))) := by
    intro s b
    simp only [χsw, etaFst_apply, etaSnd_apply, cpowChar_apply_val, Units.val_mul]
  have hχsw_mul : ∀ (s : ℂ) (b b' : ↥(adelicBorel (𝓞 F) F)), χsw s (b * b') = χsw s b * χsw s b' := by
    intro s b b'
    simp only [χsw, map_mul, Units.val_mul]
    ring
  have hχsw_one : ∀ s : ℂ, χsw s 1 = 1 := by
    intro s
    simp only [χsw, map_one, Units.val_one, one_mul]
  have hχsw_d : ∀ (b : ↥(adelicBorel (𝓞 F) F)), Differentiable ℂ (fun s => χsw s b) := by
    intro b
    have h1 : ∀ (r : ℝ), 0 < r → Differentiable ℂ (fun s : ℂ => ((r : ℂ)) ^ (-s + 1 / 2)) := fun r hr =>
      Differentiable.const_cpow ((differentiable_id.neg).add (differentiable_const _))
        (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
    have h2 : ∀ (r : ℝ), 0 < r → Differentiable ℂ (fun s : ℂ => ((r : ℂ)) ^ (-(-s + 1 / 2))) := fun r hr =>
      Differentiable.const_cpow (((differentiable_id.neg).add (differentiable_const _)).neg)
        (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
    have : (fun s => χsw s b) = fun s =>
        (((χ₁ (borelDiagFst b) : ℂˣ) : ℂ) * ((((α (borelDiagFst b) : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2))) *
          (((χ₂ (borelDiagSnd b) : ℂˣ) : ℂ) * ((((α (borelDiagSnd b) : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2)))) :=
      funext fun s => hχsw_eq s b
    rw [this]
    exact ((differentiable_const _).mul (h1 _ (hα _))).mul ((differentiable_const _).mul (h2 _ (hα _)))

  have hflaw : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F)
      (g : AdelicGL2 (𝓞 F) F), f s (b * g) = χsw s ⟨b, hb⟩ * f s g := fun s hs b hb g => hf s hs b hb g

  choose bI kI hbI hkI1 hkI2 hdecI using fun g : AdelicGL2 (𝓞 F) F => AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hkI : ∀ g, kI g ∈ adelicMaximalCompact F := fun g => mem_adelicMaximalCompact_iff.mpr ⟨hkI1 g, hkI2 g⟩

  let H : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => χsw s ⟨bI g, hbI g⟩ * h s ⟨kI g, hkI g⟩
  have hH_an : ∀ g, AnalyticOnNhd ℂ (fun s => H s g) U := fun g =>
    (((hχsw_d _).differentiableOn).analyticOnNhd hUo).mul (hh_an _)

  have hH_half : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g, H s g = f s g := by
    intro s hs g
    show χsw s ⟨bI g, hbI g⟩ * h s ⟨kI g, hkI g⟩ = f s g
    rw [hh_eq s hs]
    conv_rhs => rw [hdecI g]
    rw [hflaw s hs (bI g) (hbI g) (kI g)]

  have hone_mem : (1 : ℂ) ∈ U := hU (by show (1 / 2 : ℝ) < (1 : ℂ).re; norm_num)
  have hcore : ∀ s ∈ U, ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F)
      (hk : k ∈ adelicMaximalCompact F), H s (b * k) = χsw s ⟨b, hb⟩ * h s ⟨k, hk⟩ := by
    intro s hs b hb k hk
    have hf₁ : AnalyticOnNhd ℂ (fun s => H s (b * k)) U := hH_an _
    have hf₂ : AnalyticOnNhd ℂ (fun s => χsw s ⟨b, hb⟩ * h s ⟨k, hk⟩) U :=
      (((hχsw_d _).differentiableOn).analyticOnNhd hUo).mul (hh_an _)
    have hev : (fun s => H s (b * k)) =ᶠ[𝓝 (1 : ℂ)] (fun s => χsw s ⟨b, hb⟩ * h s ⟨k, hk⟩) := by
      have hO : IsOpen {s : ℂ | (1 / 2 : ℝ) < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have h1 : (1 : ℂ) ∈ {s : ℂ | (1 / 2 : ℝ) < s.re} := by show (1 / 2 : ℝ) < (1 : ℂ).re; norm_num
      filter_upwards [hO.mem_nhds h1] with s hs'
      rw [hH_half s hs' (b * k), hflaw s hs' b hb k, hh_eq s hs' ⟨k, hk⟩]
    exact hf₁.eqOn_of_preconnected_of_eventuallyEq hf₂ hUc hone_mem hev hs

  have hHind : ∀ s ∈ U, IsInducedSection (𝓞 F) F (etaFst χ₁ α hα (-s)) (etaSnd χ₂ α hα (-s)) (H s) := by
    intro s hs b hb g
    have hg : b * g = (b * bI g) * kI g := by rw [mul_assoc, ← hdecI g]
    rw [hg, hcore s hs (b * bI g) ((adelicBorel (𝓞 F) F).mul_mem hb (hbI g)) (kI g) (hkI g)]
    have hsplit : (⟨b * bI g, (adelicBorel (𝓞 F) F).mul_mem hb (hbI g)⟩ : ↥(adelicBorel (𝓞 F) F))
        = ⟨b, hb⟩ * ⟨bI g, hbI g⟩ := rfl
    rw [hsplit, hχsw_mul]
    show χsw s ⟨b, hb⟩ * χsw s ⟨bI g, hbI g⟩ * h s ⟨kI g, hkI g⟩ = χsw s ⟨b, hb⟩ * (χsw s ⟨bI g, hbI g⟩ * h s ⟨kI g, hkI g⟩)
    ring

  have hHK : ∀ s ∈ U, ∀ (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F), H s k = h s ⟨k, hk⟩ := by
    intro s hs k hk
    have := hcore s hs 1 (adelicBorel (𝓞 F) F).one_mem k hk
    rw [one_mul] at this
    rw [this]
    have h1 : (⟨1, (adelicBorel (𝓞 F) F).one_mem⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := rfl
    rw [h1, hχsw_one, one_mul]
  refine ⟨H, hH_an, ?_, hH_half⟩

  have hαr : Continuous (fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ)) := NumberField.TateGlobal.continuous_ideleNorm F
  have hαc : Continuous (fun y : (AdeleRing (𝓞 F) F)ˣ => (((α y : ℝˣ) : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hαr
  have hslit : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((α y : ℝˣ) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    fun y => Complex.ofReal_mem_slitPlane.2 (hα y)
  have hχ₁' : ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaFst χ₁ α hα (-p.1) p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ) := by
    have heq : (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaFst χ₁ α hα (-p.1) p.2 : ℂˣ) : ℂ))
        = fun p => ((χ₁ p.2 : ℂˣ) : ℂ) * (((α p.2 : ℝˣ) : ℝ) : ℂ) ^ (-p.1 + 1 / 2) := by
      funext p
      simp only [etaFst_apply, Units.val_mul, cpowChar_apply_val]
    rw [heq]
    refine Continuous.continuousOn ?_
    exact (hχ₁c.comp continuous_snd).mul
      ((hαc.comp continuous_snd).cpow ((continuous_fst.neg).add continuous_const) (fun p => hslit p.2))
  have hχ₂' : ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaSnd χ₂ α hα (-p.1) p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ) := by
    have heq : (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((etaSnd χ₂ α hα (-p.1) p.2 : ℂˣ) : ℂ))
        = fun p => ((χ₂ p.2 : ℂˣ) : ℂ) * (((α p.2 : ℝˣ) : ℝ) : ℂ) ^ (-(-p.1 + 1 / 2)) := by
      funext p
      simp only [etaSnd_apply, Units.val_mul, cpowChar_apply_val]
    rw [heq]
    refine Continuous.continuousOn ?_
    exact (hχ₂c.comp continuous_snd).mul
      ((hαc.comp continuous_snd).cpow (((continuous_fst.neg).add continuous_const).neg) (fun p => hslit p.2))

  have hHK_co : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2)
      (U ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) := by
    rw [continuousOn_iff_continuous_restrict]
    have hΨ : Continuous fun p : ↥(U ×ˢ {k : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) =>
        ((p.1.1, ⟨p.1.2, mem_adelicMaximalCompact_iff.mpr p.2.2⟩) : ℂ × adelicMaximalCompact F) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    have hcomp := hh_co.comp_continuous hΨ (fun p => ⟨p.2.1, Set.mem_univ _⟩)
    refine hcomp.congr fun p => ?_
    show h p.1.1 ⟨p.1.2, _⟩ = H p.1.1 p.1.2
    exact (hHK p.1.1 p.2.1 p.1.2 _).symm
  exact AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact F U hUo
    (fun s => etaFst χ₁ α hα (-s)) (fun s => etaSnd χ₂ α hα (-s)) hχ₁' hχ₂' H hHind hHK_co

end Ws31.E7

end

section E7Main

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped NNReal Classical

namespace Ws31
namespace E7

theorem archLocalChar_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : InfinitePlace K) (x : (v.Completion)ˣ) :
    archLocalChar (μ * ν⁻¹) v x = archLocalChar μ v x * (archLocalChar ν v x)⁻¹ := rfl

theorem pin_tau_quot (r τμ τν : ℝ) (hr : 0 < r) :
    ((r : ℂ) ^ (((τμ : ℝ) : ℂ) * Complex.I)) * (((r : ℂ) ^ (((τν : ℝ) : ℂ) * Complex.I)))⁻¹
      = (r : ℂ) ^ ((((τμ - τν : ℝ)) : ℂ) * Complex.I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hr0]
  congr 1
  push_cast
  ring

theorem pin_m_quot (z : ℂ) (hz : z ≠ 0) (mμ mν : ℤ) :
    z ^ mμ * (z ^ mν)⁻¹ = z ^ (mμ - mν) := by
  rw [zpow_sub₀ hz, div_eq_mul_inv]

theorem hτ_quot {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (τμ τν : InfinitePlace K → ℝ)
    (hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τμ v : ℝ) : ℂ) * Complex.I))
    (hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τν v : ℝ) : ℂ) * Complex.I)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ ((((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I) := by
  intro v x h1 h2
  rw [archLocalChar_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, hτμ v x h1 h2, hτν v x h1 h2]
  exact pin_tau_quot _ _ _ (ideleNorm_pos _)

theorem hm_quot {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (mμ mν : InfinitePlace K → ℤ)
    (hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) = (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
    (hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) = (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v)) :
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ ((fun v => mμ v - mν v) v) := by
  intro v x h
  rw [archLocalChar_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, hmμ v x h, hmν v x h]
  have hz : InfinitePlace.Completion.extensionEmbedding v (x : v.Completion) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
  exact pin_m_quot _ hz _ _

theorem isUnitaryChar_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsUnitaryChar (𝓞 K) K μ) (hν : AutomorphicForm.IsUnitaryChar (𝓞 K) K ν) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (μ * ν⁻¹) := by
  intro x
  show ‖(((μ x * (ν x)⁻¹ : ℂˣ)) : ℂ)‖ = 1
  rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hμ x, hν x, inv_one, mul_one]

theorem isIdeleClassChar_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ) (hν : AutomorphicForm.IsIdeleClassChar (𝓞 K) K ν) :
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K (μ * ν⁻¹) := by
  intro u
  show μ _ * (ν _)⁻¹ = 1
  rw [hμ u, hν u, inv_one, mul_one]

theorem continuous_mul_inv {K : Type} [Field K] [NumberField K] (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
    (hν : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * ν⁻¹) z : ℂˣ) : ℂ) := by
  have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * ν⁻¹) z : ℂˣ) : ℂ)) = fun z => ((μ z : ℂˣ) : ℂ) * (((ν z : ℂˣ) : ℂ))⁻¹ := by
    funext z; simp [Units.val_inv_eq_inv_val]
  rw [this]
  exact hμ.mul (hν.inv₀ fun z => Units.ne_zero _)

theorem eulerTprod_subtype_eq {K : Type} [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℂ) :
    (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹)
      = ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ :=
  (Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)).tprod_eq
    (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (if IsUnramifiedCharAt χ v then ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹)

noncomputable def gammaInv (K : Type) [Field K] [NumberField K]
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (w : ℂ) : ℂ :=
  ∏ v : InfinitePlace K,
    (if v.IsReal then (Complex.Gammaℝ (w + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ)))⁻¹
      else (Complex.Gammaℝ (w + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))⁻¹ *
        (Complex.Gammaℝ (w + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2 + 1))⁻¹)

theorem differentiable_finset_prod {α : Type*} (S : Finset α) (f : α → ℂ → ℂ)
    (hf : ∀ a ∈ S, Differentiable ℂ (f a)) :
    Differentiable ℂ (fun s => ∏ a ∈ S, f a s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiable_const 1
  | insert a S haS ih =>
    simp only [Finset.prod_insert haS]
    exact Differentiable.mul (hf a (Finset.mem_insert_self a S))
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

theorem differentiable_gammaInv (K : Type) [Field K] [NumberField K]
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) : Differentiable ℂ (gammaInv K τ m) := by
  unfold gammaInv
  refine differentiable_finset_prod _ _ (fun v _ => ?_)
  have hG : ∀ a : ℂ, Differentiable ℂ (fun w : ℂ => (Complex.Gammaℝ (w + a))⁻¹) := fun a =>
    Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const a)
  split_ifs with hv
  · simpa only [add_assoc] using hG (((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
  · have h1 := hG (((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)
    have h2 := hG (((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2 + 1)
    simp only [add_assoc] at h1 h2 ⊢
    exact h1.mul h2

theorem gamma_mul_gammaInv (K : Type) [Field K] [NumberField K]
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (w : ℂ) (hw : 0 < w.re) :
    (∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (w + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (w + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))) *
      gammaInv K τ m w = 1 := by
  unfold gammaInv
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun v _ => ?_)
  split_ifs with hv
  · apply mul_inv_cancel₀
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.natCast_re, mul_zero, zero_mul, sub_zero]
    positivity
  · rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    have h1 : Complex.Gammaℝ (w + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2) ≠ 0 := by
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.div_ofNat_re, Complex.natCast_re, mul_zero, zero_mul, sub_zero]
      positivity
    have h2 : Complex.Gammaℝ (w + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2 + 1) ≠ 0 := by
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.div_ofNat_re, Complex.natCast_re, Complex.one_re, mul_zero, zero_mul, sub_zero]
      positivity
    rw [mul_mul_mul_comm, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, one_mul]

theorem algebra_L (Λ0 R gi vol γ0 γ1 p0 p1 c M Le0 L71 : ℂ)
    (hA : γ0 * p0 * R = γ1 * p1 * (c * M)) (hB : Λ0 = γ0 * Le0) (hC : Le0 = p0) (hD : L71 = p1)
    (hE : γ1 * gi = 1) (hF : c * vol = 1) : Λ0 * R * gi * vol = L71 * M := by
  linear_combination (R * gi * vol) * hB + (γ0 * R * gi * vol) * hC + (gi * vol) * hA
    + (p1 * c * M * vol) * hE + (p1 * M) * hF - M * hD

theorem algebra_Q (s : ℂ) (τ : ℝ) (ΛQ0 R gi vol γ0 γ1 p0 p1 c M Qe0 Q71 : ℂ)
    (hA : γ0 * p0 * R = γ1 * p1 * (c * M))
    (hB : ΛQ0 = (2 * s + ((τ : ℝ) : ℂ) * Complex.I) * (γ0 * Qe0))
    (hC : Qe0 = (2 * s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) * p0)
    (hD : Q71 = (2 * s + 1 - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) * p1)
    (hE : γ1 * gi = 1) (hF : c * vol = 1) :
    ΛQ0 * R * gi * (vol / 2) = (s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * (Q71 * M) := by
  have hτ : ((τ / 2 : ℝ) : ℂ) = ((τ : ℝ) : ℂ) / 2 := by push_cast; ring
  rw [hτ]
  linear_combination (R * gi * (vol / 2)) * hB
    + ((2 * s + ((τ : ℝ) : ℂ) * Complex.I) * γ0 * R * gi * (vol / 2)) * hC
    + ((2 * s + ((τ : ℝ) : ℂ) * Complex.I) * (2 * s + ((τ : ℝ) : ℂ) * Complex.I - 1) * gi * (vol / 2)) * hA
    + ((2 * s + ((τ : ℝ) : ℂ) * Complex.I) * (2 * s + ((τ : ℝ) : ℂ) * Complex.I - 1) * p1 * c * M * (vol / 2)) * hE
    + ((2 * s + ((τ : ℝ) : ℂ) * Complex.I) * (2 * s + ((τ : ℝ) : ℂ) * Complex.I - 1) * p1 * M / 2) * hF
    - ((2 * s + ((τ : ℝ) : ℂ) * Complex.I - 1) / 2 * M) * hD

theorem isInducedSection_const_mul {K : Type} [Field K] [NumberField K]
    {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (a : ℂ)
    (h : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) : IsInducedSection (𝓞 K) K χ₁ χ₂ (fun g => a * φ g) := by
  intro b hb g
  dsimp only
  rw [h b hb g]
  ring

end Ws31.E7

end E7Main

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal
open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ g : AdelicGL2 (𝓞 F) F,
        (letI := adeleBorel (𝓞 F) F
         MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
          ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
            Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)),
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∀ Q : ℂ → ℂ, Differentiable ℂ Q →
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
          ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
            (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U) ∧
            ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) (U ×ˢ Set.univ) ∧
            ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
              H s g = (s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * (Q (2 * s + 1) * Mc s g)) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∀ L : ℂ → ℂ, Differentiable ℂ L →
        (∀ w : ℂ, 1 < w.re → L w =
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
          ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
            (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U) ∧
            ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) (U ×ˢ Set.univ) ∧
            ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
              H s g = L (2 * s + 1) * Mc s g) := by
  intro α hα μ ν _hμ _hν _hμic _hνic φ _hφ _hφK _hφf _hφjc _hφhol _hμc _hνc _hφKu Mc _hMc
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F

  obtain ⟨τμ, mμ, hτμ, hmμ, -⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F μ _hμ _hμc
  obtain ⟨τν, mν, hτν, hmν, -⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F ν _hν _hνc

  obtain ⟨δ, R, hδ, hRan, hRco, hpin, -⟩ :=
    AutomorphicForm.exists_analyticOnNhd_continuousOn_normalisedIntertwining_of_isInducedSection_family F hα μ ν
      _hμ _hν _hμic _hνic _hμc _hνc τμ τν hτμ hτν mμ mν hmμ hmν φ _hφ _hφK _hφf _hφjc _hφhol _hφKu

  have hχc := Ws31.E7.continuous_mul_inv μ ν _hμc _hνc
  have hχu := Ws31.E7.isUnitaryChar_mul_inv μ ν _hμ _hν
  have hχic := Ws31.E7.isIdeleClassChar_mul_inv μ ν _hμic _hνic
  have hΛ := NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
    F (μ * ν⁻¹) hχc hχu hχic (fun v => τμ v - τν v) (fun v => mμ v - mν v)
    (Ws31.E7.hτ_quot μ ν τμ τν hτμ hτν) (Ws31.E7.hm_quot μ ν mμ mν hmμ hmν)
  have hgi_d := Ws31.E7.differentiable_gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v)

  have hvol : (((adelicAddHaar (𝓞 F) F) (NumberField.AdelicBox.adelicBox F)).toReal : ℂ) ≠ 0 := by
    have hpos := NumberField.AdelicBox.adelicAddHaar_adelicBox_pos F
    have hfin := NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top F
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  have hF : (((adelicAddHaar (𝓞 F) F) (NumberField.AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
      (((adelicAddHaar (𝓞 F) F) (NumberField.AdelicBox.adelicBox F)).toReal : ℂ) = 1 := inv_mul_cancel₀ hvol

  obtain ⟨δ', hδ'pos, hδ'le, hδ'le4⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ 1 / 4 :=
    ⟨min δ (1 / 4), lt_min hδ (by norm_num), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = {s : ℂ | -δ' < s.re} := ⟨_, rfl⟩
  have hUo : IsOpen U := by rw [hU]; exact isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := by rw [hU]; exact (convex_halfSpace_re_gt (-δ')).isPreconnected
  have hUhalf : {s : ℂ | (1 / 2 : ℝ) < s.re} ⊆ U := fun s hs => by
    simp only [hU, Set.mem_setOf_eq] at hs ⊢; linarith
  have hU0 : {s : ℂ | 0 ≤ s.re} ⊆ U := fun s hs => by
    simp only [hU, Set.mem_setOf_eq] at hs ⊢; linarith
  have hUδ : U ⊆ {s : ℂ | -δ < s.re} := fun s hs => by
    simp only [hU, Set.mem_setOf_eq] at hs ⊢; linarith

  have hMind : ∀ s : ℂ, IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s))
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s)) := fun s =>
    AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hα μ ν s (φ s) (_hφ s)
  refine ⟨?_, ?_⟩
  ·
    intro τ hχeq Q hQd hQP
    obtain ⟨Qe, ΛQ, hQed, hΛQd, hQeP, hΛQ⟩ := hΛ.2 τ hχeq
    let h : ℂ → adelicMaximalCompact F → ℂ := fun s k =>
      ΛQ (2 * s) * R s k * Ws31.E7.gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * s + 1) *
        ((((adelicAddHaar (𝓞 F) F) (NumberField.AdelicBox.adelicBox F)).toReal : ℂ) / 2)
    let f : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g =>
      (s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) *
        (Q (2 * s + 1) * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)
    have hf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
        IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s)) (f s) := fun s _ => by
      intro b hb g
      dsimp only [f]
      rw [hMind s b hb g]
      ring
    have hh_an : ∀ k : adelicMaximalCompact F, AnalyticOnNhd ℂ (fun s : ℂ => h s k) U := by
      intro k s hs
      have h1 : AnalyticAt ℂ (fun s : ℂ => ΛQ (2 * s)) s :=
        (hΛQd.comp (differentiable_id.const_mul (2 : ℂ))).analyticAt s
      have h2 : AnalyticAt ℂ (fun s : ℂ => R s k) s := hRan k s (hUδ hs)
      have h3 : AnalyticAt ℂ (fun s : ℂ =>
          Ws31.E7.gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * s + 1)) s :=
        (hgi_d.comp ((differentiable_id.const_mul (2 : ℂ)).add_const 1)).analyticAt s
      exact ((h1.mul h2).mul h3).mul analyticAt_const
    have hh_co : ContinuousOn (fun p : ℂ × adelicMaximalCompact F => h p.1 p.2) (U ×ˢ Set.univ) := by
      have h1 : Continuous (fun p : ℂ × adelicMaximalCompact F => ΛQ (2 * p.1)) :=
        hΛQd.continuous.comp (continuous_const.mul continuous_fst)
      have h2 : ContinuousOn (fun p : ℂ × adelicMaximalCompact F => R p.1 p.2) (U ×ˢ Set.univ) :=
        hRco.mono (Set.prod_mono hUδ subset_rfl)
      have h3 : Continuous (fun p : ℂ × adelicMaximalCompact F =>
          Ws31.E7.gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * p.1 + 1)) :=
        hgi_d.continuous.comp ((continuous_const.mul continuous_fst).add continuous_const)
      exact ((h1.continuousOn.mul h2).mul h3.continuousOn).mul continuousOn_const
    have hh_eq : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ k : adelicMaximalCompact F,
        h s k = f s (k : AdelicGL2 (𝓞 F) F) := by
      intro s hs k
      have h2 : 1 < (2 * s).re := by simp; linarith
      have h2' : 0 < (2 * s).re := by linarith
      have h21 : 1 < (2 * s + 1).re := by simp; linarith
      have h21' : 0 < (2 * s + 1).re := by linarith
      have hA := hpin s hs k
      have hB := hΛQ (2 * s) h2'
      have hC := hQeP (2 * s) h2
      have hD := hQP (2 * s + 1) h21
      rw [Ws31.E7.eulerTprod_subtype_eq] at hD
      have hE := Ws31.E7.gamma_mul_gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * s + 1) h21'
      dsimp only [h, f]
      exact Ws31.E7.algebra_Q s τ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hD hE hF
    obtain ⟨H, hHan, hHco, hHeq⟩ := Ws31.E7.extend_from_maximalCompact F hα ν μ _hνc _hμc U hUo hUc hUhalf
      f hf h hh_an hh_co hh_eq
    refine ⟨U, hUo, hU0, H, hHan, hHco, fun s hs g => ?_⟩
    rw [hHeq s hs g]
    dsimp only [f]
    rw [(_hMc g).2 s hs]
  ·
    intro hne L hLd hLP
    obtain ⟨Le, Λ, hLed, hΛd, hLeP, hΛe⟩ := hΛ.1 hne
    let h : ℂ → adelicMaximalCompact F → ℂ := fun s k =>
      Λ (2 * s) * R s k * Ws31.E7.gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * s + 1) *
        (((adelicAddHaar (𝓞 F) F) (NumberField.AdelicBox.adelicBox F)).toReal : ℂ)
    let f : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g =>
      L (2 * s + 1) * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g
    have hf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
        IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s)) (f s) := fun s _ =>
      Ws31.E7.isInducedSection_const_mul _ (hMind s)
    have hh_an : ∀ k : adelicMaximalCompact F, AnalyticOnNhd ℂ (fun s : ℂ => h s k) U := by
      intro k s hs
      have h1 : AnalyticAt ℂ (fun s : ℂ => Λ (2 * s)) s :=
        (hΛd.comp (differentiable_id.const_mul (2 : ℂ))).analyticAt s
      have h2 : AnalyticAt ℂ (fun s : ℂ => R s k) s := hRan k s (hUδ hs)
      have h3 : AnalyticAt ℂ (fun s : ℂ =>
          Ws31.E7.gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * s + 1)) s :=
        (hgi_d.comp ((differentiable_id.const_mul (2 : ℂ)).add_const 1)).analyticAt s
      exact ((h1.mul h2).mul h3).mul analyticAt_const
    have hh_co : ContinuousOn (fun p : ℂ × adelicMaximalCompact F => h p.1 p.2) (U ×ˢ Set.univ) := by
      have h1 : Continuous (fun p : ℂ × adelicMaximalCompact F => Λ (2 * p.1)) :=
        hΛd.continuous.comp (continuous_const.mul continuous_fst)
      have h2 : ContinuousOn (fun p : ℂ × adelicMaximalCompact F => R p.1 p.2) (U ×ˢ Set.univ) :=
        hRco.mono (Set.prod_mono hUδ subset_rfl)
      have h3 : Continuous (fun p : ℂ × adelicMaximalCompact F =>
          Ws31.E7.gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * p.1 + 1)) :=
        hgi_d.continuous.comp ((continuous_const.mul continuous_fst).add continuous_const)
      exact ((h1.continuousOn.mul h2).mul h3.continuousOn).mul continuousOn_const
    have hh_eq : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ k : adelicMaximalCompact F,
        h s k = f s (k : AdelicGL2 (𝓞 F) F) := by
      intro s hs k
      have h2 : 1 < (2 * s).re := by simp; linarith
      have h2' : 0 < (2 * s).re := by linarith
      have h21 : 1 < (2 * s + 1).re := by simp; linarith
      have h21' : 0 < (2 * s + 1).re := by linarith
      have hA := hpin s hs k
      have hB := hΛe (2 * s) h2'
      have hC := hLeP (2 * s) h2
      have hD := hLP (2 * s + 1) h21
      rw [Ws31.E7.eulerTprod_subtype_eq] at hD
      have hE := Ws31.E7.gamma_mul_gammaInv F (fun v => τμ v - τν v) (fun v => mμ v - mν v) (2 * s + 1) h21'
      dsimp only [h, f]
      exact Ws31.E7.algebra_L _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hD hE hF
    obtain ⟨H, hHan, hHco, hHeq⟩ := Ws31.E7.extend_from_maximalCompact F hα ν μ _hνc _hμc U hUo hUc hUhalf
      f hf h hh_an hh_co hh_eq
    refine ⟨U, hUo, hU0, H, hHan, hHco, fun s hs g => ?_⟩
    rw [hHeq s hs g]
    dsimp only [f]
    rw [(_hMc g).2 s hs]

#print axioms solution

end S_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
end P2MW
export P2MW.S_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation (solution)
