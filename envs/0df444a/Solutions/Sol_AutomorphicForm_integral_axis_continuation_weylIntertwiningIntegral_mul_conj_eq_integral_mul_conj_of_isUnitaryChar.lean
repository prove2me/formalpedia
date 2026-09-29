-- Prove2me | solution 1 for AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ee13aa44-35d8-572e-a794-fb666a3d04ff

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne
import Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_NumberField_NormPowChar
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem"
p2m_attr_erase "instance" "Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section
namespace UnitAux

theorem ideleNorm_eq_one_of_mem_range (K : Type) [Field K] [NumberField K] {z : (AdeleRing (𝓞 K) K)ˣ}
    (hz : z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range) :
    NumberField.TateGlobal.ideleNorm K z = 1 := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hz
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap K a
  simp only [NumberField.TateGlobal.ideleNorm]
  rw [show Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom a from rfl, h]
  simp

theorem eq_zero_of_continuousAt_of_norm_le_mul_abs_sub {N : ℝ → ℂ} {t M : ℝ}
    (hN : ContinuousAt N t) (hle : ∀ᶠ t' in nhdsWithin t {t}ᶜ, ‖N t'‖ ≤ M * |t' - t|) : N t = 0 := by
  have h1 : Filter.Tendsto (fun t' => ‖N t'‖) (nhdsWithin t {t}ᶜ) (nhds ‖N t‖) :=
    (hN.norm.tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun t' : ℝ => M * |t' - t|) (nhdsWithin t {t}ᶜ) (nhds 0) := by
    have : Filter.Tendsto (fun t' : ℝ => M * |t' - t|) (nhds t) (nhds (M * |t - t|)) :=
      ((continuous_const.mul ((continuous_id.sub continuous_const).abs)).tendsto t)
    rw [sub_self, abs_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : ‖N t‖ ≤ 0 := le_of_tendsto_of_tendsto h1 h2 hle
  exact norm_le_zero_iff.mp h3

theorem continuous_integral_of_continuous {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure μ]
    {f : ℝ → Y → ℂ} (hf : Continuous fun p : ℝ × Y => f p.1 p.2) :
    Continuous fun x => ∫ y, f x y ∂μ := by
  have hf' : Continuous f.uncurry := hf
  have := continuous_parametric_integral_of_continuous (μ := μ) hf' (isCompact_univ (X := Y))
  simpa [MeasureTheory.setIntegral_univ] using this

end UnitAux
end

theorem unit_dichot
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      (_hdich : μ = ν ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) (t : ℝ),
    (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F)) =
    ∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
    Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ hdich t

  obtain ⟨c, hc, R₀, hMS⟩ := AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne F 1 2 one_pos one_lt_two (∅ : Set (AdelicGL2 (𝓞 F) F)) hαm
  obtain ⟨c₂, hc₂, R₂, hMS2⟩ := AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles F 1 2 one_pos one_lt_two (∅ : Set (AdelicGL2 (𝓞 F) F)) hαm

  obtain ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ := hEψ
  obtain ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩ := hEφ
  have hBψ := AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family F 1 2 one_pos one_lt_two (∅ : Set (AdelicGL2 (𝓞 F) F)) hαm μ ν hμ hν hμF hνF hμk hνk
    ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oψ Eψ Nψ hOψ hOψc hOψhalf hEψa hNψa hEψjc hNψjc
    (fun s hs g => by rw [hEψE s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNψN R₀
  have hBφ := AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family F 1 2 one_pos one_lt_two (∅ : Set (AdelicGL2 (𝓞 F) F)) hαm μ ν hμ hν hμF hνF hμk hνk
    φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hOφ hOφc hOφhalf hEφa hNφa hEφjc hNφjc
    (fun s hs g => by rw [hEφE s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNφN R₀
  have hBψ2 := AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family F 1 2 one_pos one_lt_two (∅ : Set (AdelicGL2 (𝓞 F) F)) hαm μ ν hμ hν hμF hνF hμk hνk
    ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oψ Eψ Nψ hOψ hOψc hOψhalf hEψa hNψa hEψjc hNψjc
    (fun s hs g => by rw [hEψE s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNψN R₂
  have hBφ2 := AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family F 1 2 one_pos one_lt_two (∅ : Set (AdelicGL2 (𝓞 F) F)) hαm μ ν hμ hν hμF hνF hμk hνk
    φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hOφ hOφc hOφhalf hEφa hNφa hEφjc hNφjc
    (fun s hs g => by rw [hEφE s hs g, AutomorphicForm.pseudoEisenstein_apply]) hNφN R₂

  set vC : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)) with hvC
  set P1 : ℝ → ℝ → ℂ := fun a b => ∫ k, φf ((a : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
      conj (ψf ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hP1
  set P2 : ℝ → ℝ → ℂ := fun a b => ∫ k, (vC⁻¹ * Nφ ((a : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) *
      conj (vC⁻¹ * Nψ ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hP2
  set P3 : ℝ → ℝ → ℂ := fun a b => ∫ k, φf ((a : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
      conj (vC⁻¹ * Nψ ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hP3
  set P4 : ℝ → ℝ → ℂ := fun a b => ∫ k, (vC⁻¹ * Nφ ((a : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) *
      conj (ψf ((b : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hP4

  have haxφ : Continuous fun p : ℝ × ↥(adelicMaximalCompact F) => φf ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 F) F) :=
    hφfjc.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const |>.prodMk
      (continuous_subtype_val.comp continuous_snd))
  have haxψ : Continuous fun p : ℝ × ↥(adelicMaximalCompact F) => ψf ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 F) F) :=
    hψfjc.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const |>.prodMk
      (continuous_subtype_val.comp continuous_snd))
  have haxNφ : Continuous fun p : ℝ × ↥(adelicMaximalCompact F) => Nφ ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 F) F) := by
    have hmap : Continuous fun p : ℝ × ↥(adelicMaximalCompact F) => (((p.1 : ℂ) * Complex.I), (p.2 : AdelicGL2 (𝓞 F) F)) :=
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)
    refine hNφjc.comp_continuous hmap fun p => ⟨hOφax (by simp), Set.mem_univ _⟩
  have haxNψ : Continuous fun p : ℝ × ↥(adelicMaximalCompact F) => Nψ ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 F) F) := by
    have hmap : Continuous fun p : ℝ × ↥(adelicMaximalCompact F) => (((p.1 : ℂ) * Complex.I), (p.2 : AdelicGL2 (𝓞 F) F)) :=
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)
    refine hNψjc.comp_continuous hmap fun p => ⟨hOψax (by simp), Set.mem_univ _⟩

  have hP1c : ∀ a : ℝ, Continuous fun b => P1 a b := by
    intro a; simp only [hP1]
    exact UnitAux.continuous_integral_of_continuous _
      ((haxφ.comp (continuous_const.prodMk continuous_snd)).mul
        (Complex.continuous_conj.comp (haxψ.comp (continuous_fst.prodMk continuous_snd))))
  have hP2c : ∀ a : ℝ, Continuous fun b => P2 a b := by
    intro a; simp only [hP2]
    exact UnitAux.continuous_integral_of_continuous _
      ((continuous_const.mul (haxNφ.comp (continuous_const.prodMk continuous_snd))).mul
        (Complex.continuous_conj.comp (continuous_const.mul (haxNψ.comp (continuous_fst.prodMk continuous_snd)))))
  have hP3c : ∀ a : ℝ, Continuous fun b => P3 a b := by
    intro a; simp only [hP3]
    exact UnitAux.continuous_integral_of_continuous _
      ((haxφ.comp (continuous_const.prodMk continuous_snd)).mul
        (Complex.continuous_conj.comp (continuous_const.mul (haxNψ.comp (continuous_fst.prodMk continuous_snd)))))
  have hP4c : ∀ a : ℝ, Continuous fun b => P4 a b := by
    intro a; simp only [hP4]
    exact UnitAux.continuous_integral_of_continuous _
      ((continuous_const.mul (haxNφ.comp (continuous_const.prodMk continuous_snd))).mul
        (Complex.continuous_conj.comp (haxψ.comp (continuous_fst.prodMk continuous_snd))))
  have hP1d : Continuous fun a : ℝ => P1 a a := by
    simp only [hP1]
    exact UnitAux.continuous_integral_of_continuous _
      ((haxφ.comp (continuous_fst.prodMk continuous_snd)).mul
        (Complex.continuous_conj.comp (haxψ.comp (continuous_fst.prodMk continuous_snd))))
  have hP2d : Continuous fun a : ℝ => P2 a a := by
    simp only [hP2]
    exact UnitAux.continuous_integral_of_continuous _
      ((continuous_const.mul (haxNφ.comp (continuous_fst.prodMk continuous_snd))).mul
        (Complex.continuous_conj.comp (continuous_const.mul (haxNψ.comp (continuous_fst.prodMk continuous_snd)))))

  show P2 t t = P1 t t

  have hmain : ∀ t : ℝ, t ≠ 0 → P2 t t = P1 t t := by
    intro t ht0
    by_cases hμν : μ = ν
    swap
    · by_cases hoff : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z
      swap
      · exact absurd hdich (not_or.mpr ⟨hμν, hoff⟩)

      set Lφ : AdelicGL2 (𝓞 F) F → ℂ := fun x => (@AutomorphicForm.lambdaT _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R₂)
            (Eφ ((t : ℂ) * Complex.I))) x with hLφ
      set Lψ : ℝ → AdelicGL2 (𝓞 F) F → ℂ := fun b x => (@AutomorphicForm.lambdaT _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R₂)
            (Eψ ((b : ℂ) * Complex.I))) x with hLψ
      set Ib : ℝ → ℂ := fun b => ∫ x in AutomorphicForm.canonicalTruncationDomain F 1 2, Lφ x * conj (Lψ b x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hIb
      have hMSb : ∀ b : ℝ, t ≠ b →
          Ib b = (c₂ : ℂ) *
            ( P1 t b * Complex.exp ((R₂ : ℂ) * (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I))
            - P2 t b * Complex.exp (-((R₂ : ℂ) * (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I)) ) := by
        intro b hb
        have h := (hMS2 μ ν hoff hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
          Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
          Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t b hb R₂ le_rfl).2
        simp only [hIb, hLφ, hLψ, hP1, hP2, hvC]
        exact h
      have hconjI : ∀ b : ℝ, conj ((b : ℂ) * Complex.I) = -((b : ℂ) * Complex.I) := by
        intro b; rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
      have hsum : ∀ b : ℝ, ((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I) = ((t - b : ℝ) : ℂ) * Complex.I := by
        intro b; rw [hconjI]; push_cast; ring
      have hIbdd : ∃ K : ℝ, ∀ᶠ b in nhds t, ‖Ib b‖ ≤ K := by
        set μΦ : MeasureTheory.Measure (AdelicGL2 (𝓞 F) F) :=
          (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (AutomorphicForm.canonicalTruncationDomain F 1 2) with hμΦ
        have hmemφ : MemLp Lφ 2 μΦ := hBφ2.1 _ (hOφax (by simp))
        have hmemψ : ∀ b : ℝ, MemLp (Lψ b) 2 μΦ := fun b => hBψ2.1 _ (hOψax (by simp))
        have hholder : ∀ b : ℝ, ‖Ib b‖ ≤ (eLpNorm Lφ 2 μΦ).toReal * (eLpNorm (Lψ b) 2 μΦ).toReal := by
          intro b
          have h1 : ‖Ib b‖ ≤ ∫ x, ‖Lφ x‖ * ‖Lψ b x‖ ∂μΦ := by
            simp only [hIb]
            refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
            congr 1; funext x; rw [norm_mul, Complex.norm_conj]
          have h2 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μΦ) (p := 2) (q := 2)
            Real.HolderConjugate.two_two
            (Filter.Eventually.of_forall fun x => norm_nonneg (Lφ x)) (Filter.Eventually.of_forall fun x => norm_nonneg (Lψ b x))
            (by simpa using hmemφ.norm) (by simpa using (hmemψ b).norm)
          refine h1.trans (h2.trans (le_of_eq ?_))
          rw [hmemφ.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
            (hmemψ b).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
            ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
          norm_num
        have hax : Filter.Tendsto (fun b : ℝ => ((b : ℂ) * Complex.I)) (nhds t) (nhdsWithin ((t : ℂ) * Complex.I) Oψ) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (((Complex.continuous_ofReal.mul continuous_const).tendsto t))
            (Filter.Eventually.of_forall fun b => hOψax (by simp))
        have hlim := (hBψ2.2 _ (hOψax (by simp : (((t : ℂ) * Complex.I)).re = 0))).comp hax
        have hev : ∀ᶠ b in nhds t, eLpNorm (Lψ b) 2 μΦ ≤ 1 + eLpNorm (Lψ t) 2 μΦ := by
          have h1 : ∀ᶠ b in nhds t, eLpNorm (Lψ b - Lψ t) 2 μΦ < 1 :=
            hlim (Iio_mem_nhds (zero_lt_one' ENNReal))
          filter_upwards [h1] with b hb
          have : Lψ b = (Lψ b - Lψ t) + Lψ t := by funext x; simp
          calc eLpNorm (Lψ b) 2 μΦ = eLpNorm ((Lψ b - Lψ t) + Lψ t) 2 μΦ := by rw [← this]
            _ ≤ eLpNorm (Lψ b - Lψ t) 2 μΦ + eLpNorm (Lψ t) 2 μΦ :=
                eLpNorm_add_le ((hmemψ b).1.sub (hmemψ t).1) (hmemψ t).1 (by norm_num)
            _ ≤ 1 + eLpNorm (Lψ t) 2 μΦ := by gcongr
        refine ⟨(eLpNorm Lφ 2 μΦ).toReal * (1 + eLpNorm (Lψ t) 2 μΦ).toReal, ?_⟩
        filter_upwards [hev] with b hb
        refine (hholder b).trans ?_
        gcongr
        · exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (hmemψ t).eLpNorm_ne_top⟩
      set Nf : ℝ → ℂ := fun b => P1 t b * Complex.exp ((R₂ : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I)) -
        P2 t b * Complex.exp (-((R₂ : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) with hNf
      have hNc : ContinuousAt Nf t := by
        simp only [hNf]
        refine ((hP1c t).continuousAt.mul ?_).sub ((hP2c t).continuousAt.mul ?_)
        · exact (Complex.continuous_exp.comp (continuous_const.mul
            ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const))).continuousAt
        · exact (Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
            ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const)))).continuousAt
      have hNt : Nf t = P1 t t - P2 t t := by
        simp only [hNf, sub_self, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one]
      have hNle : ∃ M : ℝ, ∀ᶠ b in nhdsWithin t {t}ᶜ, ‖Nf b‖ ≤ M * |b - t| := by
        obtain ⟨K, hK⟩ := hIbdd
        refine ⟨K / c₂, ?_⟩
        rw [Filter.eventually_iff_exists_mem] at hK ⊢
        obtain ⟨U, hU, hUp⟩ := hK
        refine ⟨{t}ᶜ ∩ U, inter_mem_nhdsWithin _ hU, fun b hb => ?_⟩
        obtain ⟨hbt, hbU⟩ := hb
        have hbt' : t ≠ b := fun h => hbt (h ▸ rfl)
        have hKb := hUp b hbU
        have hms := hMSb b hbt'
        rw [hsum] at hms
        have hcne : (c₂ : ℂ) ≠ 0 := by exact_mod_cast hc₂.ne'
        have htbc : ((t - b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hbt')
        have hNf_eq : Nf b = (((t - b : ℝ) : ℂ) * Complex.I) * (Ib b / (c₂ : ℂ)) := by
          simp only [hNf]
          rw [hms]
          field_simp [hcne, htbc, Complex.I_ne_zero]
        have hnD : ‖((t - b : ℝ) : ℂ) * Complex.I‖ = |b - t| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_sub_comm]
        rw [hNf_eq, norm_mul, hnD, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₂]
        exact div_le_div_of_nonneg_right hKb hc₂.le
      obtain ⟨M, hM⟩ := hNle
      have h0 := UnitAux.eq_zero_of_continuousAt_of_norm_le_mul_abs_sub hNc hM
      rw [hNt, sub_eq_zero] at h0
      exact h0.symm

    set Lφ : AdelicGL2 (𝓞 F) F → ℂ := fun x => (@AutomorphicForm.lambdaT _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R₀)
            (Eφ ((t : ℂ) * Complex.I))) x with hLφ
    set Lψ : ℝ → AdelicGL2 (𝓞 F) F → ℂ := fun b x => (@AutomorphicForm.lambdaT _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F (∅ : Set (AdelicGL2 (𝓞 F) F)) (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R₀)
            (Eψ ((b : ℂ) * Complex.I))) x with hLψ
    set Ib : ℝ → ℂ := fun b => ∫ x in AutomorphicForm.canonicalTruncationDomain F 1 2, Lφ x * conj (Lψ b x)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hIb

    have hMSb : ∀ b : ℝ, t ≠ b → t + b ≠ 0 →
        Ib b = (c : ℂ) *
          ( P1 t b * Complex.exp ((R₀ : ℂ) * (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I))
          - P2 t b * Complex.exp (-((R₀ : ℂ) * (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I))
          + P3 t b * Complex.exp ((R₀ : ℂ) * (((t : ℂ) * Complex.I) - conj ((b : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) - conj ((b : ℂ) * Complex.I))
          - P4 t b * Complex.exp (-((R₀ : ℂ) * (((t : ℂ) * Complex.I) - conj ((b : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) - conj ((b : ℂ) * Complex.I)) ) := by
      intro b hb hbb
      have h := (hMS μ ν hμν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
        Oφ Eφ Nφ ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφE, hNφN⟩
        Oψ Eψ Nψ ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψE, hNψN⟩ t b hb hbb R₀ le_rfl).2
      simp only [hIb, hLφ, hLψ, hP1, hP2, hP3, hP4, hvC]
      exact h

    have hconjI : ∀ b : ℝ, conj ((b : ℂ) * Complex.I) = -((b : ℂ) * Complex.I) := by
      intro b; rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    have hsum : ∀ b : ℝ, ((t : ℂ) * Complex.I) + conj ((b : ℂ) * Complex.I) = ((t - b : ℝ) : ℂ) * Complex.I := by
      intro b; rw [hconjI]; push_cast; ring
    have hdiff : ∀ b : ℝ, ((t : ℂ) * Complex.I) - conj ((b : ℂ) * Complex.I) = ((t + b : ℝ) : ℂ) * Complex.I := by
      intro b; rw [hconjI]; push_cast; ring

    have hIbdd : ∃ K : ℝ, ∀ᶠ b in nhds t, ‖Ib b‖ ≤ K := by
      set μΦ : MeasureTheory.Measure (AdelicGL2 (𝓞 F) F) :=
        (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (AutomorphicForm.canonicalTruncationDomain F 1 2) with hμΦ
      have hmemφ : MemLp Lφ 2 μΦ := hBφ.1 _ (hOφax (by simp))
      have hmemψ : ∀ b : ℝ, MemLp (Lψ b) 2 μΦ := fun b => hBψ.1 _ (hOψax (by simp))

      have hholder : ∀ b : ℝ, ‖Ib b‖ ≤ (eLpNorm Lφ 2 μΦ).toReal * (eLpNorm (Lψ b) 2 μΦ).toReal := by
        intro b
        have h1 : ‖Ib b‖ ≤ ∫ x, ‖Lφ x‖ * ‖Lψ b x‖ ∂μΦ := by
          simp only [hIb]
          refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
          congr 1; funext x; rw [norm_mul, Complex.norm_conj]
        have h2 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μΦ) (p := 2) (q := 2)
          Real.HolderConjugate.two_two
          (Filter.Eventually.of_forall fun x => norm_nonneg (Lφ x)) (Filter.Eventually.of_forall fun x => norm_nonneg (Lψ b x))
          (by simpa using hmemφ.norm) (by simpa using (hmemψ b).norm)
        refine h1.trans (h2.trans (le_of_eq ?_))
        have e2 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
        rw [hmemφ.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
          (hmemψ b).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
        norm_num

      have hax : Filter.Tendsto (fun b : ℝ => ((b : ℂ) * Complex.I)) (nhds t) (nhdsWithin ((t : ℂ) * Complex.I) Oψ) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((Complex.continuous_ofReal.mul continuous_const).tendsto t))
          (Filter.Eventually.of_forall fun b => hOψax (by simp))
      have hlim := (hBψ.2 _ (hOψax (by simp : (((t : ℂ) * Complex.I)).re = 0))).comp hax
      have hev : ∀ᶠ b in nhds t, eLpNorm (Lψ b) 2 μΦ ≤ 1 + eLpNorm (Lψ t) 2 μΦ := by
        have h1 : ∀ᶠ b in nhds t, eLpNorm (Lψ b - Lψ t) 2 μΦ < 1 :=
          hlim (Iio_mem_nhds (zero_lt_one' ENNReal))
        filter_upwards [h1] with b hb
        have : Lψ b = (Lψ b - Lψ t) + Lψ t := by funext x; simp
        calc eLpNorm (Lψ b) 2 μΦ = eLpNorm ((Lψ b - Lψ t) + Lψ t) 2 μΦ := by rw [← this]
          _ ≤ eLpNorm (Lψ b - Lψ t) 2 μΦ + eLpNorm (Lψ t) 2 μΦ :=
              eLpNorm_add_le ((hmemψ b).1.sub (hmemψ t).1) (hmemψ t).1 (by norm_num)
          _ ≤ 1 + eLpNorm (Lψ t) 2 μΦ := by gcongr
      refine ⟨(eLpNorm Lφ 2 μΦ).toReal * (1 + eLpNorm (Lψ t) 2 μΦ).toReal, ?_⟩
      filter_upwards [hev] with b hb
      refine (hholder b).trans ?_
      gcongr
      · exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (hmemψ t).eLpNorm_ne_top⟩

    set Nf : ℝ → ℂ := fun b => P1 t b * Complex.exp ((R₀ : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I)) -
      P2 t b * Complex.exp (-((R₀ : ℂ) * (((t - b : ℝ) : ℂ) * Complex.I))) with hNf
    have hNc : ContinuousAt Nf t := by
      simp only [hNf]
      refine ((hP1c t).continuousAt.mul ?_).sub ((hP2c t).continuousAt.mul ?_)
      · exact (Complex.continuous_exp.comp (continuous_const.mul
          ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const))).continuousAt
      · exact (Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
          ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const)))).continuousAt
    have hNt : Nf t = P1 t t - P2 t t := by
      simp only [hNf, sub_self, Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one]

    have hNle : ∃ M : ℝ, ∀ᶠ b in nhdsWithin t {t}ᶜ, ‖Nf b‖ ≤ M * |b - t| := by
      obtain ⟨K, hK⟩ := hIbdd

      have h3 : ∀ᶠ b in nhds t, ‖P3 t b‖ ≤ ‖P3 t t‖ + 1 := by
        have hc3 := ((hP3c t).continuousAt (x := t)).norm
        filter_upwards [hc3.eventually (Metric.ball_mem_nhds _ one_pos)] with b hb
        have hb' : |‖P3 t b‖ - ‖P3 t t‖| < 1 := by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hb
        linarith [le_abs_self (‖P3 t b‖ - ‖P3 t t‖)]
      have h4 : ∀ᶠ b in nhds t, ‖P4 t b‖ ≤ ‖P4 t t‖ + 1 := by
        have hc4 := ((hP4c t).continuousAt (x := t)).norm
        filter_upwards [hc4.eventually (Metric.ball_mem_nhds _ one_pos)] with b hb
        have hb' : |‖P4 t b‖ - ‖P4 t t‖| < 1 := by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hb
        linarith [le_abs_self (‖P4 t b‖ - ‖P4 t t‖)]
      have htb : ∀ᶠ b in nhds t, |t| ≤ |t + b| := by
        filter_upwards [Metric.ball_mem_nhds t (abs_pos.mpr ht0)] with b hb
        rw [Metric.mem_ball, Real.dist_eq] at hb
        have h1 := abs_sub_abs_le_abs_sub (2 * t) (t - b)
        rw [show 2 * t - (t - b) = t + b by ring, abs_mul, abs_two, abs_sub_comm] at h1
        linarith
      refine ⟨K / c + (‖P3 t t‖ + 1 + (‖P4 t t‖ + 1)) / |t|, ?_⟩
      have hall := (hK.and (h3.and (h4.and htb)))
      rw [Filter.eventually_iff_exists_mem] at hall ⊢
      obtain ⟨U, hU, hUp⟩ := hall
      refine ⟨{t}ᶜ ∩ U, inter_mem_nhdsWithin _ hU, fun b hb => ?_⟩
      obtain ⟨hbt, hbU⟩ := hb
      have hbt' : t ≠ b := fun h => hbt (h ▸ rfl)
      obtain ⟨hKb, h3b, h4b, htbb⟩ := hUp b hbU
      have htb0 : t + b ≠ 0 := fun h => by rw [h, abs_zero] at htbb; exact absurd htbb (not_le.mpr (abs_pos.mpr ht0))
      have hms := hMSb b hbt' htb0
      rw [hsum, hdiff] at hms
      have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      have hD : (((t - b : ℝ) : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (sub_ne_zero.mpr hbt')) Complex.I_ne_zero
      have hD' : (((t + b : ℝ) : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast htb0) Complex.I_ne_zero
      have he3 : ‖Complex.exp ((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I))‖ = 1 := by
        rw [show (R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I) = ((R₀ * (t + b) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      have he4 : ‖Complex.exp (-((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)))‖ = 1 := by
        rw [show -((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) = ((-(R₀ * (t + b)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      have hNf_eq : Nf b = (((t - b : ℝ) : ℂ) * Complex.I) *
          (Ib b / (c : ℂ) - (P3 t b * Complex.exp ((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) -
            P4 t b * Complex.exp (-((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)))) / (((t + b : ℝ) : ℂ) * Complex.I)) := by
        have htbc : ((t - b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hbt')
        have htbc' : ((t + b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htb0
        simp only [hNf]
        rw [hms]
        field_simp [hcne, htbc, htbc', Complex.I_ne_zero]
        ring
      have hnD : ‖((t - b : ℝ) : ℂ) * Complex.I‖ = |b - t| := by
        rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_sub_comm]
      have hnD' : ‖((t + b : ℝ) : ℂ) * Complex.I‖ = |t + b| := by
        rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      have htpos : 0 < |t| := abs_pos.mpr ht0
      have htb_pos : 0 < |t + b| := lt_of_lt_of_le htpos htbb
      rw [hNf_eq, norm_mul, hnD, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      calc ‖Ib b / (c : ℂ) - (P3 t b * Complex.exp ((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) -
              P4 t b * Complex.exp (-((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)))) / (((t + b : ℝ) : ℂ) * Complex.I)‖
          ≤ ‖Ib b / (c : ℂ)‖ + ‖(P3 t b * Complex.exp ((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) -
              P4 t b * Complex.exp (-((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)))) / (((t + b : ℝ) : ℂ) * Complex.I)‖ :=
            norm_sub_le _ _
        _ ≤ K / c + (‖P3 t t‖ + 1 + (‖P4 t t‖ + 1)) / |t| := by
            gcongr
            · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
              exact div_le_div_of_nonneg_right hKb hc.le
            · rw [norm_div, hnD']
              calc ‖P3 t b * Complex.exp ((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)) -
                      P4 t b * Complex.exp (-((R₀ : ℂ) * (((t + b : ℝ) : ℂ) * Complex.I)))‖ / |t + b|
                  ≤ (‖P3 t b‖ + ‖P4 t b‖) / |t + b| := by
                    refine div_le_div_of_nonneg_right ?_ htb_pos.le
                    refine (norm_sub_le _ _).trans ?_
                    rw [norm_mul, norm_mul, he3, he4, mul_one, mul_one]
                _ ≤ (‖P3 t t‖ + 1 + (‖P4 t t‖ + 1)) / |t| := by
                    have hnum : ‖P3 t b‖ + ‖P4 t b‖ ≤ ‖P3 t t‖ + 1 + (‖P4 t t‖ + 1) := add_le_add h3b h4b
                    calc (‖P3 t b‖ + ‖P4 t b‖) / |t + b| ≤ (‖P3 t t‖ + 1 + (‖P4 t t‖ + 1)) / |t + b| :=
                          div_le_div_of_nonneg_right hnum htb_pos.le
                      _ ≤ (‖P3 t t‖ + 1 + (‖P4 t t‖ + 1)) / |t| :=
                          div_le_div_of_nonneg_left (by positivity) htpos htbb
    obtain ⟨M, hM⟩ := hNle
    have h0 := UnitAux.eq_zero_of_continuousAt_of_norm_le_mul_abs_sub hNc hM
    rw [hNt, sub_eq_zero] at h0
    exact h0.symm

  by_cases ht0 : t ≠ 0
  · exact hmain t ht0
  · push Not at ht0
    subst ht0
    have hcl : IsClosed {a : ℝ | P2 a a = P1 a a} := isClosed_eq hP2d hP1d
    have hdense : Dense ({0}ᶜ : Set ℝ) := dense_compl_singleton 0
    have hsub : ({0}ᶜ : Set ℝ) ⊆ {a : ℝ | P2 a a = P1 a a} := fun a ha => hmain a ha
    have : (0 : ℝ) ∈ {a : ℝ | P2 a a = P1 a a} := by
      have h := hdense.closure_eq ▸ (closure_mono hsub)
      rw [hcl.closure_eq] at h
      exact h (Set.mem_univ _)
    exact this

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      (t : ℝ),
    (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F)) =
    ∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
    Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ t
  by_cases hd : μ = ν ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z
  · exact unit_dichot F hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
      Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ hd t

  push Not at hd
  obtain ⟨hne, hagree⟩ := hd

  set θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := μ⁻¹ * ν with hθ
  have hθval : ∀ z, ((θ z : ℂˣ) : ℂ) = (((μ z : ℂˣ) : ℂ))⁻¹ * ((ν z : ℂˣ) : ℂ) := by
    intro z; rw [hθ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  have hθu : IsUnitaryChar (𝓞 F) F θ := fun z => by
    rw [hθval, norm_mul, norm_inv, hμ z, hν z, inv_one, one_mul]
  have hθ1 : ∀ z ∈ NumberField.TateGlobal.normOneIdeles F, θ z = 1 := fun z hz => by
    rw [hθ, MonoidHom.mul_apply, MonoidHom.inv_apply, hagree z hz, inv_mul_cancel]
  have hθcC : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((θ z : ℂˣ) : ℂ) := by
    simp only [hθval]; exact (hμk.inv₀ fun z => Units.ne_zero _).mul hνk
  have hθc : Continuous θ := by
    refine Units.continuous_iff.mpr ⟨hθcC, ?_⟩
    simp only [Units.val_inv_eq_inv_val]
    exact hθcC.inv₀ fun z => Units.ne_zero _
  obtain ⟨t₀, ht₀⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles F θ hθc hθu hθ1
  have hν_eq : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((ν z : ℂˣ) : ℂ) =
      ((μ z : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F z : ℝ) : ℂ) ^ (Complex.I * t₀) := by
    intro z
    have h := congrArg (fun χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ => ((χ z : ℂˣ) : ℂ)) ht₀
    rw [hθval, NumberField.TateGlobal.coe_normPowChar_apply] at h
    have hμne : ((μ z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp at h
    linear_combination h

  set c : ℂ := Complex.I * (t₀ : ℂ) / 2 with hc
  have hcre : c.re = 0 := by simp [hc]
  have hαm_eq : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((αm z : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F z := fun z => rfl
  have hαpos : ∀ z : (AdeleRing (𝓞 F) F)ˣ, (0 : ℝ) < NumberField.TateGlobal.ideleNorm F z := fun z =>
    NumberField.TateGlobal.ideleNorm_pos z
  have hcpow_val : ∀ (w : ℂ) (z : (AdeleRing (𝓞 F) F)ˣ), ((cpowChar αm hαm w z : ℂˣ) : ℂ) =
      ((NumberField.TateGlobal.ideleNorm F z : ℝ) : ℂ) ^ w := fun w z => rfl
  have hbase : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((NumberField.TateGlobal.ideleNorm F z : ℝ) : ℂ) ≠ 0 := fun z => by
    exact_mod_cast (hαpos z).ne'
  set μ' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := μ * cpowChar αm hαm c with hμ'
  have hμ'val : ∀ z, ((μ' z : ℂˣ) : ℂ) = ((μ z : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F z : ℝ) : ℂ) ^ c := by
    intro z; rw [hμ', MonoidHom.mul_apply, Units.val_mul, hcpow_val]
  have hfst : ∀ s : ℂ, etaFst μ' αm hαm s = etaFst μ αm hαm (s + c) := by
    intro s; apply MonoidHom.ext; intro z; apply Units.ext
    simp only [etaFst, MonoidHom.mul_apply, Units.val_mul, hμ'val, hcpow_val]
    rw [mul_assoc, ← Complex.cpow_add _ _ (hbase z)]
    ring_nf
  have hsnd : ∀ s : ℂ, etaSnd μ' αm hαm s = etaSnd ν αm hαm (s + c) := by
    intro s; apply MonoidHom.ext; intro z; apply Units.ext
    simp only [etaSnd, MonoidHom.mul_apply, Units.val_mul, hμ'val, hcpow_val, hν_eq]
    rw [mul_assoc, mul_assoc, ← Complex.cpow_add _ _ (hbase z), ← Complex.cpow_add _ _ (hbase z)]
    congr 2
    simp only [hc]; ring

  have hμ'u : IsUnitaryChar (𝓞 F) F μ' := fun z => by
    rw [hμ'val, norm_mul, hμ z, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hαpos z), hcre, Real.rpow_zero]
  have hμ'F : IsIdeleClassChar (𝓞 F) F μ' := fun u => by
    apply Units.ext
    rw [hμ'val, hμF u, Units.val_one, one_mul, UnitAux.ideleNorm_eq_one_of_mem_range F ⟨u, rfl⟩, Complex.ofReal_one,
      Complex.one_cpow]
  have hμ'k : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ' z : ℂˣ) : ℂ) := by
    simp only [hμ'val]
    refine hμk.mul ?_
    exact Continuous.cpow (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)) continuous_const
      fun z => Complex.ofReal_mem_slitPlane.mpr (hαpos z)

  have key : ∀ b : ℝ, ((b - t₀ / 2 : ℝ) : ℂ) * Complex.I + c = (b : ℂ) * Complex.I := by
    intro b; simp only [hc]; push_cast; ring
  have hshift_re : ∀ s : ℂ, (s + c).re = s.re := fun s => by rw [Complex.add_re, hcre, add_zero]
  have hcontsh : Continuous fun s : ℂ => s + c := continuous_id.add continuous_const
  have H := unit_dichot F hαm μ' μ' hμ'u hμ'u hμ'F hμ'F hμ'k hμ'k
    (fun s => φf (s + c)) (fun s => by rw [hfst, hsnd]; exact hφf (s + c)) (fun s => hφfK (s + c)) (fun s => hφff (s + c))
    (hφfjc.comp ((hcontsh.comp continuous_fst).prodMk continuous_snd))
    (fun g => (hφfhol g).comp (differentiable_id.add_const c))
    (fun w => by obtain ⟨W, hW, hWm⟩ := hφfKu w; exact ⟨W, hW, fun s g => hWm (s + c) g⟩)
    (fun s => ψf (s + c)) (fun s => by rw [hfst, hsnd]; exact hψf (s + c)) (fun s => hψfK (s + c)) (fun s => hψff (s + c))
    (hψfjc.comp ((hcontsh.comp continuous_fst).prodMk continuous_snd))
    (fun g => (hψfhol g).comp (differentiable_id.add_const c))
    (fun w => by obtain ⟨W, hW, hWm⟩ := hψfKu w; exact ⟨W, hW, fun s g => hWm (s + c) g⟩)
    ((fun s => s + c) ⁻¹' Oφ) (fun s g => Eφ (s + c) g) (fun s g => Nφ (s + c) g)
    (by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEφ
      refine ⟨hO.preimage hcontsh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : (fun s => s + c) ⁻¹' Oφ = (fun w => w - c) '' Oφ := by
          ext s; simp only [Set.mem_preimage, Set.mem_image]
          exact ⟨fun h => ⟨s + c, h, by ring⟩, fun ⟨w, hw, hws⟩ => by rw [← hws]; simpa using hw⟩
        rw [this]; exact hOc.image _ (continuous_id.sub continuous_const).continuousOn
      · intro s hs; exact hOax (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hshift_re]; exact hs)
      · intro s hs; exact hOhalf (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hshift_re]; exact hs)
      · intro g; exact (hEa g).comp (analyticOnNhd_id.add analyticOnNhd_const) (Set.mapsTo_preimage _ _)
      · intro g; exact (hNa g).comp (analyticOnNhd_id.add analyticOnNhd_const) (Set.mapsTo_preimage _ _)
      · exact hEjc.comp ((hcontsh.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
      · exact hNjc.comp ((hcontsh.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
      · intro s hs g; exact hE (s + c) (by rw [hshift_re]; exact hs) g
      · intro s hs g; exact hN (s + c) (by rw [hshift_re]; exact hs) g)
    ((fun s => s + c) ⁻¹' Oψ) (fun s g => Eψ (s + c) g) (fun s g => Nψ (s + c) g)
    (by
      obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEψ
      refine ⟨hO.preimage hcontsh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : (fun s => s + c) ⁻¹' Oψ = (fun w => w - c) '' Oψ := by
          ext s; simp only [Set.mem_preimage, Set.mem_image]
          exact ⟨fun h => ⟨s + c, h, by ring⟩, fun ⟨w, hw, hws⟩ => by rw [← hws]; simpa using hw⟩
        rw [this]; exact hOc.image _ (continuous_id.sub continuous_const).continuousOn
      · intro s hs; exact hOax (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hshift_re]; exact hs)
      · intro s hs; exact hOhalf (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hshift_re]; exact hs)
      · intro g; exact (hEa g).comp (analyticOnNhd_id.add analyticOnNhd_const) (Set.mapsTo_preimage _ _)
      · intro g; exact (hNa g).comp (analyticOnNhd_id.add analyticOnNhd_const) (Set.mapsTo_preimage _ _)
      · exact hEjc.comp ((hcontsh.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
      · exact hNjc.comp ((hcontsh.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
      · intro s hs g; exact hE (s + c) (by rw [hshift_re]; exact hs) g
      · intro s hs g; exact hN (s + c) (by rw [hshift_re]; exact hs) g)
    (Or.inl rfl) (t - t₀ / 2)
  simp only [key] at H
  exact H

end S_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
end P2MW
export P2MW.S_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar (solution)
