-- Prove2me | solution 1 for AutomorphicForm.exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/18944d79-60ce-546d-995e-3f35c7d02632

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_AutomorphicForm_exists_polynomial_bound_eulerProduct_mul_intertwining_continuation_of_isInducedSection
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass"
p2m_attr_erase "instance" "SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed UnramifiedWhittaker.ProductMeasureData.mk.injEq"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

namespace RegularizedIntertwiningBound

private theorem quot_val_mul_inv (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((μ * ν⁻¹) x : ℂˣ) : ℂ) = ((μ x : ℂˣ) : ℂ) * (((ν x : ℂˣ) : ℂ))⁻¹ := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]

private theorem quot_continuous_of_continuous_val (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχ : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) : Continuous χ :=
  Units.isEmbedding_val₀.continuous_iff.2 hχ

private theorem isUnitaryChar_mul_inv_and_exists_mem_normOneIdeles_ne_one_of_forall_ne_normPowChar
    (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (hfree : ∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) :
    IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) ∧ IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) ∧ Continuous (μ * ν⁻¹) ∧
      ∃ x ∈ NumberField.TateGlobal.normOneIdeles F, (μ * ν⁻¹) x ≠ 1 := by
  have hunit : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := by
    intro x
    rw [quot_val_mul_inv F μ ν x, norm_mul, norm_inv, hμ x, hν x, inv_one, mul_one]
  have hcont : Continuous (μ * ν⁻¹) :=
    quot_continuous_of_continuous_val F (μ * ν⁻¹)
      ((hμc.mul (hνc.inv₀ fun x => Units.ne_zero (ν x))).congr fun x => (quot_val_mul_inv F μ ν x).symm)
  refine ⟨hunit, ?_, hcont, ?_⟩
  · intro u
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμic u, hνic u, inv_one, mul_one]
  · by_contra hcon
    obtain ⟨t, ht⟩ :=
      NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles F (μ * ν⁻¹) hcont hunit
        (fun x hx => by
          by_contra hne
          exact hcon ⟨x, hx, hne⟩)
    exact hfree t ht

end RegularizedIntertwiningBound

namespace RegularizedIntertwiningBound

private theorem zeta_one_lt_absNorm (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h2 : 1 < Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h2

private theorem zeta_absNorm_ne_zero (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h := zeta_one_lt_absNorm F v
  exact_mod_cast (zero_lt_one.trans h).ne'

private theorem zeta_one_sub_cpow_ne_zero (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {w : ℂ} (hw : 0 < w.re) :
    (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w) ≠ 0 := by
  have h1 := zeta_one_lt_absNorm F v
  have hlt : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (zero_lt_one.trans h1)), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

private theorem zeta_differentiable_factor (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (c : ℂ) :
    Differentiable ℂ fun s : ℂ => (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + c)) :=
  (differentiable_const (1 : ℂ)).sub
    (((differentiable_id.add_const c).neg).const_cpow (Or.inl (zeta_absNorm_ne_zero F v)))

private theorem zeta_differentiable_prod (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (c : ℂ) :
    Differentiable ℂ fun s : ℂ => ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + c))) := by
  classical
  refine Finset.induction_on T ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiable_const _
  · intro v T hv ih
    simp only [Finset.prod_insert hv]
    exact (zeta_differentiable_factor F v c).mul ih

open scoped Classical in

private theorem exists_differentiable_eq_sub_mul_partialEulerProduct_normPowChar
    (F : Type) [Field F] [NumberField F] (τ : ℝ) (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T},
          (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (NumberField.TateGlobal.normPowChar F τ) v.1 then
                (((NumberField.TateGlobal.normPowChar F τ) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ)
              else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  obtain ⟨R, hRd, -, hRζ, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero F
  refine ⟨fun s => R (s + (τ : ℂ) * Complex.I) *
      ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + (τ : ℂ) * Complex.I))), ?_, ?_⟩
  · exact (hRd.comp (differentiable_id.add_const _)).mul (zeta_differentiable_prod F T _)
  · intro s hs
    show R (s + (τ : ℂ) * Complex.I) *
        ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + (τ : ℂ) * Complex.I))) = _
    set w : ℂ := s + (τ : ℂ) * Complex.I with hw
    have hτre : ((τ : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have hwre : 1 < w.re := by
      rw [hw, Complex.add_re, hτre, add_zero]
      exact hs
    have hws : w - 1 = s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) := by
      rw [hw]
      ring
    set f : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℂ :=
      fun v => ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ with hf
    have hE : HasProd f (NumberField.dedekindZeta F w) :=
      NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F w hwre
    have hM : Multipliable fun v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T} => f v.1 := by
      have h := (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F T
        (fun _ => (1 : ℂ)) (fun _ => by simp)).1 w hwre
      simp only [one_mul] at h
      exact h
    have hb : HasProd (f ∘ (↑) : ((↑T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))ᶜ :
        Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) → ℂ)
        (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1) :=
      hM.hasProd
    have hsplit : NumberField.dedekindZeta F w =
        (∏ v ∈ T, f v) * ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 :=
      hE.unique ((Finset.hasProd T f).mul_compl hb)
    have hT : (∏ v ∈ T, f v) * ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [hf]
      exact inv_mul_cancel₀ (zeta_one_sub_cpow_ne_zero F v (zero_lt_one.trans hwre))
    have hP : ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 =
        NumberField.dedekindZeta F w * ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) := by
      calc ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1
          = (∏ v ∈ T, f v) * (∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) *
              ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 := by rw [hT, one_mul]
        _ = NumberField.dedekindZeta F w *
              ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) := by
            rw [hsplit]
            ring
    have hcoef : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        (if NumberField.TateGlobal.IsUnramifiedCharAt (NumberField.TateGlobal.normPowChar F τ) v then
            (((NumberField.TateGlobal.normPowChar F τ) (AutomorphicForm.uniformizerIdele F v) : ℂˣ) : ℂ)
          else 0) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) =
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w) := by
      intro v
      rw [NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg F τ v,
        ← Complex.cpow_add _ _ (zeta_absNorm_ne_zero F v), hw]
      congr 1
      ring
    calc R w * ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))
        = (w - 1) * NumberField.dedekindZeta F w *
            ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) := by rw [hRζ w hwre]
      _ = (w - 1) * ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 := by
            rw [hP]
            ring
      _ = _ := by
            rw [hws]
            congr 1
            exact tprod_congr fun v => by rw [hcoef v.1]

end RegularizedIntertwiningBound

namespace RegularizedIntertwiningBound

private theorem eq_of_normPowChar_eq (F : Type) [Field F] [NumberField F] {τ τ' : ℝ}
    (h : NumberField.TateGlobal.normPowChar F τ = NumberField.TateGlobal.normPowChar F τ') : τ = τ' := by
  by_contra hne
  have hd : τ - τ' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one F
    (Real.exp (Real.pi / (τ - τ'))) (Real.exp_pos _)
  have h1 : ((NumberField.TateGlobal.normPowChar F τ z : ℂˣ) : ℂ) =
      ((NumberField.TateGlobal.normPowChar F τ' z : ℂˣ) : ℂ) := by
    rw [h]
  rw [NumberField.TateGlobal.coe_normPowChar_apply, NumberField.TateGlobal.coe_normPowChar_apply, hz] at h1
  have hr0 : ((Real.exp (Real.pi / (τ - τ')) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hlog : Complex.log ((Real.exp (Real.pi / (τ - τ')) : ℝ) : ℂ) = ((Real.pi / (τ - τ') : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hr0, hlog] at h1
  have h2 : Complex.exp (((Real.pi / (τ - τ') : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) -
      ((Real.pi / (τ - τ') : ℝ) : ℂ) * (Complex.I * (τ' : ℂ))) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have hpi : Real.pi / (τ - τ') * (τ - τ') = Real.pi := div_mul_cancel₀ _ hd
  have h3 : ((Real.pi / (τ - τ') : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) -
      ((Real.pi / (τ - τ') : ℝ) : ℂ) * (Complex.I * (τ' : ℂ)) = (Real.pi : ℂ) * Complex.I := by
    conv_rhs => rw [← hpi]
    push_cast
    ring
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

private theorem norm_le_of_norm_mul_le_of_one_le {c m : ℂ} {t S A₁ A₂ : ℝ} {N₁ N₂ : ℕ} (ht : 0 ≤ t)
    (hA₁ : 0 ≤ A₁) (hlow : 1 ≤ A₂ * (1 + 2 * t) ^ N₂ * ‖c‖) (hup : ‖m * c‖ ≤ A₁ * (1 + t) ^ N₁ * S) :
    ‖m‖ ≤ A₁ * |A₂| * 2 ^ N₂ * (1 + t) ^ (N₁ + N₂) * S := by
  have h1 : ‖m‖ ≤ A₂ * (1 + 2 * t) ^ N₂ * ‖c‖ * ‖m‖ := le_mul_of_one_le_left (norm_nonneg m) hlow
  have h2 : A₂ * (1 + 2 * t) ^ N₂ * ‖c‖ * ‖m‖ = A₂ * (1 + 2 * t) ^ N₂ * ‖m * c‖ := by
    rw [norm_mul]
    ring
  have h12 : (1 + 2 * t) ^ N₂ ≤ (2 * (1 + t)) ^ N₂ := pow_le_pow_left₀ (by linarith) (by linarith) N₂
  have hfac : A₂ * (1 + 2 * t) ^ N₂ ≤ |A₂| * (2 * (1 + t)) ^ N₂ :=
    mul_le_mul (le_abs_self A₂) h12 (pow_nonneg (by linarith) _) (abs_nonneg _)
  have h3 : A₂ * (1 + 2 * t) ^ N₂ * ‖m * c‖ ≤ |A₂| * (2 * (1 + t)) ^ N₂ * (A₁ * (1 + t) ^ N₁ * S) :=
    mul_le_mul hfac hup (norm_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _))
  have h4 : |A₂| * (2 * (1 + t)) ^ N₂ * (A₁ * (1 + t) ^ N₁ * S) =
      A₁ * |A₂| * 2 ^ N₂ * (1 + t) ^ (N₁ + N₂) * S := by
    rw [mul_pow, pow_add]
    ring
  calc ‖m‖ ≤ A₂ * (1 + 2 * t) ^ N₂ * ‖c‖ * ‖m‖ := h1
    _ = A₂ * (1 + 2 * t) ^ N₂ * ‖m * c‖ := h2
    _ ≤ |A₂| * (2 * (1 + t)) ^ N₂ * (A₁ * (1 + t) ^ N₁ * S) := h3
    _ = A₁ * |A₂| * 2 ^ N₂ * (1 + t) ^ (N₁ + N₂) * S := h4

end RegularizedIntertwiningBound

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
            Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g))
      (σ₀ : ℝ) (_hσ₀ : 0 < σ₀),
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ →
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
        (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
          ‖(s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Mc s k‖ ≤
            A * (1 + |s.im|) ^ N * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) ∧
        ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
          ‖Mc s k‖ ≤
            A * (1 + |s.im|) ^ N * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) := by
  intro α hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφhol hμc hνc hφKu Mc hMc σ₀ hσ₀
  have hC := AutomorphicForm.exists_polynomial_bound_eulerProduct_mul_intertwining_continuation_of_isInducedSection F
    hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφhol hμc hνc hφKu Mc hMc σ₀ hσ₀
  have hre : ∀ s : ℂ, (2 * s + 1).re = 2 * s.re + 1 := by
    intro s
    simp [Complex.add_re, Complex.mul_re]
  have him : ∀ s : ℂ, |(2 * s + 1).im| = 2 * |s.im| := by
    intro s
    have h : (2 * s + 1).im = 2 * s.im := by
      simp [Complex.add_im, Complex.mul_im]
    rw [h, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  by_cases hpole : ∃ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ
  · obtain ⟨τ, hτ⟩ := hpole
    obtain ⟨Q, hQ, hQE⟩ :=
      RegularizedIntertwiningBound.exists_differentiable_eq_sub_mul_partialEulerProduct_normPowChar F τ ∅
    obtain ⟨A₁, hA₁, N₁, hC₁⟩ := hC.1 τ hτ Q hQ (by
      intro w hw
      rw [hτ]
      exact hQE w hw)
    obtain ⟨A₂, N₂, hP⟩ :=
      NumberField.TateGlobal.exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar F τ ∅ Q hQ hQE
    refine ⟨A₁ * |A₂| * 2 ^ N₂, mul_nonneg (mul_nonneg hA₁ (abs_nonneg _)) (pow_nonneg (by norm_num) _),
      N₁ + N₂, ?_⟩
    intro s hs₀ hsσ k hk
    refine ⟨?_, ?_⟩
    · intro τ' hτ'
      have hττ' : τ' = τ := RegularizedIntertwiningBound.eq_of_normPowChar_eq F (hτ'.symm.trans hτ)
      rw [hττ']
      have hlow := hP (2 * s + 1) (by
        rw [hre]
        linarith)
      rw [him] at hlow
      have hup := hC₁ s hs₀ hsσ k hk
      rw [mul_right_comm _ (Q (2 * s + 1)) (Mc s k)] at hup
      exact RegularizedIntertwiningBound.norm_le_of_norm_mul_le_of_one_le (abs_nonneg _) hA₁ hlow hup
    · intro hfree
      exact absurd hτ (hfree τ)
  · have hfree : ∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ := fun τ hτ => hpole ⟨τ, hτ⟩
    obtain ⟨hu, hic, hc, hne⟩ :=
      RegularizedIntertwiningBound.isUnitaryChar_mul_inv_and_exists_mem_normOneIdeles_ne_one_of_forall_ne_normPowChar
        F μ ν hμ hν hμic hνic hμc hνc hfree
    obtain ⟨L, hL, hLE⟩ :=
      NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one F
        (μ * ν⁻¹) hic hc hu hne ∅
    obtain ⟨A₁, hA₁, N₁, hC₂⟩ := hC.2 hfree L hL hLE
    obtain ⟨A₂, N₂, hE⟩ :=
      NumberField.TateGlobal.exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct F
        (μ * ν⁻¹) hic hc hu hne ∅ L hL hLE
    refine ⟨A₁ * |A₂| * 2 ^ N₂, mul_nonneg (mul_nonneg hA₁ (abs_nonneg _)) (pow_nonneg (by norm_num) _),
      N₁ + N₂, ?_⟩
    intro s hs₀ hsσ k hk
    refine ⟨fun τ hτ => absurd hτ (hfree τ), fun _ => ?_⟩
    have hlow := hE (2 * s + 1) (by
      rw [hre]
      linarith)
    rw [him] at hlow
    have hup := hC₂ s hs₀ hsσ k hk
    rw [mul_comm (L (2 * s + 1)) (Mc s k)] at hup
    exact RegularizedIntertwiningBound.norm_le_of_norm_mul_le_of_one_le (abs_nonneg _) hA₁ hlow hup

end S_AutomorphicForm_exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection
end P2MW
export P2MW.S_AutomorphicForm_exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection (solution)
