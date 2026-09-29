-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a8eea5e7-f05d-519c-8fdc-1aaf19439401

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AutomorphicForm.gl2Weyl_val"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) →
    ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
    ∀ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v).indicator
          (fun _ => (1 : ℂ))) I →
      ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖ ≤
        C * ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
              Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ^
            ((1 : ℝ) / 2) := by
  obtain ⟨C, hC, A, h⟩ :=
    AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
      K L σ hgen v
  set m : ℝ := (AutomorphicForm.semiLocalHaar K L v
    (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v)).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  refine ⟨C * m ^ ((1 : ℝ) / 2) * |1 + Real.log m| ^ A,
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hm0 _)) (pow_nonneg (abs_nonneg _) A), ?_⟩
  intro δ h10 h01 hN τ' hτ' hτ1 I hI
  have key := h a δ h10 h01 hN τ' hτ' hτ1 I hI
  set X : ℝ := ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  have hpow : (1 + Real.log m) ^ A ≤ |1 + Real.log m| ^ A :=
    (le_abs_self _).trans (abs_pow _ _).le
  calc ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖
      ≤ C * (X * m) ^ ((1 : ℝ) / 2) * (1 + Real.log m) ^ A := key
    _ = C * (X ^ ((1 : ℝ) / 2) * m ^ ((1 : ℝ) / 2)) * (1 + Real.log m) ^ A := by
        rw [Real.mul_rpow hX0 hm0]
    _ ≤ C * (X ^ ((1 : ℝ) / 2) * m ^ ((1 : ℝ) / 2)) * |1 + Real.log m| ^ A :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hX0 _) (Real.rpow_nonneg hm0 _)))
    _ = C * m ^ ((1 : ℝ) / 2) * |1 + Real.log m| ^ A * X ^ ((1 : ℝ) / 2) := by ring

#print axioms solution

end S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul (solution)
