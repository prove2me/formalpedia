-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/eb24f51b-3746-5185-b00f-f6c518169de7

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn
import Theorems.Thm_AutomorphicForm_isRegularSemisimple_normString_of_diagonal_of_norm_ne
import Theorems.Thm_AutomorphicForm_norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator
import Theorems.Thm_AutomorphicForm_exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn
set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 4000000
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply AutomorphicForm.gl2Weyl_val"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

noncomputable section

namespace B5Sasm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem isCompact_doubleCoset (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsCompact (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact ((AutomorphicForm.isCompact_semiLocalIntegralSet K L v).mul isCompact_singleton).mul
    (AutomorphicForm.isCompact_semiLocalIntegralSet K L v)

theorem isOpen_doubleCoset (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsOpen (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact (AutomorphicForm.isOpen_semiLocalIntegralSet K L v).mul_left

theorem isSemiLocalTestFn_indicator_doubleCoset (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.IsSemiLocalTestFn K L v
      ((AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v).indicator
        fun _ => (1 : ℂ)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (v.adicCompletion K)
  exact ⟨AutomorphicForm.isLocallyConstant_indicator_one (isOpen_doubleCoset K L v a)
      (isCompact_doubleCoset K L v a).isClosed,
    HasCompactSupport.intro (isCompact_doubleCoset K L v a) fun _ hg => Set.indicator_of_notMem hg _⟩

end B5Sasm

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 → (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) →
    ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
    ∀ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I →
      ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖ ≤
        C * ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
              Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ^ ((1 : ℝ) / 2) := by
  classical

  obtain ⟨M, hM, s, hcover⟩ :=
    AutomorphicForm.exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn
      K L v φv hφv

  choose Cf hCf using fun a : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
    AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul
      K L σ hgen v a
  have hCf0 : ∀ a, 0 ≤ Cf a := fun a => (hCf a).1
  refine ⟨M * ∑ a ∈ s, Cf a, mul_nonneg hM (Finset.sum_nonneg fun a _ => hCf0 a), ?_⟩
  intro δ h10 h01 hN τ' hτ' hτ1 I hI

  have hσ : σ ^ Module.finrank K L = 1 := by
    have h := pow_card_eq_one (G := L ≃ₐ[K] L) (x := σ)
    rwa [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L] at h

  have hreg : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) :=
    AutomorphicForm.isRegularSemisimple_normString_of_diagonal_of_norm_ne K L σ hgen v δ h10 h01 hN

  have hex : ∀ a : GL (Fin 2) (L ⊗[K] v.adicCompletion K), ∃ J : ℂ,
      AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v).indicator
          fun _ => (1 : ℂ)) J := fun a =>
    @AutomorphicForm.exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn
      K L _ _ _ _ _ v σ δ hreg τ' hτ' _ (B5Sasm.isSemiLocalTestFn_indicator_doubleCoset K L v a)
  choose J hJ using hex

  have hdom : ‖I‖ ≤ ∑ a ∈ s, M * ‖J a‖ :=
    AutomorphicForm.norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator
      K L v σ hσ δ hreg τ' hτ' φv hφv (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) s
      (fun a => AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v)
      (fun a _ => B5Sasm.isOpen_doubleCoset K L v a) (fun a _ => B5Sasm.isCompact_doubleCoset K L v a)
      (fun _ => M) (fun _ _ => hM)
      (fun g => by rw [← Finset.mul_sum]; exact hcover g)
      I hI J (fun a _ => hJ a)

  set D : ℝ := ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ with hD
  set X : ℝ := ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ^
        ((1 : ℝ) / 2) with hX
  have hD0 : 0 ≤ D := norm_nonneg _
  have hJb : ∀ a, D * ‖J a‖ ≤ Cf a * X := fun a =>
    (hCf a).2 δ h10 h01 hN τ' hτ' hτ1 (J a) (hJ a)
  calc D * ‖I‖ ≤ D * ∑ a ∈ s, M * ‖J a‖ := mul_le_mul_of_nonneg_left hdom hD0
    _ = ∑ a ∈ s, M * (D * ‖J a‖) := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
    _ ≤ ∑ a ∈ s, M * (Cf a * X) := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hJb a) hM
    _ = M * (∑ a ∈ s, Cf a) * X := by rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; ring

#print axioms solution

end
end S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn (solution)
