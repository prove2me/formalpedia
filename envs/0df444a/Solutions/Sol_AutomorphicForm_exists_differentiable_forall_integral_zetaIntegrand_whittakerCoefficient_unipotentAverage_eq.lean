-- Prove2me | solution 1 for AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/12487680-08ac-5916-8b5d-ce6319eeedad

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_continuous_unipotentAverage_rightConv
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
import Theorems.Thm_AutomorphicForm_exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

noncomputable section

namespace Ws1
namespace C5bB

open scoped NNReal ENNReal

section Unfold

variable {G : Type*} {α : Type*} [Group G] [Countable G] [MulAction G α]
  [MeasurableSpace α] {μ : Measure α} [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

omit [Countable G] in
theorem qmp_smul_restrict (g : G) (D : Set α) :
    Measure.QuasiMeasurePreserving (fun x : α => g • x) (μ.restrict D) μ := by
  have h1 : Measure.QuasiMeasurePreserving (fun x : α => g • x) μ μ :=
    (measurePreserving_smul g μ).quasiMeasurePreserving
  exact h1.mono_left Measure.restrict_le_self.absolutelyContinuous

theorem lintegral_restrict_tsum_smul {D : Set α} (hD : IsFundamentalDomain G D μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x in D, ∑' g : G, f (g • x) ∂μ = ∫⁻ x, f x ∂μ := by
  have hcomp : ∀ g : G, AEMeasurable (fun x => f (g • x)) (μ.restrict D) := fun g =>
    hf.comp_quasiMeasurePreserving (qmp_smul_restrict g D)
  rw [lintegral_tsum hcomp]
  have hreindex :
      (∑' g : G, ∫⁻ x in D, f (g • x) ∂μ) = ∑' g : G, ∫⁻ x in D, f (g⁻¹ • x) ∂μ :=
    ((Equiv.inv G).tsum_eq fun g : G => ∫⁻ x in D, f (g • x) ∂μ).symm
  rw [hreindex, ← hD.lintegral_eq_tsum' f]

theorem integral_eq_setIntegral_tsum_smul {D : Set α} (hD : IsFundamentalDomain G D μ)
    {f : α → ℂ} (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x in D, ∑' g : G, f (g • x) ∂μ := by
  have hsm : ∀ g : G, AEStronglyMeasurable (fun x => f (g • x)) (μ.restrict D) := fun g =>
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (qmp_smul_restrict g D)
  have hbound : (∑' g : G, ∫⁻ x in D, ‖f (g • x)‖ₑ ∂μ) ≠ ⊤ := by
    have hnorm : AEMeasurable (fun x => ‖f x‖ₑ) μ := hf.aestronglyMeasurable.enorm
    have hcomp : ∀ g : G, AEMeasurable (fun x => ‖f (g • x)‖ₑ) (μ.restrict D) :=
      fun g => hnorm.comp_quasiMeasurePreserving (qmp_smul_restrict g D)
    have h1 : (∑' g : G, ∫⁻ x in D, ‖f (g • x)‖ₑ ∂μ)
        = ∫⁻ x in D, ∑' g : G, ‖f (g • x)‖ₑ ∂μ := (lintegral_tsum hcomp).symm
    rw [h1, lintegral_restrict_tsum_smul hD hnorm]
    exact hf.2.ne
  calc ∫ x, f x ∂μ = ∑' g : G, ∫ x in D, f (g⁻¹ • x) ∂μ := hD.integral_eq_tsum' f hf
    _ = ∑' g : G, ∫ x in D, f (g • x) ∂μ :=
        (Equiv.inv G).tsum_eq fun g : G => ∫ x in D, f (g • x) ∂μ
    _ = ∫ x in D, ∑' g : G, f (g • x) ∂μ := (integral_tsum hsm hbound).symm

end Unfold

section Misc

open NumberField NumberField.TateGlobal NumberField.AdelicLevel

theorem min_pow_mul_rpow_le {x t : ℝ} (hx : 0 < x) {k N : ℕ} (hN : |t| ≤ N) :
    min x x⁻¹ ^ (k + N) * x ^ t ≤ min x x⁻¹ ^ k := by
  have hm0 : 0 ≤ min x x⁻¹ := le_min hx.le (inv_pos.mpr hx).le
  suffices h : min x x⁻¹ ^ N * x ^ t ≤ 1 by
    calc min x x⁻¹ ^ (k + N) * x ^ t = min x x⁻¹ ^ k * (min x x⁻¹ ^ N * x ^ t) := by rw [pow_add]; ring
      _ ≤ min x x⁻¹ ^ k * 1 := mul_le_mul_of_nonneg_left h (pow_nonneg hm0 k)
      _ = _ := mul_one _
  rcases le_or_gt 1 x with h1 | h1
  · have hmin : min x x⁻¹ = x⁻¹ := min_eq_right (le_trans (inv_le_one_of_one_le₀ h1) h1)
    rw [hmin, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith [le_abs_self t])
  · have hmin : min x x⁻¹ = x := min_eq_left (le_trans h1.le (one_le_inv_iff₀.mpr ⟨hx, h1.le⟩))
    rw [hmin, ← Real.rpow_natCast, ← Real.rpow_add hx]
    exact Real.rpow_le_one hx.le h1.le (by linarith [neg_abs_le t])

theorem continuous_diagOne {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (diagOne : Aˣ → GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h : (fun a : Aˣ => ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) =
        fun a : Aˣ => Matrix.diagonal ![(a : A), 1] := rfl
    rw [show (Units.val ∘ ⇑diagOne : Aˣ → Matrix (Fin 2) (Fin 2) A) = fun a : Aˣ => Matrix.diagonal ![(a : A), 1]
      from h]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using Units.continuous_val
    · simpa using continuous_const
  · have h : (fun a : Aˣ => (((diagOne a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) =
        fun a : Aˣ => Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1] := by
      funext a
      rw [← map_inv]
      rfl
    rw [show (fun u : Aˣ => ((diagOne u)⁻¹ : GL (Fin 2) A).val) = fun a : Aˣ => Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1]
      from h]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using Units.continuous_coe_inv
    · simpa using continuous_const

theorem ideleNorm_principal (F : Type) [Field F] [NumberField F]
    (γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) :
    ideleNorm F (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  obtain ⟨_, a, rfl⟩ := γ
  borelize (AdeleRing (𝓞 F) F)
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  unfold ideleNorm
  simp only [RingHom.toMonoidHom_eq_coe] at h ⊢
  rw [h]
  rfl

end Misc

end Ws1.C5bB

end

open scoped Pointwise in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ f (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ σ₁ : ℝ, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧
      ∀ s : ℂ, σ₁ < s.re →
        Integrable (zetaIntegrand
          (fun g => whittakerCoefficient F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s) ν ∧
        (∫ a, zetaIntegrand
          (fun g => whittakerCoefficient F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s a ∂ν) = Z s := by
  classical

  obtain ⟨σ₁, hint⟩ :=
    AutomorphicForm.exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage
      F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf B hB Φ hΦ ψ hψ χ hχ hχc ν
  have hΦc : Continuous Φ :=
    AutomorphicForm.continuous_unipotentAverage_rightConv F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf B hB Φ hΦ
  have hexp := fun a =>
    AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
      F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf B hB Φ hΦ ψ hψ a
  obtain ⟨D, hDm, hFD, htemp⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow F ν
  obtain ⟨t, ht⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F χ hχ hχc

  have hN0 : ∀ a : (AdeleRing (𝓞 F) F)ˣ, 0 < ideleNorm F a := fun a => ideleNorm_pos a
  have hNΓ : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F), ideleNorm F (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 :=
    Ws1.C5bB.ideleNorm_principal F
  have hχΓ : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F), χ (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
    rintro ⟨_, a, rfl⟩
    exact hχ a

  have hdecΦ : ∀ k : ℕ, ∃ Cst : ℝ, ∀ a : (AdeleRing (𝓞 F) F)ˣ,
      ‖Φ (diagOne a)‖ ≤ Cst * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k := by
    intro k
    obtain ⟨Cst, hC⟩ :=
      AutomorphicForm.exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
        F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf B hB Φ hΦ {1} isCompact_singleton k
    exact ⟨Cst, fun a => by simpa only [mul_one] using hC a 1 rfl⟩

  obtain ⟨h, hhdef⟩ : ∃ h : (AdeleRing (𝓞 F) F)ˣ → ℂ, h = fun a => Φ (diagOne a) * ((χ a : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hhm : AEStronglyMeasurable h (ν.restrict D) := by
    rw [hhdef]
    exact ((hΦc.comp Ws1.C5bB.continuous_diagOne).mul
      (Units.continuous_val.comp hχc)).aestronglyMeasurable
  have hhdec : ∀ k : ℕ, ∃ C : ℝ, ∀ a ∈ D, ‖h a‖ ≤ C * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k := by
    intro k
    obtain ⟨Cst, hC⟩ := hdecΦ (k + ⌈|t|⌉₊)
    refine ⟨max Cst 0, fun a _ => ?_⟩
    have hm0 : 0 ≤ min (ideleNorm F a) (ideleNorm F a)⁻¹ := le_min (hN0 a).le (inv_pos.mpr (hN0 a)).le
    rw [hhdef]
    dsimp only
    rw [norm_mul, ht a]
    calc ‖Φ (diagOne a)‖ * ideleNorm F a ^ t
        ≤ (max Cst 0 * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ (k + ⌈|t|⌉₊)) * ideleNorm F a ^ t :=
          mul_le_mul_of_nonneg_right ((hC a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (pow_nonneg hm0 _))) (Real.rpow_nonneg (hN0 a).le _)
      _ = max Cst 0 * (min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ (k + ⌈|t|⌉₊) * ideleNorm F a ^ t) := by ring
      _ ≤ max Cst 0 * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k :=
          mul_le_mul_of_nonneg_left (Ws1.C5bB.min_pow_mul_rpow_le (hN0 a) (Nat.le_ceil _)) (le_max_right _ _)
  obtain ⟨-, hK1diff⟩ :=
    NumberField.TateGlobal.integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow
      F ν D hDm htemp h hhm hhdec

  haveI : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  haveI : Countable ↥(M4aHerbrand.principalIdeles (𝓞 F) F) := by
    have hFu : Countable Fˣ :=
      Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
    exact (MonoidHom.rangeRestrict_surjective
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F))).countable

  refine ⟨σ₁, fun s => ∫ a in D, h a * ((ideleNorm F a : ℝ) : ℂ) ^ (s - 1) ∂ν, ?_, fun s hs => ⟨hint s hs, ?_⟩⟩
  · exact hK1diff.comp (differentiable_id.sub_const 1)
  · rw [Ws1.C5bB.integral_eq_setIntegral_tsum_smul hFD (hint s hs)]
    refine setIntegral_congr_fun hDm fun a _ => ?_
    have hterm : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
        zetaIntegrand (fun g => whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s (γ • a)
          = whittakerCoefficient F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne ((γ : (AdeleRing (𝓞 F) F)ˣ) * a))
            * (((χ a : ℂˣ) : ℂ) * ((ideleNorm F a : ℝ) : ℂ) ^ (s - 1)) := by
      intro γ
      rw [Subgroup.smul_def, smul_eq_mul]
      simp only [zetaIntegrand]
      rw [map_mul χ (γ : (AdeleRing (𝓞 F) F)ˣ) a, hχΓ γ, one_mul, ideleNorm_mul, hNΓ γ, one_mul]
      ring
    simp_rw [hterm]
    rw [tsum_mul_right, (hexp a).tsum_eq, hhdef]
    ring

end S_AutomorphicForm_exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq (solution)
