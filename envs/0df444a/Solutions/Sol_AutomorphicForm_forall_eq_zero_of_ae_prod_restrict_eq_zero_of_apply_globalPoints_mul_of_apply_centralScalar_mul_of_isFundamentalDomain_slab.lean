-- Prove2me | solution 1 for AutomorphicForm.forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9183c362-d419-534f-91a8-68b40d7bf51b

import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

theorem PW.step (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * g) = f g)
    (hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), f g = 0 → f (centralScalar (𝓞 K) K z * g) = 0)
    (hae : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ), f g = 0) :
    ∀ g : AdelicGL2 (𝓞 K) K, f g = 0 := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := by unfold Matrix; infer_instance
  haveI : Countable (GL (Fin 2) K) := Function.Injective.countable Units.val_injective

  have hU : IsOpen {g : AdelicGL2 (𝓞 K) K | f g ≠ 0} := isOpen_ne_fun hf continuous_const
  have hUΦ : adelicGLHaar (Fin 2) (𝓞 K) K ({g : AdelicGL2 (𝓞 K) K | f g ≠ 0} ∩ Φ) = 0 :=
    Measure.measure_inter_eq_zero_of_restrict (ae_iff.1 hae)

  have hcov : adelicGLHaar (Fin 2) (𝓞 K) K
      ({g : AdelicGL2 (𝓞 K) K | ¬ ∃ γ : (globalPoints (𝓞 K) K).range, γ • g ∈ Φ} ∩
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) = 0 :=
    Measure.measure_inter_eq_zero_of_restrict (ae_iff.1 hΦ.ae_covers)

  have hpiece : ∀ γ : GL (Fin 2) K, adelicGLHaar (Fin 2) (𝓞 K) K
      ((fun h => globalPoints (𝓞 K) K γ * h) ⁻¹' ({g : AdelicGL2 (𝓞 K) K | f g ≠ 0} ∩ Φ)) = 0 := fun γ => by
    rw [measure_preimage_mul]; exact hUΦ

  have hUS : adelicGLHaar (Fin 2) (𝓞 K) K ({g : AdelicGL2 (𝓞 K) K | f g ≠ 0} ∩
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) = 0 := by
    refine measure_mono_null ?_ (measure_union_null hcov (measure_iUnion_null_iff.2 hpiece))
    rintro g ⟨hgU, hgS⟩
    by_cases hex : ∃ γ : (globalPoints (𝓞 K) K).range, γ • g ∈ Φ
    · obtain ⟨⟨γ', hγ'⟩, hγΦ⟩ := hex
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hγ'
      refine Or.inr (Set.mem_iUnion.2 ⟨γ, ?_, ?_⟩)
      · show f (globalPoints (𝓞 K) K γ * g) ≠ 0
        rw [hΓ]; exact hgU
      · simpa [Subgroup.mk_smul, smul_eq_mul] using hγΦ
    · exact Or.inl ⟨hex, hgS⟩

  have hSo : IsOpen {g : AdelicGL2 (𝓞 K) K |
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} :=
    isOpen_Ioo.preimage (NumberField.TateGlobal.continuous_ideleNorm_det K)
  have hempty : {g : AdelicGL2 (𝓞 K) K | f g ≠ 0} ∩
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} = ∅ :=
    ((hU.inter hSo).measure_eq_zero_iff (adelicGLHaar (Fin 2) (𝓞 K) K)).1
      (measure_mono_null (Set.inter_subset_inter_right _ fun g
        (hg : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β) =>
        show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β from
          Set.Ioo_subset_Icc_self hg) hUS)
  have hslab : ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β → f g = 0 := by
    intro g hg
    by_contra h
    exact (Set.eq_empty_iff_forall_notMem.1 hempty g) ⟨h, hg⟩

  intro g
  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hr : 0 < ((α + β) / 2) / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
    div_pos (by linarith) hd
  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K
    (Real.sqrt (((α + β) / 2) / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)))
    (Real.sqrt_pos.2 hr)
  have hzg : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * g)) =
      (α + β) / 2 := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul,
      show centralScalar (𝓞 K) K z = Matrix.GeneralLinearGroup.scalar (Fin 2) z from rfl,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two, NumberField.TateGlobal.ideleNorm_mul, hz,
      Real.mul_self_sqrt hr.le, div_mul_cancel₀ _ hd.ne']
  have h1 : f (centralScalar (𝓞 K) K z * g) = 0 :=
    hslab _ (by rw [hzg]; exact ⟨by linarith, by linarith⟩)
  have h2 := hZ z⁻¹ _ h1
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h2

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (F : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K → ℂ)
    (hFx : ∀ y : AdelicGL2 (𝓞 K) K, Continuous fun x : AdelicGL2 (𝓞 K) K => F x y)
    (hFy : ∀ x : AdelicGL2 (𝓞 K) K, Continuous fun y : AdelicGL2 (𝓞 K) K => F x y)
    (hΓx : ∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K), F (globalPoints (𝓞 K) K γ * x) y = F x y)
    (hΓy : ∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K), F x (globalPoints (𝓞 K) K γ * y) = F x y)
    (hZx : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K), F x y = 0 → F (centralScalar (𝓞 K) K z * x) y = 0)
    (hZy : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K), F x y = 0 → F x (centralScalar (𝓞 K) K z * y) = 0)
    (hae : ∀ᵐ p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K
      ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ)),
      F p.1 p.2 = 0) :
    ∀ x y : AdelicGL2 (𝓞 K) K, F x y = 0 := by

  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K α β hα hαβ Φ hΦ
    rwa [Set.inter_eq_left.mpr hΦs] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := isFiniteMeasure_restrict.2 hfin.ne
  have h1 : ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ),
      ∀ᵐ y ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ), F x y = 0 :=
    Measure.ae_ae_of_ae_prod hae

  have h2 : ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ), ∀ y : AdelicGL2 (𝓞 K) K, F x y = 0 :=
    h1.mono fun x hx => PW.step K α β hα hαβ Φ hΦ (F x) (hFy x) (fun γ y => hΓy γ x y)
      (fun z y h => hZy z x y h) hx

  intro x y
  have h3 : ∀ᵐ x' ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ), F x' y = 0 := h2.mono fun x' hx' => hx' y
  exact PW.step K α β hα hαβ Φ hΦ (fun x' => F x' y) (hFx y) (fun γ x' => hΓx γ x' y)
    (fun z x' h => hZx z x' y h) h3 x

end S_AutomorphicForm_forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab (solution)
