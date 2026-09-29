-- Prove2me | solution 1 for AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3217b881-9830-58e9-983c-cefe0d821d35

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_SiegelVolume
import Theorems.Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory NumberField.SiegelVolume

open scoped ENNReal NNReal Topology Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

namespace SlabFDFinite

variable (K : Type) [Field K] [NumberField K]

local notation "G" => AdelicGL2 (𝓞 K) K
local notation "μH" => adelicGLHaar (Fin 2) (𝓞 K) K

scoped instance instCountableNumberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

scoped instance instCountableUnits {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Function.Injective.countable (f := fun u : Mˣ => (u : M)) Units.val_injective

scoped instance instCountableMatrix : Countable (Matrix (Fin 2) (Fin 2) K) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → K))

scoped instance instCountableGL : Countable (GL (Fin 2) K) := instCountableUnits

scoped instance instCountableRange : Countable (globalPoints (𝓞 K) K).range :=
  (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable

theorem measure_image_mul_right_centreCutSiegelSet_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ}
    (hd₁ : 0 < d₁) (d₂ : ℝ) (x : G) :
    μH ((· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
  haveI : BorelSpace G := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  rw [Set.image_mul_right, ← Measure.map_apply (measurable_mul_const x⁻¹)
    (measurableSet_centreCutSiegelSet c u d₁ d₂)]
  exact measure_centreCutSiegelSet_lt_top _ hc u hd₁ d₂

theorem measure_biUnion_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset G) :
    μH (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
  refine (measure_biUnion_finset_le T _).trans_lt ?_
  exact ENNReal.sum_lt_top.mpr fun x _ => measure_image_mul_right_centreCutSiegelSet_lt_top K hc u hd₁ d₂ x

end SlabFDFinite
p2m_reactivate "P2MW.S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain.SlabFDFinite"

open SlabFDFinite in
theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    adelicGLHaar (Fin 2) (𝓞 K) K
        (Φ₀ ∩ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) < ⊤ := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set slab : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hslab_def
  have hslab : MeasurableSet slab := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
  set Γ := (globalPoints (𝓞 K) K).range with hΓ
  set ν := μ.restrict slab with hν

  obtain ⟨T, c, hc, u, hcovall⟩ := SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov := hcovall 1 2 two_pos (by norm_num)
  obtain ⟨T', hT'⟩ := exists_finset_slab_covering_of_coversModCentre K c u 1 2 T (by norm_num) hcov α β hα
  set D' : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T', (· * x) '' centreCutSiegelSet K c u 1 2 with hD'
  have hD'fin : μ D' < ⊤ := measure_biUnion_lt_top K hc u one_pos 2 T'

  have hslab_smul : ∀ (γ : Γ) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ slab ↔ x ∈ slab := by
    rintro ⟨_, γ, rfl⟩ x
    show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x))
        ∈ Set.Icc α β ↔ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

  haveI : MeasurableConstSMul Γ (AdelicGL2 (𝓞 K) K) :=
    ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩
  haveI : SMulInvariantMeasure Γ (AdelicGL2 (𝓞 K) K) ν := by
    refine ⟨fun γ s hs => ?_⟩
    have hpre : MeasurableSet ((fun x => γ • x) ⁻¹' s) := hs.preimage (measurable_const_smul γ)
    rw [hν, Measure.restrict_apply hpre, Measure.restrict_apply hs]
    have : (fun x => γ • x) ⁻¹' s ∩ slab = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ slab) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact and_congr_right fun _ => (hslab_smul γ x).symm
    rw [this, measure_preimage_mul]

  have hcover : Φ₀ ∩ slab ⊆ ⋃ γ : Γ, γ • D' := by
    rintro g ⟨-, hg⟩
    obtain ⟨γ, hγ⟩ := hT' g hg
    refine Set.mem_iUnion.2 ⟨(⟨globalPoints (𝓞 K) K γ, γ, rfl⟩ : Γ)⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγ
  calc μ (Φ₀ ∩ slab)
      ≤ μ ((⋃ γ : Γ, γ • D') ∩ Φ₀ ∩ slab) := measure_mono fun g hg =>
          ⟨⟨hcover hg, hg.1⟩, hg.2⟩
    _ = ν ((⋃ γ : Γ, γ • D') ∩ Φ₀) := (Measure.restrict_apply' hslab).symm
    _ = ν (⋃ γ : Γ, γ • D' ∩ Φ₀) := by rw [Set.iUnion_inter]
    _ ≤ ∑' γ : Γ, ν (γ • D' ∩ Φ₀) := measure_iUnion_le _
    _ = ν D' := (hΦ₀.measure_eq_tsum D').symm
    _ ≤ μ D' := Measure.restrict_le_self _
    _ < ⊤ := hD'fin

end S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain (solution)
