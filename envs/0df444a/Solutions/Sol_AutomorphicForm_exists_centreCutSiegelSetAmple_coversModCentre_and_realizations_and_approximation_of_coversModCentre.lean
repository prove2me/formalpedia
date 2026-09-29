-- Prove2me | solution 1 for AutomorphicForm.exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/62d2bded-4e06-5b1f-b141-14eb3f69c59b

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_SiegelReduction
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Theorems.Thm_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Mathlib.MeasureTheory.Function.L2Space
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Mathlib.Algebra.BigOperators.Finprod
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
import Theorems.Thm_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_SiegelVolume
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.AdelicVolume"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGenuineCuspRealizationAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction SiegelCoordinates.localHeight_upper_entries_mul finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff LsXiMemberAt lsXiMemberAt_iff unipotentGL2 constantTermIntegrand constantTerm IsCuspidalFn SmoothCuspRealizationAt HeckeEigensystem SiegelReduction.archComponent_globalPoints_apply SiegelReduction.glFin_globalPoints_apply SiegelReduction.norm_coe_completion SiegelReduction.det_archComponent_globalPoints SiegelReduction.archHeight_globalPoints_mul_mul_archHeight_le SiegelReduction.mem_range_of_coe_mem_integralFiniteAdeles SiegelReduction.one_le_abs_norm_of_mem_range SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre exists_coversModCentre_centreCutSiegelSetAmple rightConv rightConv_apply archEntries archEntries_apply IsArchTestFactor IsFinTestFactor IsFactorizableTestFn exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc ideleNorm_det_globalPoints peterssonIntegral continuous_unipotentGL2 continuous_and_hasCompactSupport_of_isFactorizableTestFn isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre continuous_rightConv_and_contDiff_of_isFactorizableTestFn exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple"
namespace WindowPassage
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K]

section Transport

variable {D D' : Set (AdelicGL2 (𝓞 K) K)} {U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)}
  {gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K} {B : Set (AdeleRing (𝓞 K) K)}
  {Φ : HeckeEigensystem K ℂ}

private theorem memLp_toFun (R : SmoothCuspRealizationAt K (productionPinsOf K D U gen B) Φ) :
    MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D) := by
  have h : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
      R.centralChar D R.toFun := R.smoothCusp.1.1
  exact ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp h).2

private def transport (R : SmoothCuspRealizationAt K (productionPinsOf K D U gen B) Φ)
    (hL2 : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D')) :
    SmoothCuspRealizationAt K (productionPinsOf K D' U gen B) Φ where
  toFun := R.toFun
  exists_ne_zero := R.exists_ne_zero
  centralChar := R.centralChar
  smoothCusp := by
    refine ⟨⟨?_, R.smoothCusp.1.2⟩, R.smoothCusp.2⟩
    have h : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
        R.centralChar D R.toFun := R.smoothCusp.1.1
    have h' : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
        R.centralChar D' R.toFun :=
      (lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mpr ⟨((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp h).1, hL2⟩
    exact h'
  level_invariant := R.level_invariant
  exceptionalSet := R.exceptionalSet
  hecke_eigen := R.hecke_eigen
  central_eigen := R.central_eigen

private theorem transport_toFun (R : SmoothCuspRealizationAt K (productionPinsOf K D U gen B) Φ)
    (hL2 : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D')) :
    (transport R hL2).toFun = R.toFun := rfl

private theorem isGenuine_transport (R : SmoothCuspRealizationAt K (productionPinsOf K D U gen B) Φ)
    (hR : IsGenuineCuspRealizationAt K (productionPinsOf K D U gen B) Φ R)
    (hL2 : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D')) :
    IsGenuineCuspRealizationAt K (productionPinsOf K D' U gen B) Φ (transport R hL2) := hR

private theorem exists_transport (R : SmoothCuspRealizationAt K (productionPinsOf K D U gen B) Φ)
    (hR : IsGenuineCuspRealizationAt K (productionPinsOf K D U gen B) Φ R)
    (hL2 : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D')) :
    ∃ R' : SmoothCuspRealizationAt K (productionPinsOf K D' U gen B) Φ,
      IsGenuineCuspRealizationAt K (productionPinsOf K D' U gen B) Φ R' ∧ R'.toFun = R.toFun :=
  ⟨transport R hL2, isGenuine_transport R hR hL2, transport_toFun R hL2⟩

end Transport

section CONTproof

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace TranslationContinuity

private theorem sq_nnnorm_sub_le {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ((‖a - b‖₊ : ℝ≥0∞)) ^ 2 ≤ 2 * (((‖a‖₊ : ℝ≥0∞)) ^ 2 + ((‖b‖₊ : ℝ≥0∞)) ^ 2) := by
  have h1 : ((‖a - b‖₊ : ℝ≥0∞)) ≤ (‖a‖₊ : ℝ≥0∞) + (‖b‖₊ : ℝ≥0∞) := by
    exact_mod_cast nnnorm_sub_le a b
  have h2 : ∀ x y : ℝ≥0∞, (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    intro x y
    rcases eq_or_ne x ⊤ with rfl | hx
    · simp
    rcases eq_or_ne y ⊤ with rfl | hy
    · simp
    lift x to NNReal using hx; lift y to NNReal using hy
    have : ((x : ℝ) + y) ^ 2 ≤ 2 * ((x : ℝ) ^ 2 + y ^ 2) := by nlinarith [sq_nonneg ((x : ℝ) - y)]
    exact_mod_cast this
  exact (pow_le_pow_left' h1 2).trans (h2 _ _)

private theorem tendsto_setLIntegral_nnnorm_translate_sub_translate_sq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E]
    {mG : MeasurableSpace G} [OpensMeasurableSpace G] (μ : Measure G)
    {φ : G → E} (hφ : Continuous φ) (D : Set G) (z₀ : G)
    (htail : ∀ η : ℝ≥0∞, 0 < η → ∃ D₀ : Set G, D₀ ⊆ D ∧ IsCompact (closure D₀) ∧ μ D₀ < ⊤ ∧
      ∀ᶠ y in 𝓝 z₀, ∫⁻ g in D \ D₀, (‖φ (g * y)‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ η) :
    Tendsto (fun y => ∫⁻ g in D, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ) (𝓝 z₀) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε

  set θ : ℝ≥0∞ := ε / 5 with hθ
  have hθpos : 0 < θ := ENNReal.div_pos hε.ne' (by norm_num)
  have h5θ : 5 * θ ≤ ε := ENNReal.mul_div_le
  obtain ⟨D₀, hD₀D, hK, hμD₀, hev⟩ := htail θ hθpos

  set K : Set G := closure D₀ with hKdef
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Ψ : C(G × K, E) :=
    ⟨fun p => φ ((p.2 : G) * p.1), hφ.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)⟩
  let F : C(G, C(K, E)) := Ψ.curry
  have hF : Tendsto (fun y => F y) (𝓝 z₀) (𝓝 (F z₀)) := F.continuous.tendsto z₀
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at hF

  obtain ⟨c, hcpos, hcμ⟩ := ENNReal.exists_pos_mul_lt hμD₀.ne hθpos.ne'
  set c₁ : ℝ≥0∞ := min c 1 with hc₁
  have hc₁c : c₁ ≤ c := min_le_left _ _
  have hc₁1 : c₁ ≤ 1 := min_le_right _ _
  have hc₁top : c₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc₁1
  have hc₁pos : 0 < c₁ := lt_min hcpos zero_lt_one
  have hδ : 0 < c₁.toReal := ENNReal.toReal_pos hc₁pos.ne' hc₁top
  have hKae : ∀ᵐ g ∂(μ.restrict D₀), g ∈ K := by
    have hKc : MeasurableSet {a | a ∉ K} := isClosed_closure.measurableSet.compl
    rw [ae_iff, Measure.restrict_apply hKc]
    have : {a | a ∉ K} ∩ D₀ = ∅ := by
      ext g; simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hg hgD; exact hg (subset_closure hgD)
    rw [this, measure_empty]
  filter_upwards [hev, hF c₁.toReal hδ] with y hy hyu

  have hcap : ∫⁻ g in D₀, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ θ := by
    calc ∫⁻ g in D₀, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ
        ≤ ∫⁻ _ in D₀, c ∂μ := by
          refine lintegral_mono_ae (hKae.mono fun g hg => ?_)
          have h1 : dist ((F z₀) ⟨g, hg⟩) ((F y) ⟨g, hg⟩) < c₁.toReal := hyu ⟨g, hg⟩
          have h2 : ‖φ (g * y) - φ (g * z₀)‖ < c₁.toReal := by
            rw [dist_comm, dist_eq_norm] at h1; exact h1
          have h3 : (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ≤ c₁ := by
            rw [← ENNReal.coe_toNNReal hc₁top]
            refine ENNReal.coe_le_coe.mpr ?_
            rw [← NNReal.coe_le_coe, coe_nnnorm]
            exact h2.le
          calc (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2
              = (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) * (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) := pow_two _
            _ ≤ c₁ * 1 := mul_le_mul' h3 (h3.trans hc₁1)
            _ ≤ c := by rw [mul_one]; exact hc₁c
      _ = c * μ D₀ := setLIntegral_const _ _
      _ ≤ θ := hcμ.le

  have hz : ∫⁻ g in D \ D₀, (‖φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ θ := hev.self_of_nhds
  have hmeas : ∀ w : G, Measurable fun g => ((‖φ (g * w)‖₊ : ℝ≥0∞)) ^ 2 := by
    intro w
    have hcw : Continuous fun g => φ (g * w) := hφ.comp (continuous_id.mul continuous_const)
    exact (Measurable.coe_nnreal_ennreal (continuous_nnnorm.comp hcw).measurable).pow_const 2
  have htl : ∫⁻ g in D \ D₀, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ 2 * (θ + θ) := by
    calc ∫⁻ g in D \ D₀, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ
        ≤ ∫⁻ g in D \ D₀, 2 * (((‖φ (g * y)‖₊ : ℝ≥0∞)) ^ 2 + ((‖φ (g * z₀)‖₊ : ℝ≥0∞)) ^ 2) ∂μ :=
          lintegral_mono fun g => sq_nnnorm_sub_le _ _
      _ = 2 * (∫⁻ g in D \ D₀, (‖φ (g * y)‖₊ : ℝ≥0∞) ^ 2 ∂μ + ∫⁻ g in D \ D₀, (‖φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ) := by
          rw [lintegral_const_mul _ ((hmeas y).fun_add (hmeas z₀)), lintegral_add_left (hmeas y)]
      _ ≤ 2 * (θ + θ) := by gcongr

  calc ∫⁻ g in D, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ ∫⁻ g, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂(μ.restrict D₀ + μ.restrict (D \ D₀)) := by
        refine lintegral_mono' ?_ le_rfl
        calc μ.restrict D = μ.restrict (D₀ ∪ D \ D₀) := by rw [union_diff_cancel hD₀D]
          _ ≤ μ.restrict D₀ + μ.restrict (D \ D₀) := Measure.restrict_union_le _ _
    _ = ∫⁻ g in D₀, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ
          + ∫⁻ g in D \ D₀, (‖φ (g * y) - φ (g * z₀)‖₊ : ℝ≥0∞) ^ 2 ∂μ := lintegral_add_measure _ _ _
    _ ≤ θ + 2 * (θ + θ) := add_le_add hcap htl
    _ = 5 * θ := by ring
    _ ≤ ε := h5θ

end TranslationContinuity

end CONTproof

section MULTbodies

open scoped ENNReal

namespace WindowMultiplicity

section UnfoldingGeneric

open MeasureTheory Set
open scoped ENNReal

variable (G : Type*) {α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]

private noncomputable def orbitCount (V : Set α) (x : α) : ℝ≥0∞ :=
  ∑' g : G, V.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)

variable {G}

omit [MeasurableSpace α] in
private theorem orbitCount_mono {V W : Set α} (hVW : V ⊆ W) (x : α) :
    orbitCount G V x ≤ orbitCount G W x :=
  ENNReal.tsum_le_tsum fun _ => indicator_le_indicator_of_subset hVW (fun _ => zero_le) _

omit [MeasurableSpace α] in

private theorem orbitCount_eq_encard (V : Set α) (x : α) :
    orbitCount G V x = ({g : G | g • x ∈ V}.encard : ℝ≥0∞) := by
  unfold orbitCount
  have h : ∀ g : G, V.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)
      = {g : G | g • x ∈ V}.indicator (fun _ => (1 : ℝ≥0∞)) g := by
    intro g
    by_cases hg : g • x ∈ V
    · simp [hg]
    · simp [hg]
  simp_rw [h]
  rw [← tsum_subtype]
  exact ENNReal.tsum_set_one _

omit [MeasurableSpace α] in
private theorem orbitCount_eq_ncard {V : Set α} {x : α} (hfin : {g : G | g • x ∈ V}.Finite) :
    orbitCount G V x = ({g : G | g • x ∈ V}.ncard : ℝ≥0∞) := by
  rw [orbitCount_eq_encard, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]

variable [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] [Countable G]

private theorem setLIntegral_eq_setLIntegral_orbitCount_mul {S : Set α} (hS : IsFundamentalDomain G S μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hinv : ∀ (g : G) (x : α), f (g • x) = f x)
    {V : Set α} (hV : MeasurableSet V) :
    ∫⁻ x in V, f x ∂μ = ∫⁻ x in S, orbitCount G V x * f x ∂μ := by
  have hpt : ∀ (g : G) (x : α),
      V.indicator f (g • x) = V.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) * f x := by
    intro g x
    by_cases hx : g • x ∈ V
    · simp [hx, hinv]
    · simp [hx]
  have hmeas : ∀ g : G,
      AEMeasurable (fun x => V.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) * f x) (μ.restrict S) := by
    intro g
    exact ((measurable_const.indicator hV).comp (measurable_const_smul g)).aemeasurable.mul hf.restrict
  calc ∫⁻ x in V, f x ∂μ = ∫⁻ x, V.indicator f x ∂μ := (lintegral_indicator hV f).symm
    _ = ∑' g : G, ∫⁻ x in S, V.indicator f (g • x) ∂μ := hS.lintegral_eq_tsum'' _
    _ = ∑' g : G, ∫⁻ x in S, V.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) * f x ∂μ :=
        tsum_congr fun g => lintegral_congr fun x => hpt g x
    _ = ∫⁻ x in S, ∑' g : G, V.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) * f x ∂μ :=
        (lintegral_tsum hmeas).symm
    _ = ∫⁻ x in S, orbitCount G V x * f x ∂μ :=
        lintegral_congr fun x => by simp only [orbitCount]; exact ENNReal.tsum_mul_right

private theorem setLIntegral_le_mul_setLIntegral_of_orbitCount_le {S : Set α}
    (hS : IsFundamentalDomain G S μ) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hinv : ∀ (g : G) (x : α), f (g • x) = f x) {V W : Set α} (hV : MeasurableSet V) (hW : MeasurableSet W)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hcount : ∀ x : α, orbitCount G V x ≤ C * orbitCount G W x) :
    ∫⁻ x in V, f x ∂μ ≤ C * ∫⁻ x in W, f x ∂μ := by
  rw [setLIntegral_eq_setLIntegral_orbitCount_mul hS hf hinv hV,
    setLIntegral_eq_setLIntegral_orbitCount_mul hS hf hinv hW, ← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun x => ?_
  rw [← mul_assoc]
  exact mul_le_mul_left (hcount x) _

end UnfoldingGeneric

section LatticeCount

open NumberField

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
private theorem norm_algebraMap_completion_eq (w : InfinitePlace F) (x : F) :
    ‖algebraMap F w.Completion x‖ = w x := by
  have he : algebraMap F w.Completion x = ((WithAbs.equiv w.1).symm x : w.Completion) := rfl
  rw [he, InfinitePlace.Completion.norm_coe]
  rfl

private theorem finite_setOf_forall_norm_le (B : ℝ) :
    {η : 𝓞 F | ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (η : F)‖ ≤ B}.Finite := by
  have hfin := Embeddings.finite_of_norm_le F ℂ B
  refine (hfin.preimage (f := fun η : 𝓞 F => (η : F)) ?_).subset ?_
  · intro a _ b _ hab
    exact RingOfIntegers.ext hab
  · intro η hη
    refine ⟨RingOfIntegers.isIntegral_coe η, fun φ => ?_⟩
    have h := hη (InfinitePlace.mk φ)
    rwa [norm_algebraMap_completion_eq, InfinitePlace.apply] at h

private theorem exists_forall_ncard_box_le (u : ℝ) :
    ∃ A : ℕ, ∀ z : (w : InfinitePlace F) → w.Completion,
      {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ u}.ncard ≤ A := by
  refine ⟨{η : 𝓞 F | ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (η : F)‖ ≤ 2 * u}.ncard, fun z => ?_⟩
  by_cases hne : {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ u}.Nonempty
  · obtain ⟨ξ₀, hξ₀⟩ := hne
    refine Set.ncard_le_ncard_of_injOn (fun ξ => ξ - ξ₀) ?_ ?_ (finite_setOf_forall_norm_le (2 * u))
    · intro ξ hξ w
      have h1 := hξ w
      have h2 := hξ₀ w
      have hsub : algebraMap F w.Completion ((ξ - ξ₀ : 𝓞 F) : F)
          = (z w - algebraMap F w.Completion (ξ₀ : F)) - (z w - algebraMap F w.Completion (ξ : F)) := by
        rw [show ((ξ - ξ₀ : 𝓞 F) : F) = (ξ : F) - (ξ₀ : F) from map_sub (algebraMap (𝓞 F) F) ξ ξ₀, map_sub]
        ring
      rw [hsub]
      calc ‖(z w - algebraMap F w.Completion (ξ₀ : F)) - (z w - algebraMap F w.Completion (ξ : F))‖
          ≤ ‖z w - algebraMap F w.Completion (ξ₀ : F)‖ + ‖z w - algebraMap F w.Completion (ξ : F)‖ :=
            norm_sub_le _ _
        _ ≤ u + u := add_le_add h2 h1
        _ = 2 * u := by ring
    · intro a _ b _ hab
      simpa using hab
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
    exact Nat.zero_le _

end LatticeCount

section UnitBalancing

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem

variable {F : Type} [Field F] [NumberField F]

private theorem exists_forall_mem_fundamentalCone_abs_deviation_le :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ fundamentalCone F, ∀ w : InfinitePlace F,
      |Real.log (normAtPlace w x) - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹| ≤ R := by
  classical
  obtain ⟨R₀, hR₀⟩ :=
    (ZSpan.fundamentalDomain_isBounded ((basisUnitLattice F).ofZLatticeBasis ℝ _)).exists_norm_le
  refine ⟨(Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0, by positivity, fun x hx w => ?_⟩
  have hcone : logMap x ∈ ZSpan.fundamentalDomain ((basisUnitLattice F).ofZLatticeBasis ℝ _) := hx.1
  have hlog : ‖logMap x‖ ≤ R₀ := hR₀ _ hcone

  have hcomp : ∀ v : {v : InfinitePlace F // v ≠ w₀},
      |(mult v.1 : ℝ) * (Real.log (normAtPlace v.1 x)
        - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹)| ≤ max R₀ 0 := by
    intro v
    have h1 : ‖logMap x v‖ ≤ ‖logMap x‖ := norm_le_pi_norm (logMap x) v
    rw [logMap_apply, Real.norm_eq_abs] at h1
    exact h1.trans (hlog.trans (le_max_left _ _))

  have hne : ∀ v : InfinitePlace F, normAtPlace v x ≠ 0 :=
    fun v => (fundamentalCone.normAtPlace_pos_of_mem hx v).ne'
  have hfinrank : (Module.finrank ℚ F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hsum : ∑ v : InfinitePlace F, (mult v : ℝ) * (Real.log (normAtPlace v x)
      - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹) = 0 := by
    have hprod : Real.log (mixedEmbedding.norm x)
        = ∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (normAtPlace v x) := by
      rw [mixedEmbedding.norm_apply, Real.log_prod (fun v _ => pow_ne_zero _ (hne v))]
      simp only [Real.log_pow]
    have hmult : ∑ v : InfinitePlace F, (mult v : ℝ) = (Module.finrank ℚ F : ℝ) := by
      exact_mod_cast sum_mult_eq (K := F)
    have hlin : ∑ v : InfinitePlace F, (mult v : ℝ) * (Real.log (normAtPlace v x)
          - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹)
        = (∑ v : InfinitePlace F, (mult v : ℝ) * Real.log (normAtPlace v x))
          - (∑ v : InfinitePlace F, (mult v : ℝ))
            * (Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    have hcancel : (Module.finrank ℚ F : ℝ)
          * (Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹)
        = Real.log (mixedEmbedding.norm x) := by
      field_simp
    rw [hlin, ← hprod, hmult, hcancel, sub_self]

  set dev : InfinitePlace F → ℝ := fun v => Real.log (normAtPlace v x)
    - Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ F : ℝ)⁻¹ with hdev
  have hweighted : |(mult w : ℝ) * dev w| ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := by
    by_cases hw : w = w₀
    ·
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset (InfinitePlace F))
        (fun v => (mult v : ℝ) * dev v) (Finset.mem_univ w)
      have hzero : ∑ v, (mult v : ℝ) * dev v = 0 := hsum
      have hw_eq : (mult w : ℝ) * dev w = - ∑ v ∈ Finset.univ.erase w, (mult v : ℝ) * dev v := by
        linarith [hsplit, hzero]
      rw [hw_eq, abs_neg]
      calc |∑ v ∈ Finset.univ.erase w, (mult v : ℝ) * dev v|
          ≤ ∑ v ∈ Finset.univ.erase w, |(mult v : ℝ) * dev v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v ∈ Finset.univ.erase w, max R₀ 0 := by
            refine Finset.sum_le_sum fun v hv => ?_
            have hv' : v ≠ w₀ := hw ▸ (Finset.mem_erase.mp hv).1
            exact hcomp ⟨v, hv'⟩
        _ = ((Finset.univ.erase w).card : ℝ) * max R₀ 0 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := by
            gcongr
            exact_mod_cast Finset.card_le_univ _
    · calc |(mult w : ℝ) * dev w| ≤ max R₀ 0 := hcomp ⟨w, hw⟩
        _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := by
            have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
              exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
            exact le_mul_of_one_le_left (le_max_right _ _) hcard
  have hmult_one : (1 : ℝ) ≤ mult w := one_le_mult
  calc |dev w| ≤ (mult w : ℝ) * |dev w| := le_mul_of_one_le_left (abs_nonneg _) hmult_one
    _ = |(mult w : ℝ) * dev w| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < mult w)]
    _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * max R₀ 0 := hweighted

private theorem exists_forall_exists_unit_forall_mul_le_mul :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ h : InfinitePlace F → ℝ, (∀ w, 0 < h w) →
      ∃ u : (𝓞 F)ˣ, ∀ w w' : InfinitePlace F,
        (w (algebraMap (𝓞 F) F u)) ^ 2 * h w ≤ κ * ((w' (algebraMap (𝓞 F) F u)) ^ 2 * h w') := by
  obtain ⟨R, hR, hdev⟩ := exists_forall_mem_fundamentalCone_abs_deviation_le (F := F)
  refine ⟨Real.exp (4 * R), Real.one_le_exp_iff.mpr (by positivity), fun h hpos => ?_⟩

  set y : mixedSpace F := mixedSpaceOfRealSpace (fun w => Real.sqrt (h w)) with hy
  have hyw : ∀ w : InfinitePlace F, normAtPlace w y = Real.sqrt (h w) :=
    fun w => normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _)
  have hynorm : mixedEmbedding.norm y ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr fun w => by rw [hyw]; exact (Real.sqrt_pos.mpr (hpos w)).ne'
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem hynorm
  refine ⟨u, fun w w' => ?_⟩

  have hnorm_smul : ∀ v : InfinitePlace F,
      normAtPlace v (u • y) = v (algebraMap (𝓞 F) F u) * Real.sqrt (h v) := by
    intro v
    rw [unitSMul_smul, map_mul, normAtPlace_apply, hyw]
  have hpos_smul : ∀ v : InfinitePlace F, 0 < normAtPlace v (u • y) :=
    fundamentalCone.normAtPlace_pos_of_mem hu

  have hw := hdev _ hu w
  have hw' := hdev _ hu w'
  have hlog : Real.log (normAtPlace w (u • y)) ≤ Real.log (normAtPlace w' (u • y)) + 2 * R := by
    have h1 := (abs_le.mp hw).2
    have h2 := (abs_le.mp hw').1
    linarith
  have hle : normAtPlace w (u • y) ≤ Real.exp (2 * R) * normAtPlace w' (u • y) := by
    have h3 : normAtPlace w (u • y) = Real.exp (Real.log (normAtPlace w (u • y))) :=
      (Real.exp_log (hpos_smul w)).symm
    have h4 : normAtPlace w' (u • y) = Real.exp (Real.log (normAtPlace w' (u • y))) :=
      (Real.exp_log (hpos_smul w')).symm
    rw [h3, h4, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

  have hsq : normAtPlace w (u • y) ^ 2 ≤ (Real.exp (2 * R) * normAtPlace w' (u • y)) ^ 2 :=
    pow_le_pow_left₀ (normAtPlace_nonneg _ _) hle 2
  rw [hnorm_smul, hnorm_smul, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hpos w).le,
    Real.sq_sqrt (hpos w').le] at hsq
  have h4 : Real.exp (4 * R) = Real.exp (2 * R) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [h4]
  exact hsq

end UnitBalancing

section UnfoldingSum

open MeasureTheory Set
open scoped ENNReal

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]

private theorem measurable_orbitCount {V : Set α} (hV : MeasurableSet V) : Measurable (orbitCount G V) := by
  have h : orbitCount G V
      = fun x => ⨆ s : Finset G, ∑ g ∈ s, V.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) := by
    funext x
    exact ENNReal.tsum_eq_iSup_sum
  rw [h]
  exact Measurable.iSup fun s => Finset.measurable_sum s fun g _ =>
    (measurable_const.indicator hV).comp (measurable_const_smul g)

variable {μ : Measure α} [SMulInvariantMeasure G α μ]

private theorem setLIntegral_le_mul_sum_setLIntegral_of_orbitCount_le {S : Set α}
    (hS : IsFundamentalDomain G S μ) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hinv : ∀ (g : G) (x : α), f (g • x) = f x) {V : Set α} (hV : MeasurableSet V) {ι : Type*} (s : Finset ι)
    {W : ι → Set α} (hW : ∀ i, MeasurableSet (W i)) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hcount : ∀ x : α, orbitCount G V x ≤ C * ∑ i ∈ s, orbitCount G (W i) x) :
    ∫⁻ x in V, f x ∂μ ≤ C * ∑ i ∈ s, ∫⁻ x in W i, f x ∂μ := by
  have hmeas : ∀ i ∈ s, AEMeasurable (fun x => orbitCount G (W i) x * f x) (μ.restrict S) := fun i _ =>
    (measurable_orbitCount (hW i)).aemeasurable.mul hf.restrict
  calc ∫⁻ x in V, f x ∂μ = ∫⁻ x in S, orbitCount G V x * f x ∂μ :=
        setLIntegral_eq_setLIntegral_orbitCount_mul hS hf hinv hV
    _ ≤ ∫⁻ x in S, C * ∑ i ∈ s, orbitCount G (W i) x * f x ∂μ := by
        refine lintegral_mono fun x => ?_
        calc orbitCount G V x * f x ≤ (C * ∑ i ∈ s, orbitCount G (W i) x) * f x := mul_le_mul_left (hcount x) _
          _ = C * ∑ i ∈ s, orbitCount G (W i) x * f x := by rw [mul_assoc, Finset.sum_mul]
    _ = C * ∑ i ∈ s, ∫⁻ x in W i, f x ∂μ := by
        rw [lintegral_const_mul' _ _ hC, lintegral_finsetSum' s hmeas]
        congr 1
        exact Finset.sum_congr rfl fun i _ => (setLIntegral_eq_setLIntegral_orbitCount_mul hS hf hinv (hW i)).symm

end UnfoldingSum

section CubeCount

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def cosetPt (b : Module.Basis ι ℝ E) (v : E) (m : ℕ) (n : ι → ℤ) : E :=
  v + (m : ℝ) • ∑ i, ((n i : ℤ) : ℝ) • b i

omit [FiniteDimensional ℝ E] in
private theorem repr_cosetPt_sub (b : Module.Basis ι ℝ E) (v x : E) (m : ℕ) (n : ι → ℤ) (i : ι) :
    b.repr (cosetPt b v m n - x) i = b.repr (v - x) i + (m : ℝ) * (n i : ℝ) := by
  have h : cosetPt b v m n - x = (v - x) + (m : ℝ) • ∑ j, ((n j : ℤ) : ℝ) • b j := by
    unfold cosetPt; abel
  rw [h, map_add, map_smul, map_sum]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

private theorem finite_setOf_cosetPt_mem_closedBall (b : Module.Basis ι ℝ E) (v x : E) {m : ℕ}
    (hm : 1 ≤ m) (R : ℝ) : {n : ι → ℤ | cosetPt b v m n ∈ Metric.closedBall x R}.Finite := by

  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let c : ι → ℝ := fun i => ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * R + |b.repr (v - x) i|
  refine (Set.Finite.subset (Set.Finite.pi (t := fun i => Set.Icc (-⌈c i / m⌉) ⌈c i / m⌉)
    fun i => Set.finite_Icc _ _) ?_)
  intro n hn
  simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm] at hn
  simp only [Set.mem_univ_pi, Set.mem_Icc]
  have key : ∀ i, |(n i : ℝ)| ≤ c i / m := by
    intro i
    have h1 : |b.repr (cosetPt b v m n - x) i| ≤
        ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * R := by
      have := (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm (cosetPt b v m n - x)
      simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
    rw [repr_cosetPt_sub] at h1
    have h2 : (m : ℝ) * |(n i : ℝ)| ≤ c i := by
      have h3 : |(m : ℝ) * (n i : ℝ)| ≤
          |b.repr (v - x) i + (m : ℝ) * (n i : ℝ)| + |b.repr (v - x) i| := by
        have := abs_sub (b.repr (v - x) i + (m : ℝ) * (n i : ℝ)) (b.repr (v - x) i)
        simpa using this
      rw [abs_mul, Nat.abs_cast] at h3
      simp only [c]
      linarith
    rwa [le_div_iff₀ hm', mul_comm]
  intro i
  constructor
  · have h : ((-n i : ℤ) : ℝ) ≤ ((⌈c i / m⌉ : ℤ) : ℝ) := by
      push_cast
      linarith [(abs_le.mp (key i)).1, Int.le_ceil (c i / m)]
    have h' := Int.cast_le.mp h
    omega
  · have h : ((n i : ℤ) : ℝ) ≤ ((⌈c i / m⌉ : ℤ) : ℝ) := by
      linarith [(abs_le.mp (key i)).2, Int.le_ceil (c i / m)]
    exact Int.cast_le.mp h

omit [FiniteDimensional ℝ E] in

private theorem cosetPt_sub_eq_sum (b : Module.Basis ι ℝ E) (v x : E) (m : ℕ) (n : ι → ℤ) :
    cosetPt b v m n - x = ∑ i, (b.repr (v - x) i + (m : ℝ) * (n i : ℝ)) • b i := by
  conv_lhs => rw [← b.sum_repr (cosetPt b v m n - x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_cosetPt_sub]

private theorem exists_forall_pow_le_ncard_cosetPt (b : Module.Basis ι ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v x : E) (m : ℕ), 1 ≤ m → ∀ R : ℝ, C * m ≤ R →
      (R / (C * m)) ^ Fintype.card ι ≤
        (({n : ι → ℤ | cosetPt b v m n ∈ Metric.closedBall x R}.ncard : ℕ) : ℝ) := by
  classical
  set K₀ : ℝ := ∑ i, ‖b i‖ with hK₀
  have hK₀0 : 0 ≤ K₀ := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨K₀ + 1, by linarith, ?_⟩
  intro v x m hm R hR
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hC : (0 : ℝ) < K₀ + 1 := by linarith
  set ρ : ℝ := R / (K₀ + 1) with hρ
  have hρm : (m : ℝ) ≤ ρ := by
    rw [hρ, le_div_iff₀ hC]; linarith [hR]
  have hρ0 : 0 ≤ ρ := hm'.le.trans hρm
  set a : ι → ℝ := fun i => b.repr (v - x) i with ha

  set lo : ι → ℤ := fun i => ⌈(-ρ - a i) / m⌉ with hlo
  set hi : ι → ℤ := fun i => ⌊(ρ - a i) / m⌋ with hhi
  set S : Finset (ι → ℤ) := Fintype.piFinset fun i => Finset.Icc (lo i) (hi i) with hS

  have hsub : (S : Set (ι → ℤ)) ⊆ {n : ι → ℤ | cosetPt b v m n ∈ Metric.closedBall x R} := by
    intro n hn
    simp only [Finset.mem_coe, hS, Fintype.mem_piFinset, Finset.mem_Icc] at hn
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, cosetPt_sub_eq_sum]
    have hcoord : ∀ i, |a i + (m : ℝ) * (n i : ℝ)| ≤ ρ := by
      intro i
      obtain ⟨h1, h2⟩ := hn i
      have h1' : ((-ρ - a i) / m : ℝ) ≤ ((n i : ℤ) : ℝ) :=
        (Int.le_ceil _).trans (by exact_mod_cast h1)
      have h2' : ((n i : ℤ) : ℝ) ≤ (ρ - a i) / m :=
        (Int.cast_le.mpr h2).trans (Int.floor_le _)
      rw [le_div_iff₀ hm'] at h2'
      rw [div_le_iff₀ hm'] at h1'
      rw [abs_le]
      constructor <;> nlinarith
    calc ‖∑ i, (a i + (m : ℝ) * (n i : ℝ)) • b i‖
        ≤ ∑ i, ‖(a i + (m : ℝ) * (n i : ℝ)) • b i‖ := norm_sum_le _ _
      _ = ∑ i, |a i + (m : ℝ) * (n i : ℝ)| * ‖b i‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, ρ * ‖b i‖ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcoord i) (norm_nonneg _)
      _ = ρ * K₀ := by rw [← Finset.mul_sum]
      _ ≤ ρ * (K₀ + 1) := by nlinarith
      _ = R := by rw [hρ]; field_simp

  have hcard : (ρ / m) ^ Fintype.card ι ≤ (S.card : ℝ) := by
    rw [hS, Fintype.card_piFinset, Nat.cast_prod, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    rw [Int.card_Icc]
    have h1 : ((lo i : ℤ) : ℝ) < (-ρ - a i) / m + 1 := by
      simp only [hlo]; exact Int.ceil_lt_add_one _
    have h2 : ((ρ - a i) / m : ℝ) - 1 < ((hi i : ℤ) : ℝ) := by
      simp only [hhi]; linarith [Int.sub_one_lt_floor ((ρ - a i) / m)]
    have h3 : ρ / m ≤ ((hi i + 1 - lo i : ℤ) : ℝ) := by
      push_cast
      have : ((-ρ - a i) / m : ℝ) = -(ρ / m) - a i / m := by ring
      have : ((ρ - a i) / m : ℝ) = ρ / m - a i / m := by ring
      have hρm' : (1 : ℝ) ≤ ρ / m := by rw [le_div_iff₀ hm']; linarith
      linarith
    calc ρ / m ≤ ((hi i + 1 - lo i : ℤ) : ℝ) := h3
      _ ≤ (((hi i + 1 - lo i).toNat : ℕ) : ℝ) := by exact_mod_cast Int.self_le_toNat _

  have hfin := finite_setOf_cosetPt_mem_closedBall b v x hm R
  have hle : S.card ≤ {n : ι → ℤ | cosetPt b v m n ∈ Metric.closedBall x R}.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub hfin
  calc (R / ((K₀ + 1) * m)) ^ Fintype.card ι = (ρ / m) ^ Fintype.card ι := by
        rw [hρ, div_div]
    _ ≤ (S.card : ℝ) := hcard
    _ ≤ _ := by exact_mod_cast hle

end CubeCount

section Packing

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem packing_finset_le_of_pairwise_le_dist (t : Finset E) {R lam : ℝ} {x₀ : E} (hR : 0 ≤ R)
    (hlam : 0 < lam) (hsep : (t : Set E).Pairwise fun x y => lam ≤ dist x y)
    (ht : (t : Set E) ⊆ Metric.closedBall x₀ R) :
    (t.card : ℝ) ≤ ((2 * R + lam) / lam) ^ Module.finrank ℝ E := by
  borelize E
  set μ : MeasureTheory.Measure E := (Module.finBasis ℝ E).addHaar
  have hhalf : 0 < lam / 2 := by positivity
  have hbig : 0 < R + lam / 2 := by positivity
  have hdisj : (t : Set E).PairwiseDisjoint fun x => Metric.ball x (lam / 2) := by
    intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by linarith [hsep hx hy hxy])
  have hsub : (⋃ x ∈ t, Metric.ball x (lam / 2)) ⊆ Metric.ball x₀ (R + lam / 2) := by
    refine Set.iUnion₂_subset fun x hx => Metric.ball_subset_ball' ?_
    have := Metric.mem_closedBall.1 (ht hx)
    linarith
  have hmeas : μ (⋃ x ∈ t, Metric.ball x (lam / 2)) =
      t.card * μ (Metric.ball (0 : E) 1) * ENNReal.ofReal ((lam / 2) ^ Module.finrank ℝ E) := by
    rw [MeasureTheory.measure_biUnion_finset hdisj fun x _ => Metric.isOpen_ball.measurableSet]
    simp_rw [MeasureTheory.Measure.addHaar_ball_of_pos μ _ hhalf]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hle := (MeasureTheory.measure_mono (μ := μ) hsub).trans_eq
    (MeasureTheory.Measure.addHaar_ball_of_pos μ x₀ hbig)
  rw [hmeas] at hle
  have hμpos : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ (0 : E) one_pos).ne'
  have hμtop : μ (Metric.ball (0 : E) 1) ≠ ⊤ := MeasureTheory.measure_ball_lt_top.ne
  have hreal : (t.card : ℝ) * (lam / 2) ^ Module.finrank ℝ E ≤ (R + lam / 2) ^ Module.finrank ℝ E := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμtop) hle
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hhalf.le _), ENNReal.toReal_ofReal (pow_nonneg hbig.le _)] at h1
    have hb : 0 < (μ (Metric.ball (0 : E) 1)).toReal := ENNReal.toReal_pos hμpos hμtop
    nlinarith [h1, hb]
  have hpow : (0 : ℝ) < (lam / 2) ^ Module.finrank ℝ E := pow_pos hhalf _
  calc (t.card : ℝ)
      = (t.card : ℝ) * (lam / 2) ^ Module.finrank ℝ E / (lam / 2) ^ Module.finrank ℝ E := by
        field_simp
    _ ≤ (R + lam / 2) ^ Module.finrank ℝ E / (lam / 2) ^ Module.finrank ℝ E := by gcongr
    _ = ((2 * R + lam) / lam) ^ Module.finrank ℝ E := by
        rw [← div_pow]
        congr 1
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring

private theorem finite_and_ncard_le_of_pairwise_le_dist (s : Set E) (x₀ : E) {R lam : ℝ} (hR : 0 ≤ R)
    (hlam : 0 < lam) (hsep : s.Pairwise fun x y => lam ≤ dist x y) (hs : s ⊆ closedBall x₀ R) :
    s.Finite ∧ (s.ncard : ℝ) ≤ ((2 * R + lam) / lam) ^ Module.finrank ℝ E := by
  classical
  have key : ∀ t : Finset E, (t : Set E) ⊆ s →
      (t.card : ℝ) ≤ ((2 * R + lam) / lam) ^ Module.finrank ℝ E := fun t ht =>
    packing_finset_le_of_pairwise_le_dist t hR hlam (hsep.mono ht) (ht.trans hs)
  have hfin : s.Finite := by
    by_contra hinf
    obtain ⟨u, hus, hufin, hucard⟩ := Set.Infinite.exists_subset_ncard_eq hinf
      (⌊((2 * R + lam) / lam) ^ Module.finrank ℝ E⌋₊ + 1)
    have h := key hufin.toFinset (by rw [hufin.coe_toFinset]; exact hus)
    rw [← Set.ncard_eq_toFinset_card u hufin, hucard] at h
    push_cast at h
    linarith [Nat.lt_floor_add_one (((2 * R + lam) / lam) ^ Module.finrank ℝ E)]
  refine ⟨hfin, ?_⟩
  have h := key hfin.toFinset (by rw [hfin.coe_toFinset])
  rwa [← Set.ncard_eq_toFinset_card s hfin] at h

end Packing

section FloorRegionCounts

open Metric

variable {κ : Type} [Fintype κ] {ι : Type} [Fintype ι] [DecidableEq ι]

private def floorRegion (t : κ → ℝ) (t₀ : ℝ) : Set (κ → ℝ) :=
  {y | (∀ i, -t i ≤ y i) ∧ ∑ i, y i ≤ t₀}

private theorem floorRegion_mono {t t' : κ → ℝ} (ht : ∀ i, t i ≤ t' i) {t₀ t₀' : ℝ} (ht₀ : t₀ ≤ t₀') :
    floorRegion t t₀ ⊆ floorRegion t' t₀' := fun _ hy =>
  ⟨fun i => (neg_le_neg (ht i)).trans (hy.1 i), hy.2.trans ht₀⟩

private theorem floorRegion_subset_closedBall (t : κ → ℝ) (t₀ : ℝ) :
    floorRegion t t₀ ⊆ closedBall (-t) (max 0 (t₀ + ∑ i, t i)) := by
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (le_max_left _ _)).2 fun i => ?_
  have h0 : ∀ j, 0 ≤ y j + t j := fun j => by linarith [hy.1 j]
  have hsum : y i + t i ≤ t₀ + ∑ j, t j := by
    have h1 : y i + t i ≤ ∑ j, (y j + t j) :=
      Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
    rw [Finset.sum_add_distrib] at h1
    linarith [hy.2]
  rw [Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add, Real.norm_eq_abs, abs_of_nonneg (h0 i)]
  exact hsum.trans (le_max_right _ _)

private theorem closedBall_subset_floorRegion (t : κ → ℝ) (t₀ : ℝ) {ρ : ℝ}
    (hρσ : 2 * ρ * Fintype.card κ ≤ t₀ + ∑ i, t i) :
    closedBall (-t + fun _ => ρ) ρ ⊆ floorRegion t t₀ := by
  intro y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  have hco : ∀ i, |y i + t i - ρ| ≤ ρ := fun i => by
    have := (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hy)).1 hy i
    simpa [Real.norm_eq_abs, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  refine ⟨fun i => by linarith [(abs_le.1 (hco i)).1], ?_⟩
  have h2 : ∀ i, y i ≤ 2 * ρ - t i := fun i => by linarith [(abs_le.1 (hco i)).2]
  calc ∑ i, y i ≤ ∑ i : κ, (2 * ρ - t i) := Finset.sum_le_sum fun i _ => h2 i
    _ = 2 * ρ * Fintype.card κ - ∑ i, t i := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ t₀ := by linarith

private theorem repr_cosetPt_zero_one (b : Module.Basis ι ℝ (κ → ℝ)) (n : ι → ℤ) (i : ι) :
    b.repr (cosetPt b 0 1 n) i = n i := by
  have h := repr_cosetPt_sub b 0 0 1 n i
  simpa using h

private theorem cosetPt_zero_one_injective (b : Module.Basis ι ℝ (κ → ℝ)) :
    Function.Injective (cosetPt b 0 1) := fun n n' h => by
  funext i
  have := repr_cosetPt_zero_one b n i
  rw [h, repr_cosetPt_zero_one] at this
  exact_mod_cast this.symm

private theorem exists_forall_le_dist_cosetPt (b : Module.Basis ι ℝ (κ → ℝ)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ n n' : ι → ℤ, n ≠ n' → lam ≤ dist (cosetPt b 0 1 n) (cosetPt b 0 1 n') := by
  set L : ℝ := ∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖ with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨1 / (L + 1), by positivity, fun n n' hnn => ?_⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hnn
  have h1 : (1 : ℝ) ≤ |((n i : ℝ)) - n' i| := by
    have : (1 : ℤ) ≤ |n i - n' i| := Int.one_le_abs (sub_ne_zero.2 hi)
    exact_mod_cast this
  have h2 : |((n i : ℝ)) - n' i| ≤
      ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * dist (cosetPt b 0 1 n) (cosetPt b 0 1 n') := by
    have h := (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm (cosetPt b 0 1 n - cosetPt b 0 1 n')
    rw [dist_eq_norm]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, map_sub, repr_cosetPt_zero_one,
      Real.norm_eq_abs] at h
    exact h
  have h3 : ‖LinearMap.toContinuousLinearMap (b.coord i)‖ ≤ L := by
    rw [hL]
    exact Finset.single_le_sum (f := fun j => ‖LinearMap.toContinuousLinearMap (b.coord j)‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have hd : 0 ≤ dist (cosetPt b 0 1 n) (cosetPt b 0 1 n') := dist_nonneg
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h3 hd]

private theorem exists_forall_finite_and_ncard_floorRegion_le (b : Module.Basis ι ℝ (κ → ℝ)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (t : κ → ℝ) (t₀ : ℝ),
      {n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.Finite ∧
        ({n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.ncard : ℝ)
          ≤ ((2 * max 0 (t₀ + ∑ i, t i) + lam) / lam) ^ Fintype.card ι := by
  classical
  obtain ⟨lam, hlam, hsep⟩ := exists_forall_le_dist_cosetPt b
  have hrank : Module.finrank ℝ (κ → ℝ) = Fintype.card ι := Module.finrank_eq_card_basis b
  refine ⟨lam, hlam, fun t t₀ => ?_⟩
  set N := {n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀} with hN
  have hsub : cosetPt b 0 1 '' N ⊆ closedBall (-t) (max 0 (t₀ + ∑ i, t i)) := by
    rintro _ ⟨n, hn, rfl⟩
    exact floorRegion_subset_closedBall t t₀ hn
  have hpair : (cosetPt b 0 1 '' N).Pairwise fun x y => lam ≤ dist x y := by
    rintro _ ⟨n, -, rfl⟩ _ ⟨n', -, rfl⟩ hne
    exact hsep n n' fun h => hne (by rw [h])
  obtain ⟨hfin, hcard⟩ :=
    finite_and_ncard_le_of_pairwise_le_dist (cosetPt b 0 1 '' N) (-t) (le_max_left _ _) hlam hpair hsub
  rw [hrank, Set.ncard_image_of_injective N (cosetPt_zero_one_injective b)] at hcard
  exact ⟨hfin.of_finite_image (cosetPt_zero_one_injective b).injOn, hcard⟩

private theorem exists_forall_ncard_floorRegion_relax_le (b : Module.Basis ι ℝ (κ → ℝ)) (δ : κ → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (δ₀ : ℝ) (hδ₀ : 0 ≤ δ₀) :
    ∃ K C₀ s₀ : ℝ, ∀ (t : κ → ℝ) (t₀ : ℝ),
      {n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion (t + δ) (t₀ + δ₀)}.Finite ∧
      (t₀ + ∑ i, t i < s₀ →
        ({n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion (t + δ) (t₀ + δ₀)}.ncard : ℝ) ≤ C₀) ∧
      (s₀ ≤ t₀ + ∑ i, t i →
        ({n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion (t + δ) (t₀ + δ₀)}.ncard : ℝ)
          ≤ K * ({n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.ncard : ℝ)) := by
  classical
  obtain ⟨C, hC, hA⟩ := exists_forall_pow_le_ncard_cosetPt b
  obtain ⟨lam, hlam, hup⟩ := exists_forall_finite_and_ncard_floorRegion_le b
  set r : ℕ := Fintype.card ι with hr
  set D : ℝ := δ₀ + ∑ i, δ i with hD
  have hD0 : 0 ≤ D := add_nonneg hδ₀ (Finset.sum_nonneg fun i _ => hδ i)
  set m : ℝ := 2 * ((Fintype.card κ : ℝ) + 1) with hm
  have hm0 : 0 < m := by positivity
  set s₀ : ℝ := max 1 (m * C) with hs₀
  set A : ℝ := (2 * (1 + D) + lam) / lam with hA_def
  have hsize : ∀ (t : κ → ℝ) (t₀ : ℝ), t₀ + δ₀ + ∑ i, (t + δ) i = t₀ + ∑ i, t i + D := by
    intro t t₀
    simp only [Pi.add_apply, Finset.sum_add_distrib, hD]; ring
  refine ⟨(A * (m * C)) ^ r, ((2 * max 0 (s₀ + D) + lam) / lam) ^ r, s₀, fun t t₀ => ?_⟩
  obtain ⟨hfin, hcard⟩ := hup (t + δ) (t₀ + δ₀)
  rw [hsize] at hcard
  refine ⟨hfin, fun hsmall => ?_, fun hbig => ?_⟩
  · refine hcard.trans (pow_le_pow_left₀ (by positivity) ?_ r)
    rw [div_le_div_iff_of_pos_right hlam]
    have hmx := max_le_max (le_refl (0 : ℝ)) (show t₀ + ∑ i, t i + D ≤ s₀ + D by linarith)
    linarith
  · set σ : ℝ := t₀ + ∑ i, t i with hσ
    have h1σ : 1 ≤ σ := (le_max_left _ _).trans hbig
    have hmC : m * C ≤ σ := (le_max_right _ _).trans hbig
    set ρ : ℝ := σ / m with hρ
    have hρC : C * ((1 : ℕ) : ℝ) ≤ ρ := by
      rw [Nat.cast_one, mul_one, hρ, le_div_iff₀ hm0]; linarith
    have hρσ : 2 * ρ * Fintype.card κ ≤ t₀ + ∑ i, t i := by
      have hle : 2 * (Fintype.card κ : ℝ) ≤ m := by rw [hm]; linarith
      have hσ0 : 0 ≤ σ := by linarith
      calc 2 * ρ * Fintype.card κ = σ * (2 * (Fintype.card κ : ℝ) / m) := by rw [hρ]; ring
        _ ≤ σ * 1 := by gcongr; exact (div_le_one hm0).2 hle
        _ = t₀ + ∑ i, t i := by rw [mul_one]
    have hfin' : {n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.Finite :=
      hfin.subset fun n hn => floorRegion_mono (fun i => by simpa using hδ i) (by linarith) hn
    have hlow : (ρ / (C * ((1 : ℕ) : ℝ))) ^ r ≤
        ({n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.ncard : ℝ) := by
      refine (hA 0 (-t + fun _ => ρ) 1 le_rfl ρ hρC).trans ?_
      exact_mod_cast Set.ncard_le_ncard (s := {n : ι → ℤ | cosetPt b 0 1 n ∈ closedBall (-t + fun _ => ρ) ρ})
        (t := {n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀})
        (fun n hn => closedBall_subset_floorRegion t t₀ hρσ hn) hfin'
    rw [Nat.cast_one, mul_one] at hlow
    have hmax : max 0 (σ + D) = σ + D := max_eq_right (by linarith)
    rw [hmax] at hcard
    have hsizeA : (2 * (σ + D) + lam) / lam ≤ σ * A := by
      rw [hA_def, ← mul_div_assoc, div_le_div_iff_of_pos_right hlam]
      nlinarith
    have hfactor : σ * A = ρ / C * (A * (m * C)) := by
      rw [hρ]; field_simp
    calc ({n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion (t + δ) (t₀ + δ₀)}.ncard : ℝ)
        ≤ ((2 * (σ + D) + lam) / lam) ^ r := hcard
      _ ≤ (σ * A) ^ r := pow_le_pow_left₀ (by positivity) hsizeA r
      _ = (A * (m * C)) ^ r * (ρ / C) ^ r := by rw [hfactor, mul_pow, mul_comm]
      _ ≤ (A * (m * C)) ^ r * ({n : ι → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.ncard : ℝ) := by
          gcongr

end FloorRegionCounts

section CentralNet

open MeasureTheory Matrix
open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.AdelicVolume"

variable {F : Type} [Field F] [NumberField F]

private noncomputable def archNetUnit (a : (w : InfinitePlace F) → (w.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := ((fun w => (a w : w.Completion)), 1)
  inv := ((fun w => (((a w)⁻¹ : (w.Completion)ˣ) : w.Completion)), 1)
  val_inv := by
    refine Prod.ext (funext fun w => ?_) (one_mul 1)
    show (a w : w.Completion) * (((a w)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
    exact Units.mul_inv (a w)
  inv_val := by
    refine Prod.ext (funext fun w => ?_) (one_mul 1)
    show (((a w)⁻¹ : (w.Completion)ˣ) : w.Completion) * (a w : w.Completion) = 1
    exact Units.inv_mul (a w)

private theorem archNetUnit_fst (a : (w : InfinitePlace F) → (w.Completion)ˣ) (w : InfinitePlace F) :
    ((archNetUnit a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = (a w : w.Completion) := rfl

private theorem archNetUnit_snd (a : (w : InfinitePlace F) → (w.Completion)ˣ) :
    ((archNetUnit a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

private noncomputable abbrev netScalar (a : (w : InfinitePlace F) → (w.Completion)ˣ) : AdelicGL2 (𝓞 F) F :=
  centralScalar (𝓞 F) F (archNetUnit a)

private theorem archComponent_netScalar_apply (a : (w : InfinitePlace F) → (w.Completion)ˣ) (w : InfinitePlace F)
    (i j : Fin 2) :
    (archComponent F w (glArch (𝓞 F) F (netScalar a)) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then (a w : w.Completion) else 0 := by
  rw [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
    rfl
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

private theorem archComponent_netScalar_mul (a : (w : InfinitePlace F) → (w.Completion)ˣ) (w : InfinitePlace F)
    (g : AdelicGL2 (𝓞 F) F) :
    archComponent F w (glArch (𝓞 F) F (netScalar a * g))
      = archComponent F w (glArch (𝓞 F) F (netScalar a)) * archComponent F w (glArch (𝓞 F) F g) := by
  rw [map_mul, map_mul]

private theorem localHeight_netScalar_mul (a : (w : InfinitePlace F) → (w.Completion)ˣ) (w : InfinitePlace F)
    (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (netScalar a * g)))
      = localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [archComponent_netScalar_mul]
  have hs := archComponent_netScalar_apply a w
  exact localHeight_scalar_entries_mul (a w).ne_zero (by rw [hs]; simp) (by rw [hs]; simp) (by rw [hs]; simp)
    (by rw [hs]; simp) _

private theorem xWindowSq_netScalar_mul (a : (w : InfinitePlace F) → (w.Completion)ˣ) (w : InfinitePlace F)
    (g : AdelicGL2 (𝓞 F) F) :
    xWindowSq (archComponent F w (glArch (𝓞 F) F (netScalar a * g)))
      = xWindowSq (archComponent F w (glArch (𝓞 F) F g)) := by
  rw [archComponent_netScalar_mul]
  have hs := archComponent_netScalar_apply a w
  exact xWindowSq_scalar_entries_mul (a w).ne_zero (by rw [hs]; simp) (by rw [hs]; simp) (by rw [hs]; simp)
    (by rw [hs]; simp) _

private theorem glFin_netScalar_mul (a : (w : InfinitePlace F) → (w.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (netScalar a * g) = glFin (𝓞 F) F g := by
  rw [map_mul, glFin_scalar_eq_one F (archNetUnit_snd a) (centralScalar_apply_eq _ 0)
    (centralScalar_apply_ne _ (by decide)) (centralScalar_apply_ne _ (by decide)) (centralScalar_apply_eq _ 1),
    one_mul]

private theorem archDetNorm_netScalar_mul (a : (w : InfinitePlace F) → (w.Completion)ˣ) (w : InfinitePlace F)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (netScalar a * g) = ‖(a w : w.Completion)‖ * ‖(a w : w.Completion)‖ * archDetNorm w g := by
  unfold archDetNorm
  rw [archComponent_netScalar_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  have hs := archComponent_netScalar_apply a w
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

private theorem netScalar_mul_globalPoints_mul (a : (w : InfinitePlace F) → (w.Completion)ˣ)
    (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    netScalar a * (globalPoints (𝓞 F) F γ * g) = globalPoints (𝓞 F) F γ * (netScalar a * g) := by
  rw [← mul_assoc, ← mul_centralScalar_comm (archNetUnit a) (globalPoints (𝓞 F) F γ), mul_assoc]

end CentralNet

section MassMoves

open MeasureTheory

private theorem setLIntegral_image_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulRightInvariant] (F : G → ℝ≥0∞) {S : Set G} (hS : MeasurableSet S) (x : G) :
    ∫⁻ y in (· * x) '' S, F y ∂μ = ∫⁻ y in S, F (y * x) ∂μ := by
  have hpre : MeasurableSet ((· * x⁻¹) ⁻¹' S) := hS.preimage (measurable_mul_const x⁻¹)
  rw [Set.image_mul_right, ← lintegral_indicator hpre, ← lintegral_indicator hS,
    ← lintegral_mul_right_eq_self (((· * x⁻¹) ⁻¹' S).indicator F) x]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · have hy' : y * x ∈ (· * x⁻¹) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']
  · have hy' : y * x ∉ (· * x⁻¹) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']

private theorem setLIntegral_biUnion_finset_le {G : Type} [MeasurableSpace G] (μ : Measure G) (F : G → ℝ≥0∞)
    (S : G → Set G) (T : Finset G) : ∫⁻ y in ⋃ x ∈ T, S x, F y ∂μ ≤ ∑ x ∈ T, ∫⁻ y in S x, F y ∂μ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (by gcongr)

private theorem setLIntegral_image_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (F : G → ℝ≥0∞) {S : Set G} (hS : MeasurableSet S) (z : G) :
    ∫⁻ y in (z * ·) '' S, F y ∂μ = ∫⁻ y in S, F (z * y) ∂μ := by
  have hpre : MeasurableSet ((z⁻¹ * ·) ⁻¹' S) := hS.preimage (measurable_const_mul z⁻¹)
  rw [Set.image_mul_left, ← lintegral_indicator hpre, ← lintegral_indicator hS,
    ← lintegral_mul_left_eq_self (((z⁻¹ * ·) ⁻¹' S).indicator F) z]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · have hy' : z * y ∈ (z⁻¹ * ·) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']
  · have hy' : z * y ∉ (z⁻¹ * ·) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']

end MassMoves

noncomputable section MovesCarried

open NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.AdelicVolume"

variable {K : Type} [Field K] [NumberField K]

section Moves

open Matrix AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

private def upperGL (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, t]
    (by rw [Matrix.det_fin_two_of]; simp [ha, ht])

omit [NumberField K] in
private theorem upperGL_apply_zero_zero (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 0 0 = a := rfl

omit [NumberField K] in
private theorem upperGL_apply_zero_one (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 0 1 = b := rfl

omit [NumberField K] in
private theorem upperGL_apply_one_zero (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := rfl

omit [NumberField K] in
private theorem upperGL_apply_one_one (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 1 1 = t := rfl

private theorem archComponent_globalPoints_upperGL_entries (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0)
    (ht : t ≠ 0) :
    let s : GL (Fin 2) w.Completion :=
      archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht)))
    (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (a : w.Completion) ∧
      (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = (b : w.Completion) ∧
      (s : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 ∧
      (s : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (t : w.Completion) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [archComponent_globalPoints_apply]
  · rfl
  · rfl
  · rw [upperGL_apply_one_zero]; exact NumberField.InfinitePlace.Completion.coe_zero (K := K) (v := w)
  · rfl

omit [NumberField K] in
private theorem coe_completion_ne_zero (w : InfinitePlace K) {t : K} (ht : t ≠ 0) : (t : w.Completion) ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [norm_coe_completion, norm_zero] at this
  exact ht (of_not_not ((w.pos_iff.not).mp (not_lt.mpr this.le)))

private theorem archComponent_globalPoints_mul (w : InfinitePlace K) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * g))
      = archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ))
          * archComponent K w (glArch (𝓞 K) K g) := by
  rw [map_mul, map_mul]

private theorem localHeight_globalPoints_upperGL_mul (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht) * g)))
      = w a / w t * localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  obtain ⟨h00, -, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a b t ha ht
  rw [archComponent_globalPoints_mul,
    localHeight_upper_entries_mul (coe_completion_ne_zero w ht) h00 h10 h11, norm_coe_completion,
    norm_coe_completion]

private theorem xWindowSq_globalPoints_diag_mul (w : InfinitePlace K) (a t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    xWindowSq (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a 0 t ha ht) * g)))
      = (w a / w t) ^ 2 * xWindowSq (archComponent K w (glArch (𝓞 K) K g)) := by
  obtain ⟨h00, h01, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a 0 t ha ht
  rw [archComponent_globalPoints_mul,
    xWindowSq_diag_entries_mul (coe_completion_ne_zero w ht) h00 (by rw [h01]; exact NumberField.InfinitePlace.Completion.coe_zero (K := K) (v := w))
      h10 h11,
    norm_coe_completion, norm_coe_completion]

private theorem archDetNorm_globalPoints_upperGL_mul (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (globalPoints (𝓞 K) K (upperGL a b t ha ht) * g) = w a * w t * archDetNorm w g := by
  obtain ⟨h00, -, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a b t ha ht
  unfold archDetNorm
  rw [archComponent_globalPoints_mul, det_upper_entries_mul h00 h10 h11, norm_mul, norm_mul, norm_coe_completion,
    norm_coe_completion]

open scoped Classical in

private noncomputable def placeEmb (w : InfinitePlace K) : w.Completion →+* ℂ :=
  if hw : w.IsReal then Complex.ofRealHom.comp (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)
  else InfinitePlace.Completion.extensionEmbedding w

omit [NumberField K] in
private theorem norm_placeEmb (w : InfinitePlace K) (x : w.Completion) : ‖placeEmb w x‖ = ‖x‖ := by
  unfold placeEmb
  split_ifs with hw
  · rw [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

private noncomputable def xAtP (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  xCoord (((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) w.Completion).map (placeEmb w))

private theorem xWindowSq_eq_norm_xAtP_sq (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    xWindowSq (archComponent K w (glArch (𝓞 K) K g)) = ‖xAtP w g‖ ^ 2 :=
  xWindowSq_eq_norm_xCoord_map_sq (placeEmb w) (norm_placeEmb w) _

private theorem xAtP_globalPoints_upperGL_mul (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    xAtP w (globalPoints (𝓞 K) K (upperGL a b t ha ht) * g)
      = placeEmb w a / placeEmb w t * xAtP w g + placeEmb w b / placeEmb w t := by
  obtain ⟨h00, h01, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a b t ha ht
  set φ := placeEmb w
  set s : GL (Fin 2) w.Completion :=
    archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht))) with hs
  set h : GL (Fin 2) w.Completion := archComponent K w (glArch (𝓞 K) K g) with hh
  have hφt : φ (t : w.Completion) ≠ 0 := (map_ne_zero φ).mpr (coe_completion_ne_zero w ht)
  have hlaw := xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ s) (a := φ (a : w.Completion))
    (b := φ (b : w.Completion)) (t := φ (t : w.Completion)) hφt
    (by rw [coe_map, Matrix.map_apply, h00]) (by rw [coe_map, Matrix.map_apply, h01])
    (by rw [coe_map, Matrix.map_apply, h10, map_zero]) (by rw [coe_map, Matrix.map_apply, h11])
    (Matrix.GeneralLinearGroup.map φ h)
  unfold xAtP
  rw [archComponent_globalPoints_mul, ← hs, ← hh, ← coe_map, ← coe_map, ← map_mul, coe_map, ← coe_map] at *
  rw [map_mul (archComponent K w)]
  exact hlaw

private theorem exists_placeEmb_eq_xAtP (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    ∃ x : w.Completion, placeEmb w x = xAtP w g := by
  by_cases hw : w.IsReal
  ·
    have hsurj : Function.Surjective (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw).surjective
    have hreal : ∀ z : w.Completion,
        placeEmb w z = ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hw z : ℝ) : ℂ) := by
      intro z; simp only [placeEmb, dif_pos hw, RingHom.comp_apply, Complex.ofRealHom_eq_coe]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = xAtP w g := by
      refine ⟨(xAtP w g).re, ?_⟩
      unfold xAtP xCoord
      simp only [hreal, Matrix.map_apply]
      apply Complex.ext <;>
        simp [Complex.ofReal_re, Complex.ofReal_im, -InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    obtain ⟨x, hx⟩ := hsurj r
    exact ⟨x, by rw [hreal, hx, hr]⟩
  · have hsurj : Function.Surjective (InfinitePlace.Completion.extensionEmbedding w) :=
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    obtain ⟨x, hx⟩ := hsurj (xAtP w g)
    exact ⟨x, by simp only [placeEmb, dif_neg hw]; exact hx⟩

private theorem algebraMap_mem_integralFiniteAdeles (a : 𝓞 K) :
    algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K a)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  intro v
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one a

private theorem glFin_globalPoints_upperGL_entries_mem (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (hai : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hbi : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) b ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hti : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) t ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (i j : Fin 2) :
    ((glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht)) :
          GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [glFin_globalPoints_apply]
  fin_cases i <;> fin_cases j
  · exact hai
  · exact hbi
  · show algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (0 : K) ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K
    rw [map_zero]; exact AdelicLevel.zero_mem_integralFiniteAdeles
  · exact hti

omit [NumberField K] in

private theorem upperGL_inv (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht)⁻¹ = upperGL a⁻¹ (-b / (a * t)) t⁻¹ (inv_ne_zero ha) (inv_ne_zero ht) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two, ha, ht] <;>
    field_simp <;> ring

private theorem glFin_globalPoints_upperGL_mem (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (hai : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hbi : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) b ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hti : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) t ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hai' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a⁻¹ ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hbi' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (-b / (a * t))
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hti' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) t⁻¹ ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht)) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨glFin_globalPoints_upperGL_entries_mem a b t ha ht hai hbi hti, fun i j => ?_⟩
  rw [← map_inv, ← map_inv, upperGL_inv]
  exact glFin_globalPoints_upperGL_entries_mem _ _ _ _ _ hai' hbi' hti' i j

private theorem algebraMap_zero_mem :
    algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (0 : K) ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [map_zero]; exact AdelicLevel.zero_mem_integralFiniteAdeles

omit [NumberField K] in
private theorem algebraMap_units_inv_eq (ε : (𝓞 K)ˣ) :
    (algebraMap (𝓞 K) K (ε : 𝓞 K))⁻¹ = algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) :=
  inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])

private theorem algebraMap_units_inv_mem (ε : (𝓞 K)ˣ) :
    algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K (ε : 𝓞 K))⁻¹
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [algebraMap_units_inv_eq]; exact algebraMap_mem_integralFiniteAdeles _

private theorem glFin_globalPoints_diagUnits_mem (ε ε' : (𝓞 K)ˣ) :
    glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL (algebraMap (𝓞 K) K ε) 0 (algebraMap (𝓞 K) K ε')
        (RingOfIntegers.coe_ne_zero_iff.mpr ε.ne_zero) (RingOfIntegers.coe_ne_zero_iff.mpr ε'.ne_zero)))
      ∈ finiteIntegralGL2 (𝓞 K) K := by
  have hai : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_mem_integralFiniteAdeles _
  have hti : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε')
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_mem_integralFiniteAdeles _
  have hai' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε)⁻¹
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_units_inv_mem _
  have hti' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε')⁻¹
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_units_inv_mem _
  have hbi' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
      (-(0 : K) / (algebraMap (𝓞 K) K ε * algebraMap (𝓞 K) K ε')) ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [neg_zero, zero_div]; exact algebraMap_zero_mem
  exact glFin_globalPoints_upperGL_mem _ _ _ _ _ hai algebraMap_zero_mem hti hai' hbi' hti'

private theorem glFin_globalPoints_shift_mem (ξ : 𝓞 K) :
    glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL 1 (algebraMap (𝓞 K) K ξ) 1 one_ne_zero one_ne_zero))
      ∈ finiteIntegralGL2 (𝓞 K) K := by
  have h1 : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (1 : K)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [map_one]; exact AdelicLevel.one_mem_integralFiniteAdeles
  refine glFin_globalPoints_upperGL_mem _ _ _ _ _ h1 (algebraMap_mem_integralFiniteAdeles ξ) h1 (by rwa [inv_one])
    ?_ (by rwa [inv_one])
  rw [mul_one, div_one, ← map_neg]
  exact algebraMap_mem_integralFiniteAdeles (-ξ)

end Moves

end MovesCarried

section Slab

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume NumberField.TateGlobal
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain Set"

variable {K : Type} [Field K] [NumberField K]

private theorem valued_det_le_one (v : HeightOneSpectrum (𝓞 K)) {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    (h : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
  · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

private theorem det_fst_apply (X : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
      = ((archComponent K w (glArch (𝓞 K) K X) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((archEval K w).comp (adeleArch (𝓞 K) K)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det = _
  rw [RingHom.map_det]
  rfl

private theorem ideleNorm_det_eq_prod_archDetNorm_pow (X : AdelicGL2 (𝓞 K) K)
    (hX : glFin (𝓞 K) K X ∈ finiteIntegralGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det X)
      = ∏ w : InfinitePlace K, archDetNorm w X ^ w.mult := by
  exact NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K X hX

private theorem exists_bounds_ideleNorm_det (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ x ∈ T, ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Icc a b := by
  classical
  set N : Finset ℝ :=
    insert (1 : ℝ) (T.image fun x : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det x))
  have hNne : N.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpos : ∀ r ∈ N, 0 < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact one_pos
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hr
      exact ideleNorm_pos _
  refine ⟨N.min' hNne, N.max' hNne, hpos _ (N.min'_mem hNne), N.min'_le_max' hNne,
    fun x hx => ?_⟩
  have hmem : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ N :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
  exact ⟨N.min'_le _ hmem, N.le_max' _ hmem⟩

private theorem prod_pow_mult_pos {d : ℝ} (hd : 0 < d) : 0 < ∏ w : InfinitePlace K, d ^ w.mult :=
  Finset.prod_pos fun _ _ => pow_pos hd _

private theorem prod_pow_mult_lt_prod_pow_mult {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    ∏ w : InfinitePlace K, d₁ ^ w.mult < ∏ w : InfinitePlace K, d₂ ^ w.mult := by
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  refine Finset.prod_lt_prod_of_nonempty (fun w _ => pow_pos hd₁ _) (fun w _ => ?_) ⟨w₀, Finset.mem_univ w₀⟩
  exact pow_lt_pow_left₀ hd hd₁.le (InfinitePlace.mult_pos (w := w)).ne'

private theorem ideleNorm_det_mem_of_mem_centreCutSiegelSetAmple {c u d₁ d₂ κ : ℝ} (hd₁ : 0 < d₁)
    {h : AdelicGL2 (𝓞 K) K} (hh : h ∈ centreCutSiegelSetAmple K c u d₁ d₂ κ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det h) ∈
      Icc (∏ w : InfinitePlace K, d₁ ^ w.mult) (∏ w : InfinitePlace K, d₂ ^ w.mult) := by
  have hint : glFin (𝓞 K) K h ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hh.1).1
  have hwindow : ∀ v : InfinitePlace K, archDetNorm v h ∈ Icc d₁ d₂ := hh.1.2.2.2
  rw [ideleNorm_det_eq_prod_archDetNorm_pow h hint]
  constructor
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _)
      (fun w _ => pow_le_pow_left₀ hd₁.le (hwindow w).1 _)
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w h).le _)
      (fun w _ => pow_le_pow_left₀ (archDetNorm_pos w h).le (hwindow w).2 _)

private theorem exists_window_subset_slab (K : Type) [Field K] [NumberField K] (c u d₁ d₂ κ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) (hd : d₁ < d₂) (hd₁ : 0 < d₁) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ) ⊆
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  obtain ⟨a, b, ha, hab, hT⟩ := exists_bounds_ideleNorm_det (K := K) T
  have hP₁ : 0 < ∏ w : InfinitePlace K, d₁ ^ w.mult := prod_pow_mult_pos hd₁
  have hP : ∏ w : InfinitePlace K, d₁ ^ w.mult < ∏ w : InfinitePlace K, d₂ ^ w.mult :=
    prod_pow_mult_lt_prod_pow_mult hd₁ hd
  refine ⟨(∏ w : InfinitePlace K, d₁ ^ w.mult) * a, (∏ w : InfinitePlace K, d₂ ^ w.mult) * b,
    mul_pos hP₁ ha, ?_, ?_⟩
  · calc (∏ w : InfinitePlace K, d₁ ^ w.mult) * a < (∏ w : InfinitePlace K, d₂ ^ w.mult) * a :=
          mul_lt_mul_of_pos_right hP ha
      _ ≤ (∏ w : InfinitePlace K, d₂ ^ w.mult) * b := mul_le_mul_of_nonneg_left hab (hP₁.trans hP).le
  · intro g hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg
    obtain ⟨x, hx, h, hh, rfl⟩ := hg
    have hh' := ideleNorm_det_mem_of_mem_centreCutSiegelSetAmple hd₁ hh
    have hx' := hT x hx
    show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (h * x)) ∈ Set.Icc _ _
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
    exact ⟨mul_le_mul hh'.1 hx'.1 ha.le (hP₁.le.trans hh'.1),
      mul_le_mul hh'.2 hx'.2 (NumberField.TateGlobal.ideleNorm_pos _).le (hP₁.trans hP).le⟩

private theorem ideleNorm_det_mem_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁)
    {h : AdelicGL2 (𝓞 K) K} (hh : h ∈ centreCutSiegelSet K c u d₁ d₂) :
    ideleNorm K (Matrix.GeneralLinearGroup.det h) ∈
      Icc (∏ w : InfinitePlace K, d₁ ^ w.mult) (∏ w : InfinitePlace K, d₂ ^ w.mult) := by
  have hint : glFin (𝓞 K) K h ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hh).1
  have hwindow : ∀ v : InfinitePlace K, archDetNorm v h ∈ Icc d₁ d₂ := hh.2.2.2
  rw [ideleNorm_det_eq_prod_archDetNorm_pow h hint]
  constructor
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _)
      (fun w _ => pow_le_pow_left₀ hd₁.le (hwindow w).1 _)
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w h).le _)
      (fun w _ => pow_le_pow_left₀ (archDetNorm_pos w h).le (hwindow w).2 _)

private theorem exists_bounds_ideleNorm_det_of_isCompact {R : Set (AdelicGL2 (𝓞 K) K)} (hR : IsCompact R) :
    ∃ m M : ℝ, 0 < m ∧ 1 ≤ M ∧ ∀ y ∈ R, m ≤ ideleNorm K (Matrix.GeneralLinearGroup.det y) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det y) ≤ M := by
  have hcont : Continuous fun g : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
    continuous_ideleNorm_det K
  obtain ⟨M₀, hM₀⟩ := hR.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨M₁, hM₁⟩ := hR.exists_bound_of_continuousOn
    (hcont.inv₀ fun g => (ideleNorm_pos _).ne').continuousOn
  refine ⟨(max M₁ 1)⁻¹, max M₀ 1, inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _)), le_max_right _ _,
    fun y hy => ⟨?_, ?_⟩⟩
  · have h₁ : (ideleNorm K (Matrix.GeneralLinearGroup.det y))⁻¹ ≤ M₁ :=
      (le_abs_self _).trans (by simpa using hM₁ y hy)
    have hpos : 0 < ideleNorm K (Matrix.GeneralLinearGroup.det y) := ideleNorm_pos _
    rw [inv_le_comm₀ (lt_of_lt_of_le one_pos (le_max_right _ _)) hpos]
    exact h₁.trans (le_max_left _ _)
  · have h₀ : ideleNorm K (Matrix.GeneralLinearGroup.det y) ≤ M₀ := (le_abs_self _).trans (by simpa using hM₀ y hy)
    exact h₀.trans (le_max_left _ _)

private theorem exists_window_and_translates_subset_slab (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂) (hd₁ : 0 < d₁) {R : Set (AdelicGL2 (𝓞 K) K)} (hR : IsCompact R) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ⊆
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc α β} ∧
      ∀ y ∈ R, (· * y) '' (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ⊆
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc α β} := by
  obtain ⟨a, b, ha, hab, hT⟩ := exists_bounds_ideleNorm_det (K := K) T
  obtain ⟨m, M, hm, hM, hRb⟩ := exists_bounds_ideleNorm_det_of_isCompact (K := K) hR
  have hP₁ : 0 < ∏ w : InfinitePlace K, d₁ ^ w.mult := prod_pow_mult_pos hd₁
  have hP : ∏ w : InfinitePlace K, d₁ ^ w.mult < ∏ w : InfinitePlace K, d₂ ^ w.mult :=
    prod_pow_mult_lt_prod_pow_mult hd₁ hd
  set P₁ := ∏ w : InfinitePlace K, d₁ ^ w.mult with hP₁def
  set P₂ := ∏ w : InfinitePlace K, d₂ ^ w.mult with hP₂def
  have hm' : 0 < min m 1 := lt_min hm one_pos

  have hwin : ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
      P₁ * a ≤ ideleNorm K (Matrix.GeneralLinearGroup.det g) ∧
        ideleNorm K (Matrix.GeneralLinearGroup.det g) ≤ P₂ * b := by
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg
    obtain ⟨x, hx, h, hh, rfl⟩ := hg
    have hh' := ideleNorm_det_mem_of_mem_centreCutSiegelSet hd₁ hh
    have hx' := hT x hx
    rw [map_mul, ideleNorm_mul]
    exact ⟨mul_le_mul hh'.1 hx'.1 ha.le (hP₁.le.trans hh'.1),
      mul_le_mul hh'.2 hx'.2 (ideleNorm_pos _).le (hP₁.trans hP).le⟩
  refine ⟨P₁ * a * min m 1, P₂ * b * M, mul_pos (mul_pos hP₁ ha) hm', ?_, fun g hg => ?_, fun y hy g hg => ?_⟩
  · calc P₁ * a * min m 1 ≤ P₁ * a * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_pos hP₁ ha).le
      _ = P₁ * a := mul_one _
      _ < P₂ * b := by
          calc P₁ * a < P₂ * a := mul_lt_mul_of_pos_right hP ha
            _ ≤ P₂ * b := mul_le_mul_of_nonneg_left hab (hP₁.trans hP).le
      _ = P₂ * b * 1 := (mul_one _).symm
      _ ≤ P₂ * b * M := mul_le_mul_of_nonneg_left hM (mul_pos (hP₁.trans hP) (ha.trans_le hab)).le
  · obtain ⟨h₁, h₂⟩ := hwin g hg
    refine ⟨?_, ?_⟩
    · calc P₁ * a * min m 1 ≤ P₁ * a * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_pos hP₁ ha).le
        _ = P₁ * a := mul_one _
        _ ≤ _ := h₁
    · calc ideleNorm K (Matrix.GeneralLinearGroup.det g) ≤ P₂ * b := h₂
        _ = P₂ * b * 1 := (mul_one _).symm
        _ ≤ P₂ * b * M := mul_le_mul_of_nonneg_left hM (mul_pos (hP₁.trans hP) (ha.trans_le hab)).le
  · obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨h₁, h₂⟩ := hwin h hh
    obtain ⟨hy₁, hy₂⟩ := hRb y hy
    show ideleNorm K (Matrix.GeneralLinearGroup.det (h * y)) ∈ Icc _ _
    rw [map_mul, ideleNorm_mul]
    refine ⟨?_, ?_⟩
    · calc P₁ * a * min m 1 ≤ P₁ * a * m := mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_pos hP₁ ha).le
        _ ≤ _ := mul_le_mul h₁ hy₁ hm.le ((mul_pos hP₁ ha).le.trans h₁)
    · exact mul_le_mul h₂ hy₂ (ideleNorm_pos _).le (mul_pos (hP₁.trans hP) (ha.trans_le hab)).le

end Slab

section RelaxationClasses

p2m_open "NumberField NumberField.InfinitePlace AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel"
open AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction NumberField.AdelicVolume
open NumberField.AdelicLevel

variable {F : Type} [Field F] [NumberField F]

private def IsIntegralUpper (β : AdelicGL2 (𝓞 F) F) : Prop :=
  ∃ (a t : (𝓞 F)ˣ) (b : 𝓞 F), β = globalPoints (𝓞 F) F
    (upperGL (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (algebraMap (𝓞 F) F t)
      (RingOfIntegers.coe_ne_zero_iff.mpr a.ne_zero) (RingOfIntegers.coe_ne_zero_iff.mpr t.ne_zero))

private noncomputable def intUpper (a t : (𝓞 F)ˣ) (b : 𝓞 F) : AdelicGL2 (𝓞 F) F :=
  globalPoints (𝓞 F) F (upperGL (algebraMap (𝓞 F) F (a : 𝓞 F)) (algebraMap (𝓞 F) F b)
    (algebraMap (𝓞 F) F (t : 𝓞 F)) (RingOfIntegers.coe_ne_zero_iff.mpr a.ne_zero)
    (RingOfIntegers.coe_ne_zero_iff.mpr t.ne_zero))

private theorem isIntegralUpper_intUpper (a t : (𝓞 F)ˣ) (b : 𝓞 F) : IsIntegralUpper (intUpper a t b) :=
  ⟨a, t, b, rfl⟩

private theorem IsIntegralUpper.exists_eq_intUpper {β : AdelicGL2 (𝓞 F) F} (hβ : IsIntegralUpper β) :
    ∃ (a t : (𝓞 F)ˣ) (b : 𝓞 F), β = intUpper a t b :=
  hβ

omit [NumberField F] in
private theorem upperGL_eq_of_eq {a b t a' b' t' : F} {ha : a ≠ 0} {ht : t ≠ 0} {ha' : a' ≠ 0} {ht' : t' ≠ 0}
    (h₁ : a = a') (h₂ : b = b') (h₃ : t = t') : upperGL a b t ha ht = upperGL a' b' t' ha' ht' := by
  subst h₁ h₂ h₃
  rfl

omit [NumberField F] in
private theorem upperGL_mul (a b t a' b' t' : F) (ha : a ≠ 0) (ht : t ≠ 0) (ha' : a' ≠ 0) (ht' : t' ≠ 0) :
    upperGL a b t ha ht * upperGL a' b' t' ha' ht'
      = upperGL (a * a') (a * b' + b * t') (t * t') (mul_ne_zero ha ha') (mul_ne_zero ht ht') := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, upperGL_apply_zero_zero, upperGL_apply_zero_one,
      upperGL_apply_one_zero, upperGL_apply_one_one]

private theorem intUpper_mul (a t a' t' : (𝓞 F)ˣ) (b b' : 𝓞 F) :
    intUpper a t b * intUpper a' t' b' = intUpper (a * a') (t * t') ((a : 𝓞 F) * b' + b * (t' : 𝓞 F)) := by
  unfold intUpper
  rw [← map_mul, upperGL_mul]
  congr 1

private theorem intUpper_inv (a t : (𝓞 F)ˣ) (b : 𝓞 F) :
    (intUpper a t b)⁻¹ = intUpper a⁻¹ t⁻¹ (-b * ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((t⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) := by
  unfold intUpper
  rw [← map_inv, upperGL_inv]
  congr 1
  refine upperGL_eq_of_eq (algebraMap_units_inv_eq a) ?_ (algebraMap_units_inv_eq t)
  rw [map_mul, map_mul, map_neg, ← algebraMap_units_inv_eq, ← algebraMap_units_inv_eq, div_eq_mul_inv, mul_inv]
  ring

private theorem intUpper_one_one_zero : intUpper (1 : (𝓞 F)ˣ) 1 (0 : 𝓞 F) = (1 : AdelicGL2 (𝓞 F) F) := by
  unfold intUpper
  rw [← map_one (globalPoints (𝓞 F) F)]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperGL_apply_zero_zero, upperGL_apply_zero_one, upperGL_apply_one_zero, upperGL_apply_one_one]

private theorem isIntegralUpper_one : IsIntegralUpper (1 : AdelicGL2 (𝓞 F) F) := by
  rw [← intUpper_one_one_zero]
  exact isIntegralUpper_intUpper _ _ _

private theorem IsIntegralUpper.mul {β β' : AdelicGL2 (𝓞 F) F} (hβ : IsIntegralUpper β) (hβ' : IsIntegralUpper β') :
    IsIntegralUpper (β * β') := by
  obtain ⟨a, t, b, rfl⟩ := hβ.exists_eq_intUpper
  obtain ⟨a', t', b', rfl⟩ := hβ'.exists_eq_intUpper
  rw [intUpper_mul]
  exact isIntegralUpper_intUpper _ _ _

private theorem IsIntegralUpper.inv {β : AdelicGL2 (𝓞 F) F} (hβ : IsIntegralUpper β) : IsIntegralUpper β⁻¹ := by
  obtain ⟨a, t, b, rfl⟩ := hβ.exists_eq_intUpper
  rw [intUpper_inv]
  exact isIntegralUpper_intUpper _ _ _

private theorem intUpper_mem_range (a t : (𝓞 F)ˣ) (b : 𝓞 F) : intUpper a t b ∈ (globalPoints (𝓞 F) F).range :=
  ⟨_, rfl⟩

private theorem glFin_intUpper_mem (a t : (𝓞 F)ˣ) (b : 𝓞 F) :
    glFin (𝓞 F) F (intUpper a t b) ∈ finiteIntegralGL2 (𝓞 F) F := by
  unfold intUpper
  refine glFin_globalPoints_upperGL_mem _ _ _ _ _ (algebraMap_mem_integralFiniteAdeles _)
    (algebraMap_mem_integralFiniteAdeles _) (algebraMap_mem_integralFiniteAdeles _) (algebraMap_units_inv_mem a) ?_
    (algebraMap_units_inv_mem t)
  have h : -algebraMap (𝓞 F) F b / (algebraMap (𝓞 F) F (a : 𝓞 F) * algebraMap (𝓞 F) F (t : 𝓞 F))
      = algebraMap (𝓞 F) F (-b * ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((t⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) := by
    rw [map_mul, map_mul, map_neg, ← algebraMap_units_inv_eq, ← algebraMap_units_inv_eq, div_eq_mul_inv, mul_inv]
    ring
  rw [h]
  exact algebraMap_mem_integralFiniteAdeles _

private theorem localHeight_intUpper_mul (a t : (𝓞 F)ˣ) (b : 𝓞 F) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (intUpper a t b * g)))
      = w (algebraMap (𝓞 F) F (a : 𝓞 F)) / w (algebraMap (𝓞 F) F (t : 𝓞 F))
          * localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
  unfold intUpper
  exact localHeight_globalPoints_upperGL_mul w _ _ _ _ _ g

private theorem archDetNorm_intUpper_mul (a t : (𝓞 F)ˣ) (b : 𝓞 F) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (intUpper a t b * g)
      = w (algebraMap (𝓞 F) F (a : 𝓞 F)) * w (algebraMap (𝓞 F) F (t : 𝓞 F)) * archDetNorm w g := by
  unfold intUpper
  exact archDetNorm_globalPoints_upperGL_mul w _ _ _ _ _ g

private theorem xAtP_intUpper_mul (a t : (𝓞 F)ˣ) (b : 𝓞 F) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    xAtP w (intUpper a t b * g)
      = placeEmb w (algebraMap (𝓞 F) F (a : 𝓞 F) : w.Completion)
            / placeEmb w (algebraMap (𝓞 F) F (t : 𝓞 F) : w.Completion) * xAtP w g
        + placeEmb w (algebraMap (𝓞 F) F b : w.Completion)
            / placeEmb w (algebraMap (𝓞 F) F (t : 𝓞 F) : w.Completion) := by
  unfold intUpper
  exact xAtP_globalPoints_upperGL_mul w _ _ _ _ _ g

omit [NumberField F] in

private theorem place_units_inv (w : InfinitePlace F) (ε : (𝓞 F)ˣ) :
    w (algebraMap (𝓞 F) F ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) = (w (algebraMap (𝓞 F) F (ε : 𝓞 F)))⁻¹ := by
  rw [← algebraMap_units_inv_eq, map_inv₀]

omit [NumberField F] in
private theorem place_units_pos (w : InfinitePlace F) (ε : (𝓞 F)ˣ) : 0 < w (algebraMap (𝓞 F) F (ε : 𝓞 F)) :=
  InfinitePlace.pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr ε.ne_zero)

private theorem exists_one_le_place_units (ε : (𝓞 F)ˣ) :
    ∃ w : InfinitePlace F, 1 ≤ w (algebraMap (𝓞 F) F (ε : 𝓞 F)) := by
  by_contra hcon
  push Not at hcon
  have hprod : ∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ mult w < 1 := by
    calc ∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ mult w
        < ∏ _w : InfinitePlace F, (1 : ℝ) :=
          Finset.prod_lt_prod_of_nonempty (fun w _ => pow_pos (place_units_pos w ε) _)
            (fun w _ => pow_lt_one₀ (place_units_pos w ε).le (hcon w) mult_ne_zero) Finset.univ_nonempty
      _ = 1 := Finset.prod_const_one
  rw [prod_eq_abs_norm, NumberField.Units.norm] at hprod
  norm_num at hprod

omit [NumberField F] in

private theorem coe_completion_eq_algebraMap (w : InfinitePlace F) (x : F) :
    (x : w.Completion) = algebraMap F w.Completion x := rfl

private theorem exists_isIntegralUpper_mul_mem_ample (c u d₁ d₂ lam κ : ℝ) (hc : 0 < c) (hlam : 1 ≤ lam)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hbal : ∀ h : InfinitePlace F → ℝ, (∀ w, 0 < h w) → ∃ ε : (𝓞 F)ˣ, ∀ w w' : InfinitePlace F,
      (w (algebraMap (𝓞 F) F ε)) ^ 2 * h w ≤ κ * ((w' (algebraMap (𝓞 F) F ε)) ^ 2 * h w'))
    (hκ : 1 ≤ κ) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)) :
    ∃ β : AdelicGL2 (𝓞 F) F, IsIntegralUpper β ∧
      β * g ∈ centreCutSiegelSetAmple F (c / (lam * κ)) u (d₁ / lam) (lam * d₂) κ := by
  obtain ⟨hgfin, hgh, -, hgd⟩ := mem_centreCutSiegelSet_iff.1 hg
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ
  have hfloor : 0 < c / lam := div_pos hc hlam0

  set h : InfinitePlace F → ℝ := fun w => localHeight (archComponent F w (glArch (𝓞 F) F g)) with hh
  have hpos : ∀ w, 0 < h w := fun w => lt_of_lt_of_le hfloor (hgh w)
  obtain ⟨ε, hε⟩ := hbal h hpos

  set g₁ : AdelicGL2 (𝓞 F) F := intUpper ε ε⁻¹ 0 * g with hg₁
  have hε0 : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F (ε : 𝓞 F)) := fun w => place_units_pos w ε
  have hh₁ : ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g₁))
      = (w (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w := by
    intro w
    rw [hg₁, localHeight_intUpper_mul, place_units_inv, div_inv_eq_mul, sq]
  have hd₁' : ∀ w : InfinitePlace F, archDetNorm w g₁ = archDetNorm w g := by
    intro w
    rw [hg₁, archDetNorm_intUpper_mul, place_units_inv, mul_inv_cancel₀ (hε0 w).ne', one_mul]

  choose x hx using fun w : InfinitePlace F => exists_placeEmb_eq_xAtP w g₁
  obtain ⟨ξ, hξ⟩ := hu x
  set β : AdelicGL2 (𝓞 F) F := intUpper 1 1 (-ξ) * intUpper ε ε⁻¹ 0 with hβ
  refine ⟨β, (isIntegralUpper_intUpper _ _ _).mul (isIntegralUpper_intUpper _ _ _), ?_⟩
  have hβg : β * g = intUpper 1 1 (-ξ) * g₁ := by rw [hβ, hg₁, mul_assoc]
  have hone : ∀ w : InfinitePlace F,
      placeEmb w (algebraMap (𝓞 F) F ((1 : (𝓞 F)ˣ) : 𝓞 F) : w.Completion) = 1 := by
    intro w
    have h1 : algebraMap (𝓞 F) F ((1 : (𝓞 F)ˣ) : 𝓞 F) = (1 : F) := by simp
    rw [h1]
    show placeEmb w (algebraMap F w.Completion (1 : F)) = 1
    rw [map_one, map_one]
  have hheight : ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F (β * g)))
      = (w (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w := by
    intro w
    rw [hβg, localHeight_intUpper_mul, hh₁]
    simp
  have hdet : ∀ w : InfinitePlace F, archDetNorm w (β * g) = archDetNorm w g := by
    intro w
    rw [hβg, archDetNorm_intUpper_mul, hd₁' w]
    simp

  have hfloor' : ∀ w : InfinitePlace F, c / (lam * κ) ≤ (w (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w := by
    intro w
    obtain ⟨w₀, hw₀⟩ := exists_one_le_place_units (F := F) ε
    have h₀ : c / lam ≤ (w₀ (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w₀ :=
      calc c / lam ≤ h w₀ := hgh w₀
        _ = 1 * h w₀ := (one_mul _).symm
        _ ≤ (w₀ (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w₀ :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hw₀) (hpos w₀).le
    have hb := hε w₀ w
    rw [div_mul_eq_div_div, div_le_iff₀ hκ0]
    calc c / lam ≤ (w₀ (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w₀ := h₀
      _ ≤ κ * ((w (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w) := hb
      _ = (w (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * h w * κ := mul_comm _ _

  have hcoord : ∀ w : InfinitePlace F, xWindowSq (archComponent F w (glArch (𝓞 F) F (β * g))) ≤ u ^ 2 := by
    intro w
    have hu0 : 0 ≤ u := le_trans (norm_nonneg _) (hξ w)
    rw [xWindowSq_eq_norm_xAtP_sq, hβg, xAtP_intUpper_mul, hone, div_one, div_one, one_mul, ← hx w, ← map_add,
      norm_placeEmb]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖x w + (algebraMap (𝓞 F) F (-ξ) : w.Completion)‖
        = ‖x w - algebraMap F w.Completion (ξ : F)‖ := by
          rw [coe_completion_eq_algebraMap, map_neg, map_neg, ← sub_eq_add_neg,
            NumberField.RingOfIntegers.coe_eq_algebraMap]
      _ ≤ u := hξ w
  refine mem_centreCutSiegelSetAmple_iff.2 ⟨mem_centreCutSiegelSet_iff.2 ⟨?_, ?_, hcoord, ?_⟩, ?_⟩
  · have hβfin : glFin (𝓞 F) F β ∈ finiteIntegralGL2 (𝓞 F) F := by
      rw [hβ, map_mul]
      exact Subgroup.mul_mem _ (glFin_intUpper_mem _ _ _) (glFin_intUpper_mem _ _ _)
    rw [map_mul]
    exact Subgroup.mul_mem _ hβfin hgfin
  · intro w
    rw [hheight]
    exact hfloor' w
  · intro w
    rw [hdet]
    exact hgd w
  · intro w w'
    rw [hheight, hheight]
    exact hε w w'

private def upperOrbit (g : AdelicGL2 (𝓞 F) F) : Set (AdelicGL2 (𝓞 F) F) :=
  {h | ∃ β : AdelicGL2 (𝓞 F) F, IsIntegralUpper β ∧ h = β * g}

private theorem self_mem_upperOrbit (g : AdelicGL2 (𝓞 F) F) : g ∈ upperOrbit g :=
  ⟨1, isIntegralUpper_one, (one_mul g).symm⟩

private theorem upperOrbit_eq_of_mem {g h : AdelicGL2 (𝓞 F) F} (hh : h ∈ upperOrbit g) :
    upperOrbit h = upperOrbit g := by
  obtain ⟨β, hβ, rfl⟩ := hh
  ext k
  constructor
  · rintro ⟨β', hβ', rfl⟩
    exact ⟨β' * β, hβ'.mul hβ, (mul_assoc _ _ _).symm⟩
  · rintro ⟨β', hβ', rfl⟩
    refine ⟨β' * β⁻¹, hβ'.mul hβ.inv, ?_⟩
    rw [mul_assoc, inv_mul_cancel_left]

private noncomputable def orbitPick (A : Set (AdelicGL2 (𝓞 F) F)) (O : Set (AdelicGL2 (𝓞 F) F)) : AdelicGL2 (𝓞 F) F :=
  open scoped Classical in
  if hO : ∃ k, k ∈ A ∧ k ∈ O then hO.choose else 1

private theorem orbitPick_spec {A O : Set (AdelicGL2 (𝓞 F) F)} (hO : ∃ k, k ∈ A ∧ k ∈ O) :
    orbitPick A O ∈ A ∧ orbitPick A O ∈ O := by
  unfold orbitPick
  rw [dif_pos hO]
  exact hO.choose_spec

private theorem exists_nat_forall_exists_finset_representatives
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (lam : ℝ) (hlam : 1 ≤ lam) :
    ∃ N₀ : ℕ, ∀ x : AdelicGL2 (𝓞 F) F, ∃ REP : Finset (AdelicGL2 (𝓞 F) F), REP.card ≤ N₀ ∧
      (∀ γ₀ ∈ REP, γ₀ ∈ (globalPoints (𝓞 F) F).range) ∧
      (∀ γ ∈ (globalPoints (𝓞 F) F).range,
        γ * x ∈ (⋃ y ∈ T, (· * y) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)) →
          ∃ γ₀ ∈ REP, ∃ β : AdelicGL2 (𝓞 F) F, IsIntegralUpper β ∧ γ = β * γ₀) ∧
      (∀ γ₀ ∈ REP, ∀ γ₁ ∈ REP, (∃ β : AdelicGL2 (𝓞 F) F, IsIntegralUpper β ∧ γ₁ = β * γ₀) → γ₀ = γ₁) := by
  classical
  obtain ⟨κ, hκ, hbal⟩ := exists_forall_exists_unit_forall_mul_le_mul (F := F)
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ
  obtain ⟨N, hN⟩ := exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le F
    (c / (lam * κ)) u (d₁ / lam) (lam * d₂) κ hκ (div_pos hc (mul_pos hlam0 hκ0)) (div_pos hd₁ hlam0) T
  refine ⟨N, fun x => ?_⟩
  obtain ⟨hfin, hcard⟩ := hN x

  set AMP : Set (AdelicGL2 (𝓞 F) F) :=
    {ρ | ρ ∈ (globalPoints (𝓞 F) F).range ∧
      ρ * x ∈ ⋃ y ∈ T, (· * y) '' centreCutSiegelSetAmple F (c / (lam * κ)) u (d₁ / lam) (lam * d₂) κ} with hAMP
  have hAMPsub : AMP ⊆ globalPoints (𝓞 F) F ''
      {γ : Matrix.GeneralLinearGroup (Fin 2) F | globalPoints (𝓞 F) F γ * x ∈
        ⋃ y ∈ T, (· * y) '' centreCutSiegelSetAmple F (c / (lam * κ)) u (d₁ / lam) (lam * d₂) κ} := by
    rintro ρ ⟨⟨γ, rfl⟩, hρ⟩
    exact ⟨γ, hρ, rfl⟩
  have hAMPfin : AMP.Finite := (hfin.image _).subset hAMPsub
  have hAMPcard : AMP.ncard ≤ N :=
    le_trans (Set.ncard_le_ncard hAMPsub (hfin.image _)) (le_trans (Set.ncard_image_le hfin) hcard)
  refine ⟨hAMPfin.toFinset.image (fun ρ => orbitPick AMP (upperOrbit ρ)), ?_, ?_, ?_, ?_⟩
  · calc (hAMPfin.toFinset.image (fun ρ => orbitPick AMP (upperOrbit ρ))).card ≤ hAMPfin.toFinset.card :=
          Finset.card_image_le
      _ = AMP.ncard := (Set.ncard_eq_toFinset_card AMP hAMPfin).symm
      _ ≤ N := hAMPcard
  · intro γ₀ hγ₀
    rw [Finset.mem_image] at hγ₀
    obtain ⟨ρ, hρ, rfl⟩ := hγ₀
    rw [hAMPfin.mem_toFinset] at hρ
    exact (orbitPick_spec ⟨ρ, hρ, self_mem_upperOrbit ρ⟩).1.1
  · rintro γ ⟨γm, rfl⟩ hγ
    rw [Set.mem_iUnion₂] at hγ
    obtain ⟨y, hy, g, hg, hgy⟩ := hγ
    obtain ⟨β, hβ, hβg⟩ := exists_isIntegralUpper_mul_mem_ample c u d₁ d₂ lam κ hc hlam hu hbal hκ hg

    have hρ : β * globalPoints (𝓞 F) F γm ∈ AMP := by
      refine ⟨?_, ?_⟩
      · obtain ⟨a, t, b, rfl⟩ := hβ.exists_eq_intUpper
        exact Subgroup.mul_mem _ (intUpper_mem_range a t b) ⟨γm, rfl⟩
      · rw [Set.mem_iUnion₂]
        refine ⟨y, hy, β * g, hβg, ?_⟩
        simp only [mul_assoc, hgy]
    obtain ⟨hpickA, β', hβ', hpick⟩ :=
      orbitPick_spec ⟨_, hρ, self_mem_upperOrbit (β * globalPoints (𝓞 F) F γm)⟩
    refine ⟨orbitPick AMP (upperOrbit (β * globalPoints (𝓞 F) F γm)), ?_, (β' * β)⁻¹, (hβ'.mul hβ).inv, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨_, hAMPfin.mem_toFinset.2 hρ, rfl⟩
    · rw [hpick]
      simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · intro γ₀ hγ₀ γ₁ hγ₁ hrel
    rw [Finset.mem_image] at hγ₀ hγ₁
    obtain ⟨ρ₀, hρ₀, rfl⟩ := hγ₀
    obtain ⟨ρ₁, hρ₁, rfl⟩ := hγ₁
    rw [hAMPfin.mem_toFinset] at hρ₀ hρ₁
    have h₀ := (orbitPick_spec ⟨ρ₀, hρ₀, self_mem_upperOrbit ρ₀⟩).2
    have h₁ := (orbitPick_spec ⟨ρ₁, hρ₁, self_mem_upperOrbit ρ₁⟩).2

    obtain ⟨β, hβ, hβ₁⟩ := hrel
    have hmem : orbitPick AMP (upperOrbit ρ₁) ∈ upperOrbit ρ₀ := by
      rw [← upperOrbit_eq_of_mem h₀]
      exact ⟨β, hβ, hβ₁⟩
    have horb : upperOrbit ρ₁ = upperOrbit ρ₀ := by
      rw [← upperOrbit_eq_of_mem h₁, upperOrbit_eq_of_mem hmem]
    rw [horb]

end RelaxationClasses

section RelaxationUnits

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

private noncomputable def unitBasis (F : Type) [Field F] [NumberField F] :
    Module.Basis (Fin (rank F)) ℝ (logSpace F) :=
  (basisUnitLattice F).ofZLatticeBasis ℝ _

private theorem logEmbedding_mem_unitLattice (ε : (𝓞 F)ˣ) : logEmbedding F (Additive.ofMul ε) ∈ unitLattice F :=
  Submodule.mem_map.2 ⟨Additive.ofMul ε, Submodule.mem_top, rfl⟩

private noncomputable def unitCoords (ε : (𝓞 F)ˣ) : Fin (rank F) → ℤ :=
  fun i => (basisUnitLattice F).repr ⟨logEmbedding F (Additive.ofMul ε), logEmbedding_mem_unitLattice ε⟩ i

open scoped Classical in
private theorem cosetPt_unitCoords (ε : (𝓞 F)ˣ) :
    cosetPt (unitBasis F) 0 1 (unitCoords ε) = logEmbedding F (Additive.ofMul ε) := by
  apply (unitBasis F).ext_elem
  intro i
  rw [repr_cosetPt_zero_one]
  simp only [unitBasis, unitCoords]
  exact (Module.Basis.ofZLatticeBasis_repr_apply ℝ (unitLattice F) (basisUnitLattice F)
    ⟨logEmbedding F (Additive.ofMul ε), logEmbedding_mem_unitLattice ε⟩ i).symm

open scoped Classical in
private theorem cosetPt_unitBasis_mem_unitLattice (n : Fin (rank F) → ℤ) :
    cosetPt (unitBasis F) 0 1 n ∈ unitLattice F := by
  unfold cosetPt
  simp only [zero_add, Nat.cast_one, one_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  refine (unitLattice F).toAddSubgroup.zsmul_mem ?_ _
  simp only [unitBasis]
  rw [(basisUnitLattice F).ofZLatticeBasis_apply (K := ℝ)]
  exact ((basisUnitLattice F) i).2

open scoped Classical in
private theorem exists_logEmbedding_eq_cosetPt (n : Fin (rank F) → ℤ) :
    ∃ ε : (𝓞 F)ˣ, logEmbedding F (Additive.ofMul ε) = cosetPt (unitBasis F) 0 1 n := by
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 (cosetPt_unitBasis_mem_unitLattice n)
  exact ⟨x.toMul, hx⟩

private theorem mul_inv_mem_torsion_of_logEmbedding_eq {ε ε' : (𝓞 F)ˣ}
    (h : logEmbedding F (Additive.ofMul ε) = logEmbedding F (Additive.ofMul ε')) : ε * ε'⁻¹ ∈ torsion F := by
  rw [← logEmbedding_eq_zero_iff]
  have : Additive.ofMul (ε * ε'⁻¹) = Additive.ofMul ε - Additive.ofMul ε' := rfl
  rw [this, map_sub, h, sub_self]

open scoped Classical in

private theorem exists_basis_nat_forall_finite_and_ncard_le_and_ncard_le :
    ∃ (b : Module.Basis (Fin (rank F)) ℝ (logSpace F)) (T₀ : ℕ), 0 < T₀ ∧
      ∀ S : Set (logSpace F), {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.Finite →
        {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.Finite ∧
        {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.ncard
            ≤ {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.ncard ∧
        {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.ncard
            ≤ T₀ * {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.ncard := by
  classical
  haveI : Fintype ((torsion F : Set (𝓞 F)ˣ) : Type) := Fintype.ofFinite (torsion F)
  refine ⟨unitBasis F, Fintype.card (torsion F), Fintype.card_pos, fun S hS => ?_⟩
  set N : Set (Fin (rank F) → ℤ) := {n | cosetPt (unitBasis F) 0 1 n ∈ S} with hN
  set U : Set (𝓞 F)ˣ := {ε | logEmbedding F (Additive.ofMul ε) ∈ S} with hU

  choose ρ hρ using fun n : Fin (rank F) → ℤ => exists_logEmbedding_eq_cosetPt (F := F) n
  have hρU : ∀ n ∈ N, ρ n ∈ U := fun n hn => by
    show logEmbedding F (Additive.ofMul (ρ n)) ∈ S
    rw [hρ n]
    exact hn
  have hcoordsN : ∀ ε ∈ U, unitCoords ε ∈ N := fun ε hε => by
    show cosetPt (unitBasis F) 0 1 (unitCoords ε) ∈ S
    rw [cosetPt_unitCoords]
    exact hε

  set Φ : (𝓞 F)ˣ → (Fin (rank F) → ℤ) × (𝓞 F)ˣ := fun ε => (unitCoords ε, ε * (ρ (unitCoords ε))⁻¹) with hΦ
  have hΦmaps : ∀ ε ∈ U, Φ ε ∈ N ×ˢ (torsion F : Set (𝓞 F)ˣ) := fun ε hε => by
    refine Set.mk_mem_prod (hcoordsN ε hε) ?_
    refine mul_inv_mem_torsion_of_logEmbedding_eq ?_
    rw [hρ, cosetPt_unitCoords]
  have hΦinj : Set.InjOn Φ U := fun ε _ ε' _ h => by
    simp only [hΦ, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [h₁] at h₂
    exact mul_right_cancel h₂
  have hprodfin : (N ×ˢ (torsion F : Set (𝓞 F)ˣ)).Finite := hS.prod (Set.toFinite _)
  have hUfin : U.Finite := Set.Finite.of_finite_image (hprodfin.subset (Set.image_subset_iff.2 hΦmaps)) hΦinj
  refine ⟨hUfin, ?_, ?_⟩
  ·
    refine Set.ncard_le_ncard_of_injOn ρ hρU (fun n _ n' _ h => ?_) hUfin
    apply cosetPt_zero_one_injective (unitBasis F)
    rw [← hρ n, ← hρ n', h]
  · calc U.ncard ≤ (N ×ˢ (torsion F : Set (𝓞 F)ˣ)).ncard := Set.ncard_le_ncard_of_injOn Φ hΦmaps hΦinj hprodfin
      _ = N.ncard * (torsion F : Set (𝓞 F)ˣ).ncard := Set.ncard_prod
      _ = Fintype.card (torsion F) * N.ncard := by
          rw [mul_comm, Set.ncard_eq_toFinset_card', Set.toFinset_card]
          congr 1

private theorem neg_neg_div_two_le_iff {m x y : ℝ} (hm : 0 < m) : -(-(m * x) / 2) ≤ m * y ↔ x ≤ 2 * y := by
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

open scoped Classical in

private theorem forall_le_sq_iff_logEmbedding_mem_floorRegion (r : InfinitePlace F → ℝ) (hr : ∀ w, 0 < r w)
    (ε : (𝓞 F)ˣ) :
    (∀ w : InfinitePlace F, r w ≤ (w (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2) ↔
      logEmbedding F (Additive.ofMul ε) ∈
        floorRegion (fun w : {w : InfinitePlace F // w ≠ w₀} => -(mult w.1 * Real.log (r w.1)) / 2)
          (-(mult (w₀ : InfinitePlace F) * Real.log (r w₀)) / 2) := by
  have hε : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F (ε : 𝓞 F)) := fun w => place_units_pos w ε
  have hmult : ∀ w : InfinitePlace F, (0 : ℝ) < mult w := fun w => by exact_mod_cast mult_pos

  have key : ∀ w : InfinitePlace F, r w ≤ (w (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 ↔
      -(-(mult w * Real.log (r w)) / 2) ≤ mult w * Real.log (w (algebraMap (𝓞 F) F (ε : 𝓞 F))) := by
    intro w
    rw [← Real.log_le_log_iff (hr w) (pow_pos (hε w) 2), Real.log_pow, neg_neg_div_two_le_iff (hmult w)]
    push_cast
    exact Iff.rfl
  have hcomp : ∀ w : {w : InfinitePlace F // w ≠ w₀},
      logEmbedding F (Additive.ofMul ε) w = mult w.1 * Real.log (w.1 (algebraMap (𝓞 F) F (ε : 𝓞 F))) :=
    fun w => logEmbedding_component ε w
  have hsum : ∑ w, logEmbedding F (Additive.ofMul ε) w
      = -mult (w₀ : InfinitePlace F) * Real.log (w₀ (algebraMap (𝓞 F) F (ε : 𝓞 F))) :=
    sum_logEmbedding_component ε
  constructor
  · intro h
    refine ⟨fun w => ?_, ?_⟩
    · rw [hcomp]
      exact (key w.1).1 (h w.1)
    · rw [hsum]
      have := (key w₀).1 (h w₀)
      linarith
  · rintro ⟨h₁, h₂⟩ w
    by_cases hw : w = w₀
    · rw [hsum] at h₂
      rw [hw]
      exact (key w₀).2 (by linarith)
    · have := h₁ ⟨w, hw⟩
      rw [hcomp] at this
      exact (key w).2 this

private theorem exists_one_lt_and_sq_le {q : ℝ} (hq : 1 < q) : ∃ ρ : ℚ, 1 < (ρ : ℝ) ∧ (ρ : ℝ) ^ 2 ≤ q := by
  have hmin : 0 < min 1 ((q - 1) / 3) := lt_min one_pos (by linarith)
  obtain ⟨ρ, h₁, h₂⟩ := exists_rat_btwn (show (1 : ℝ) < 1 + min 1 ((q - 1) / 3) by linarith)
  refine ⟨ρ, h₁, ?_⟩
  have hm₁ : min 1 ((q - 1) / 3) ≤ 1 := min_le_left _ _
  have hm₂ : min 1 ((q - 1) / 3) ≤ (q - 1) / 3 := min_le_right _ _
  nlinarith

private noncomputable def ratPowFamily (ρ : ℚ) (hρ : (ρ : F) ≠ 0) (k : InfinitePlace F → ℤ) :
    (w : InfinitePlace F) → (w.Completion)ˣ :=
  fun w => Units.mk0 (((ρ : F) ^ k w : F) : w.Completion) (coe_completion_ne_zero w (zpow_ne_zero _ hρ))

omit [NumberField F] in
private theorem norm_ratPowFamily {ρ : ℚ} (hρ0 : (0 : ℝ) < ρ) (hρ : (ρ : F) ≠ 0) (k : InfinitePlace F → ℤ)
    (w : InfinitePlace F) : ‖((ratPowFamily ρ hρ k w : (w.Completion)ˣ) : w.Completion)‖ = (ρ : ℝ) ^ k w := by
  unfold ratPowFamily
  rw [Units.val_mk0, AutomorphicForm.SiegelReduction.norm_coe_completion, map_zpow₀, InfinitePlace.map_ratCast,
    ← Rat.norm_cast_real, Real.norm_of_nonneg hρ0.le]

private theorem exists_finset_forall_exists_forall_norm_mul_norm_mul_mem_Icc (d₁ d₂ lam : ℝ) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hlam : 1 ≤ lam) :
    ∃ Z : Finset ((w : InfinitePlace F) → (w.Completion)ˣ),
      ∀ D : InfinitePlace F → ℝ, (∀ w, D w ∈ Set.Icc (d₁ / lam) (lam * d₂)) →
        ∃ a ∈ Z, ∀ w : InfinitePlace F,
          ‖(a w : w.Completion)‖ * ‖(a w : w.Completion)‖ * D w ∈ Set.Icc d₁ d₂ := by
  classical
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  obtain ⟨ρ, hρ1, hρsq⟩ := exists_one_lt_and_sq_le (show 1 < d₂ / d₁ from (one_lt_div hd₁).2 hd)
  have hρ0 : (0 : ℝ) < ρ := lt_trans one_pos hρ1
  have hρF : (ρ : F) ≠ 0 := by exact_mod_cast hρ0.ne'
  set y : ℝ := (ρ : ℝ) ^ 2 with hy
  have hy1 : 1 < y := by rw [hy]; nlinarith
  have hy0 : 0 < y := lt_trans one_pos hy1
  have hyd : y * d₁ ≤ d₂ := by rw [hy]; exact (le_div_iff₀ hd₁).1 hρsq

  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (lam * d₂ / d₁) hy1
  obtain ⟨B', hB'⟩ := pow_unbounded_of_one_lt lam hy1
  refine ⟨(Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(B' : ℤ)) (B : ℤ)).image
      (fun k => ratPowFamily ρ hρF (fun w => -k w)), fun D hD => ?_⟩
  have hDpos : ∀ w, 0 < D w := fun w => lt_of_lt_of_le (div_pos hd₁ hlam0) (hD w).1

  choose n hn using fun w : InfinitePlace F => exists_mem_Ico_zpow (div_pos (hDpos w) hd₁) hy1
  refine ⟨ratPowFamily ρ hρF (fun w => -n w),
    Finset.mem_image.2 ⟨n, Fintype.mem_piFinset.2 fun w => ?_, rfl⟩, fun w => ?_⟩
  · obtain ⟨hlo, hhi⟩ := hn w
    have hDle : D w / d₁ ≤ lam * d₂ / d₁ := div_le_div_of_nonneg_right (hD w).2 hd₁.le
    have hDge : lam⁻¹ ≤ D w / d₁ := by
      rw [le_div_iff₀ hd₁, inv_mul_eq_div]
      exact (hD w).1
    rw [Finset.mem_Icc]
    constructor
    ·
      have h₁ : y ^ (-(B' : ℤ)) < y ^ (n w + 1) := by
        rw [zpow_neg, zpow_natCast]
        exact lt_of_lt_of_le (inv_strictAnti₀ hlam0 hB') (le_trans hDge hhi.le)
      have h₂ := (zpow_lt_zpow_iff_right₀ hy1).1 h₁
      omega
    ·
      have h₁ : y ^ n w < y ^ (B : ℤ) := by
        rw [zpow_natCast]
        exact lt_of_le_of_lt (le_trans hlo hDle) hB
      have h₂ := (zpow_lt_zpow_iff_right₀ hy1).1 h₁
      omega
  · obtain ⟨hlo, hhi⟩ := hn w
    have hP : 0 < y ^ n w := zpow_pos hy0 _
    have hnorm : ‖((ratPowFamily ρ hρF (fun w => -n w) w : (w.Completion)ˣ) : w.Completion)‖
        * ‖((ratPowFamily ρ hρF (fun w => -n w) w : (w.Completion)ˣ) : w.Completion)‖ = (y ^ n w)⁻¹ := by
      rw [norm_ratPowFamily hρ0, ← mul_zpow, ← sq, ← hy, zpow_neg]
    rw [hnorm, Set.mem_Icc, le_inv_mul_iff₀ hP, inv_mul_le_iff₀ hP]
    constructor
    ·
      have := (le_div_iff₀ hd₁).1 hlo
      linarith
    ·
      have h₁ : D w < y ^ (n w + 1) * d₁ := (div_lt_iff₀ hd₁).1 hhi
      rw [zpow_add_one₀ hy0.ne'] at h₁
      have h₂ : y ^ n w * y * d₁ ≤ y ^ n w * d₂ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hyd hP.le
      linarith

end RelaxationUnits

section RelaxedWindowCount

open MeasureTheory Set
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.AdelicLevel NumberField.AdelicHaar NumberField.TateGlobal NumberField.AdelicVolume
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction Matrix
open scoped ENNReal Classical

variable {F : Type} [Field F] [NumberField F]

private theorem intUpper_inj {a a' t t' : (𝓞 F)ˣ} {b b' : 𝓞 F} (h : intUpper a t b = intUpper a' t' b') :
    a = a' ∧ t = t' := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hc : archComponent F w (glArch (𝓞 F) F (intUpper a t b))
      = archComponent F w (glArch (𝓞 F) F (intUpper a' t' b')) := by rw [h]
  obtain ⟨h00, -, -, h11⟩ := archComponent_globalPoints_upperGL_entries w (algebraMap (𝓞 F) F (a : 𝓞 F))
    (algebraMap (𝓞 F) F b) (algebraMap (𝓞 F) F (t : 𝓞 F)) (RingOfIntegers.coe_ne_zero_iff.mpr a.ne_zero)
    (RingOfIntegers.coe_ne_zero_iff.mpr t.ne_zero)
  obtain ⟨h00', -, -, h11'⟩ := archComponent_globalPoints_upperGL_entries w (algebraMap (𝓞 F) F (a' : 𝓞 F))
    (algebraMap (𝓞 F) F b') (algebraMap (𝓞 F) F (t' : 𝓞 F)) (RingOfIntegers.coe_ne_zero_iff.mpr a'.ne_zero)
    (RingOfIntegers.coe_ne_zero_iff.mpr t'.ne_zero)
  unfold intUpper at hc
  rw [hc] at h00 h11
  rw [h00', coe_completion_eq_algebraMap, coe_completion_eq_algebraMap] at h00
  rw [h11', coe_completion_eq_algebraMap, coe_completion_eq_algebraMap] at h11
  exact ⟨Units.ext (RingOfIntegers.ext ((algebraMap F w.Completion).injective h00.symm)),
    Units.ext (RingOfIntegers.ext ((algebraMap F w.Completion).injective h11.symm))⟩

omit [NumberField F] in
private theorem place_units_mul (w : InfinitePlace F) (a t : (𝓞 F)ˣ) :
    w (algebraMap (𝓞 F) F ((a * t : (𝓞 F)ˣ) : 𝓞 F))
      = w (algebraMap (𝓞 F) F (a : 𝓞 F)) * w (algebraMap (𝓞 F) F (t : 𝓞 F)) := by
  rw [Units.val_mul, map_mul, map_mul]

private noncomputable def mkUpper (η a : (𝓞 F)ˣ) (ξ : 𝓞 F) : AdelicGL2 (𝓞 F) F :=
  intUpper a (η * a⁻¹) (ξ * ((η * a⁻¹ : (𝓞 F)ˣ) : 𝓞 F))

private theorem isIntegralUpper_mkUpper (η a : (𝓞 F)ˣ) (ξ : 𝓞 F) : IsIntegralUpper (mkUpper η a ξ) :=
  isIntegralUpper_intUpper _ _ _

private theorem IsIntegralUpper.exists_eq_mkUpper {β : AdelicGL2 (𝓞 F) F} (hβ : IsIntegralUpper β) :
    ∃ (η a : (𝓞 F)ˣ) (ξ : 𝓞 F), β = mkUpper η a ξ := by
  obtain ⟨a, t, b, rfl⟩ := hβ.exists_eq_intUpper
  refine ⟨a * t, a, b * ((t⁻¹ : (𝓞 F)ˣ) : 𝓞 F), ?_⟩
  unfold mkUpper
  rw [mul_comm a t, mul_inv_cancel_right, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

private theorem mkUpper_inj {η η' a a' : (𝓞 F)ˣ} {ξ ξ' : 𝓞 F} (h : mkUpper η a ξ = mkUpper η' a' ξ') :
    η = η' ∧ a = a' := by
  obtain ⟨ha, ht⟩ := intUpper_inj h
  subst ha
  exact ⟨mul_right_cancel ht, rfl⟩

private theorem IsIntegralUpper.mem_range {β : AdelicGL2 (𝓞 F) F} (hβ : IsIntegralUpper β) :
    β ∈ (globalPoints (𝓞 F) F).range := by
  obtain ⟨a, t, b, rfl⟩ := hβ.exists_eq_intUpper
  exact intUpper_mem_range a t b

private theorem localHeight_mkUpper_mul (η a : (𝓞 F)ˣ) (ξ : 𝓞 F) (w : InfinitePlace F) (q : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (mkUpper η a ξ * q)))
      = (w (algebraMap (𝓞 F) F (a : 𝓞 F))) ^ 2 / w (algebraMap (𝓞 F) F (η : 𝓞 F))
          * localHeight (archComponent F w (glArch (𝓞 F) F q)) := by
  unfold mkUpper
  rw [localHeight_intUpper_mul, place_units_mul, place_units_inv]
  have ha := (place_units_pos w a).ne'
  have hη := (place_units_pos w η).ne'
  congr 1
  field_simp

private theorem archDetNorm_mkUpper_mul (η a : (𝓞 F)ˣ) (ξ : 𝓞 F) (w : InfinitePlace F) (q : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (mkUpper η a ξ * q) = w (algebraMap (𝓞 F) F (η : 𝓞 F)) * archDetNorm w q := by
  unfold mkUpper
  rw [archDetNorm_intUpper_mul, place_units_mul, place_units_inv, mul_comm (w (algebraMap (𝓞 F) F (η : 𝓞 F))),
    mul_inv_cancel_left₀ (place_units_pos w a).ne']

private noncomputable def boxCentre (x : (w : InfinitePlace F) → w.Completion) (η a : (𝓞 F)ˣ) (w : InfinitePlace F) :
    w.Completion :=
  -((algebraMap F w.Completion (algebraMap (𝓞 F) F (a : 𝓞 F))
      / algebraMap F w.Completion (algebraMap (𝓞 F) F ((η * a⁻¹ : (𝓞 F)ˣ) : 𝓞 F))) * x w)

private theorem xWindowSq_mkUpper_mul (x : (w : InfinitePlace F) → w.Completion) {q : AdelicGL2 (𝓞 F) F}
    (hx : ∀ w, placeEmb w (x w) = xAtP w q) (η a : (𝓞 F)ˣ) (ξ : 𝓞 F) (w : InfinitePlace F) :
    xWindowSq (archComponent F w (glArch (𝓞 F) F (mkUpper η a ξ * q)))
      = ‖boxCentre x η a w - algebraMap F w.Completion (ξ : F)‖ ^ 2 := by
  have ht : algebraMap F w.Completion (algebraMap (𝓞 F) F ((η * a⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) ≠ 0 :=
    (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.mpr (η * a⁻¹).ne_zero)
  have hpt : placeEmb w (algebraMap F w.Completion (algebraMap (𝓞 F) F ((η * a⁻¹ : (𝓞 F)ˣ) : 𝓞 F))) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_placeEmb, norm_algebraMap_completion_eq]
    exact (place_units_pos w (η * a⁻¹)).ne'
  unfold mkUpper boxCentre
  rw [xWindowSq_eq_norm_xAtP_sq, xAtP_intUpper_mul, ← hx w]
  congr 1
  rw [← norm_placeEmb w, ← norm_neg]
  congr 1
  simp only [coe_completion_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_neg,
    map_div₀]
  field_simp
  ring

private noncomputable def floorsOf (r : InfinitePlace F → ℝ) : {w : InfinitePlace F // w ≠ w₀} → ℝ :=
  fun w => -(mult w.1 * Real.log (r w.1)) / 2

private noncomputable def floorsOf₀ (r : InfinitePlace F → ℝ) : ℝ :=
  -(mult (w₀ : InfinitePlace F) * Real.log (r w₀)) / 2

private noncomputable def relaxShift (lam : ℝ) : {w : InfinitePlace F // w ≠ w₀} → ℝ :=
  fun w => mult w.1 * Real.log lam / 2

private noncomputable def relaxShift₀ (F : Type) [Field F] [NumberField F] (lam : ℝ) : ℝ :=
  mult (w₀ : InfinitePlace F) * Real.log lam / 2

private theorem relaxShift_nonneg {lam : ℝ} (hlam : 1 ≤ lam) (w : {w : InfinitePlace F // w ≠ w₀}) :
    0 ≤ relaxShift lam w := by
  unfold relaxShift
  have := Real.log_nonneg hlam
  positivity

private theorem relaxShift₀_nonneg {lam : ℝ} (hlam : 1 ≤ lam) : 0 ≤ relaxShift₀ F lam := by
  unfold relaxShift₀
  have := Real.log_nonneg hlam
  positivity

private noncomputable def thresholds (c : ℝ) (h : InfinitePlace F → ℝ) (η : (𝓞 F)ˣ) : InfinitePlace F → ℝ :=
  fun w => c * w (algebraMap (𝓞 F) F (η : 𝓞 F)) / h w

omit [NumberField F] in
private theorem thresholds_pos {c : ℝ} (hc : 0 < c) {h : InfinitePlace F → ℝ} (hh : ∀ w, 0 < h w) (η : (𝓞 F)ˣ)
    (w : InfinitePlace F) : 0 < thresholds c h η w :=
  div_pos (mul_pos hc (place_units_pos w η)) (hh w)

private theorem mem_floorRegion_thresholds_iff {c : ℝ} (hc : 0 < c) {h : InfinitePlace F → ℝ} (hh : ∀ w, 0 < h w)
    (η a : (𝓞 F)ˣ) :
    logEmbedding F (Additive.ofMul a) ∈ floorRegion (floorsOf (thresholds c h η)) (floorsOf₀ (thresholds c h η)) ↔
      ∀ w : InfinitePlace F,
        c ≤ (w (algebraMap (𝓞 F) F (a : 𝓞 F))) ^ 2 / w (algebraMap (𝓞 F) F (η : 𝓞 F)) * h w := by
  unfold floorsOf floorsOf₀
  rw [← forall_le_sq_iff_logEmbedding_mem_floorRegion (thresholds c h η) (thresholds_pos hc hh η) a]
  refine forall_congr' fun w => ?_
  unfold thresholds
  rw [div_le_iff₀ (hh w), div_mul_eq_mul_div, le_div_iff₀ (place_units_pos w η)]

private theorem floorsOf_thresholds_div {c : ℝ} (hc : 0 < c) {h : InfinitePlace F → ℝ} (hh : ∀ w, 0 < h w)
    (η : (𝓞 F)ˣ) {lam : ℝ} (hlam : 0 < lam) :
    floorsOf (thresholds (c / lam) h η) = floorsOf (thresholds c h η) + relaxShift lam ∧
      floorsOf₀ (thresholds (c / lam) h η) = floorsOf₀ (thresholds c h η) + relaxShift₀ F lam := by
  have key : ∀ w : InfinitePlace F, thresholds (c / lam) h η w = thresholds c h η w / lam := by
    intro w
    unfold thresholds
    ring
  constructor
  · funext w
    simp only [floorsOf, relaxShift, Pi.add_apply, key]
    rw [Real.log_div (thresholds_pos hc hh η w.1).ne' hlam.ne']
    ring
  · simp only [floorsOf₀, relaxShift₀, key]
    rw [Real.log_div (thresholds_pos hc hh η w₀).ne' hlam.ne']
    ring

private theorem finite_box (z : (w : InfinitePlace F) → w.Completion) (r : ℝ) :
    {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ r}.Finite := by
  by_cases hne : ∃ ξ₀ : 𝓞 F, ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ₀ : F)‖ ≤ r
  · obtain ⟨ξ₀, hξ₀⟩ := hne
    refine Set.Finite.of_finite_image ((finite_setOf_forall_norm_le (F := F) (2 * r)).subset ?_)
      (fun ξ _ ξ' _ h => by simpa using h : Set.InjOn (fun ξ : 𝓞 F => ξ - ξ₀) _)
    rintro _ ⟨ξ, hξ, rfl⟩ w
    have hsub : algebraMap F w.Completion ((ξ - ξ₀ : 𝓞 F) : F)
        = (z w - algebraMap F w.Completion (ξ₀ : F)) - (z w - algebraMap F w.Completion (ξ : F)) := by
      rw [show ((ξ - ξ₀ : 𝓞 F) : F) = (ξ : F) - (ξ₀ : F) from map_sub (algebraMap (𝓞 F) F) ξ ξ₀, map_sub]
      ring
    rw [hsub]
    calc ‖(z w - algebraMap F w.Completion (ξ₀ : F)) - (z w - algebraMap F w.Completion (ξ : F))‖
        ≤ ‖z w - algebraMap F w.Completion (ξ₀ : F)‖ + ‖z w - algebraMap F w.Completion (ξ : F)‖ :=
          norm_sub_le _ _
      _ ≤ r + r := add_le_add (hξ₀ w) (hξ w)
      _ = 2 * r := by ring
  · convert Set.finite_empty
    exact Set.eq_empty_of_forall_notMem fun ξ hξ => hne ⟨ξ, hξ⟩

private theorem finite_setOf_forall_le_place {r : ℝ} (hr : 0 < r) :
    {η : (𝓞 F)ˣ | ∀ w : InfinitePlace F, r ≤ w (algebraMap (𝓞 F) F (η : 𝓞 F))}.Finite := by
  obtain ⟨b, T₀, -, hb⟩ := exists_basis_nat_forall_finite_and_ncard_le_and_ncard_le (F := F)
  obtain ⟨_lamR, -, hfin⟩ := exists_forall_finite_and_ncard_floorRegion_le b
  refine ((hb _ (hfin (floorsOf (F := F) fun _ => r ^ 2) (floorsOf₀ (F := F) fun _ => r ^ 2)).1).1).subset
    fun η hη => ?_
  show logEmbedding F (Additive.ofMul η) ∈
    floorRegion (floorsOf (F := F) fun _ => r ^ 2) (floorsOf₀ (F := F) fun _ => r ^ 2)
  unfold floorsOf floorsOf₀
  exact (forall_le_sq_iff_logEmbedding_mem_floorRegion (F := F) (fun _ => r ^ 2) (fun _ => pow_pos hr 2) η).1
    fun w => pow_le_pow_left₀ hr.le (hη w) 2

private theorem norm_le_abs_of_sq_le_sq {v : ℝ} (hv : 0 ≤ v) {s : ℝ} (h : v ^ 2 ≤ s ^ 2) : v ≤ |s| := by
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg hv] at this

private def unitsIn (S : Set (logSpace F)) : Set (𝓞 F)ˣ := {ε | logEmbedding F (Additive.ofMul ε) ∈ S}

private def latticeIn (b : Module.Basis (Fin (rank F)) ℝ (logSpace F)) (S : Set (logSpace F)) :
    Set (Fin (rank F) → ℤ) :=
  {n | cosetPt b 0 1 n ∈ S}

private noncomputable def heightRegion (c : ℝ) (h : InfinitePlace F → ℝ) (η : (𝓞 F)ˣ) : Set (logSpace F) :=
  floorRegion (floorsOf (thresholds c h η)) (floorsOf₀ (thresholds c h η))

private theorem mem_unitsIn_heightRegion_iff {c : ℝ} (hc : 0 < c) {h : InfinitePlace F → ℝ} (hh : ∀ w, 0 < h w)
    (η a : (𝓞 F)ˣ) :
    a ∈ unitsIn (heightRegion c h η) ↔
      ∀ w : InfinitePlace F, c ≤ (w (algebraMap (𝓞 F) F (a : 𝓞 F))) ^ 2 / w (algebraMap (𝓞 F) F (η : 𝓞 F)) * h w :=
  mem_floorRegion_thresholds_iff hc hh η a

private theorem heightRegion_div {c : ℝ} (hc : 0 < c) {h : InfinitePlace F → ℝ} (hh : ∀ w, 0 < h w) (η : (𝓞 F)ˣ)
    {lam : ℝ} (hlam : 0 < lam) :
    heightRegion (c / lam) h η = floorRegion (floorsOf (thresholds c h η) + relaxShift lam)
      (floorsOf₀ (thresholds c h η) + relaxShift₀ F lam) := by
  obtain ⟨h₁, h₂⟩ := floorsOf_thresholds_div hc hh η hlam
  unfold heightRegion
  rw [h₁, h₂]

private theorem exists_finset_class_bound (c u d₁ d₂ lam : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hlam : 1 ≤ lam)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (A : ℕ) (hA : ∀ z : (w : InfinitePlace F) → w.Completion,
      {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ |lam * u|}.ncard ≤ A)
    (b : Module.Basis (Fin (rank F)) ℝ (logSpace F)) (T₀ : ℕ)
    (hb : ∀ S : Set (logSpace F), {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.Finite →
      {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.Finite ∧
      {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.ncard
          ≤ {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.ncard ∧
      {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.ncard
          ≤ T₀ * {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.ncard)
    (hlat : ∀ (t : {w : InfinitePlace F // w ≠ w₀} → ℝ) (t₀ : ℝ),
      {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.Finite)
    (K C₀ s₀ : ℝ)
    (hKC : ∀ (t : {w : InfinitePlace F // w ≠ w₀} → ℝ) (t₀ : ℝ),
      (t₀ + ∑ i, t i < s₀ →
        ({n : Fin (rank F) → ℤ |
          cosetPt b 0 1 n ∈ floorRegion (t + relaxShift lam) (t₀ + relaxShift₀ F lam)}.ncard : ℝ) ≤ C₀) ∧
      (s₀ ≤ t₀ + ∑ i, t i →
        ({n : Fin (rank F) → ℤ |
          cosetPt b 0 1 n ∈ floorRegion (t + relaxShift lam) (t₀ + relaxShift₀ F lam)}.ncard : ℝ)
          ≤ K * ({n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.ncard : ℝ)))
    (ρ₀ : ℝ) (hρ₀ : ρ₀ = lam ^ 2 * d₂ / d₁) (H₀ : Finset (𝓞 F)ˣ)
    (hH₀ : ∀ η : (𝓞 F)ˣ, η ∈ H₀ ↔ ∀ w : InfinitePlace F,
      ρ₀⁻¹ ≤ w (algebraMap (𝓞 F) F (η : 𝓞 F)) ∧ w (algebraMap (𝓞 F) F (η : 𝓞 F)) ≤ ρ₀)
    (Z : Finset (AdeleRing (𝓞 F) F)ˣ)
    (hZ : ∀ D : InfinitePlace F → ℝ, (∀ w, D w ∈ Icc (d₁ / (lam * ρ₀)) (lam * ρ₀ * d₂)) →
      ∃ fam : (w : InfinitePlace F) → (w.Completion)ˣ, (archNetUnit fam)⁻¹ ∈ Z ∧
        ∀ w : InfinitePlace F, ‖(fam w : w.Completion)‖ * ‖(fam w : w.Completion)‖ * D w ∈ Icc d₁ d₂)
    {q : AdelicGL2 (𝓞 F) F} (hq : q ∈ centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)) :
    ∃ (P : Finset (AdelicGL2 (𝓞 F) F)) (Φ : (AdeleRing (𝓞 F) F)ˣ → Finset (AdelicGL2 (𝓞 F) F)),
      (∀ β : AdelicGL2 (𝓞 F) F, IsIntegralUpper β →
        β * q ∈ centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂) → β ∈ P) ∧
      (∀ z : (AdeleRing (𝓞 F) F)ˣ, ∀ β ∈ Φ z, IsIntegralUpper β ∧
        β * q ∈ (· * centralScalar (𝓞 F) F z) '' centreCutSiegelSet F c u d₁ d₂) ∧
      (P.card : ℝ) ≤ A * T₀ * max 0 K * ∑ z ∈ Z, ((Φ z).card : ℝ) + A * T₀ * max 0 C₀ * H₀.card := by
  classical
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hd₂ : 0 < d₂ := hd₁.trans hd
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hcl : 0 < c / lam := div_pos hc hlam0
  obtain ⟨hqfin, hqh, -, hqd⟩ := mem_centreCutSiegelSet_iff.1 hq

  set hgt : InfinitePlace F → ℝ := fun w => localHeight (archComponent F w (glArch (𝓞 F) F q)) with hhgt
  have hhpos : ∀ w, 0 < hgt w := fun w => lt_of_lt_of_le hcl (hqh w)
  choose xq hxq using fun w : InfinitePlace F => exists_placeEmb_eq_xAtP w q
  have hlatR : ∀ (c' : ℝ) (η : (𝓞 F)ˣ), (latticeIn b (heightRegion c' hgt η)).Finite := fun c' η => hlat _ _
  have hEfin : ∀ η : (𝓞 F)ˣ, (unitsIn (heightRegion c hgt η)).Finite := fun η => (hb _ (hlatR c η)).1
  have hErfin : ∀ η : (𝓞 F)ˣ, (unitsIn (heightRegion (c / lam) hgt η)).Finite := fun η => (hb _ (hlatR (c / lam) η)).1

  have hfamall : ∀ p : (Σ _ : (𝓞 F)ˣ, (𝓞 F)ˣ), ∃ fam : (w : InfinitePlace F) → (w.Completion)ˣ,
      p.1 ∈ H₀ → (archNetUnit fam)⁻¹ ∈ Z ∧ ∀ w : InfinitePlace F,
        ‖(fam w : w.Completion)‖ * ‖(fam w : w.Completion)‖
          * (w (algebraMap (𝓞 F) F (p.1 : 𝓞 F)) * archDetNorm w q) ∈ Icc d₁ d₂ := by
    intro p
    by_cases hp : p.1 ∈ H₀
    · obtain ⟨fam, hfam₁, hfam₂⟩ :=
        hZ (fun w => w (algebraMap (𝓞 F) F (p.1 : 𝓞 F)) * archDetNorm w q) fun w => by
          obtain ⟨hη₁, hη₂⟩ := (hH₀ p.1).1 hp w
          obtain ⟨hD₁, hD₂⟩ := hqd w
          have hDpos : 0 < archDetNorm w q := lt_of_lt_of_le (div_pos hd₁ hlam0) hD₁
          have hlamne := hlam0.ne'
          have hρ₀ne := hρ₀pos.ne'
          constructor
          · calc d₁ / (lam * ρ₀) = ρ₀⁻¹ * (d₁ / lam) := by field_simp
              _ ≤ w (algebraMap (𝓞 F) F (p.1 : 𝓞 F)) * archDetNorm w q :=
                mul_le_mul hη₁ hD₁ (div_pos hd₁ hlam0).le ((inv_pos.2 hρ₀pos).le.trans hη₁)
          · calc w (algebraMap (𝓞 F) F (p.1 : 𝓞 F)) * archDetNorm w q ≤ ρ₀ * (lam * d₂) :=
                mul_le_mul hη₂ hD₂ hDpos.le hρ₀pos.le
              _ = lam * ρ₀ * d₂ := by ring
      exact ⟨fam, fun _ => ⟨hfam₁, hfam₂⟩⟩
    · exact ⟨fun _ => 1, fun h => absurd h hp⟩
  choose fam hfam using hfamall
  choose ξf hξf using fun p : (Σ _ : (𝓞 F)ˣ, (𝓞 F)ˣ) => hu (boxCentre xq p.1 p.2)
  refine ⟨(H₀.sigma fun η => (hErfin η).toFinset.sigma fun a =>
      (finite_box (boxCentre xq η a) |lam * u|).toFinset).image fun p => mkUpper p.1 p.2.1 p.2.2,
    fun z => ((H₀.sigma fun η => (hEfin η).toFinset).filter fun p => (archNetUnit (fam p))⁻¹ = z).image
      fun p => mkUpper p.1 p.2 (ξf p), ?_, ?_, ?_⟩
  ·
    intro β hβ hβq
    obtain ⟨η, a, ξ, rfl⟩ := hβ.exists_eq_mkUpper
    obtain ⟨-, hbh, hbx, hbd⟩ := mem_centreCutSiegelSet_iff.1 hβq
    refine Finset.mem_image.2 ⟨⟨η, a, ξ⟩, Finset.mem_sigma.2 ⟨?_, Finset.mem_sigma.2 ⟨?_, ?_⟩⟩, rfl⟩
    ·
      rw [hH₀]
      intro w
      obtain ⟨hD₁, hD₂⟩ := hqd w
      obtain ⟨hβ₁, hβ₂⟩ := hbd w
      rw [archDetNorm_mkUpper_mul] at hβ₁ hβ₂
      have hDpos : 0 < archDetNorm w q := lt_of_lt_of_le (div_pos hd₁ hlam0) hD₁
      have hηpos := place_units_pos w η
      have hlamne := hlam0.ne'
      constructor
      · have h1 : d₁ / lam ≤ w (algebraMap (𝓞 F) F (η : 𝓞 F)) * (lam * d₂) :=
          hβ₁.trans (mul_le_mul_of_nonneg_left hD₂ hηpos.le)
        rw [div_le_iff₀ hlam0] at h1
        rw [hρ₀, inv_eq_one_div, div_le_iff₀ (by positivity), mul_div_assoc', le_div_iff₀ hd₁, one_mul]
        nlinarith [h1]
      · have h1 : w (algebraMap (𝓞 F) F (η : 𝓞 F)) * (d₁ / lam) ≤ lam * d₂ :=
          (mul_le_mul_of_nonneg_left hD₁ hηpos.le).trans hβ₂
        have h2 : w (algebraMap (𝓞 F) F (η : 𝓞 F)) * d₁ ≤ lam * (lam * d₂) := by
          calc w (algebraMap (𝓞 F) F (η : 𝓞 F)) * d₁
              = lam * (w (algebraMap (𝓞 F) F (η : 𝓞 F)) * (d₁ / lam)) := by field_simp
            _ ≤ lam * (lam * d₂) := mul_le_mul_of_nonneg_left h1 hlam0.le
        rw [hρ₀, le_div_iff₀ hd₁]
        nlinarith [h2]
    ·
      rw [Set.Finite.mem_toFinset, mem_unitsIn_heightRegion_iff hcl hhpos]
      intro w
      have := hbh w
      rwa [localHeight_mkUpper_mul] at this
    ·
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro w
      have hx := hbx w
      rw [xWindowSq_mkUpper_mul xq hxq] at hx
      exact norm_le_abs_of_sq_le_sq (norm_nonneg _) hx
  ·
    intro z β hβ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hβ
    obtain ⟨hpDom, hpz⟩ := Finset.mem_filter.1 hp
    have hpz' : (archNetUnit (fam p))⁻¹ = z := hpz
    obtain ⟨hpη, hpa⟩ := Finset.mem_sigma.1 hpDom
    obtain ⟨-, hfamD⟩ := hfam p hpη
    rw [Set.Finite.mem_toFinset, mem_unitsIn_heightRegion_iff hc hhpos] at hpa
    refine ⟨isIntegralUpper_mkUpper _ _ _,
      centralScalar (𝓞 F) F (archNetUnit (fam p)) * (mkUpper p.1 p.2 (ξf p) * q), ?_, ?_⟩
    · refine mem_centreCutSiegelSet_iff.2 ⟨?_, ?_, ?_, ?_⟩
      · rw [glFin_netScalar_mul, map_mul]
        exact Subgroup.mul_mem _ (glFin_intUpper_mem _ _ _) hqfin
      · intro w
        rw [localHeight_netScalar_mul, localHeight_mkUpper_mul]
        exact hpa w
      · intro w
        rw [xWindowSq_netScalar_mul, xWindowSq_mkUpper_mul xq hxq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hξf p w) 2
      · intro w
        rw [archDetNorm_netScalar_mul, archDetNorm_mkUpper_mul]
        exact hfamD w
    ·
      show centralScalar (𝓞 F) F (archNetUnit (fam p)) * (mkUpper p.1 p.2 (ξf p) * q) * centralScalar (𝓞 F) F z
        = mkUpper p.1 p.2 (ξf p) * q
      rw [← hpz', ← mul_centralScalar_comm (archNetUnit (fam p)), mul_assoc,
        ← map_mul (centralScalar (𝓞 F) F) (archNetUnit (fam p)) (archNetUnit (fam p))⁻¹, mul_inv_cancel, map_one,
        mul_one]
  ·
    have hinj : Set.InjOn (fun p : (Σ _ : (𝓞 F)ˣ, (𝓞 F)ˣ) => mkUpper p.1 p.2 (ξf p))
        ↑(H₀.sigma fun η => (hEfin η).toFinset) := by
      intro p _ p' _ hpp'
      obtain ⟨hη, ha⟩ := mkUpper_inj hpp'
      exact Sigma.ext hη (heq_of_eq ha)

    have hright : ∑ z ∈ Z, ((((H₀.sigma fun η => (hEfin η).toFinset).filter
          fun p => (archNetUnit (fam p))⁻¹ = z).image fun p => mkUpper p.1 p.2 (ξf p)).card : ℝ)
        = ∑ η ∈ H₀, ((unitsIn (heightRegion c hgt η)).ncard : ℝ) := by
      have hζZ : ∀ p ∈ (H₀.sigma fun η => (hEfin η).toFinset), (archNetUnit (fam p))⁻¹ ∈ Z :=
        fun p hp => (hfam p (Finset.mem_sigma.1 hp).1).1
      rw [← Nat.cast_sum, ← Nat.cast_sum]
      congr 1
      calc ∑ z ∈ Z, (((H₀.sigma fun η => (hEfin η).toFinset).filter
              fun p => (archNetUnit (fam p))⁻¹ = z).image fun p => mkUpper p.1 p.2 (ξf p)).card
          = ∑ z ∈ Z, ((H₀.sigma fun η => (hEfin η).toFinset).filter fun p => (archNetUnit (fam p))⁻¹ = z).card :=
            Finset.sum_congr rfl fun z _ =>
              Finset.card_image_of_injOn (hinj.mono fun p hp => (Finset.mem_filter.1 hp).1)
        _ = (H₀.sigma fun η => (hEfin η).toFinset).card := (Finset.card_eq_sum_card_fiberwise hζZ).symm
        _ = ∑ η ∈ H₀, ((hEfin η).toFinset).card := Finset.card_sigma _ _
        _ = _ := Finset.sum_congr rfl fun η _ => by rw [Set.ncard_eq_toFinset_card _ (hEfin η)]

    have hleft : (((H₀.sigma fun η => (hErfin η).toFinset.sigma fun a =>
          (finite_box (boxCentre xq η a) |lam * u|).toFinset).image fun p => mkUpper p.1 p.2.1 p.2.2).card : ℝ)
        ≤ A * ∑ η ∈ H₀, ((unitsIn (heightRegion (c / lam) hgt η)).ncard : ℝ) := by
      rw [Finset.mul_sum]
      refine (Nat.cast_le.2 Finset.card_image_le).trans ?_
      rw [Finset.card_sigma, Nat.cast_sum]
      refine Finset.sum_le_sum fun η _ => ?_
      rw [Finset.card_sigma, Nat.cast_sum, Set.ncard_eq_toFinset_card _ (hErfin η)]
      calc _ ≤ ∑ _a ∈ (hErfin η).toFinset, (A : ℝ) := Finset.sum_le_sum fun a _ => ?_
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [← Set.ncard_eq_toFinset_card _ (finite_box (boxCentre xq η a) |lam * u|)]
      exact_mod_cast hA (boxCentre xq η a)

    have hper : ∀ η : (𝓞 F)ˣ, ((unitsIn (heightRegion (c / lam) hgt η)).ncard : ℝ)
        ≤ T₀ * (max 0 K * ((unitsIn (heightRegion c hgt η)).ncard : ℝ) + max 0 C₀) := by
      intro η
      have hreg := heightRegion_div hc hhpos η hlam0
      obtain ⟨-, -, hEr₂⟩ := hb _ (hlat (floorsOf (thresholds c hgt η) + relaxShift lam)
        (floorsOf₀ (thresholds c hgt η) + relaxShift₀ F lam))
      obtain ⟨-, hE₁, -⟩ := hb _ (hlatR c η)
      obtain ⟨hsmall, hlarge⟩ := hKC (floorsOf (thresholds c hgt η)) (floorsOf₀ (thresholds c hgt η))
      set Lr : ℝ := ((latticeIn b (floorRegion (floorsOf (thresholds c hgt η) + relaxShift lam)
        (floorsOf₀ (thresholds c hgt η) + relaxShift₀ F lam))).ncard : ℝ) with hLr
      set L : ℝ := ((latticeIn b (heightRegion c hgt η)).ncard : ℝ) with hL
      have hEr₂' : ((unitsIn (heightRegion (c / lam) hgt η)).ncard : ℝ) ≤ T₀ * Lr := by
        rw [hreg, hLr]
        unfold unitsIn latticeIn
        exact_mod_cast hEr₂
      have hE₁' : L ≤ ((unitsIn (heightRegion c hgt η)).ncard : ℝ) := by
        rw [hL]
        unfold unitsIn latticeIn
        exact_mod_cast hE₁
      have hsmall' : floorsOf₀ (thresholds c hgt η) + ∑ i, floorsOf (thresholds c hgt η) i < s₀ → Lr ≤ C₀ := hsmall
      have hlarge' : s₀ ≤ floorsOf₀ (thresholds c hgt η) + ∑ i, floorsOf (thresholds c hgt η) i → Lr ≤ K * L := hlarge
      have hT₀ : (0 : ℝ) ≤ T₀ := Nat.cast_nonneg _
      have hKnn : 0 ≤ max 0 K := le_max_left _ _
      have hC₀ : C₀ ≤ max 0 C₀ := le_max_right _ _
      have hC₀nn : (0 : ℝ) ≤ max 0 C₀ := le_max_left _ _
      have hEnn : (0 : ℝ) ≤ ((unitsIn (heightRegion c hgt η)).ncard : ℝ) := Nat.cast_nonneg _
      have hLnn : 0 ≤ L := Nat.cast_nonneg _
      refine hEr₂'.trans (mul_le_mul_of_nonneg_left ?_ hT₀)
      rcases lt_or_ge (floorsOf₀ (thresholds c hgt η) + ∑ i, floorsOf (thresholds c hgt η) i) s₀ with hs | hs
      · have h := hsmall' hs
        nlinarith [mul_nonneg hKnn hEnn]
      · have h := hlarge' hs
        nlinarith [mul_nonneg (sub_nonneg.2 (le_max_right (0 : ℝ) K)) hLnn, mul_nonneg hKnn (sub_nonneg.2 hE₁')]

    calc _ ≤ _ := hleft
      _ ≤ A * ∑ η ∈ H₀, (T₀ * (max 0 K * ((unitsIn (heightRegion c hgt η)).ncard : ℝ) + max 0 C₀)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun η _ => hper η) (Nat.cast_nonneg _)
      _ = A * T₀ * max 0 K * ∑ η ∈ H₀, ((unitsIn (heightRegion c hgt η)).ncard : ℝ) + A * T₀ * max 0 C₀ * H₀.card := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ = _ := by rw [hright]

private theorem exists_finset_class_bound' (c u d₁ d₂ lam : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hlam : 1 ≤ lam)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (A : ℕ) (hA : ∀ z : (w : InfinitePlace F) → w.Completion,
      {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ |lam * u|}.ncard ≤ A)
    (b : Module.Basis (Fin (rank F)) ℝ (logSpace F)) (T₀ : ℕ)
    (hb : ∀ S : Set (logSpace F), {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.Finite →
      {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.Finite ∧
      {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.ncard
          ≤ {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.ncard ∧
      {ε : (𝓞 F)ˣ | logEmbedding F (Additive.ofMul ε) ∈ S}.ncard
          ≤ T₀ * {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ S}.ncard)
    (hlat : ∀ (t : {w : InfinitePlace F // w ≠ w₀} → ℝ) (t₀ : ℝ),
      {n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.Finite)
    (K C₀ s₀ : ℝ)
    (hKC : ∀ (t : {w : InfinitePlace F // w ≠ w₀} → ℝ) (t₀ : ℝ),
      (t₀ + ∑ i, t i < s₀ →
        ({n : Fin (rank F) → ℤ |
          cosetPt b 0 1 n ∈ floorRegion (t + relaxShift lam) (t₀ + relaxShift₀ F lam)}.ncard : ℝ) ≤ C₀) ∧
      (s₀ ≤ t₀ + ∑ i, t i →
        ({n : Fin (rank F) → ℤ |
          cosetPt b 0 1 n ∈ floorRegion (t + relaxShift lam) (t₀ + relaxShift₀ F lam)}.ncard : ℝ)
          ≤ K * ({n : Fin (rank F) → ℤ | cosetPt b 0 1 n ∈ floorRegion t t₀}.ncard : ℝ)))
    (ρ₀ : ℝ) (hρ₀ : ρ₀ = lam ^ 2 * d₂ / d₁) (H₀ : Finset (𝓞 F)ˣ)
    (hH₀ : ∀ η : (𝓞 F)ˣ, η ∈ H₀ ↔ ∀ w : InfinitePlace F,
      ρ₀⁻¹ ≤ w (algebraMap (𝓞 F) F (η : 𝓞 F)) ∧ w (algebraMap (𝓞 F) F (η : 𝓞 F)) ≤ ρ₀)
    (Z : Finset (AdeleRing (𝓞 F) F)ˣ)
    (hZ : ∀ D : InfinitePlace F → ℝ, (∀ w, D w ∈ Icc (d₁ / (lam * ρ₀)) (lam * ρ₀ * d₂)) →
      ∃ fam : (w : InfinitePlace F) → (w.Completion)ˣ, (archNetUnit fam)⁻¹ ∈ Z ∧
        ∀ w : InfinitePlace F, ‖(fam w : w.Completion)‖ * ‖(fam w : w.Completion)‖ * D w ∈ Icc d₁ d₂)
    (q : AdelicGL2 (𝓞 F) F) :
    ∃ (P : Finset (AdelicGL2 (𝓞 F) F)) (Φ : (AdeleRing (𝓞 F) F)ˣ → Finset (AdelicGL2 (𝓞 F) F)),
      (∀ β : AdelicGL2 (𝓞 F) F, IsIntegralUpper β →
        β * q ∈ centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂) → β ∈ P) ∧
      (∀ z : (AdeleRing (𝓞 F) F)ˣ, ∀ β ∈ Φ z, IsIntegralUpper β ∧
        β * q ∈ (· * centralScalar (𝓞 F) F z) '' centreCutSiegelSet F c u d₁ d₂) ∧
      (P.card : ℝ) ≤ A * T₀ * max 0 K * ∑ z ∈ Z, ((Φ z).card : ℝ) + A * T₀ * max 0 C₀ * H₀.card := by
  classical
  by_cases hne : ∃ β₁ : AdelicGL2 (𝓞 F) F, IsIntegralUpper β₁ ∧
      β₁ * q ∈ centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)
  · obtain ⟨β₁, hβ₁, hβ₁q⟩ := hne
    obtain ⟨P, Φ, hP, hΦ, hcard⟩ := exists_finset_class_bound c u d₁ d₂ lam hc hd₁ hd hlam hu A hA b T₀ hb hlat K C₀ s₀
      hKC ρ₀ hρ₀ H₀ hH₀ Z hZ hβ₁q
    refine ⟨P.image (· * β₁), fun z => (Φ z).image (· * β₁), ?_, ?_, ?_⟩
    · intro β hβ hβq
      refine Finset.mem_image.2 ⟨β * β₁⁻¹, hP _ (hβ.mul hβ₁.inv) ?_, by simp⟩
      rwa [mul_assoc, ← mul_assoc β₁⁻¹, inv_mul_cancel, one_mul]
    · intro z β hβ
      obtain ⟨β', hβ', rfl⟩ := Finset.mem_image.1 hβ
      obtain ⟨hβ'IU, hβ'q⟩ := hΦ z β' hβ'
      exact ⟨hβ'IU.mul hβ₁, by rwa [mul_assoc]⟩
    · have himg : ∀ z, ((Φ z).image (· * β₁)).card = (Φ z).card :=
        fun z => Finset.card_image_of_injective _ (mul_left_injective β₁)
      simp only [himg]
      exact (Nat.cast_le.2 Finset.card_image_le).trans hcard
  · refine ⟨∅, fun _ => ∅, fun β hβ hβq => absurd ⟨β, hβ, hβq⟩ hne,
      fun z β hβ => absurd hβ (Finset.notMem_empty β), ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, mul_zero, zero_add]
    positivity

end RelaxedWindowCount

section MassRelaxLeMulOfCoveringParameter
open scoped ENNReal
open MeasureTheory IsDedekindDomain Matrix
open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal Topology
attribute [local instance] glBorel

section RelaxedWindowComparison

open MeasureTheory IsDedekindDomain Matrix Set
open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.TateGlobal
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal

attribute [local instance] glBorel

variable {F : Type} [Field F] [NumberField F]

private theorem countable_of_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

private theorem countable_globalPoints_range : Countable (globalPoints (𝓞 F) F).range := by
  haveI : Countable F := countable_of_numberField
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (Set.countable_range (globalPoints (𝓞 F) F)).to_subtype

private theorem measurableConstSMul_globalPoints_range :
    MeasurableConstSMul (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine ⟨fun γ => ?_⟩
  simpa only [Subgroup.smul_def, smul_eq_mul] using
    (show Continuous fun x : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * x from
      continuous_const.mul continuous_id).measurable

private theorem preimage_globalPoints_mul_slab (γ : (globalPoints (𝓞 F) F).range) (a b : ℝ) :
    (fun x : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * x) ⁻¹'
        {g | ideleNorm F (GeneralLinearGroup.det g) ∈ Icc a b}
      = {g | ideleNorm F (GeneralLinearGroup.det g) ∈ Icc a b} := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ← hγ₀, map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

private theorem smulInvariantMeasure_restrict_slab (a b : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (GeneralLinearGroup.det g) ∈ Icc a b}) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  simp only [Subgroup.smul_def, smul_eq_mul]
  have hm : Measurable fun x : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * x :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.restrict_apply (hs.preimage hm), Measure.restrict_apply hs,
    ← preimage_globalPoints_mul_slab γ a b, ← Set.preimage_inter, measure_preimage_mul,
    preimage_globalPoints_mul_slab γ a b]

private theorem orbitCount_eq_zero_of_subset_slab {a b : ℝ} {V : Set (AdelicGL2 (𝓞 F) F)}
    (hV : V ⊆ {g | ideleNorm F (GeneralLinearGroup.det g) ∈ Icc a b}) {x : AdelicGL2 (𝓞 F) F}
    (hx : ideleNorm F (GeneralLinearGroup.det x) ∉ Icc a b) :
    orbitCount (globalPoints (𝓞 F) F).range V x = 0 := by
  simp only [orbitCount]
  refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_apply_eq_zero.2 fun hmem => (hx ?_).elim
  have h := hV hmem
  rw [Subgroup.smul_def, smul_eq_mul] at h
  have h' := (Set.ext_iff.1 (preimage_globalPoints_mul_slab γ a b) x).1 h
  exact h'

private theorem measurableSet_translates (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine T.measurableSet_biUnion fun x _ => ?_
  rw [Set.image_mul_right]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (continuous_id.mul continuous_const).measurable

private theorem setLIntegral_image_mul_centralScalar {χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ χ φ) {W : Set (AdelicGL2 (𝓞 F) F)}
    (hW : MeasurableSet W) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ∫⁻ y in (· * centralScalar (𝓞 F) F z) '' W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 *
          ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isMulRightInvariant_adelicGLHaar F
  rw [setLIntegral_image_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) _ hW, ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun hW fun y _ => ?_
  rw [mul_centralScalar_comm, hφ.central_transform ⟨z, Subgroup.mem_top z⟩ y, nnnorm_mul, ENNReal.coe_mul, mul_pow]

private theorem exists_finset_forall_orbitCount_relaxedWindow_le
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (lam : ℝ) (hlam : 1 ≤ lam) {a b : ℝ} (ha : 0 < a) :
    ∃ Z : Finset (AdeleRing (𝓞 F) F)ˣ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : AdelicGL2 (𝓞 F) F,
      ideleNorm F (GeneralLinearGroup.det x) ∈ Icc a b →
        orbitCount (globalPoints (𝓞 F) F).range
            (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)) x
          ≤ ENNReal.ofReal M * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
              ((· * centralScalar (𝓞 F) F z) '' ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) x := by
  classical
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hd₂ : 0 < d₂ := hd₁.trans hd

  rcases le_or_gt a b with hab | hab
  swap
  · exact ⟨∅, 0, le_rfl, fun x hx => absurd (hx.1.trans hx.2) (not_le.2 hab)⟩

  obtain ⟨N₀, hN₀⟩ := exists_nat_forall_exists_finset_representatives c u d₁ d₂ T hc hd₁ hu lam hlam
  obtain ⟨bb, T₀, -, hb⟩ := exists_basis_nat_forall_finite_and_ncard_le_and_ncard_le (F := F)
  obtain ⟨_lamR, -, hfin⟩ := exists_forall_finite_and_ncard_floorRegion_le bb
  obtain ⟨K, C₀, s₀, hKC⟩ := exists_forall_ncard_floorRegion_relax_le bb (relaxShift lam) (relaxShift_nonneg hlam)
    (relaxShift₀ F lam) (relaxShift₀_nonneg hlam)
  obtain ⟨A, hA⟩ := exists_forall_ncard_box_le (F := F) |lam * u|
  set ρ₀ : ℝ := lam ^ 2 * d₂ / d₁ with hρ₀
  have hρ₀pos : 0 < ρ₀ := by positivity
  have hρ₀one : 1 ≤ ρ₀ := by
    rw [hρ₀, le_div_iff₀ hd₁, one_mul]
    have := one_le_pow₀ (n := 2) hlam
    nlinarith
  set H₀ : Finset (𝓞 F)ˣ := (finite_setOf_forall_le_place (inv_pos.2 hρ₀pos)).toFinset.filter
    fun η => ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F (η : 𝓞 F)) ≤ ρ₀ with hH₀def
  have hH₀ : ∀ η : (𝓞 F)ˣ, η ∈ H₀ ↔ ∀ w : InfinitePlace F,
      ρ₀⁻¹ ≤ w (algebraMap (𝓞 F) F (η : 𝓞 F)) ∧ w (algebraMap (𝓞 F) F (η : 𝓞 F)) ≤ ρ₀ := by
    intro η
    rw [hH₀def, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h w => ⟨h.1 w, h.2 w⟩, fun h => ⟨fun w => (h w).1, fun w => (h w).2⟩⟩
  obtain ⟨Znet, hZnet⟩ := exists_finset_forall_exists_forall_norm_mul_norm_mul_mem_Icc (F := F) d₁ d₂ (lam * ρ₀) hd₁ hd
    (one_le_mul_of_one_le_of_one_le hlam hρ₀one)
  obtain ⟨Zslab, hZslab⟩ :=
    exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc F c u d₁ d₂ T hd₁
      hd hcov a b ha hab
  set Z : Finset (AdeleRing (𝓞 F) F)ˣ :=
    Znet.image (fun fam => (archNetUnit fam)⁻¹) ∪ Zslab.image (fun z => z⁻¹) with hZdef
  have hZ : ∀ D : InfinitePlace F → ℝ, (∀ w, D w ∈ Icc (d₁ / (lam * ρ₀)) (lam * ρ₀ * d₂)) →
      ∃ fam : (w : InfinitePlace F) → (w.Completion)ˣ, (archNetUnit fam)⁻¹ ∈ Z ∧
        ∀ w : InfinitePlace F, ‖(fam w : w.Completion)‖ * ‖(fam w : w.Completion)‖ * D w ∈ Icc d₁ d₂ := by
    intro D hD
    obtain ⟨fam, hfamZ, hfamD⟩ := hZnet D hD
    exact ⟨fam, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hfamZ), hfamD⟩
  set M₁ : ℝ := A * T₀ * max 0 K with hM₁
  set M₂ : ℝ := A * T₀ * max 0 C₀ * H₀.card with hM₂
  have hM₁nn : 0 ≤ M₁ := by rw [hM₁]; positivity
  have hM₂nn : 0 ≤ M₂ := by rw [hM₂]; positivity
  refine ⟨Z, N₀ * T.card * (M₁ + M₂), by positivity, fun x hx => ?_⟩

  have hcls := fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
    exists_finset_class_bound' c u d₁ d₂ lam hc hd₁ hd hlam hu A hA bb T₀ hb (fun t t₀ => (hfin t t₀).1) K C₀ s₀
      (fun t t₀ => ⟨(hKC t t₀).2.1, (hKC t t₀).2.2⟩) ρ₀ hρ₀ H₀ hH₀ Z hZ (p.1 * x * p.2⁻¹)
  choose P Φ hP hΦ hcard using hcls
  obtain ⟨REP, hREPcard, hREPmem, hREPcover, -⟩ := hN₀ x

  set Q : Finset (AdelicGL2 (𝓞 F) F) := (REP ×ˢ T).biUnion fun p => (P p).image (· * p.1) with hQdef
  have hQmem : ∀ g : (globalPoints (𝓞 F) F).range,
      (g : AdelicGL2 (𝓞 F) F) * x
          ∈ ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂) →
        (g : AdelicGL2 (𝓞 F) F) ∈ Q := by
    intro g hg
    obtain ⟨γ₀, hγ₀, β, hβ, hgβ⟩ := hREPcover g g.2 hg
    rw [Set.mem_iUnion₂] at hg
    obtain ⟨y, hy, v, hv, hvy⟩ := hg
    have hvy' : v * y = (g : AdelicGL2 (𝓞 F) F) * x := hvy
    have hβq : β * (γ₀ * x * y⁻¹) ∈ centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂) := by
      have : β * (γ₀ * x * y⁻¹) = v := by
        calc β * (γ₀ * x * y⁻¹) = β * γ₀ * x * y⁻¹ := by group
          _ = v * y * y⁻¹ := by rw [← hgβ, ← hvy']
          _ = v := mul_inv_cancel_right v y
      rw [this]
      exact hv
    rw [hQdef, Finset.mem_biUnion]
    exact ⟨(γ₀, y), Finset.mem_product.2 ⟨hγ₀, hy⟩, Finset.mem_image.2 ⟨β, hP (γ₀, y) β hβ hβq, hgβ.symm⟩⟩
  have hleft : orbitCount (globalPoints (𝓞 F) F).range
      (⋃ y ∈ T, (· * y) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)) x ≤ Q.card := by
    set SQ : Finset (globalPoints (𝓞 F) F).range :=
      Q.preimage (fun g : (globalPoints (𝓞 F) F).range => (g : AdelicGL2 (𝓞 F) F)) Subtype.val_injective.injOn
      with hSQ
    unfold orbitCount
    calc ∑' g : (globalPoints (𝓞 F) F).range,
          (⋃ y ∈ T, (· * y) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)).indicator
            (fun _ => (1 : ENNReal)) (g • x)
        = ∑ g ∈ SQ, (⋃ y ∈ T, (· * y) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)).indicator
            (fun _ => (1 : ENNReal)) (g • x) := by
          refine tsum_eq_sum fun g hg => ?_
          refine Set.indicator_of_notMem (fun hmem => hg ?_) _
          rw [hSQ, Finset.mem_preimage]
          exact hQmem g hmem
      _ ≤ ∑ _g ∈ SQ, (1 : ENNReal) := by
          refine Finset.sum_le_sum fun g _ => ?_
          unfold Set.indicator
          split_ifs <;> simp
      _ = SQ.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (SQ.image fun g : (globalPoints (𝓞 F) F).range => (g : AdelicGL2 (𝓞 F) F)).card := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective]
      _ ≤ Q.card := by
          refine Nat.cast_le.2 (Finset.card_le_card fun g hg => ?_)
          obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hg
          rw [hSQ, Finset.mem_preimage] at hg'
          exact hg'

  have hright : ∀ p ∈ REP ×ˢ T, ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((Φ p z).card : ENNReal) ≤
      orbitCount (globalPoints (𝓞 F) F).range
        ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x := by
    intro p hp z
    obtain ⟨hγ₀, hy⟩ := Finset.mem_product.1 hp
    have hγ₀R : p.1 ∈ (globalPoints (𝓞 F) F).range := hREPmem p.1 hγ₀
    let ι : {β // β ∈ Φ p z} → (globalPoints (𝓞 F) F).range :=
      fun β => ⟨β.1 * p.1, Subgroup.mul_mem _ (hΦ p z β.1 β.2).1.mem_range hγ₀R⟩
    have hι : Function.Injective ι := by
      intro β β' h
      have h' : β.1 * p.1 = β'.1 * p.1 := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel h')
    have hιmem : ∀ g ∈ (Finset.univ : Finset {β // β ∈ Φ p z}).image ι,
        (g : AdelicGL2 (𝓞 F) F) * x
          ∈ (· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂ := by
      intro g hg
      obtain ⟨β, -, rfl⟩ := Finset.mem_image.1 hg
      obtain ⟨v, hv, hvz⟩ := (hΦ p z β.1 β.2).2
      have hvz' : v * centralScalar (𝓞 F) F z = β.1 * (p.1 * x * p.2⁻¹) := hvz
      refine ⟨v * p.2, Set.mem_iUnion₂.2 ⟨p.2, hy, v, hv, rfl⟩, ?_⟩
      show v * p.2 * centralScalar (𝓞 F) F z = β.1 * p.1 * x
      calc v * p.2 * centralScalar (𝓞 F) F z = v * centralScalar (𝓞 F) F z * p.2 := by
            rw [mul_assoc, mul_centralScalar_comm z p.2, ← mul_assoc]
        _ = β.1 * (p.1 * x * p.2⁻¹) * p.2 := by rw [hvz']
        _ = β.1 * p.1 * x := by group
    unfold orbitCount
    calc ((Φ p z).card : ENNReal)
        = (((Finset.univ : Finset {β // β ∈ Φ p z}).image ι).card : ENNReal) := by
          rw [Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_coe]
      _ = ∑ g ∈ (Finset.univ : Finset {β // β ∈ Φ p z}).image ι, (1 : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ g ∈ (Finset.univ : Finset {β // β ∈ Φ p z}).image ι,
            ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂).indicator
              (fun _ => (1 : ENNReal)) (g • x) :=
          Finset.sum_congr rfl fun g hg => (Set.indicator_of_mem (hιmem g hg) fun _ => (1 : ENNReal)).symm
      _ ≤ _ := ENNReal.sum_le_tsum _

  have hone : (1 : ENNReal) ≤ ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
      ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x := by
    obtain ⟨γ, z₀, hz₀, hγ⟩ := hZslab x hx
    have hz₀Z : z₀⁻¹ ∈ Z := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz₀)
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hz₀Z)
    unfold orbitCount
    refine le_trans ?_ (ENNReal.le_tsum (⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ : (globalPoints (𝓞 F) F).range))
    rw [Set.indicator_of_mem]
    refine ⟨globalPoints (𝓞 F) F γ * x * centralScalar (𝓞 F) F z₀, hγ, ?_⟩
    show globalPoints (𝓞 F) F γ * x * centralScalar (𝓞 F) F z₀ * centralScalar (𝓞 F) F z₀⁻¹
      = globalPoints (𝓞 F) F γ * x
    rw [mul_assoc, ← map_mul (centralScalar (𝓞 F) F) z₀ z₀⁻¹, mul_inv_cancel, map_one, mul_one]

  have hclass : ∀ p ∈ REP ×ˢ T, ((P p).card : ENNReal) ≤ ENNReal.ofReal (M₁ + M₂) * ∑ z ∈ Z,
      orbitCount (globalPoints (𝓞 F) F).range
        ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x := by
    intro p hp
    calc ((P p).card : ENNReal) = ENNReal.ofReal ((P p).card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (M₁ * ∑ z ∈ Z, ((Φ p z).card : ℝ) + M₂) := ENNReal.ofReal_le_ofReal (hcard p)
      _ = ENNReal.ofReal M₁ * ∑ z ∈ Z, ((Φ p z).card : ENNReal) + ENNReal.ofReal M₂ := by
          rw [ENNReal.ofReal_add (mul_nonneg hM₁nn (Finset.sum_nonneg fun z _ => Nat.cast_nonneg _)) hM₂nn,
            ENNReal.ofReal_mul hM₁nn,
            ENNReal.ofReal_sum_of_nonneg fun z _ => Nat.cast_nonneg _]
          simp only [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal M₁ * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
            ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x
          + ENNReal.ofReal M₂ * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
            ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x := by
          exact add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => hright p hp z) zero_le)
            (le_mul_of_one_le_right' hone)
      _ = ENNReal.ofReal (M₁ + M₂) * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
            ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x := by
          rw [ENNReal.ofReal_add hM₁nn hM₂nn, add_mul]

  have hQcard : (Q.card : ENNReal) ≤ ∑ p ∈ REP ×ˢ T, ((P p).card : ENNReal) := by
    rw [hQdef]
    refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun p _ => Nat.cast_le.2 Finset.card_image_le
  have hREP : ((REP ×ˢ T).card : ENNReal) ≤ (N₀ : ENNReal) * T.card := by
    rw [Finset.card_product, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hREPcard) zero_le
  have hM : ENNReal.ofReal (N₀ * T.card * (M₁ + M₂)) = (N₀ : ENNReal) * T.card * ENNReal.ofReal (M₁ + M₂) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  calc _ ≤ (Q.card : ENNReal) := hleft
    _ ≤ ∑ p ∈ REP ×ˢ T, ((P p).card : ENNReal) := hQcard
    _ ≤ ∑ _p ∈ REP ×ˢ T, ENNReal.ofReal (M₁ + M₂) * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
          ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x :=
        Finset.sum_le_sum hclass
    _ = ((REP ×ˢ T).card : ENNReal) * (ENNReal.ofReal (M₁ + M₂) * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
          ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N₀ : ENNReal) * T.card * (ENNReal.ofReal (M₁ + M₂) * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
          ((· * centralScalar (𝓞 F) F z) '' ⋃ y ∈ T, (· * y) '' centreCutSiegelSet F c u d₁ d₂) x) :=
        mul_le_mul_of_nonneg_right hREP zero_le
    _ = _ := by rw [hM]; ring

end RelaxedWindowComparison

end MassRelaxLeMulOfCoveringParameter

section SetLIntegralTranslateLeMulOfLtLocalHeightOfCoveringParameter
open scoped ENNReal
open MeasureTheory IsDedekindDomain Matrix
open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal Topology
attribute [local instance] glBorel

private theorem lowerNormSq_mul_le_entries {K : Type*} [NormedField K] (g y : GL (Fin 2) K) :
    rowNormSq ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ 4 * (∑ i : Fin 2, ∑ j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2)
          * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  have hY : ∀ i j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2 := fun i j =>
    le_trans
      (Finset.single_le_sum (f := fun j => ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun i => ∑ j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  have hentry : ∀ j : Fin 2,
      ‖((g : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K)) 1 j‖ ^ 2
        ≤ 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2)
            * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    intro j
    have hp := hY 0 j
    have hq := hY 1 j
    have h1 : ‖((g : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K)) 1 j‖
        ≤ ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(y : Matrix (Fin 2) (Fin 2) K) 0 j‖
          + ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ * ‖(y : Matrix (Fin 2) (Fin 2) K) 1 j‖ := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(y : Matrix (Fin 2) (Fin 2) K) 0 j‖
          + ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ * ‖(y : Matrix (Fin 2) (Fin 2) K) 1 j‖) ^ 2
        ≤ 2 * (‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 * ‖(y : Matrix (Fin 2) (Fin 2) K) 0 j‖ ^ 2)
          + 2 * (‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 * ‖(y : Matrix (Fin 2) (Fin 2) K) 1 j‖ ^ 2) := by
      nlinarith [sq_nonneg (‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(y : Matrix (Fin 2) (Fin 2) K) 0 j‖
        - ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ * ‖(y : Matrix (Fin 2) (Fin 2) K) 1 j‖)]
    have h4 := mul_le_mul_of_nonneg_left hp (sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖)
    have h5 := mul_le_mul_of_nonneg_left hq (sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖)
    have hrow : rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
        = ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 := rfl
    rw [hrow]
    nlinarith [h2, h3, h4, h5]
  have hdef : rowNormSq ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖((g : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K)) 1 0‖ ^ 2
        + ‖((g : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K)) 1 1‖ ^ 2 := by
    rw [Units.val_mul]
    rfl
  rw [hdef]
  have h0 := hentry 0
  have h1 := hentry 1
  linarith

private theorem localHeight_le_entries_div_det_mul {K : Type*} [NormedField K] (g y : GL (Fin 2) K) :
    localHeight g
      ≤ 4 * (∑ i : Fin 2, ∑ j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2)
          / ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ * localHeight (g * y) := by
  have hr := rowNormSq_pos g
  have hry := rowNormSq_pos (g * y)
  have hry' := hry.ne'
  have hdy : 0 < ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ :=
    norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero y)
  have hdy' := hdy.ne'
  have hdg : 0 ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := norm_nonneg _
  have hdet : ‖((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul]
  have hle := lowerNormSq_mul_le_entries g y
  unfold localHeight
  rw [hdet, div_le_iff₀ hr]
  have hkey : 4 * (∑ i : Fin 2, ∑ j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2)
        / ‖(y : Matrix (Fin 2) (Fin 2) K).det‖
        * (‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖
          / rowNormSq ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
        * rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
        * (4 * (∑ i : Fin 2, ∑ j : Fin 2, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ^ 2)
            * rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
          / rowNormSq ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    field_simp
  rw [hkey]
  exact le_mul_of_one_le_right hdg ((one_le_div hry).mpr hle)

private noncomputable def heightFactor {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (y : AdelicGL2 (𝓞 F) F) : ℝ :=
  4 * (∑ i : Fin 2, ∑ j : Fin 2,
      ‖(archComponent F w (glArch (𝓞 F) F y) : Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ^ 2)
    / AdelicVolume.archDetNorm w y

private theorem localHeight_le_heightFactor_mul {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (g y : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F g))
      ≤ heightFactor w y * localHeight (archComponent F w (glArch (𝓞 F) F (g * y))) := by
  unfold heightFactor AdelicVolume.archDetNorm
  rw [map_mul, map_mul]
  exact localHeight_le_entries_div_det_mul _ _

private theorem continuous_heightFactor {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    Continuous (heightFactor (F := F) w) := by
  unfold heightFactor
  refine Continuous.div (continuous_const.mul ?_) (AdelicVolume.continuous_archDetNorm w)
    fun y => (AdelicVolume.archDetNorm_pos w y).ne'
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((Units.continuous_val.comp ((continuous_archComponent F w).comp
    (continuous_glArch (𝓞 F) F))).matrix_elem i j).norm.pow 2

private theorem exists_forall_localHeight_le_mul_localHeight_mul {F : Type} [Field F] [NumberField F]
    {R : Set (AdelicGL2 (𝓞 F) F)} (hR : IsCompact R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ R, ∀ (g : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F),
      localHeight (archComponent F w (glArch (𝓞 F) F g))
        ≤ C * localHeight (archComponent F w (glArch (𝓞 F) F (g * y))) := by
  have hb : ∀ w : InfinitePlace F, ∃ B : ℝ, ∀ y ∈ R, heightFactor w y ≤ B := fun w => by
    obtain ⟨B, hB⟩ := hR.exists_bound_of_continuousOn (continuous_heightFactor w).continuousOn
    exact ⟨B, fun y hy => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB y hy)⟩
  choose B hB using hb
  refine ⟨1 + ∑ w : InfinitePlace F, |B w|,
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _), fun y hy g w => ?_⟩
  refine (localHeight_le_heightFactor_mul w g y).trans
    (mul_le_mul_of_nonneg_right ?_ (localHeight_pos _).le)
  calc heightFactor w y ≤ B w := hB w y hy
    _ ≤ |B w| := le_abs_self _
    _ ≤ ∑ w' : InfinitePlace F, |B w'| :=
        Finset.single_le_sum (f := fun w' => |B w'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
    _ ≤ 1 + ∑ w' : InfinitePlace F, |B w'| := le_add_of_nonneg_left zero_le_one

private theorem norm_natCast_completion {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (n : ℕ) :
    ‖(n : w.Completion)‖ = n := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_natCast,
    RCLike.norm_natCast]

private noncomputable def ratioUnit {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (n : ℕ) :
    (w.Completion)ˣ :=
  Units.mk0 (((n + 2 : ℕ) : w.Completion) / ((n + 1 : ℕ) : w.Completion)) (by
    rw [← norm_pos_iff, norm_div, norm_natCast_completion, norm_natCast_completion]
    positivity)

private theorem norm_ratioUnit {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (n : ℕ) :
    ‖((ratioUnit w n : (w.Completion)ˣ) : w.Completion)‖ = ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  simp only [ratioUnit, Units.val_mk0, norm_div, norm_natCast_completion]

private theorem exists_nat_ratio_sq_le {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ n : ℕ, (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ ρ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / (ρ - 1))
  refine ⟨n, ?_⟩
  have hρ' : 0 < ρ - 1 := sub_pos.mpr hρ
  rw [div_lt_iff₀ hρ'] at hn
  have h2 : 3 * ((n : ℝ) + 2) < (n : ℝ) * (ρ - 1) * ((n : ℝ) + 2) := mul_lt_mul_of_pos_right hn (by positivity)
  push_cast
  rw [div_pow, div_le_iff₀ (by positivity)]
  nlinarith [h2, hρ']

private theorem exists_zpow_mul_mem_Icc {b d₁ d₂ M : ℝ} (hb : 1 < b) (hd₁ : 0 < d₁) (hbd : b * d₁ ≤ d₂)
    (hM : 0 < M) {K : ℕ} (hK : d₂ / d₁ * M < b ^ K) {x : ℝ} (hx : x ∈ Set.Icc (d₁ / M) (d₂ * M)) :
    ∃ k : ℤ, k ∈ Finset.Icc (-(K : ℤ)) K ∧ b ^ k * x ∈ Set.Icc d₁ d₂ := by
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb
  have hx0 : 0 < x := (div_pos hd₁ hM).trans_le hx.1
  have hd₂ : 0 < d₂ := (mul_pos hb0 hd₁).trans_le hbd
  obtain ⟨m, hm⟩ := exists_mem_Ico_zpow (div_pos hd₁ hx0) hb
  have hlo : b ^ m * x ≤ d₁ := (le_div_iff₀ hx0).mp hm.1
  have hhi : d₁ < b ^ (m + 1) * x := (div_lt_iff₀ hx0).mp hm.2
  refine ⟨m + 1, ?_, hhi.le, ?_⟩
  · rw [Finset.mem_Icc]
    constructor
    · have h1 : d₁ / (d₂ * M) ≤ d₁ / x := div_le_div_of_nonneg_left hd₁.le hx0 hx.2
      have hpos : 0 < d₂ / d₁ * M := by positivity
      have h2 : b ^ (-(K : ℤ)) < d₁ / (d₂ * M) := by
        rw [_root_.zpow_neg, zpow_natCast]
        have heq : d₁ / (d₂ * M) = (d₂ / d₁ * M)⁻¹ := by
          field_simp
        rw [heq]
        exact inv_strictAnti₀ hpos hK
      have h3 : b ^ (-(K : ℤ)) < b ^ (m + 1) := h2.trans_le (h1.trans hm.2.le)
      exact ((zpow_lt_zpow_iff_right₀ hb).mp h3).le
    · have hxM : d₁ ≤ x * M := (div_le_iff₀ hM).mp hx.1
      have h1 : d₁ / x ≤ M := by
        rw [div_le_iff₀ hx0]
        linarith
      have h2 : M ≤ d₂ / d₁ * M := by
        have hone : 1 ≤ d₂ / d₁ := (one_le_div₀ hd₁).mpr ((le_mul_of_one_le_left hd₁.le hb.le).trans hbd)
        nlinarith [hone, hM]
      have h3 : b ^ m < b ^ (K : ℤ) := by
        rw [zpow_natCast]
        exact (hm.1.trans (h1.trans h2)).trans_lt hK
      have h4 : m < (K : ℤ) := (zpow_lt_zpow_iff_right₀ hb).mp h3
      omega
  · rw [zpow_add_one₀ hb0.ne']
    calc b ^ m * b * x = b * (b ^ m * x) := by ring
      _ ≤ b * d₁ := mul_le_mul_of_nonneg_left hlo hb0.le
      _ ≤ d₂ := hbd

private theorem exists_finset_forall_exists_archNetUnit_mem_archDetNorm_mem {F : Type} [Field F] [NumberField F]
    {d₁ d₂ M : ℝ} (hd₁ : 0 < d₁) (hd : d₁ < d₂) (hM : 0 < M) :
    ∃ Z : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      (∀ w : InfinitePlace F, AdelicVolume.archDetNorm w g ∈ Set.Icc (d₁ / M) (d₂ * M)) →
      ∃ a : (w : InfinitePlace F) → (w.Completion)ˣ, archNetUnit a ∈ Z ∧
        ∀ w : InfinitePlace F, AdelicVolume.archDetNorm w (netScalar a * g) ∈ Set.Icc d₁ d₂ := by
  classical
  have hρ : 1 < d₂ / d₁ := (one_lt_div hd₁).mpr hd
  obtain ⟨n, hn⟩ := exists_nat_ratio_sq_le hρ
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hq] at hn
  have hq1 : 1 < q := by
    rw [hq, one_lt_div (by positivity)]
    exact Nat.cast_lt.mpr (by omega)
  have hb1 : 1 < q * q := by nlinarith [hq1]
  have hbd : q * q * d₁ ≤ d₂ := by
    have hle : q * q ≤ d₂ / d₁ := by
      rw [← sq]
      exact hn
    rwa [le_div_iff₀ hd₁] at hle
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (d₂ / d₁ * M) hb1
  refine ⟨(Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(K : ℤ)) K).image
    (fun k : InfinitePlace F → ℤ => archNetUnit fun w => ratioUnit w n ^ k w), fun g hg => ?_⟩
  have hk : ∀ w : InfinitePlace F, ∃ k : ℤ, k ∈ Finset.Icc (-(K : ℤ)) K ∧
      (q * q) ^ k * AdelicVolume.archDetNorm w g ∈ Set.Icc d₁ d₂ := fun w =>
    exists_zpow_mul_mem_Icc hb1 hd₁ hbd hM hK (hg w)
  choose k hkmem hkal using hk
  refine ⟨fun w => ratioUnit w n ^ k w, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hkmem), fun w => ?_⟩
  have hnorm : ‖((ratioUnit w n ^ k w : (w.Completion)ˣ) : w.Completion)‖ = q ^ k w := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_ratioUnit, ← hq]
  simp only [archDetNorm_netScalar_mul, hnorm, ← mul_zpow]
  exact hkal w

private noncomputable def shiftPoint {F : Type} [Field F] [NumberField F] (ξ : 𝓞 F) : AdelicGL2 (𝓞 F) F :=
  globalPoints (𝓞 F) F (upperGL 1 (algebraMap (𝓞 F) F ξ) 1 one_ne_zero one_ne_zero)

private theorem exists_shiftPoint_mul_integral_and_le_sq {F : Type} [Field F] [NumberField F] {u : ℝ}
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    {g : AdelicGL2 (𝓞 F) F} (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) :
    ∃ ξ : 𝓞 F, glFin (𝓞 F) F (shiftPoint ξ * g) ∈ finiteIntegralGL2 (𝓞 F) F ∧
      (∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F (shiftPoint ξ * g)))
        = localHeight (archComponent F w (glArch (𝓞 F) F g))) ∧
      (∀ w : InfinitePlace F, xWindowSq (archComponent F w (glArch (𝓞 F) F (shiftPoint ξ * g))) ≤ u ^ 2) ∧
      ∀ w : InfinitePlace F, AdelicVolume.archDetNorm w (shiftPoint ξ * g) = AdelicVolume.archDetNorm w g := by
  choose x hx using fun w : InfinitePlace F => exists_placeEmb_eq_xAtP w g
  obtain ⟨ξ, hξ⟩ := hu fun w => -x w
  refine ⟨ξ, ?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [map_mul]
    exact Subgroup.mul_mem _ (glFin_globalPoints_shift_mem ξ) hg
  · rw [shiftPoint, localHeight_globalPoints_upperGL_mul, map_one, div_one, one_mul]
  · have h1 : placeEmb w ((1 : F) : w.Completion) = 1 := by
      rw [show ((1 : F) : w.Completion) = 1 from rfl, map_one]
    have hcoe : ((algebraMap (𝓞 F) F ξ : F) : w.Completion) = algebraMap F w.Completion (ξ : F) := rfl
    have hξ' : ‖x w + algebraMap F w.Completion (ξ : F)‖ ≤ u := by
      rw [← norm_neg, neg_add, ← sub_eq_add_neg]
      exact hξ w
    rw [xWindowSq_eq_norm_xAtP_sq, shiftPoint, xAtP_globalPoints_upperGL_mul, h1, div_one, div_one, one_mul,
      ← hx w, hcoe, ← map_add, norm_placeEmb]
    exact pow_le_pow_left₀ (norm_nonneg _) hξ' 2
  · rw [shiftPoint, archDetNorm_globalPoints_upperGL_mul, map_one, one_mul, one_mul]

private theorem archDetNorm_mul_eq {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (g y : AdelicGL2 (𝓞 F) F) :
    AdelicVolume.archDetNorm w (g * y) = AdelicVolume.archDetNorm w g * AdelicVolume.archDetNorm w y := by
  unfold AdelicVolume.archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

private theorem exists_forall_archDetNorm_mem_Icc_one_div {F : Type} [Field F] [NumberField F]
    {R : Set (AdelicGL2 (𝓞 F) F)} (hR : IsCompact R) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ y ∈ R, ∀ w : InfinitePlace F, AdelicVolume.archDetNorm w y ∈ Set.Icc (1 / M) M := by
  have hup : ∀ w : InfinitePlace F, ∃ B : ℝ, ∀ y ∈ R, AdelicVolume.archDetNorm w y ≤ B := fun w => by
    obtain ⟨B, hB⟩ := hR.exists_bound_of_continuousOn (AdelicVolume.continuous_archDetNorm w).continuousOn
    exact ⟨B, fun y hy => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB y hy)⟩
  have hlow : ∀ w : InfinitePlace F, ∃ B : ℝ, ∀ y ∈ R, (AdelicVolume.archDetNorm w y)⁻¹ ≤ B := fun w => by
    obtain ⟨B, hB⟩ := hR.exists_bound_of_continuousOn ((AdelicVolume.continuous_archDetNorm w).inv₀
      fun y => (AdelicVolume.archDetNorm_pos w y).ne').continuousOn
    exact ⟨B, fun y hy => (le_abs_self _).trans (by first | exact hB y hy | simpa only [Real.norm_eq_abs] using hB y hy | simpa +zetaDelta only [Real.norm_eq_abs] using hB y hy)⟩
  choose B hB using hup
  choose B' hB' using hlow
  refine ⟨1 + ∑ w : InfinitePlace F, (|B w| + |B' w|),
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity), fun y hy w => ?_⟩
  have hsum : |B w| + |B' w| ≤ ∑ w' : InfinitePlace F, (|B w'| + |B' w'|) :=
    Finset.single_le_sum (f := fun w' => |B w'| + |B' w'|) (fun _ _ => by positivity) (Finset.mem_univ w)
  have hpos := AdelicVolume.archDetNorm_pos w y
  have hMpos : (0 : ℝ) < 1 + ∑ w' : InfinitePlace F, (|B w'| + |B' w'|) := by positivity
  constructor
  · rw [one_div, inv_le_comm₀ hMpos hpos]
    linarith [hB' w y hy, le_abs_self (B' w), abs_nonneg (B w)]
  · linarith [hB w y hy, le_abs_self (B w), abs_nonneg (B' w)]

private theorem exists_forall_exists_netScalar_mul_shiftPoint_mul_mem {F : Type} [Field F] [NumberField F]
    {u d₁ d₂ : ℝ}
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hd₁ : 0 < d₁) (hd : d₁ < d₂) {R : Set (AdelicGL2 (𝓞 F) F)} (hR : IsCompact R) {l : ℝ} (hl : 1 ≤ l)
    {d₁' d₂' : ℝ} (hd₁' : 0 < d₁') :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Z : Finset (AdeleRing (𝓞 F) F)ˣ,
      ∀ (c' u' : ℝ) (p : AdelicGL2 (𝓞 F) F), p ∈ centreCutSiegelSet F c' u' d₁' d₂' →
        ∀ y ∈ R, ∀ X : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F (p * y)))
            ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F X))) →
          (∀ w : InfinitePlace F, AdelicVolume.archDetNorm w (p * y) ≤ l * AdelicVolume.archDetNorm w X ∧
            AdelicVolume.archDetNorm w X ≤ l * AdelicVolume.archDetNorm w (p * y)) →
          ∃ (ξ : 𝓞 F) (a : (w : InfinitePlace F) → (w.Completion)ˣ), archNetUnit a ∈ Z ∧
            netScalar a * (shiftPoint ξ * X) ∈ centreCutSiegelSet F (c' / (C * l)) u d₁ d₂ ∧
            ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F p))
              ≤ C * l * localHeight (archComponent F w (glArch (𝓞 F) F (netScalar a * (shiftPoint ξ * X)))) := by
  obtain ⟨C, hC1, hC⟩ := exists_forall_localHeight_le_mul_localHeight_mul hR
  obtain ⟨M, hM1, hM⟩ := exists_forall_archDetNorm_mem_Icc_one_div hR
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hM0 : 0 < M := zero_lt_one.trans_le hM1
  have hd₂ : 0 < d₂ := hd₁.trans hd

  set B : ℝ := max (d₁ * (l * M) / d₁') (d₂' * (l * M) / d₂) with hB_def
  have hB0 : 0 < B := lt_max_of_lt_left (by positivity)
  obtain ⟨Z, hZ⟩ := exists_finset_forall_exists_archNetUnit_mem_archDetNorm_mem (F := F) hd₁ hd hB0
  refine ⟨C, hC1, Z, fun c' u' p hp y hy X hXf hXh hXd => ?_⟩
  obtain ⟨hpf, hpfloor, -, hpdet⟩ := (mem_centreCutSiegelSet_iff (F := F)).mp hp
  obtain ⟨ξ, hξf, hξh, hξx, hξd⟩ := exists_shiftPoint_mul_integral_and_le_sq hu hXf

  have hrange : ∀ w : InfinitePlace F,
      AdelicVolume.archDetNorm w (shiftPoint ξ * X) ∈ Set.Icc (d₁ / B) (d₂ * B) := by
    intro w
    rw [hξd w]
    have hy' := hM y hy w
    have hXd' := hXd w
    rw [archDetNorm_mul_eq] at hXd'
    have hpd := hpdet w
    have hX0 := AdelicVolume.archDetNorm_pos w X
    have hy0 := AdelicVolume.archDetNorm_pos w y
    have hp0 := AdelicVolume.archDetNorm_pos w p
    have hyM : AdelicVolume.archDetNorm w y ≤ M := hy'.2
    have hyM' : 1 / M ≤ AdelicVolume.archDetNorm w y := hy'.1
    have hB1 : d₁ * (l * M) / d₁' ≤ B := le_max_left _ _
    have hB2 : d₂' * (l * M) / d₂ ≤ B := le_max_right _ _
    constructor
    ·
      have h1 : d₁ / B ≤ d₁' / (l * M) := by
        rw [div_le_div_iff₀ hB0 (by positivity)]
        have := (div_le_iff₀ hd₁').mp hB1
        linarith
      have h2 : d₁' / (l * M) ≤ AdelicVolume.archDetNorm w X := by
        rw [div_le_iff₀ (by positivity)]
        have h3 : d₁' * (1 / M) ≤ AdelicVolume.archDetNorm w p * AdelicVolume.archDetNorm w y :=
          mul_le_mul hpd.1 hyM' (by positivity) hp0.le
        have h4 : d₁' * (1 / M) * M = d₁' := by
          field_simp
        nlinarith [hXd'.1, h3, h4, hM0, hl0]
      exact h1.trans h2
    ·
      have h1 : AdelicVolume.archDetNorm w X ≤ l * (d₂' * M) :=
        hXd'.2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hpd.2 hyM hy0.le (hp0.le.trans hpd.2)) hl0.le)
      have h2 : l * (d₂' * M) ≤ d₂ * B := by
        have := (div_le_iff₀ hd₂).mp hB2
        linarith
      exact h1.trans h2
  obtain ⟨a, haZ, ha⟩ := hZ _ hrange
  refine ⟨ξ, a, haZ, ?_, fun w => ?_⟩
  · rw [mem_centreCutSiegelSet_iff]
    refine ⟨?_, fun w => ?_, fun w => ?_, fun w => ha w⟩
    · rw [glFin_netScalar_mul]
      exact hξf
    · rw [localHeight_netScalar_mul, hξh w]

      have h1 := hpfloor w
      have h2 := hC y hy p w
      have h3 := hXh w
      have hX0 := localHeight_pos (archComponent F w (glArch (𝓞 F) F X))
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h1, h2, h3, hC1, hl, hX0]
    · rw [xWindowSq_netScalar_mul]
      exact hξx w
  · rw [localHeight_netScalar_mul, hξh w]
    have h2 := hC y hy p w
    have h3 := hXh w
    nlinarith [h2, h3, hC1, hl, localHeight_pos (archComponent F w (glArch (𝓞 F) F X)),
      localHeight_pos (archComponent F w (glArch (𝓞 F) F (p * y)))]

private theorem norm_xAtP_le_abs_of_mem {F : Type} [Field F] [NumberField F] {c' u' d₁' d₂' : ℝ}
    {p : AdelicGL2 (𝓞 F) F} (hp : p ∈ centreCutSiegelSet F c' u' d₁' d₂') (w : InfinitePlace F) :
    ‖xAtP w p‖ ≤ |u'| := by
  have h := ((mem_centreCutSiegelSet_iff (F := F)).mp hp).2.2.1 w
  rw [xWindowSq_eq_norm_xAtP_sq] at h
  have h' : ‖xAtP w p‖ ^ 2 ≤ |u'| ^ 2 := by
    rw [sq_abs]
    exact h
  simpa only [abs_norm] using abs_le_of_sq_le_sq h' (abs_nonneg _)

private theorem encard_setOf_shiftPoint_mul_eq_le {F : Type} [Field F] [NumberField F] {c' u' d₁' d₂' : ℝ}
    {a b t : F} {ha : a ≠ 0} {ht : t ≠ 0} {ρ : ℝ} (hρ : ∀ w : InfinitePlace F, w a / w t ≤ ρ) {A : ℕ}
    (hA : ∀ z : (w : InfinitePlace F) → w.Completion,
      {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ |u'| * ρ}.ncard ≤ A)
    (Q : AdelicGL2 (𝓞 F) F) :
    {ξ : 𝓞 F | ∃ p ∈ centreCutSiegelSet F c' u' d₁' d₂',
      shiftPoint ξ * (globalPoints (𝓞 F) F (upperGL a b t ha ht) * p) = Q}.encard ≤ (A : ℕ∞) := by
  choose x hx using fun w : InfinitePlace F => exists_placeEmb_eq_xAtP w Q
  obtain ⟨z, hz⟩ : ∃ z : (w : InfinitePlace F) → w.Completion,
      ∀ w, z w = x w - (b : w.Completion) / (t : w.Completion) := ⟨_, fun _ => rfl⟩
  have hsub : {ξ : 𝓞 F | ∃ p ∈ centreCutSiegelSet F c' u' d₁' d₂',
        shiftPoint ξ * (globalPoints (𝓞 F) F (upperGL a b t ha ht) * p) = Q}
      ⊆ {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ |u'| * ρ} := by
    rintro ξ ⟨p, hp, hpQ⟩ w
    have h1 : placeEmb w ((1 : F) : w.Completion) = 1 := by
      rw [show ((1 : F) : w.Completion) = 1 from rfl, map_one]
    have hQ : xAtP w Q = placeEmb w (a : w.Completion) / placeEmb w (t : w.Completion) * xAtP w p
        + placeEmb w (b : w.Completion) / placeEmb w (t : w.Completion)
        + placeEmb w ((algebraMap (𝓞 F) F ξ : F) : w.Completion) := by
      rw [← hpQ, shiftPoint, xAtP_globalPoints_upperGL_mul, xAtP_globalPoints_upperGL_mul, h1]
      ring
    have hcoe : algebraMap F w.Completion (ξ : F) = ((algebraMap (𝓞 F) F ξ : F) : w.Completion) := rfl
    have hnorm : ‖z w - algebraMap F w.Completion (ξ : F)‖
        = ‖placeEmb w (a : w.Completion) / placeEmb w (t : w.Completion)‖ * ‖xAtP w p‖ := by
      rw [← norm_placeEmb, ← norm_mul]
      congr 1
      rw [hcoe, hz w, map_sub, map_sub, map_div₀, hx w, hQ]
      ring
    rw [hnorm, norm_div, norm_placeEmb, norm_placeEmb, SiegelReduction.norm_coe_completion,
      SiegelReduction.norm_coe_completion, mul_comm]
    exact mul_le_mul (norm_xAtP_le_abs_of_mem hp w) (hρ w) (div_nonneg (apply_nonneg w a) (apply_nonneg w t))
      (abs_nonneg _)
  have hfin : {ξ : 𝓞 F | ∀ w : InfinitePlace F,
      ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ |u'| * ρ}.Finite := by
    refine (finite_setOf_forall_norm_le (|u'| * ρ + ∑ w : InfinitePlace F, ‖z w‖)).subset fun ξ hξ w => ?_
    have h1 := hξ w
    have h2 : ‖z w‖ ≤ ∑ w' : InfinitePlace F, ‖z w'‖ :=
      Finset.single_le_sum (f := fun w' => ‖z w'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
    calc ‖algebraMap F w.Completion (ξ : F)‖
        = ‖z w - (z w - algebraMap F w.Completion (ξ : F))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖z w‖ + ‖z w - algebraMap F w.Completion (ξ : F)‖ := norm_sub_le _ _
      _ ≤ |u'| * ρ + ∑ w' : InfinitePlace F, ‖z w'‖ := by linarith
  calc _ ≤ _ := Set.encard_le_encard hsub
    _ = _ := hfin.cast_ncard_eq.symm
    _ ≤ (A : ℕ∞) := by exact_mod_cast hA z

private theorem exists_eq_upperGL {F : Type} [Field F] [NumberField F] (β : GL (Fin 2) F)
    (h : (β : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ∃ (a b t : F) (ha : a ≠ 0) (ht : t ≠ 0), β = upperGL a b t ha ht := by
  have hdet : (β : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero β
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  refine ⟨_, (β : Matrix (Fin 2) (Fin 2) F) 0 1, _, left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · exact (upperGL_apply_zero_zero _ _ _ _ _).symm
  · exact (upperGL_apply_zero_one _ _ _ _ _).symm
  · exact h.trans (upperGL_apply_one_zero _ _ _ _ _).symm
  · exact (upperGL_apply_one_one _ _ _ _ _).symm

private theorem centreCutSiegelSet_subset_of_le {F : Type} [Field F] [NumberField F] {c₁ c₂ u d₁ d₂ : ℝ}
    (h : c₂ ≤ c₁) : centreCutSiegelSet F c₁ u d₁ d₂ ⊆ centreCutSiegelSet F c₂ u d₁ d₂ := by
  intro g hg
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  exact ⟨hg.1, fun w => h.trans (hg.2.1 w), hg.2.2.1, hg.2.2.2⟩

open scoped Pointwise in

private def integralMulImage {F : Type} [Field F] [NumberField F] (R : Set (AdelicGL2 (𝓞 F) F)) :
    Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) * (glFin (𝓞 F) F '' R)

open scoped Pointwise in
private theorem isCompact_integralMulImage {F : Type} [Field F] [NumberField F] {R : Set (AdelicGL2 (𝓞 F) F)}
    (hR : IsCompact R) : IsCompact (integralMulImage R) :=
  (isCompact_finiteLevelZero (R := 𝓞 F) (K := F) (N := ⊤)).mul (hR.image (continuous_glFin (𝓞 F) F))

open scoped Pointwise in
private theorem glFin_mul_mem_integralMulImage {F : Type} [Field F] [NumberField F] {R : Set (AdelicGL2 (𝓞 F) F)}
    {p y : AdelicGL2 (𝓞 F) F} (hp : glFin (𝓞 F) F p ∈ finiteIntegralGL2 (𝓞 F) F) (hy : y ∈ R) :
    glFin (𝓞 F) F (p * y) ∈ integralMulImage R := by
  rw [map_mul]
  exact Set.mul_mem_mul hp (Set.mem_image_of_mem _ hy)

private def aboveLevel (F : Type) [Field F] [NumberField F] (H : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ∃ w : InfinitePlace F, H < localHeight (archComponent F w (glArch (𝓞 F) F g))}

private theorem shiftPoint_mul_globalPoints_mem {F : Type} [Field F] [NumberField F] (ξ : 𝓞 F)
    (β : GL (Fin 2) F) : shiftPoint ξ * globalPoints (𝓞 F) F β ∈ (globalPoints (𝓞 F) F).range :=
  mul_mem (MonoidHom.mem_range.mpr ⟨upperGL 1 (algebraMap (𝓞 F) F ξ) 1 one_ne_zero one_ne_zero, rfl⟩)
    (MonoidHom.mem_range.mpr ⟨β, rfl⟩)

private noncomputable def shiftElt {F : Type} [Field F] [NumberField F] (ξ : 𝓞 F) (β : GL (Fin 2) F) :
    (globalPoints (𝓞 F) F).range :=
  ⟨shiftPoint ξ * globalPoints (𝓞 F) F β, shiftPoint_mul_globalPoints_mem ξ β⟩

private theorem shiftElt_coe {F : Type} [Field F] [NumberField F] (ξ : 𝓞 F) (β : GL (Fin 2) F) :
    ((shiftElt ξ β : (globalPoints (𝓞 F) F).range) : AdelicGL2 (𝓞 F) F) = shiftPoint ξ * globalPoints (𝓞 F) F β :=
  rfl

private theorem netScalar_mul_shiftPoint_mul_mul_eq {F : Type} [Field F] [NumberField F]
    (a : (w : InfinitePlace F) → (w.Completion)ˣ) (ξ : 𝓞 F) (β : GL (Fin 2) F) (q : AdelicGL2 (𝓞 F) F)
    (z : (AdeleRing (𝓞 F) F)ˣ) (t : AdelicGL2 (𝓞 F) F) :
    netScalar a * (shiftPoint ξ * (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z * t⁻¹)) * t
      = shiftPoint ξ * globalPoints (𝓞 F) F β * q * (centralScalar (𝓞 F) F z * netScalar a) := by
  have h1 : ∀ X : AdelicGL2 (𝓞 F) F, netScalar a * X = X * netScalar a := fun X =>
    (mul_centralScalar_comm (archNetUnit a) X).symm
  rw [h1, mul_assoc, h1 t]
  group

private theorem div_mul_lt_of_lt_of_le_mul {H l₁ l₂ h₀ h₁ h₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hH : H < h₀)
    (h01 : h₀ ≤ l₁ * h₁) (h12 : h₁ ≤ l₂ * h₂) : H / (l₁ * l₂) < h₂ := by
  rw [div_lt_iff₀ (mul_pos hl₁ hl₂)]
  have h := mul_le_mul_of_nonneg_left h12 hl₁.le
  nlinarith

private theorem mul_mem_iUnion_inter_aboveLevel {F : Type} [Field F] [NumberField F] {u d₁ d₂ c' H C l CT : ℝ}
    {T : Finset (AdelicGL2 (𝓞 F) F)} (hc' : 0 < c') (hC : 1 ≤ C) (hl : 1 ≤ l) (hCT1 : 1 ≤ CT)
    (hCT : ∀ t ∈ (T : Set (AdelicGL2 (𝓞 F) F)), ∀ (g : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F),
      localHeight (archComponent F w (glArch (𝓞 F) F g))
        ≤ CT * localHeight (archComponent F w (glArch (𝓞 F) F (g * t))))
    {p P t : AdelicGL2 (𝓞 F) F} (hpH : p ∈ aboveLevel F H) (ht : t ∈ T)
    (hP : P ∈ centreCutSiegelSet F (c' / (C * l)) u d₁ d₂)
    (hht : ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F p))
      ≤ C * l * localHeight (archComponent F w (glArch (𝓞 F) F P))) :
    P * t ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / (C * l * CT)) u d₁ d₂)
      ∩ aboveLevel F (H / (C * l * CT)) := by
  have hCl : 0 < C * l := mul_pos (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hl)
  refine ⟨Set.mem_iUnion₂.mpr ⟨t, ht, P, centreCutSiegelSet_subset_of_le ?_ hP, rfl⟩, ?_⟩
  · exact div_le_div_of_nonneg_left hc'.le hCl (le_mul_of_one_le_right hCl.le hCT1)
  · obtain ⟨w, hw⟩ := hpH
    show ∃ w : InfinitePlace F, _
    exact ⟨w, div_mul_lt_of_lt_of_le_mul hCl (zero_lt_one.trans_le hCT1) hw (hht w) (hCT t ht P w)⟩

private def fiberSet {F : Type} [Field F] [NumberField F] (c' u' d₁' d₂' H : ℝ) (y s : AdelicGL2 (𝓞 F) F)
    (β : GL (Fin 2) F) (g' : (globalPoints (𝓞 F) F).range) : Set (globalPoints (𝓞 F) F).range :=
  {g | g • s ∈ (· * y) '' (centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H) ∧ ∃ ξ : 𝓞 F, g' = shiftElt ξ β * g}

private theorem encard_fiberSet_le {F : Type} [Field F] [NumberField F] {c' u' d₁' d₂' H : ℝ}
    {y s : AdelicGL2 (𝓞 F) F} {β : GL (Fin 2) F} (hβ : (β : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) {ρ : ℝ}
    (hρ : ∀ w : InfinitePlace F,
      w ((β : Matrix (Fin 2) (Fin 2) F) 0 0) / w ((β : Matrix (Fin 2) (Fin 2) F) 1 1) ≤ ρ)
    {A : ℕ} (hA : ∀ z : (w : InfinitePlace F) → w.Completion,
      {ξ : 𝓞 F | ∀ w : InfinitePlace F, ‖z w - algebraMap F w.Completion (ξ : F)‖ ≤ |u'| * ρ}.ncard ≤ A)
    (g' : (globalPoints (𝓞 F) F).range) : (fiberSet c' u' d₁' d₂' H y s β g').encard ≤ (A : ℕ∞) := by
  obtain ⟨a, b, t, ha, ht, hβeq⟩ := exists_eq_upperGL β hβ
  have hρ' : ∀ w : InfinitePlace F, w a / w t ≤ ρ := fun w => by
    have h := hρ w
    rwa [hβeq, upperGL_apply_zero_zero, upperGL_apply_one_one] at h
  have h6 := encard_setOf_shiftPoint_mul_eq_le (c' := c') (d₁' := d₁') (d₂' := d₂') (b := b) (ha := ha) (ht := ht)
    hρ' hA ((g' : AdelicGL2 (𝓞 F) F) * s * y⁻¹)
  rw [← hβeq] at h6
  have hsub : fiberSet c' u' d₁' d₂' H y s β g' ⊆ (fun ξ : 𝓞 F => (shiftElt ξ β)⁻¹ * g') ''
      {ξ : 𝓞 F | ∃ p ∈ centreCutSiegelSet F c' u' d₁' d₂',
        shiftPoint ξ * (globalPoints (𝓞 F) F β * p) = (g' : AdelicGL2 (𝓞 F) F) * s * y⁻¹} := by
    rintro g ⟨⟨p, ⟨hpS, -⟩, hpy⟩, ξ, hξ⟩
    have hpy' : p * y = (g : AdelicGL2 (𝓞 F) F) * s := hpy
    refine ⟨ξ, ⟨p, hpS, ?_⟩, ?_⟩
    · calc shiftPoint ξ * (globalPoints (𝓞 F) F β * p)
          = shiftPoint ξ * globalPoints (𝓞 F) F β * (p * y) * y⁻¹ := by group
        _ = (g' : AdelicGL2 (𝓞 F) F) * s * y⁻¹ := by
          rw [hpy', hξ, Subgroup.coe_mul, shiftElt_coe]
          group
    · simp only [hξ, inv_mul_cancel_left]
  calc (fiberSet c' u' d₁' d₂' H y s β g').encard ≤ _ := Set.encard_le_encard hsub
    _ ≤ _ := Set.encard_image_le _ _
    _ ≤ (A : ℕ∞) := h6

private theorem coe_encard_le_mul_coe_encard_of_cover {X E Y : Type*} {Lset : Set X} {Rset : Set Y} (Lst : Finset E)
    (fib : E → Y → Set X) (k : ℕ) (hk : k ≠ 0) (hfib : ∀ e ∈ Lst, ∀ g' : Y, (fib e g').encard ≤ (k : ℕ∞))
    (hcover : ∀ x ∈ Lset, ∃ e ∈ Lst, ∃ g' ∈ Rset, x ∈ fib e g') :
    (Lset.encard : ℝ≥0∞) ≤ ((Lst.card * k : ℕ) : ℝ≥0∞) * (Rset.encard : ℝ≥0∞) := by
  have hnat : Lset.encard ≤ ((Lst.card * k : ℕ) : ℕ∞) * Rset.encard := by
    rcases Lset.eq_empty_or_nonempty with hL | ⟨x₀, hx₀⟩
    · rw [hL, Set.encard_empty]
      exact _root_.zero_le
    obtain ⟨e₀, he₀, -⟩ := hcover x₀ hx₀
    have hN : (Lst.card * k : ℕ) ≠ 0 := Nat.mul_ne_zero (Finset.card_ne_zero.mpr ⟨e₀, he₀⟩) hk
    by_cases hR : Rset.Finite
    · have hsub : Lset ⊆ ⋃ e ∈ Lst, ⋃ g' ∈ hR.toFinset, fib e g' := fun x hx => by
        obtain ⟨e, he, g', hg', hfx⟩ := hcover x hx
        exact Set.mem_iUnion₂.mpr ⟨e, he, Set.mem_iUnion₂.mpr ⟨g', hR.mem_toFinset.mpr hg', hfx⟩⟩
      calc Lset.encard ≤ (⋃ e ∈ Lst, ⋃ g' ∈ hR.toFinset, fib e g').encard := Set.encard_le_encard hsub
        _ ≤ ∑ e ∈ Lst, (⋃ g' ∈ hR.toFinset, fib e g').encard := Finset.set_encard_biUnion_le _ _
        _ ≤ ∑ e ∈ Lst, ∑ g' ∈ hR.toFinset, (fib e g').encard :=
          Finset.sum_le_sum fun e _ => Finset.set_encard_biUnion_le _ _
        _ ≤ ∑ e ∈ Lst, ∑ _g' ∈ hR.toFinset, (k : ℕ∞) :=
          Finset.sum_le_sum fun e he => Finset.sum_le_sum fun g' _ => hfib e he g'
        _ = ((Lst.card * k : ℕ) : ℕ∞) * Rset.encard := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hR.encard_eq_coe_toFinset_card]
          push_cast
          ring
    · rw [Set.encard_eq_top_iff.mpr hR, ENat.mul_top (by exact_mod_cast hN)]
      exact le_top
  calc (Lset.encard : ℝ≥0∞) ≤ ((((Lst.card * k : ℕ) : ℕ∞) * Rset.encard : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr hnat
    _ = _ := by rw [ENat.toENNReal_mul, ENat.toENNReal_coe]

section IntegralClasses

open NumberField.AdelicVolume NumberField.TateGlobal

variable {F : Type} [Field F] [NumberField F]

private noncomputable def integralConjStable (T : Finset (AdelicGL2 (𝓞 F) F)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  finiteIntegralGL2 (𝓞 F) F ⊓
    ⨅ t ∈ T, (finiteIntegralGL2 (𝓞 F) F).comap (MulAut.conj (glFin (𝓞 F) F t)).toMonoidHom

private theorem mem_integralConjStable_iff {T : Finset (AdelicGL2 (𝓞 F) F)}
    {k : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)} :
    k ∈ integralConjStable T ↔
      k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ t ∈ T, glFin (𝓞 F) F t * k * (glFin (𝓞 F) F t)⁻¹ ∈ finiteIntegralGL2 (𝓞 F) F := by
  simp only [integralConjStable, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

private theorem isOpen_finiteIntegralGL2' :
    IsOpen (finiteIntegralGL2 (𝓞 F) F : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  isOpen_finiteLevelZero (𝓞 F) F top_ne_bot

private theorem isOpen_integralConjStable (T : Finset (AdelicGL2 (𝓞 F) F)) :
    IsOpen (integralConjStable T : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  have hset : (integralConjStable T : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
      = (finiteIntegralGL2 (𝓞 F) F : Set _) ∩
          ⋂ t ∈ T, (fun k => glFin (𝓞 F) F t * k * (glFin (𝓞 F) F t)⁻¹) ⁻¹' (finiteIntegralGL2 (𝓞 F) F : Set _) := by
    ext k
    simp only [SetLike.mem_coe, mem_integralConjStable_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  refine isOpen_finiteIntegralGL2'.inter (isOpen_biInter_finset fun t _ => ?_)
  exact isOpen_finiteIntegralGL2'.preimage ((continuous_const.mul continuous_id).mul continuous_const)

private theorem exists_finset_forall_exists_inv_mul_mem (T : Finset (AdelicGL2 (𝓞 F) F))
    {C : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F))} (hC : IsCompact C) :
    ∃ s : Finset (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)),
      ∀ k ∈ C, ∃ k₀ ∈ s, k₀⁻¹ * k ∈ integralConjStable T := by
  classical
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover
    (fun k : C => {x | (k : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F))⁻¹ * x ∈ integralConjStable T})
    (fun k => (isOpen_integralConjStable T).preimage (continuous_const.mul continuous_id))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp only [Set.mem_setOf_eq, inv_mul_cancel, Subgroup.one_mem]⟩)
  refine ⟨s.image Subtype.val, fun k hk => ?_⟩
  obtain ⟨k₀, hk₀s, hk₀⟩ := Set.mem_iUnion₂.1 (hs hk)
  exact ⟨k₀, Finset.mem_image_of_mem _ hk₀s, hk₀⟩

private theorem glFin_mul_mem_of_inv_mul_mem {T : Finset (AdelicGL2 (𝓞 F) F)} {t : AdelicGL2 (𝓞 F) F} (ht : t ∈ T)
    (β : Matrix.GeneralLinearGroup (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ) {q₀ q : AdelicGL2 (𝓞 F) F}
    (h₀ : glFin (𝓞 F) F (globalPoints (𝓞 F) F β * q₀ * centralScalar (𝓞 F) F z * t⁻¹) ∈ finiteIntegralGL2 (𝓞 F) F)
    (hq : (glFin (𝓞 F) F q₀)⁻¹ * glFin (𝓞 F) F q ∈ integralConjStable T) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z * t⁻¹) ∈ finiteIntegralGL2 (𝓞 F) F := by
  have hsplit : globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z * t⁻¹
      = (globalPoints (𝓞 F) F β * q₀ * centralScalar (𝓞 F) F z * t⁻¹) * (t * (q₀⁻¹ * q) * t⁻¹) := by
    have hz : q₀⁻¹ * q * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * (q₀⁻¹ * q) :=
      mul_centralScalar_comm z _
    calc globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z * t⁻¹
        = globalPoints (𝓞 F) F β * (q₀ * (q₀⁻¹ * q * centralScalar (𝓞 F) F z)) * t⁻¹ := by group
      _ = globalPoints (𝓞 F) F β * (q₀ * (centralScalar (𝓞 F) F z * (q₀⁻¹ * q))) * t⁻¹ := by rw [hz]
      _ = (globalPoints (𝓞 F) F β * q₀ * centralScalar (𝓞 F) F z * t⁻¹) * (t * (q₀⁻¹ * q) * t⁻¹) := by group
  rw [hsplit, map_mul]
  refine Subgroup.mul_mem _ h₀ ?_
  have hk := (mem_integralConjStable_iff.1 hq).2 t ht
  simpa only [map_mul, map_inv] using hk

private theorem algebraMap_mem_integralFiniteAdeles' (r : 𝓞 F) :
    algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r ∈ AdelicLevel.integralFiniteAdeles (𝓞 F) F := by
  intro v
  exact AdelicLevel.algebraMap_mem_adicCompletionIntegers v r

private theorem prod_algebraMap_mem_integralFiniteAdeles {ι : Type*} (s : Finset ι) (f : ι → 𝓞 F) :
    (∏ p ∈ s, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (f p)) ∈ AdelicLevel.integralFiniteAdeles (𝓞 F) F :=
  Finset.prod_induction _ (· ∈ AdelicLevel.integralFiniteAdeles (𝓞 F) F) (fun _ _ => mul_mem_integralFiniteAdeles)
    one_mem_integralFiniteAdeles fun p _ => algebraMap_mem_integralFiniteAdeles' (f p)

private theorem exists_ne_zero_forall_mul_mem_range (m : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F,
      glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * m ∈ finiteIntegralGL2 (𝓞 F) F →
        ∀ i j : Fin 2, (D : F) * (γ : Matrix (Fin 2) (Fin 2) F) i j ∈ (algebraMap (𝓞 F) F).range := by
  classical
  choose s hs0 hs using fun p : Fin 2 × Fin 2 => exists_mul_mem_integralFiniteAdeles (𝓞 F) F
    (((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) p.1 p.2)
  refine ⟨∏ p : Fin 2 × Fin 2, s p, Finset.prod_ne_zero_iff.2 fun p _ => hs0 p, fun γ hγ i j => ?_⟩
  set κ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F) := glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * m
    with hκdef
  have hκ : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) = κ * m⁻¹ := by
    rw [hκdef, mul_inv_cancel_right]
  have hentry : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((γ : Matrix (Fin 2) (Fin 2) F) i j)
      = ∑ l : Fin 2,
          (κ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i l *
            ((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) l j := by
    rw [← SiegelReduction.glFin_globalPoints_apply F γ i j, hκ, Units.val_mul, Matrix.mul_apply]

  have hterm : ∀ l : Fin 2,
      algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (∏ p : Fin 2 × Fin 2, s p) *
          ((κ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i l *
            ((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) l j)
        ∈ AdelicLevel.integralFiniteAdeles (𝓞 F) F := by
    intro l
    rw [map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (l, j))]
    have hrest := prod_algebraMap_mem_integralFiniteAdeles (Finset.univ.erase (l, j)) s
    have hκl := (mem_finiteIntegralGL2_iff.1 hγ).1 i l
    have hmain : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (s (l, j)) *
        ((m⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) l j ∈ AdelicLevel.integralFiniteAdeles (𝓞 F) F :=
      hs (l, j)
    convert mul_mem_integralFiniteAdeles hκl (mul_mem_integralFiniteAdeles hrest hmain) using 1
    ring
  apply SiegelReduction.mem_range_of_coe_mem_integralFiniteAdeles F
  rw [map_mul, hentry, Finset.mul_sum, ← IsScalarTower.algebraMap_apply, Fin.sum_univ_two]
  exact add_mem_integralFiniteAdeles (hterm 0) (hterm 1)

private theorem localHeight_globalPoints_mul (β : Matrix.GeneralLinearGroup (Fin 2) F)
    (hβ : (β : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (q : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F β * q)))
      = w ((β : Matrix (Fin 2) (Fin 2) F) 0 0) / w ((β : Matrix (Fin 2) (Fin 2) F) 1 1)
          * localHeight (archComponent F w (glArch (𝓞 F) F q)) := by
  have hdet : (β : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units β).ne_zero
  have h11 : (β : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h
    apply hdet
    rw [Matrix.det_fin_two, hβ, h]
    ring
  rw [map_mul, map_mul]
  rw [SiegelCoordinates.localHeight_upper_entries_mul (a := ((β : Matrix (Fin 2) (Fin 2) F) 0 0 : w.Completion))
    (t := ((β : Matrix (Fin 2) (Fin 2) F) 1 1 : w.Completion)) ?_
    (SiegelReduction.archComponent_globalPoints_apply F w β 0 0) ?_
    (SiegelReduction.archComponent_globalPoints_apply F w β 1 1)]
  · rw [SiegelReduction.norm_coe_completion, SiegelReduction.norm_coe_completion]
  · rw [← norm_ne_zero_iff, SiegelReduction.norm_coe_completion]
    exact (InfinitePlace.pos_iff.2 h11).ne'
  · rw [SiegelReduction.archComponent_globalPoints_apply, ← norm_eq_zero, SiegelReduction.norm_coe_completion, hβ,
      map_zero]

private theorem archDetNorm_globalPoints_mul (β : Matrix.GeneralLinearGroup (Fin 2) F) (q : AdelicGL2 (𝓞 F) F)
    (w : InfinitePlace F) :
    archDetNorm w (globalPoints (𝓞 F) F β * q) = w ((β : Matrix (Fin 2) (Fin 2) F).det) * archDetNorm w q := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul, SiegelReduction.det_archComponent_globalPoints,
    SiegelReduction.norm_coe_completion]

private theorem centralScalar_fst_apply_ne_zero (z : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((z : AdeleRing (𝓞 F) F).1 w : w.Completion) ≠ 0 := by
  have h : archEval F w (adeleArch (𝓞 F) F (z : AdeleRing (𝓞 F) F)) *
      archEval F w (adeleArch (𝓞 F) F ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) = 1 := by
    rw [← map_mul, ← map_mul, z.mul_inv, map_one, map_one]
  exact left_ne_zero_of_mul_eq_one h

private theorem archComponent_centralScalar_apply (z : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) (i j : Fin 2) :
    (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then ((z : AdeleRing (𝓞 F) F).1 w : w.Completion) else 0 := by
  rw [archComponent_apply, glArch_apply, centralScalar_val, Matrix.diagonal_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij]
    exact (show archEval F w (adeleArch (𝓞 F) F 0) = 0 by rw [map_zero, map_zero])

private theorem localHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (q : AdelicGL2 (𝓞 F) F)
    (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z * q)))
      = localHeight (archComponent F w (glArch (𝓞 F) F q)) := by
  rw [map_mul, map_mul]
  exact localHeight_scalar_entries_mul (centralScalar_fst_apply_ne_zero z w)
    (by rw [archComponent_centralScalar_apply]; simp) (by rw [archComponent_centralScalar_apply]; simp)
    (by rw [archComponent_centralScalar_apply]; simp) (by rw [archComponent_centralScalar_apply]; simp) _

private theorem archDetNorm_centralScalar_mul' (z : (AdeleRing (𝓞 F) F)ˣ) (q : AdelicGL2 (𝓞 F) F)
    (w : InfinitePlace F) :
    archDetNorm w (centralScalar (𝓞 F) F z * q)
      = ‖((z : AdeleRing (𝓞 F) F).1 w : w.Completion)‖ ^ 2 * archDetNorm w q := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  rw [Matrix.det_fin_two, archComponent_centralScalar_apply, archComponent_centralScalar_apply,
    archComponent_centralScalar_apply, archComponent_centralScalar_apply]
  simp [sq, norm_mul]

private theorem exists_one_le_forall_localHeight_le_and_archDetNorm_le (β : Matrix.GeneralLinearGroup (Fin 2) F)
    (hβ : (β : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ∃ l : ℝ, 1 ≤ l ∧ ∀ (q : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F),
      (localHeight (archComponent F w (glArch (𝓞 F) F q))
          ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F
              (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z))) ∧
        localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z)))
          ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F q))) ∧
      (archDetNorm w q ≤ l * archDetNorm w (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z) ∧
        archDetNorm w (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z) ≤ l * archDetNorm w q) := by
  have hdet : (β : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units β).ne_zero
  have h11 : (β : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h
    apply hdet
    rw [Matrix.det_fin_two, hβ, h]
    ring
  have h00 : (β : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hdet
    rw [Matrix.det_fin_two, hβ, h]
    ring

  set ρ : InfinitePlace F → ℝ := fun w =>
    w ((β : Matrix (Fin 2) (Fin 2) F) 0 0) / w ((β : Matrix (Fin 2) (Fin 2) F) 1 1) with hρ
  set δ : InfinitePlace F → ℝ := fun w =>
    ‖((z : AdeleRing (𝓞 F) F).1 w : w.Completion)‖ ^ 2 * w ((β : Matrix (Fin 2) (Fin 2) F).det) with hδ
  have hρpos : ∀ w, 0 < ρ w := fun w => div_pos (InfinitePlace.pos_iff.2 h00) (InfinitePlace.pos_iff.2 h11)
  have hδpos : ∀ w, 0 < δ w := fun w =>
    mul_pos (pow_pos (norm_pos_iff.2 (centralScalar_fst_apply_ne_zero z w)) 2) (InfinitePlace.pos_iff.2 hdet)
  refine ⟨1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹)), ?_, fun q w => ?_⟩
  · have : 0 ≤ ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹)) :=
      Finset.sum_nonneg fun w _ => by have := hρpos w; have := hδpos w; positivity
    linarith
  have hterm : ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹) ≤ ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹)) :=
    Finset.single_le_sum (f := fun w => ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹))
      (fun w _ => by have := hρpos w; have := hδpos w; positivity) (Finset.mem_univ w)
  have hρw := hρpos w
  have hδw := hδpos w
  have hρinv : 0 < (ρ w)⁻¹ := inv_pos.2 hρw
  have hδinv : 0 < (δ w)⁻¹ := inv_pos.2 hδw
  have hρl : ρ w ≤ 1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹)) := by linarith
  have hρl' : (ρ w)⁻¹ ≤ 1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹)) := by linarith
  have hδl : δ w ≤ 1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹)) := by linarith
  have hδl' : (δ w)⁻¹ ≤ 1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹)) := by linarith

  have hheight : localHeight (archComponent F w (glArch (𝓞 F) F
      (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z)))
        = ρ w * localHeight (archComponent F w (glArch (𝓞 F) F q)) := by
    rw [mul_centralScalar_comm, localHeight_centralScalar_mul, localHeight_globalPoints_mul β hβ]
  have hdetn : archDetNorm w (globalPoints (𝓞 F) F β * q * centralScalar (𝓞 F) F z) = δ w * archDetNorm w q := by
    rw [mul_centralScalar_comm, archDetNorm_centralScalar_mul', archDetNorm_globalPoints_mul, hδ]
    ring
  have hq := localHeight_pos (archComponent F w (glArch (𝓞 F) F q))
  have hd := archDetNorm_pos w q
  rw [hheight, hdetn]
  have hρ1 : 1 ≤ (1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹))) * ρ w := by
    calc (1 : ℝ) = (ρ w)⁻¹ * ρ w := (inv_mul_cancel₀ hρw.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hρl' hρw.le
  have hδ1 : 1 ≤ (1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹))) * δ w := by
    calc (1 : ℝ) = (δ w)⁻¹ * δ w := (inv_mul_cancel₀ hδw.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hδl' hδw.le
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · calc localHeight (archComponent F w (glArch (𝓞 F) F q))
        = 1 * localHeight (archComponent F w (glArch (𝓞 F) F q)) := (one_mul _).symm
      _ ≤ ((1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹))) * ρ w) *
          localHeight (archComponent F w (glArch (𝓞 F) F q)) := mul_le_mul_of_nonneg_right hρ1 hq.le
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right hρl hq.le
  · calc archDetNorm w q = 1 * archDetNorm w q := (one_mul _).symm
      _ ≤ ((1 + ∑ w : InfinitePlace F, (ρ w + (ρ w)⁻¹ + (δ w + (δ w)⁻¹))) * δ w) * archDetNorm w q :=
          mul_le_mul_of_nonneg_right hδ1 hd.le
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right hδl hd.le

private theorem archHeight_glArch_eq_prod (h : AdelicGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F h)
      = ∏ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F h)) ^ w.mult := rfl

private theorem pow_le_archHeight {c : ℝ} (hc : 0 ≤ c) (h : AdelicGL2 (𝓞 F) F)
    (hh : ∀ w : InfinitePlace F, c ≤ localHeight (archComponent F w (glArch (𝓞 F) F h))) :
    c ^ (∑ w : InfinitePlace F, w.mult) ≤ archHeight F (glArch (𝓞 F) F h) := by
  rw [archHeight_glArch_eq_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg hc _) fun w _ => pow_le_pow_left₀ hc (hh w) _

private theorem exists_forall_entry_eq_zero {c : ℝ} (hc : 0 < c) (d₂ : ℝ) (h₀ : AdelicGL2 (𝓞 F) F) :
    ∃ A : ℝ, ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (h : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F h = glFin (𝓞 F) F h₀ → (∀ w : InfinitePlace F, archDetNorm w h = archDetNorm w h₀) →
        A < archHeight F (glArch (𝓞 F) F h) →
          glFin (𝓞 F) F (globalPoints (𝓞 F) F γ * h) ∈ finiteIntegralGL2 (𝓞 F) F →
            (∀ w : InfinitePlace F,
              c ≤ localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ * h)))) →
              (∀ w : InfinitePlace F, archDetNorm w (globalPoints (𝓞 F) F γ * h) ≤ d₂) →
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨D, hD0, hD⟩ := exists_ne_zero_forall_mul_mem_range (glFin (𝓞 F) F h₀)

  set ND : ℝ := |(Algebra.norm ℚ (D : F) : ℝ)| with hND
  have hND1 : 1 ≤ ND := SiegelReduction.one_le_abs_norm_of_mem_range F ⟨D, rfl⟩ (by exact_mod_cast hD0)
  set B : ℝ := ∏ w : InfinitePlace F, (d₂ / archDetNorm w h₀) ^ w.mult with hB
  set c₀ : ℝ := c ^ (∑ w : InfinitePlace F, w.mult) with hc₀
  have hc₀pos : 0 < c₀ := pow_pos hc _
  refine ⟨B * ND ^ 2 / c₀, fun γ h hfin hdet hA hint hfloor hcap => ?_⟩
  by_contra hγ

  have hclass : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * glFin (𝓞 F) F h₀ ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [← hfin, ← map_mul]
    exact hint
  have hD10 := hD γ hclass 1 0
  have hN10 : 1 ≤ ND * |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℝ)| := by
    have h1 := SiegelReduction.one_le_abs_norm_of_mem_range F hD10 (mul_ne_zero (by exact_mod_cast hD0) hγ)
    rwa [map_mul, Rat.cast_mul, abs_mul] at h1

  have hdetγ : ∀ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det) ≤ d₂ / archDetNorm w h₀ := by
    intro w
    have h1 := hcap w
    rw [archDetNorm_globalPoints_mul, hdet w] at h1
    exact (le_div_iff₀ (archDetNorm_pos w h₀)).2 h1
  have hNdet : |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F).det) : ℝ)| ≤ B := by
    rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (apply_nonneg w _) _)
      fun w _ => pow_le_pow_left₀ (apply_nonneg w _) (hdetγ w) _
  have hB0 : 0 ≤ B :=
    Finset.prod_nonneg fun w _ => pow_nonneg ((apply_nonneg w _).trans (hdetγ w)) _

  have hred := SiegelReduction.archHeight_globalPoints_mul_mul_archHeight_le F γ hγ (glArch (𝓞 F) F h)
  rw [← map_mul] at hred
  have hlow : c₀ ≤ archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ * h)) := pow_le_archHeight hc.le _ hfloor
  have hhpos : 0 < archHeight F (glArch (𝓞 F) F h) := by
    rw [archHeight_glArch_eq_prod]
    exact Finset.prod_pos fun w _ => pow_pos (localHeight_pos _) _
  set N10 : ℝ := |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℝ)| with hN10def
  have hN10pos : 0 < N10 := by
    by_contra hle
    have h0 : N10 = 0 := le_antisymm (not_lt.1 hle) (abs_nonneg _)
    rw [h0, mul_zero] at hN10
    exact absurd hN10 (by norm_num)
  have hquot : |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F).det) : ℝ)| / N10 ^ 2 ≤ B * ND ^ 2 := by
    rw [div_le_iff₀ (pow_pos hN10pos 2)]
    calc |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F).det) : ℝ)| ≤ B := hNdet
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * (ND * N10) ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hN10) hB0
      _ = B * ND ^ 2 * N10 ^ 2 := by ring
  have hA' : B * ND ^ 2 < archHeight F (glArch (𝓞 F) F h) * c₀ := (div_lt_iff₀ hc₀pos).1 hA
  have hchain : archHeight F (glArch (𝓞 F) F h) * c₀
      ≤ archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ * h)) * archHeight F (glArch (𝓞 F) F h) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hlow hhpos.le
  exact absurd (hchain.trans (hred.trans hquot)) (not_le.2 hA')

private theorem archHeight_glArch_pos (h : AdelicGL2 (𝓞 F) F) : 0 < archHeight F (glArch (𝓞 F) F h) := by
  rw [archHeight_glArch_eq_prod]
  exact Finset.prod_pos fun w _ => pow_pos (localHeight_pos _) _

private theorem det_snd_eq (g : AdelicGL2 (𝓞 F) F) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2
      = ((glFin (𝓞 F) F g : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change adeleFin (𝓞 F) F (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

private theorem det_eq_of_glFin_eq {g g' : AdelicGL2 (𝓞 F) F} (hfin : glFin (𝓞 F) F g = glFin (𝓞 F) F g')
    (harch : ∀ w : InfinitePlace F,
      ((archComponent F w (glArch (𝓞 F) F g) : Matrix.GeneralLinearGroup (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det
        = ((archComponent F w (glArch (𝓞 F) F g') : Matrix.GeneralLinearGroup (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det g' := by
  apply Units.ext
  apply Prod.ext
  · funext w
    rw [det_fst_apply, det_fst_apply, harch w]
  · rw [det_snd_eq, det_snd_eq, hfin]

private noncomputable def diagElt (w : InfinitePlace F) (y : w.Completion) (hy : y ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![y, y⁻¹]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp [mul_inv_cancel₀ hy])

omit [NumberField F] in
private theorem norm_natCast_completion' (w : InfinitePlace F) (n : ℕ) : ‖(n : w.Completion)‖ = n := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_natCast,
    RCLike.norm_natCast]

private theorem exists_glFin_eq_and_lt_archHeight (q₀ : AdelicGL2 (𝓞 F) F) (A : ℝ) :
    ∃ g : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F g = glFin (𝓞 F) F q₀ ∧
      Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det q₀ ∧
        (∀ w : InfinitePlace F, archDetNorm w g = archDetNorm w q₀) ∧ A < archHeight F (glArch (𝓞 F) F g) := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hH := archHeight_glArch_pos q₀
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (|A| / archHeight F (glArch (𝓞 F) F q₀) + 1))
  set y : w₀.Completion := (N : w₀.Completion) with hydef
  have hy : max 1 (|A| / archHeight F (glArch (𝓞 F) F q₀) + 1) < ‖y‖ := by
    rw [hydef, norm_natCast_completion']
    exact hN
  have hy1 : 1 < ‖y‖ := (le_max_left _ _).trans_lt hy
  have hy0 : y ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  set s : Matrix.GeneralLinearGroup (Fin 2) w₀.Completion := diagElt w₀ y hy0 with hs
  have hs00 : (s : Matrix (Fin 2) (Fin 2) w₀.Completion) 0 0 = y := by simp [hs, diagElt]
  have hs10 : (s : Matrix (Fin 2) (Fin 2) w₀.Completion) 1 0 = 0 := by simp [hs, diagElt]
  have hs11 : (s : Matrix (Fin 2) (Fin 2) w₀.Completion) 1 1 = y⁻¹ := by simp [hs, diagElt]
  have hsdet : (s : Matrix (Fin 2) (Fin 2) w₀.Completion).det = 1 := by
    rw [Matrix.det_fin_two, hs00, hs10, hs11]
    simp [mul_inv_cancel₀ hy0]
  refine ⟨SiegelVolume.archEmbed F w₀ s * q₀, SiegelVolume.glFin_archEmbed_mul w₀ s q₀, ?_, ?_, ?_⟩
  · refine det_eq_of_glFin_eq (SiegelVolume.glFin_archEmbed_mul w₀ s q₀) fun w => ?_
    by_cases hw : w = w₀
    · subst hw
      rw [SiegelVolume.archComponent_glArch_archEmbed_mul_self, Units.val_mul, Matrix.det_mul, hsdet, one_mul]
    · rw [SiegelVolume.archComponent_glArch_archEmbed_mul_of_ne hw]
  · intro w
    by_cases hw : w = w₀
    · subst hw
      rw [SiegelVolume.archDetNorm_archEmbed_mul_self, hsdet, norm_one, one_mul]
    · exact SiegelVolume.archDetNorm_archEmbed_mul_of_ne hw s q₀
  ·
    have hw₀ : localHeight (archComponent F w₀ (glArch (𝓞 F) F (SiegelVolume.archEmbed F w₀ s * q₀)))
        = ‖y‖ ^ 2 * localHeight (archComponent F w₀ (glArch (𝓞 F) F q₀)) := by
      rw [SiegelVolume.archComponent_glArch_archEmbed_mul_self,
        SiegelCoordinates.localHeight_upper_entries_mul (inv_ne_zero hy0) hs00 hs10 hs11, norm_inv, div_inv_eq_mul,
        sq]
    have hother : ∀ w : InfinitePlace F, w ≠ w₀ →
        localHeight (archComponent F w (glArch (𝓞 F) F (SiegelVolume.archEmbed F w₀ s * q₀)))
          = localHeight (archComponent F w (glArch (𝓞 F) F q₀)) := fun w hw => by
      rw [SiegelVolume.archComponent_glArch_archEmbed_mul_of_ne hw]
    have hsplit : archHeight F (glArch (𝓞 F) F (SiegelVolume.archEmbed F w₀ s * q₀))
        = (‖y‖ ^ 2) ^ w₀.mult * archHeight F (glArch (𝓞 F) F q₀) := by
      rw [archHeight_glArch_eq_prod, archHeight_glArch_eq_prod,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀),
        ← Finset.mul_prod_erase Finset.univ (fun w => localHeight (archComponent F w (glArch (𝓞 F) F q₀)) ^ w.mult)
          (Finset.mem_univ w₀), hw₀, mul_pow]
      rw [Finset.prod_congr rfl fun w hw => by rw [hother w (Finset.ne_of_mem_erase hw)]]
      ring
    have hy2 : ‖y‖ ^ 2 ≤ (‖y‖ ^ 2) ^ w₀.mult :=
      le_self_pow₀ (one_le_pow₀ hy1.le) (show 0 < w₀.mult from InfinitePlace.mult_pos).ne'
    have hyA : |A| / archHeight F (glArch (𝓞 F) F q₀) + 1 < ‖y‖ ^ 2 := by
      have h1 := (le_max_right _ _).trans_lt hy
      nlinarith [hy1, abs_nonneg A, div_nonneg (abs_nonneg A) hH.le]
    rw [hsplit]
    calc A ≤ |A| := le_abs_self A
      _ < (|A| / archHeight F (glArch (𝓞 F) F q₀) + 1) * archHeight F (glArch (𝓞 F) F q₀) := by
          rw [add_mul, div_mul_cancel₀ _ hH.ne', one_mul]
          linarith
      _ ≤ ‖y‖ ^ 2 * archHeight F (glArch (𝓞 F) F q₀) := mul_le_mul_of_nonneg_right hyA.le hH.le
      _ ≤ (‖y‖ ^ 2) ^ w₀.mult * archHeight F (glArch (𝓞 F) F q₀) := mul_le_mul_of_nonneg_right hy2 hH.le

private theorem archDetNorm_mul' (w : InfinitePlace F) (x y : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (x * y) = archDetNorm w x * archDetNorm w y := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

private theorem archDetNorm_mul_archDetNorm_inv (w : InfinitePlace F) (t : AdelicGL2 (𝓞 F) F) :
    archDetNorm w t * archDetNorm w t⁻¹ = 1 := by
  rw [← archDetNorm_mul', mul_inv_cancel]
  unfold archDetNorm
  rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one]

private theorem le_mul_of_eq_mul_aux {l₁ C l₂ dq dY dX dt dti : ℝ} (hl₁ : 0 ≤ l₁) (hC : 1 ≤ C) (hl₂ : 1 ≤ l₂)
    (hdX : dX = dY * dti) (hdY : dY = dX * dt) (d1 : dq ≤ l₁ * dY) (d2 : dY ≤ l₁ * dq) (ht : dt ≤ l₂) (hti : dti ≤ l₂)
    (hXpos : 0 ≤ dX) (hqpos : 0 ≤ dq) (hdti : 0 ≤ dti) :
    dq ≤ l₁ * C * l₂ * dX ∧ dX ≤ l₁ * C * l₂ * dq := by
  have hl₂0 : 0 ≤ l₂ := by linarith
  constructor
  · calc dq ≤ l₁ * dY := d1
      _ = l₁ * (dX * dt) := by rw [hdY]
      _ ≤ l₁ * (dX * l₂) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hXpos) hl₁
      _ = l₁ * 1 * l₂ * dX := by ring
      _ ≤ l₁ * C * l₂ * dX := by
          apply mul_le_mul_of_nonneg_right _ hXpos
          apply mul_le_mul_of_nonneg_right _ hl₂0
          exact mul_le_mul_of_nonneg_left hC hl₁
  · calc dX = dY * dti := hdX
      _ ≤ (l₁ * dq) * l₂ := mul_le_mul d2 hti hdti (mul_nonneg hl₁ hqpos)
      _ = l₁ * 1 * l₂ * dq := by ring
      _ ≤ l₁ * C * l₂ * dq := by
          apply mul_le_mul_of_nonneg_right _ hqpos
          apply mul_le_mul_of_nonneg_right _ hl₂0
          exact mul_le_mul_of_nonneg_left hC hl₁

private theorem exists_triple_forall_of_inv_mul_mem {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)} (hc : 0 < c)
    (hd₁ : 0 < d₁) (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (q₀ : AdelicGL2 (𝓞 F) F) :
    ∃ e : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ × Matrix.GeneralLinearGroup (Fin 2) F, ∃ l : ℝ, 1 ≤ l ∧
      e.1 ∈ T ∧ (e.2.2 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        ∀ q : AdelicGL2 (𝓞 F) F, (glFin (𝓞 F) F q₀)⁻¹ * glFin (𝓞 F) F q ∈ integralConjStable T →
          glFin (𝓞 F) F (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)
              ∈ finiteIntegralGL2 (𝓞 F) F ∧
            (∀ w : InfinitePlace F,
              localHeight (archComponent F w (glArch (𝓞 F) F q))
                  ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F
                      (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹))) ∧
                localHeight (archComponent F w (glArch (𝓞 F) F
                    (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)))
                  ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F q))) ∧
            (∀ w : InfinitePlace F,
              archDetNorm w q
                  ≤ l * archDetNorm w (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹) ∧
                archDetNorm w (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)
                  ≤ l * archDetNorm w q) := by
  classical

  obtain ⟨Z, hZ⟩ := exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
    F c u d₁ d₂ T hd₁ hd hcov (ideleNorm F (Matrix.GeneralLinearGroup.det q₀))
    (ideleNorm F (Matrix.GeneralLinearGroup.det q₀)) (ideleNorm_pos _) le_rfl

  choose A hA using fun p : (AdeleRing (𝓞 F) F)ˣ × AdelicGL2 (𝓞 F) F =>
    exists_forall_entry_eq_zero hc d₂ (q₀ * centralScalar (𝓞 F) F p.1 * p.2⁻¹)
  set A₀ : ℝ := ∑ p ∈ Z ×ˢ T, |A p| with hA₀

  set R₀ : Finset (AdelicGL2 (𝓞 F) F) := T ∪ T.image (fun t => t⁻¹) with hR₀
  obtain ⟨C, hC1, hC⟩ := exists_forall_localHeight_le_mul_localHeight_mul (R := (R₀ : Set (AdelicGL2 (𝓞 F) F)))
    R₀.finite_toSet.isCompact
  have hCpos : 0 < C := by linarith
  set n : ℕ := ∑ w : InfinitePlace F, w.mult with hn

  obtain ⟨g, hgfin, hgdet, hgdets, hgA⟩ := exists_glFin_eq_and_lt_archHeight q₀ (|A₀| * C ^ n)
  obtain ⟨γ, z, hzZ, hmem⟩ := hZ g (by rw [hgdet]; exact ⟨le_rfl, le_rfl⟩)
  obtain ⟨t, ht, p, hp, hpt⟩ := Set.mem_iUnion₂.1 hmem
  have htR : t ∈ (R₀ : Set (AdelicGL2 (𝓞 F) F)) := Finset.mem_coe.2 (Finset.mem_union_left _ ht)
  have htinvR : t⁻¹ ∈ (R₀ : Set (AdelicGL2 (𝓞 F) F)) :=
    Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))

  have hX₀ : globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z * t⁻¹ ∈ centreCutSiegelSet F c u d₁ d₂ := by
    rw [← hpt, mul_inv_cancel_right]
    exact hp
  obtain ⟨hXfin, hXfloor, -, hXdet⟩ := (mem_centreCutSiegelSet_iff (F := F)).1 hX₀
  have hassoc : globalPoints (𝓞 F) F γ * (g * centralScalar (𝓞 F) F z * t⁻¹)
      = globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z * t⁻¹ := by simp only [mul_assoc]

  have hAlt : A (z, t) < archHeight F (glArch (𝓞 F) F (g * centralScalar (𝓞 F) F z * t⁻¹)) := by
    have hA₀le : A (z, t) ≤ |A₀| := by
      refine (le_abs_self _).trans ((Finset.single_le_sum (f := fun p => |A p|) (fun p _ => abs_nonneg _)
        (Finset.mem_product.2 ⟨hzZ, ht⟩)).trans (le_abs_self _))
    have hplace : ∀ w : InfinitePlace F,
        localHeight (archComponent F w (glArch (𝓞 F) F g)) / C
          ≤ localHeight (archComponent F w (glArch (𝓞 F) F (g * centralScalar (𝓞 F) F z * t⁻¹))) := by
      intro w
      have h1 := hC t⁻¹ htinvR (g * centralScalar (𝓞 F) F z) w
      have h2 : localHeight (archComponent F w (glArch (𝓞 F) F (g * centralScalar (𝓞 F) F z)))
          = localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
        rw [mul_centralScalar_comm, localHeight_centralScalar_mul]
      rw [h2] at h1
      rw [div_le_iff₀ hCpos, mul_comm _ C]
      exact h1
    have hprod : archHeight F (glArch (𝓞 F) F g) / C ^ n
        ≤ archHeight F (glArch (𝓞 F) F (g * centralScalar (𝓞 F) F z * t⁻¹)) := by
      rw [archHeight_glArch_eq_prod, archHeight_glArch_eq_prod, hn, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_div_distrib]
      exact Finset.prod_le_prod (fun w _ => div_nonneg (pow_nonneg (localHeight_pos _).le _) (pow_nonneg hCpos.le _))
        fun w _ => by rw [← div_pow]; exact pow_le_pow_left₀ (div_nonneg (localHeight_pos _).le hCpos.le) (hplace w) _
    have hCn : 0 < C ^ n := pow_pos hCpos n
    calc A (z, t) ≤ |A₀| := hA₀le
      _ = |A₀| * C ^ n / C ^ n := (mul_div_cancel_right₀ _ hCn.ne').symm
      _ < archHeight F (glArch (𝓞 F) F g) / C ^ n := by gcongr
      _ ≤ _ := hprod

  have hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    refine hA (z, t) γ (g * centralScalar (𝓞 F) F z * t⁻¹) ?_ ?_ hAlt ?_ ?_ ?_
    · simp only [map_mul, map_inv, hgfin]
    · intro w
      simp only [archDetNorm_mul', hgdets w]
    · rw [hassoc]; exact hXfin
    · intro w; rw [hassoc]; exact hXfloor w
    · intro w; rw [hassoc]; exact (hXdet w).2

  have hq₀fin : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ * q₀ * centralScalar (𝓞 F) F z * t⁻¹)
      ∈ finiteIntegralGL2 (𝓞 F) F := by
    have h : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ * q₀ * centralScalar (𝓞 F) F z * t⁻¹)
        = glFin (𝓞 F) F (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z * t⁻¹) := by
      simp only [map_mul, map_inv, hgfin]
    rw [h]; exact hXfin

  obtain ⟨l₁, hl₁, hlaws⟩ := exists_one_le_forall_localHeight_le_and_archDetNorm_le γ hγ z
  set l₂ : ℝ := 1 + ∑ w : InfinitePlace F, (archDetNorm w t + archDetNorm w t⁻¹) with hl₂def
  have hl₂ : 1 ≤ l₂ := by
    have : 0 ≤ ∑ w : InfinitePlace F, (archDetNorm w t + archDetNorm w t⁻¹) :=
      Finset.sum_nonneg fun w _ => add_nonneg (archDetNorm_pos w t).le (archDetNorm_pos w t⁻¹).le
    linarith
  have hl₂t : ∀ w : InfinitePlace F, archDetNorm w t ≤ l₂ ∧ archDetNorm w t⁻¹ ≤ l₂ := by
    intro w
    have h := Finset.single_le_sum (f := fun w => archDetNorm w t + archDetNorm w t⁻¹)
      (fun w _ => add_nonneg (archDetNorm_pos w t).le (archDetNorm_pos w t⁻¹).le) (Finset.mem_univ w)
    have h1 := archDetNorm_pos w t
    have h2 := archDetNorm_pos w t⁻¹
    constructor <;> linarith
  have hl₁0 : 0 ≤ l₁ := by linarith
  have hl₁C : 0 ≤ l₁ * C := mul_nonneg hl₁0 hCpos.le
  refine ⟨(t, z, γ), l₁ * C * l₂, ?_, ht, hγ, fun q hq => ?_⟩
  · calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ l₁ * C * l₂ := by gcongr

  set Y : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F γ * q * centralScalar (𝓞 F) F z with hY
  have hYX : Y = Y * t⁻¹ * t := (inv_mul_cancel_right Y t).symm
  refine ⟨glFin_mul_mem_of_inv_mul_mem ht γ z hq₀fin hq, fun w => ?_, fun w => ?_⟩
  · obtain ⟨⟨h1, h2⟩, -⟩ := hlaws q w
    have h3 := hC t⁻¹ htinvR Y w
    have h4 := hC t htR (Y * t⁻¹) w
    rw [← hYX] at h4
    have hXpos := localHeight_pos (archComponent F w (glArch (𝓞 F) F (Y * t⁻¹)))
    have hqpos := localHeight_pos (archComponent F w (glArch (𝓞 F) F q))
    constructor
    · calc localHeight (archComponent F w (glArch (𝓞 F) F q))
          ≤ l₁ * localHeight (archComponent F w (glArch (𝓞 F) F Y)) := h1
        _ ≤ l₁ * (C * localHeight (archComponent F w (glArch (𝓞 F) F (Y * t⁻¹)))) :=
            mul_le_mul_of_nonneg_left h3 hl₁0
        _ = l₁ * C * 1 * localHeight (archComponent F w (glArch (𝓞 F) F (Y * t⁻¹))) := by ring
        _ ≤ l₁ * C * l₂ * localHeight (archComponent F w (glArch (𝓞 F) F (Y * t⁻¹))) := by gcongr
    · calc localHeight (archComponent F w (glArch (𝓞 F) F (Y * t⁻¹)))
          ≤ C * localHeight (archComponent F w (glArch (𝓞 F) F Y)) := h4
        _ ≤ C * (l₁ * localHeight (archComponent F w (glArch (𝓞 F) F q))) := mul_le_mul_of_nonneg_left h2 hCpos.le
        _ = l₁ * C * 1 * localHeight (archComponent F w (glArch (𝓞 F) F q)) := by ring
        _ ≤ l₁ * C * l₂ * localHeight (archComponent F w (glArch (𝓞 F) F q)) := by gcongr
  · obtain ⟨-, d1, d2⟩ := hlaws q w
    have hdX : archDetNorm w (Y * t⁻¹) = archDetNorm w Y * archDetNorm w t⁻¹ := archDetNorm_mul' w Y t⁻¹
    have hdY : archDetNorm w Y = archDetNorm w (Y * t⁻¹) * archDetNorm w t := by
      rw [hdX, mul_assoc, mul_comm (archDetNorm w t⁻¹), archDetNorm_mul_archDetNorm_inv, mul_one]
    obtain ⟨ht₁, ht₂⟩ := hl₂t w
    have d1' : archDetNorm w q ≤ l₁ * archDetNorm w Y := d1
    have d2' : archDetNorm w Y ≤ l₁ * archDetNorm w q := d2
    exact le_mul_of_eq_mul_aux hl₁0 hC1 hl₂ hdX hdY d1' d2' ht₁ ht₂ (archDetNorm_pos w (Y * t⁻¹)).le
      (archDetNorm_pos w q).le (archDetNorm_pos w t⁻¹).le

end IntegralClasses

private theorem exists_finset_forall_exists_mem_finiteIntegralGL2_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Q : Set (AdelicGL2 (𝓞 F) F)) {C : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F))}
    (hC : IsCompact C) (hQ : ∀ q ∈ Q, glFin (𝓞 F) F q ∈ C) :
    ∃ l : ℝ, 1 ≤ l ∧
      ∃ L : Finset (AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ × Matrix.GeneralLinearGroup (Fin 2) F),
        (∀ e ∈ L, e.1 ∈ T ∧ (e.2.2 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) ∧
          ∀ q ∈ Q, ∃ e ∈ L,
            glFin (𝓞 F) F (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)
                ∈ finiteIntegralGL2 (𝓞 F) F ∧
              (∀ w : InfinitePlace F,
                localHeight (archComponent F w (glArch (𝓞 F) F q))
                    ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F
                        (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹))) ∧
                  localHeight (archComponent F w (glArch (𝓞 F) F
                      (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)))
                    ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F q))) ∧
              (∀ w : InfinitePlace F,
                NumberField.AdelicVolume.archDetNorm w q
                    ≤ l * NumberField.AdelicVolume.archDetNorm w
                        (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹) ∧
                  NumberField.AdelicVolume.archDetNorm w
                      (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)
                    ≤ l * NumberField.AdelicVolume.archDetNorm w q) := by
  classical

  obtain ⟨t₀, ht₀⟩ : T.Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    subst hT
    exact not_coversModCentre_empty (F := F) (by simpa using hcov)
  obtain ⟨s, hs⟩ := exists_finset_forall_exists_inv_mul_mem T hC

  have hclass : ∀ k₀ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F),
      ∃ e : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ × Matrix.GeneralLinearGroup (Fin 2) F, ∃ l : ℝ, 1 ≤ l ∧
        e.1 ∈ T ∧ (e.2.2 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
          ∀ q ∈ Q, k₀⁻¹ * glFin (𝓞 F) F q ∈ integralConjStable T →
            glFin (𝓞 F) F (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)
                ∈ finiteIntegralGL2 (𝓞 F) F ∧
              (∀ w : InfinitePlace F,
                localHeight (archComponent F w (glArch (𝓞 F) F q))
                    ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F
                        (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹))) ∧
                  localHeight (archComponent F w (glArch (𝓞 F) F
                      (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)))
                    ≤ l * localHeight (archComponent F w (glArch (𝓞 F) F q))) ∧
              (∀ w : InfinitePlace F,
                NumberField.AdelicVolume.archDetNorm w q
                    ≤ l * NumberField.AdelicVolume.archDetNorm w
                        (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹) ∧
                  NumberField.AdelicVolume.archDetNorm w
                      (globalPoints (𝓞 F) F e.2.2 * q * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹)
                    ≤ l * NumberField.AdelicVolume.archDetNorm w q) := by
    intro k₀
    by_cases hk : ∃ q₀ ∈ Q, k₀⁻¹ * glFin (𝓞 F) F q₀ ∈ integralConjStable T
    · obtain ⟨q₀, -, hq₀⟩ := hk
      obtain ⟨e, l, hl, het, hetri, he⟩ := exists_triple_forall_of_inv_mul_mem hc hd₁ hd hcov q₀
      refine ⟨e, l, hl, het, hetri, fun q _ hq => he q ?_⟩
      have h : (glFin (𝓞 F) F q₀)⁻¹ * glFin (𝓞 F) F q = (k₀⁻¹ * glFin (𝓞 F) F q₀)⁻¹ * (k₀⁻¹ * glFin (𝓞 F) F q) := by
        group
      rw [h]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hq₀) hq
    · refine ⟨(t₀, 1, 1), 1, le_rfl, ht₀, by simp, fun q hqQ hq => absurd ⟨q, hqQ, hq⟩ hk⟩
  choose e l hl₁ heT hetri he using hclass
  refine ⟨1 + ∑ k₀ ∈ s, l k₀, ?_, s.image e, ?_, fun q hq => ?_⟩
  · have : 0 ≤ ∑ k₀ ∈ s, l k₀ := Finset.sum_nonneg fun k₀ _ => by linarith [hl₁ k₀]
    linarith
  · intro e' he'
    obtain ⟨k₀, -, rfl⟩ := Finset.mem_image.1 he'
    exact ⟨heT k₀, hetri k₀⟩
  obtain ⟨k₀, hk₀s, hk₀⟩ := hs _ (hQ q hq)
  obtain ⟨hfin, hheight, hdet⟩ := he k₀ q hq hk₀
  have hlk : l k₀ ≤ 1 + ∑ k₀ ∈ s, l k₀ := by
    have h := Finset.single_le_sum (f := l) (fun k₀ _ => by linarith [hl₁ k₀]) hk₀s
    linarith
  refine ⟨e k₀, Finset.mem_image_of_mem e hk₀s, hfin, fun w => ?_, fun w => ?_⟩
  · obtain ⟨h1, h2⟩ := hheight w
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hlk (localHeight_pos _).le),
      h2.trans (mul_le_mul_of_nonneg_right hlk (localHeight_pos _).le)⟩
  · obtain ⟨h1, h2⟩ := hdet w
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hlk (NumberField.AdelicVolume.archDetNorm_pos _ _).le),
      h2.trans (mul_le_mul_of_nonneg_right hlk (NumberField.AdelicVolume.archDetNorm_pos _ _).le)⟩

private theorem exists_forall_orbitCount_le_mul_orbitCount {F : Type} [Field F] [NumberField F] {c u d₁ d₂ : ℝ}
    {T : Finset (AdelicGL2 (𝓞 F) F)} (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    {c' u' d₁' d₂' : ℝ} (hc' : 0 < c') (hd₁' : 0 < d₁') {R : Set (AdelicGL2 (𝓞 F) F)} (hR : IsCompact R) :
    ∃ N : ℕ, ∃ l : ℝ, 1 ≤ l ∧ ∃ Z : Finset (AdeleRing (𝓞 F) F)ˣ,
      ∀ H : ℝ, ∀ y ∈ R, ∀ s : AdelicGL2 (𝓞 F) F,
        orbitCount (globalPoints (𝓞 F) F).range
            ((· * y) '' (centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H)) s
          ≤ (N : ℝ≥0∞) * orbitCount (globalPoints (𝓞 F) F).range
            (⋃ z ∈ Z, (· * centralScalar (𝓞 F) F z) ''
              ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩ aboveLevel F (H / l))) s := by
  classical

  have hQ : ∀ q ∈ {q : AdelicGL2 (𝓞 F) F | ∃ p ∈ centreCutSiegelSet F c' u' d₁' d₂', ∃ y ∈ R, p * y = q},
      glFin (𝓞 F) F q ∈ integralMulImage R := by
    rintro q ⟨p, hp, y, hy, rfl⟩
    exact glFin_mul_mem_integralMulImage ((mem_centreCutSiegelSet_iff (F := F)).mp hp).1 hy
  obtain ⟨lE, hlE, L, hL, hE⟩ := exists_finset_forall_exists_mem_finiteIntegralGL2_of_coversModCentre F c u d₁ d₂ T
    hc hd₁ hd hcov _ (isCompact_integralMulImage hR) hQ

  obtain ⟨C, hC1, Znet, h4⟩ := exists_forall_exists_netScalar_mul_shiftPoint_mul_mem hu hd₁ hd hR hlE hd₁'
  obtain ⟨CT, hCT1, hCT⟩ :=
    exists_forall_localHeight_le_mul_localHeight_mul (R := (T : Set (AdelicGL2 (𝓞 F) F))) T.finite_toSet.isCompact

  have hterm : ∀ (e : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ × GL (Fin 2) F) (w : InfinitePlace F),
      0 ≤ w ((e.2.2 : Matrix (Fin 2) (Fin 2) F) 0 0) / w ((e.2.2 : Matrix (Fin 2) (Fin 2) F) 1 1) :=
    fun e w => div_nonneg (apply_nonneg w _) (apply_nonneg w _)
  have hρ : ∀ e ∈ L, ∀ w : InfinitePlace F,
      w ((e.2.2 : Matrix (Fin 2) (Fin 2) F) 0 0) / w ((e.2.2 : Matrix (Fin 2) (Fin 2) F) 1 1)
        ≤ ∑ e' ∈ L, ∑ w' : InfinitePlace F,
          w' ((e'.2.2 : Matrix (Fin 2) (Fin 2) F) 0 0) / w' ((e'.2.2 : Matrix (Fin 2) (Fin 2) F) 1 1) :=
    fun e he w =>
      (Finset.single_le_sum (f := fun w' : InfinitePlace F =>
          w' ((e.2.2 : Matrix (Fin 2) (Fin 2) F) 0 0) / w' ((e.2.2 : Matrix (Fin 2) (Fin 2) F) 1 1))
        (fun w' _ => hterm e w') (Finset.mem_univ w)).trans
      (Finset.single_le_sum (f := fun e' : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ × GL (Fin 2) F =>
          ∑ w' : InfinitePlace F,
            w' ((e'.2.2 : Matrix (Fin 2) (Fin 2) F) 0 0) / w' ((e'.2.2 : Matrix (Fin 2) (Fin 2) F) 1 1))
        (fun e' _ => Finset.sum_nonneg fun w' _ => hterm e' w') he)
  obtain ⟨A, hA⟩ := exists_forall_ncard_box_le (F := F) (|u'| * ∑ e' ∈ L, ∑ w' : InfinitePlace F,
    w' ((e'.2.2 : Matrix (Fin 2) (Fin 2) F) 0 0) / w' ((e'.2.2 : Matrix (Fin 2) (Fin 2) F) 1 1))
  have hl1 : 1 ≤ C * lE * CT := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC1 hlE) hCT1
  refine ⟨L.card * max A 1, C * lE * CT, hl1, (L ×ˢ Znet).image fun ez => (ez.1.2.1 * ez.2)⁻¹, fun H y hy s => ?_⟩
  rw [orbitCount_eq_encard, orbitCount_eq_encard]
  refine coe_encard_le_mul_coe_encard_of_cover L (fun e g' => fiberSet c' u' d₁' d₂' H y s e.2.2 g') (max A 1)
    (by omega) (fun e he g' => ?_) (fun g hg => ?_)
  · exact (encard_fiberSet_le (c' := c') (d₁' := d₁') (d₂' := d₂') (H := H) (y := y) (s := s) (hL e he).2 (hρ e he)
      hA g').trans (by exact_mod_cast le_max_left A 1)

  obtain ⟨p, ⟨hpS, hpH⟩, hpy⟩ := hg
  have hpy' : p * y = (g : AdelicGL2 (𝓞 F) F) * s := hpy
  obtain ⟨e, heL, hXf, hXh, hXd⟩ := hE (p * y) ⟨p, hpS, y, hy, rfl⟩
  obtain ⟨heT, hβ⟩ := hL e heL
  obtain ⟨ξ, a, haZ, hmem, hht⟩ := h4 c' u' p hpS y hy _ hXf (fun w => (hXh w).1) hXd
  refine ⟨e, heL, shiftElt ξ e.2.2 * g, ?_, ⟨p, ⟨hpS, hpH⟩, hpy⟩, ξ, rfl⟩
  show (shiftElt ξ e.2.2 * g) • s ∈ (_ : Set (AdelicGL2 (𝓞 F) F))
  have hland := mul_mem_iUnion_inter_aboveLevel (u := u) (d₁ := d₁) (d₂ := d₂) hc' hC1 hlE hCT1 hCT hpH heT hmem hht
  refine Set.mem_iUnion₂.mpr ⟨(e.2.1 * archNetUnit a)⁻¹,
    Finset.mem_image.mpr ⟨(e, archNetUnit a), Finset.mem_product.mpr ⟨heL, haZ⟩, rfl⟩, _, hland, ?_⟩
  show netScalar a * (shiftPoint ξ * (globalPoints (𝓞 F) F e.2.2 * (p * y) * centralScalar (𝓞 F) F e.2.1 * e.1⁻¹))
      * e.1 * centralScalar (𝓞 F) F (e.2.1 * archNetUnit a)⁻¹
      = (shiftElt ξ e.2.2 * g : (globalPoints (𝓞 F) F).range) • s
  rw [netScalar_mul_shiftPoint_mul_mul_eq, map_inv, map_mul, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
    shiftElt_coe, hpy']
  group

private theorem centreCutSiegelSet_subset_of_le_right {F : Type} [Field F] [NumberField F] {c u d₁ d₂ d₂' : ℝ}
    (h : d₂ ≤ d₂') : centreCutSiegelSet F c u d₁ d₂ ⊆ centreCutSiegelSet F c u d₁ d₂' := by
  intro g hg
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  exact ⟨hg.1, hg.2.1, hg.2.2.1, fun w => Set.Icc_subset_Icc_right h (hg.2.2.2 w)⟩

private def detSlab (F : Type) [Field F] [NumberField F] (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private theorem detSlab_subset_detSlab {F : Type} [Field F] [NumberField F] {α β α' β' : ℝ} (hα : α' ≤ α)
    (hβ : β ≤ β') : detSlab F α β ⊆ detSlab F α' β' := fun _ hg => Set.Icc_subset_Icc hα hβ hg

private theorem exists_forall_image_inter_aboveLevel_subset_detSlab {F : Type} [Field F] [NumberField F]
    {c' u' d₁' d₂' : ℝ} (hd₁' : 0 < d₁') {R : Set (AdelicGL2 (𝓞 F) F)} (hR : IsCompact R) :
    ∃ α β : ℝ, ∀ y ∈ R, ∀ H : ℝ,
      (· * y) '' (centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H) ⊆ detSlab F α β := by
  obtain ⟨α, β, -, -, -, h⟩ := exists_window_and_translates_subset_slab c' u' d₁' (max d₂' (d₁' + 1)) {1}
    (lt_max_of_lt_right (lt_add_one d₁')) hd₁' hR
  refine ⟨α, β, fun y hy H => ?_⟩
  rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
  refine h y hy ⟨p, Set.mem_iUnion₂.mpr ⟨1, Finset.mem_singleton_self 1, p, ?_, mul_one p⟩, rfl⟩
  exact centreCutSiegelSet_subset_of_le_right (le_max_left _ _) hp

private theorem exists_forall_iUnion_image_subset_detSlab {F : Type} [Field F] [NumberField F] {c u d₁ d₂ : ℝ}
    (hd₁ : 0 < d₁) (hd : d₁ < d₂) (T : Finset (AdelicGL2 (𝓞 F) F)) (Z : Finset (AdeleRing (𝓞 F) F)ˣ) :
    ∃ α β : ℝ, ∀ H : ℝ, (⋃ z ∈ Z, (· * centralScalar (𝓞 F) F z) ''
      ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ aboveLevel F H)) ⊆ detSlab F α β := by
  classical
  obtain ⟨α, β, -, -, -, h⟩ := exists_window_and_translates_subset_slab c u d₁ d₂ T hd hd₁
    (Z.image (centralScalar (𝓞 F) F)).finite_toSet.isCompact
  refine ⟨α, β, fun H => Set.iUnion₂_subset fun z hz => ?_⟩
  rintro _ ⟨r, ⟨hr, -⟩, rfl⟩
  exact h _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)) ⟨r, hr, rfl⟩

private theorem measurableSet_aboveLevel {F : Type} [Field F] [NumberField F] (H : ℝ) :
    MeasurableSet (aboveLevel F H) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  rw [aboveLevel, Set.setOf_exists]
  exact (isOpen_iUnion fun w => isOpen_lt continuous_const (continuous_localHeight_place w)).measurableSet

private theorem measurableSet_image_mul_right_inter_aboveLevel {F : Type} [Field F] [NumberField F]
    (c' u' d₁' d₂' H : ℝ) (y : AdelicGL2 (𝓞 F) F) :
    MeasurableSet ((· * y) '' (centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H)) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  rw [Set.image_mul_right]
  exact ((measurableSet_centreCutSiegelSet c' u' d₁' d₂').inter (measurableSet_aboveLevel H)).preimage
    (measurable_mul_const _)

private theorem measurableSet_iUnion_inter_aboveLevel {F : Type} [Field F] [NumberField F] (c u d₁ d₂ H : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) :
    MeasurableSet ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ aboveLevel F H) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine (Finset.measurableSet_biUnion T fun x _ => ?_).inter (measurableSet_aboveLevel H)
  rw [Set.image_mul_right]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const _)

private theorem measurableSet_iUnion_image_mul_centralScalar {F : Type} [Field F] [NumberField F]
    (Z : Finset (AdeleRing (𝓞 F) F)ˣ) {V : Set (AdelicGL2 (𝓞 F) F)} (hV : MeasurableSet V) :
    MeasurableSet (⋃ z ∈ Z, (· * centralScalar (𝓞 F) F z) '' V) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine Finset.measurableSet_biUnion Z fun z _ => ?_
  rw [Set.image_mul_right]
  exact hV.preimage (measurable_mul_const _)

private theorem setLIntegral_biUnion_finset_le_of_index {ι G : Type*} [MeasurableSpace G] (μ : Measure G)
    (f : G → ℝ≥0∞) (S : ι → Set G) (Z : Finset ι) : ∫⁻ y in ⋃ i ∈ Z, S i, f y ∂μ ≤ ∑ i ∈ Z, ∫⁻ y in S i, f y ∂μ := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a Z ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (by gcongr)

private theorem countable_range_globalPoints (F : Type) [Field F] [NumberField F] :
    Countable (globalPoints (𝓞 F) F).range := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (Set.countable_range (globalPoints (𝓞 F) F)).to_subtype

private theorem globalPoints_mul_mem_detSlab_iff {F : Type} [Field F] [NumberField F] {α β : ℝ} (γ : GL (Fin 2) F)
    (g : AdelicGL2 (𝓞 F) F) : globalPoints (𝓞 F) F γ * g ∈ detSlab F α β ↔ g ∈ detSlab F α β := by
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * g)) ∈ Set.Icc α β
    ↔ _
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  exact Iff.rfl

private theorem smulInvariantMeasure_restrict_detSlab {F : Type} [Field F] [NumberField F] (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detSlab F α β)) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.mp γ.2
  have hγ : ∀ g : AdelicGL2 (𝓞 F) F, γ • g = globalPoints (𝓞 F) F γ₀ * g := fun g => by
    rw [Subgroup.smul_def, smul_eq_mul, hγ₀]
  have hpre : (fun g => γ • g) ⁻¹' detSlab F α β = detSlab F α β := by
    ext g
    simp only [Set.mem_preimage, hγ, globalPoints_mul_mem_detSlab_iff]
  have hset : (fun g => γ • g) ⁻¹' s ∩ detSlab F α β = (fun g => γ • g) ⁻¹' (s ∩ detSlab F α β) := by
    rw [Set.preimage_inter, hpre]
  rw [Measure.restrict_apply (hs.preimage (measurable_const_smul γ)), Measure.restrict_apply hs, hset]
  show adelicGLHaar (Fin 2) (𝓞 F) F ((fun g => (γ : AdelicGL2 (𝓞 F) F) * g) ⁻¹' (s ∩ detSlab F α β)) = _
  exact measure_preimage_mul _ _ _

private theorem setLIntegral_nnnorm_mul_centralScalar_sq {F : Type} [Field F] [NumberField F]
    {χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hLs : IsLsXiFunction (𝓞 F) F ⊤ χ φ)
    (z : (AdeleRing (𝓞 F) F)ˣ) (V : Set (AdelicGL2 (𝓞 F) F)) :
    ∫⁻ x in V, (‖φ (x * centralScalar (𝓞 F) F z)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ ^ 2 : NNReal) : ℝ≥0∞)
          * ∫⁻ x in V, (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun x => ?_
  rw [mul_centralScalar_comm, show φ (centralScalar (𝓞 F) F z * x) = ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ x from
    hLs.central_transform ⟨z, Subgroup.mem_top z⟩ x, nnnorm_mul]
  push_cast
  ring

end SetLIntegralTranslateLeMulOfLtLocalHeightOfCoveringParameter

section TranslatesLeMulOfCoveringParameter
open scoped ENNReal
open MeasureTheory IsDedekindDomain Matrix
open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal Topology
attribute [local instance] glBorel

section CoveringWindowInclusions

open MeasureTheory
open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal

private theorem centreCutSiegelSet_subset_centreCutSiegelSet_of_le_of_sq_le_of_le_of_le
    {F : Type} [Field F] [NumberField F] {c c' u u' d₁ d₁' d₂ d₂' : ℝ} (hc : c' ≤ c) (hu : u ^ 2 ≤ u' ^ 2)
    (hd₁ : d₁' ≤ d₁) (hd₂ : d₂ ≤ d₂') :
    centreCutSiegelSet F c u d₁ d₂ ⊆ centreCutSiegelSet F c' u' d₁' d₂' := by
  intro g hg
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  exact ⟨hg.1, fun w => hc.trans (hg.2.1 w), fun w => (hg.2.2.1 w).trans hu,
    fun w => Set.Icc_subset_Icc hd₁ hd₂ (hg.2.2.2 w)⟩

private theorem centreCutSiegelSet_subset_centreCutSiegelSet_relaxed_of_pos
    {F : Type} [Field F] [NumberField F] {c c₀ u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hc₀ : 0 < c₀) :
    centreCutSiegelSet F c₀ u d₁ d₂ ⊆ centreCutSiegelSet F (c / max 1 (c / c₀)) (max 1 (c / c₀) * u)
      (d₁ / max 1 (c / c₀)) (max 1 (c / c₀) * d₂) := by
  refine centreCutSiegelSet_subset_centreCutSiegelSet_of_le_of_sq_le_of_le_of_le ?_ ?_ ?_ ?_
  · have hc' := hc.ne'
    have hc₀' := hc₀.ne'
    calc c / max 1 (c / c₀) ≤ c / (c / c₀) := div_le_div_of_nonneg_left hc.le (div_pos hc hc₀) (le_max_right _ _)
      _ = c₀ := by field_simp
  · rw [mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg u) (one_le_pow₀ (le_max_left _ _))
  · exact div_le_self hd₁.le (le_max_left _ _)
  · exact le_mul_of_one_le_left (hd₁.trans hd).le (le_max_left _ _)

end CoveringWindowInclusions

end TranslatesLeMulOfCoveringParameter

section Interface

open MeasureTheory IsDedekindDomain Matrix
open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal Topology

attribute [local instance] glBorel

private theorem setLIntegral_translate_le_mul_of_lt_localHeight_of_coveringParameter
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁')
    {R : Set (AdelicGL2 (𝓞 F) F)} (hR : IsCompact R) :
    ∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∃ l : ℝ, 1 ≤ l ∧
      ∀ H : ℝ, ∀ y ∈ R, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ χ φ →
        ∫⁻ x in centreCutSiegelSet F c' u' d₁' d₂' ∩
            {g | ∃ w : InfinitePlace F, H < localHeight (archComponent F w (glArch (𝓞 F) F g))},
            (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
          ≤ N * ∫⁻ x in (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩
              {g | ∃ w : InfinitePlace F, H / l < localHeight (archComponent F w (glArch (𝓞 F) F g))},
              (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar F
  obtain ⟨N, l, hl1, Z, hcount⟩ := exists_forall_orbitCount_le_mul_orbitCount hc hd₁ hd hu hcov hc' hd₁' hR
  obtain ⟨α₁, β₁, hleft⟩ :=
    exists_forall_image_inter_aboveLevel_subset_detSlab (c' := c') (u' := u') (d₂' := d₂') hd₁' hR
  obtain ⟨α₂, β₂, hright⟩ := exists_forall_iUnion_image_subset_detSlab (c := c' / l) (u := u) hd₁ hd T Z
  obtain ⟨S, -, hS⟩ := exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F (min α₁ α₂)
    (max β₁ β₂)
  haveI : SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (min α₁ α₂) (max β₁ β₂)}) :=
    smulInvariantMeasure_restrict_detSlab (F := F) (min α₁ α₂) (max β₁ β₂)
  haveI := countable_range_globalPoints F
  refine ⟨(N : ℝ≥0∞) * ((∑ z ∈ Z, ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ ^ 2 : NNReal) : ℝ≥0∞),
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.coe_ne_top, l, hl1, fun H y hy φ hφ hLs => ?_⟩
  have hV := measurableSet_image_mul_right_inter_aboveLevel (F := F) c' u' d₁' d₂' H y
  have hRel := measurableSet_iUnion_inter_aboveLevel (F := F) (c' / l) u d₁ d₂ (H / l) T
  have hW := measurableSet_iUnion_image_mul_centralScalar Z hRel
  have hVsub : (· * y) '' (centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H) ⊆ detSlab F (min α₁ α₂) (max β₁ β₂) :=
    (hleft y hy H).trans (detSlab_subset_detSlab (min_le_left _ _) (le_max_left _ _))
  have hWsub : (⋃ z ∈ Z, (· * centralScalar (𝓞 F) F z) ''
      ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩ aboveLevel F (H / l)))
        ⊆ detSlab F (min α₁ α₂) (max β₁ β₂) :=
    (hright (H / l)).trans (detSlab_subset_detSlab (min_le_right _ _) (le_max_right _ _))
  have hfm : AEMeasurable (fun g : AdelicGL2 (𝓞 F) F => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detSlab F (min α₁ α₂) (max β₁ β₂))) :=
    ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp hφ.nnnorm)).measurable.aemeasurable
  have hinv : ∀ (g : (globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F),
      (‖φ (g • x)‖₊ : ℝ≥0∞) ^ 2 = (‖φ x‖₊ : ℝ≥0∞) ^ 2 := by
    rintro ⟨g, hg⟩ x
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hg
    show (‖φ (globalPoints (𝓞 F) F γ * x)‖₊ : ℝ≥0∞) ^ 2 = _
    rw [hLs.left_invariant]
  calc ∫⁻ x in centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H, (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = ∫⁻ x in (· * y) '' (centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H), (‖φ x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
        (setLIntegral_image_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
          ((measurableSet_centreCutSiegelSet c' u' d₁' d₂').inter (measurableSet_aboveLevel H)) y).symm
    _ = ∫⁻ x in (· * y) '' (centreCutSiegelSet F c' u' d₁' d₂' ∩ aboveLevel F H), (‖φ x‖₊ : ℝ≥0∞) ^ 2
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detSlab F (min α₁ α₂) (max β₁ β₂))) := by
        rw [Measure.restrict_restrict hV, Set.inter_eq_self_of_subset_left hVsub]
    _ ≤ (N : ℝ≥0∞) * ∫⁻ x in ⋃ z ∈ Z, (· * centralScalar (𝓞 F) F z) ''
          ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩ aboveLevel F (H / l)), (‖φ x‖₊ : ℝ≥0∞) ^ 2
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detSlab F (min α₁ α₂) (max β₁ β₂))) :=
        setLIntegral_le_mul_setLIntegral_of_orbitCount_le hS hfm hinv hV hW (ENNReal.natCast_ne_top N) (hcount H y hy)
    _ = (N : ℝ≥0∞) * ∫⁻ x in ⋃ z ∈ Z, (· * centralScalar (𝓞 F) F z) ''
          ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩ aboveLevel F (H / l)), (‖φ x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [Measure.restrict_restrict hW, Set.inter_eq_self_of_subset_left hWsub]
    _ ≤ (N : ℝ≥0∞) * ∑ z ∈ Z, ∫⁻ x in (· * centralScalar (𝓞 F) F z) ''
          ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩ aboveLevel F (H / l)), (‖φ x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
        mul_le_mul_right (setLIntegral_biUnion_finset_le_of_index (adelicGLHaar (Fin 2) (𝓞 F) F) _ _ Z) _
    _ = (N : ℝ≥0∞) * ∑ z ∈ Z, ∫⁻ x in (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩
          aboveLevel F (H / l), (‖φ (x * centralScalar (𝓞 F) F z)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        congr 1
        exact Finset.sum_congr rfl fun z _ =>
          setLIntegral_image_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2) hRel _
    _ = (N : ℝ≥0∞) * ∑ z ∈ Z, ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ ^ 2 : NNReal) : ℝ≥0∞) *
          ∫⁻ x in (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩ aboveLevel F (H / l),
            (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        congr 1
        exact Finset.sum_congr rfl fun z _ => setLIntegral_nnnorm_mul_centralScalar_sq hLs z _
    _ = (N : ℝ≥0∞) * ((∑ z ∈ Z, ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ ^ 2 : NNReal) : ℝ≥0∞) *
          ∫⁻ x in (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂) ∩ aboveLevel F (H / l),
            (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        push_cast
        rw [mul_assoc, Finset.sum_mul]

private theorem mass_relax_le_mul_of_coveringParameter
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (lam : ℝ) (hlam : 1 ≤ lam) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsLsXiFunction (𝓞 F) F ⊤ χ φ → Continuous φ →
        ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂), (‖φ x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
          ≤ ENNReal.ofReal N *
            ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ x‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := countable_globalPoints_range (F := F)
  haveI := measurableConstSMul_globalPoints_range (F := F)
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hd₁' : 0 < d₁ / lam := div_pos hd₁ hlam0
  have hd' : d₁ / lam < lam * d₂ :=
    calc d₁ / lam ≤ d₁ := div_le_self hd₁.le hlam
      _ < d₂ := hd
      _ ≤ lam * d₂ := le_mul_of_one_le_left (hd₁.trans hd).le hlam
  obtain ⟨a, b, ha, -, hVslab, -⟩ := exists_window_and_translates_subset_slab (K := F) (c / lam) (lam * u)
    (d₁ / lam) (lam * d₂) T hd' hd₁' (R := {1}) isCompact_singleton
  obtain ⟨Z, M, hM, hcount⟩ :=
    exists_finset_forall_orbitCount_relaxedWindow_le c u d₁ d₂ T hc hd₁ hd hu hcov lam hlam (b := b) ha
  obtain ⟨S, -, hS⟩ := exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F a b
  haveI := smulInvariantMeasure_restrict_slab (F := F) a b
  refine ⟨M * ∑ z ∈ Z, ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ) ^ 2), fun φ hφ hφc => ?_⟩
  have hVm := measurableSet_translates (F := F) (c / lam) (lam * u) (d₁ / lam) (lam * d₂) T
  have hWm := measurableSet_translates (F := F) c u d₁ d₂ T
  have hWzm : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      MeasurableSet ((· * centralScalar (𝓞 F) F z) '' ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
    intro z
    rw [Set.image_mul_right]
    exact hWm.preimage (continuous_id.mul continuous_const).measurable
  have hf : AEMeasurable (fun y : AdelicGL2 (𝓞 F) F => (‖φ y‖₊ : ℝ≥0∞) ^ 2)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | TateGlobal.ideleNorm F (GeneralLinearGroup.det g) ∈ Set.Icc a b}) :=
    (hφc.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
  have hinv : ∀ (γ : (globalPoints (𝓞 F) F).range) (y : AdelicGL2 (𝓞 F) F),
      (‖φ (γ • y)‖₊ : ℝ≥0∞) ^ 2 = (‖φ y‖₊ : ℝ≥0∞) ^ 2 := by
    rintro ⟨_, γ₀, rfl⟩ y
    show (‖φ (globalPoints (𝓞 F) F γ₀ * y)‖₊ : ℝ≥0∞) ^ 2 = _
    rw [hφ.left_invariant γ₀ y]
  have hcount' : ∀ y : AdelicGL2 (𝓞 F) F,
      orbitCount (globalPoints (𝓞 F) F).range
          (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂)) y
        ≤ ENNReal.ofReal M * ∑ z ∈ Z, orbitCount (globalPoints (𝓞 F) F).range
            ((· * centralScalar (𝓞 F) F z) '' ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) y := by
    intro y
    by_cases hy : TateGlobal.ideleNorm F (GeneralLinearGroup.det y) ∈ Set.Icc a b
    · exact hcount y hy
    · rw [orbitCount_eq_zero_of_subset_slab hVslab hy]
      exact zero_le
  calc ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂),
          (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / lam) (lam * u) (d₁ / lam) (lam * d₂),
          (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
            {g | TateGlobal.ideleNorm F (GeneralLinearGroup.det g) ∈ Set.Icc a b}) := by
          rw [Measure.restrict_restrict hVm, Set.inter_eq_self_of_subset_left hVslab]
    _ ≤ ENNReal.ofReal M * ∑ z ∈ Z, ∫⁻ y in
          (· * centralScalar (𝓞 F) F z) '' ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
          (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
            {g | TateGlobal.ideleNorm F (GeneralLinearGroup.det g) ∈ Set.Icc a b}) :=
          setLIntegral_le_mul_sum_setLIntegral_of_orbitCount_le hS hf hinv hVm Z hWzm ENNReal.ofReal_ne_top hcount'
    _ ≤ ENNReal.ofReal M * ∑ z ∈ Z, ∫⁻ y in
          (· * centralScalar (𝓞 F) F z) '' ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
          (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          gcongr with z hz
          exact Measure.restrict_le_self
    _ = ENNReal.ofReal M * ∑ z ∈ Z, ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 *
          ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
            (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          congr 1
          exact Finset.sum_congr rfl fun z _ => setLIntegral_image_mul_centralScalar hφ hWm z
    _ = ENNReal.ofReal (M * ∑ z ∈ Z, ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ) ^ 2)) *
          ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
            (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          rw [← Finset.sum_mul, ENNReal.ofReal_mul hM, mul_assoc,
            ENNReal.ofReal_sum_of_nonneg fun z _ => by positivity]
          congr 2
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

private theorem translates_le_mul_of_coveringParameter
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {R : Set (AdelicGL2 (𝓞 F) F)} (hR : IsCompact R) :
    ∃ N : ℝ, ∀ y ∈ R, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsLsXiFunction (𝓞 F) F ⊤ χ φ → Continuous φ →
        ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
          ≤ ENNReal.ofReal N *
            ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ x‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar F
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hR' : IsCompact (⋃ t ∈ T, (t * ·) '' R) := T.isCompact_biUnion fun t _ => hR.image (continuous_const_mul t)
  obtain ⟨N₁, hN₁, l, hl, hcore⟩ :=
    setLIntegral_translate_le_mul_of_lt_localHeight_of_coveringParameter F c u d₁ d₂ T hc hd₁ hd hu hcov χ
      c u d₁ d₂ hc hd₁ hR'
  obtain ⟨N₂, hrel⟩ := mass_relax_le_mul_of_coveringParameter F c u d₁ d₂ T hc hd₁ hd hu hcov χ (max 1 (c / (c / l)))
    (le_max_left _ _)
  have hincl : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂)
      ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / max 1 (c / (c / l))) (max 1 (c / (c / l)) * u)
        (d₁ / max 1 (c / (c / l))) (max 1 (c / (c / l)) * d₂) :=
    Set.iUnion₂_mono fun x _ => Set.image_mono
      (centreCutSiegelSet_subset_centreCutSiegelSet_relaxed_of_pos hc hd₁ hd (div_pos hc (zero_lt_one.trans_le hl)))
  refine ⟨((T.card : ℝ≥0∞) * N₁ * ENNReal.ofReal N₂).toReal, fun y hy φ hLs hφ => ?_⟩
  rw [ENNReal.ofReal_toReal
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hN₁) ENNReal.ofReal_ne_top)]
  have hpiece : ∀ t ∈ T,
      ∫⁻ x in (· * t) '' centreCutSiegelSet F c u d₁ d₂, (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ N₁ * ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂, (‖φ x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro t ht
    rw [setLIntegral_image_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ (g * y)‖₊ : ℝ≥0∞) ^ 2)
      (measurableSet_centreCutSiegelSet c u d₁ d₂) t]
    simp only [mul_assoc]
    have hmem : t * y ∈ ⋃ t ∈ T, (t * ·) '' R := Set.mem_iUnion₂.2 ⟨t, ht, y, hy, rfl⟩
    refine (lintegral_mono_set ?_).trans ((hcore 0 (t * y) hmem φ hφ hLs).trans ?_)
    · intro g hg
      exact ⟨hg, w₀, localHeight_pos _⟩
    · exact mul_le_mul_right (lintegral_mono_set Set.inter_subset_left) _
  refine (setLIntegral_biUnion_finset_le (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ (g * y)‖₊ : ℝ≥0∞) ^ 2)
    (fun t => (· * t) '' centreCutSiegelSet F c u d₁ d₂) T).trans ?_
  refine (Finset.sum_le_sum hpiece).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine (mul_le_mul_right (mul_le_mul_right ((lintegral_mono_set hincl).trans (hrel φ hLs hφ)) N₁)
    (T.card : ℝ≥0∞)).trans (le_of_eq ?_)
  ring

private theorem window_le_mul_window_of_coveringParameter
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)) (hc' : 0 < c') (hd₁' : 0 < d₁') (hd' : d₁' < d₂')
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ χ φ →
      @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂'))
          (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2) ≤
        N * @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
          (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar F
  have _ := hd'
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨N₁, hN₁, l, hl, hcore⟩ :=
    setLIntegral_translate_le_mul_of_lt_localHeight_of_coveringParameter F c u d₁ d₂ T hc hd₁ hd hu hcov χ
      c' u' d₁' d₂' hc' hd₁' T'.finite_toSet.isCompact
  obtain ⟨N₂, hrel⟩ := mass_relax_le_mul_of_coveringParameter F c u d₁ d₂ T hc hd₁ hd hu hcov χ (max 1 (c / (c' / l)))
    (le_max_left _ _)
  have hincl : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂)
      ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / max 1 (c / (c' / l))) (max 1 (c / (c' / l)) * u)
        (d₁ / max 1 (c / (c' / l))) (max 1 (c / (c' / l)) * d₂) :=
    Set.iUnion₂_mono fun x _ => Set.image_mono
      (centreCutSiegelSet_subset_centreCutSiegelSet_relaxed_of_pos hc hd₁ hd (div_pos hc' (zero_lt_one.trans_le hl)))
  refine ⟨(T'.card : ℝ≥0∞) * N₁ * ENNReal.ofReal N₂,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hN₁) ENNReal.ofReal_ne_top, fun φ hφ hLs => ?_⟩
  have hpiece : ∀ t ∈ T',
      ∫⁻ x in (· * t) '' centreCutSiegelSet F c' u' d₁' d₂', (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ N₁ * ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c' / l) u d₁ d₂, (‖φ x‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro t ht
    rw [setLIntegral_image_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
      (measurableSet_centreCutSiegelSet c' u' d₁' d₂') t]
    refine (lintegral_mono_set ?_).trans ((hcore 0 t (Finset.mem_coe.2 ht) φ hφ hLs).trans ?_)
    · intro g hg
      exact ⟨hg, w₀, localHeight_pos _⟩
    · exact mul_le_mul_right (lintegral_mono_set Set.inter_subset_left) _
  refine (setLIntegral_biUnion_finset_le (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
    (fun t => (· * t) '' centreCutSiegelSet F c' u' d₁' d₂') T').trans ?_
  refine (Finset.sum_le_sum hpiece).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine (mul_le_mul_right (mul_le_mul_right ((lintegral_mono_set hincl).trans (hrel φ hLs hφ)) N₁)
    (T'.card : ℝ≥0∞)).trans (le_of_eq ?_)
  ring

private theorem exists_tail_le_of_coveringParameter
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hu : ∀ x : (w : InfinitePlace F) → w.Completion, ∃ ξ : 𝓞 F, ∀ w : InfinitePlace F,
      ‖x w - algebraMap F w.Completion (ξ : F)‖ ≤ u)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hχ : IsLsXiFunction (𝓞 F) F ⊤ χ φ)
    (hmass : ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ x‖₊ : ℝ≥0∞) ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤) :
    ∀ η : ℝ≥0∞, 0 < η → ∃ D₀ : Set (AdelicGL2 (𝓞 F) F),
      D₀ ⊆ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∧ IsCompact (closure D₀) ∧
        adelicGLHaar (Fin 2) (𝓞 F) F D₀ < ⊤ ∧
        ∀ᶠ y in 𝓝 (1 : AdelicGL2 (𝓞 F) F),
          ∫⁻ x in (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) \ D₀, (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤ η := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  intro η hη
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
  have hK' : IsCompact (⋃ t ∈ T, (t * ·) '' K) := T.isCompact_biUnion fun t _ => hK.image (continuous_const_mul t)
  obtain ⟨N₁, hN₁, l, hl, hcore⟩ :=
    setLIntegral_translate_le_mul_of_lt_localHeight_of_coveringParameter F c u d₁ d₂ T hc hd₁ hd hu hcov χ
      c u d₁ d₂ hc hd₁ hK'
  have hl0 : l ≠ 0 := (zero_lt_one.trans_le hl).ne'
  obtain ⟨N₂, hrel⟩ := mass_relax_le_mul_of_coveringParameter F c u d₁ d₂ T hc hd₁ hd hu hcov χ (max 1 (c / (c / l)))
    (le_max_left _ _)
  have hincl : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂)
      ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / max 1 (c / (c / l))) (max 1 (c / (c / l)) * u)
        (d₁ / max 1 (c / (c / l))) (max 1 (c / (c / l)) * d₂) :=
    Set.iUnion₂_mono fun x _ => Set.image_mono
      (centreCutSiegelSet_subset_centreCutSiegelSet_relaxed_of_pos hc hd₁ hd (div_pos hc (zero_lt_one.trans_le hl)))
  have hmeas : ∀ m : ℕ,
      MeasurableSet ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂) ∩ aboveLevel F (m : ℝ)) :=
    fun m => measurableSet_iUnion_inter_aboveLevel (c / l) u d₁ d₂ (m : ℝ) T
  have hanti : Antitone fun m : ℕ =>
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂) ∩ aboveLevel F (m : ℝ) := by
    intro m m' hmm' g hg
    obtain ⟨w, hw⟩ := hg.2
    exact ⟨hg.1, w, lt_of_le_of_lt (by exact_mod_cast hmm') hw⟩
  have hfin : (adelicGLHaar (Fin 2) (𝓞 F) F).withDensity (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
      ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂) ∩ aboveLevel F ((0 : ℕ) : ℝ)) ≠ ⊤ := by
    rw [withDensity_apply _ (hmeas 0)]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmass.ne)
      ((lintegral_mono_set Set.inter_subset_left).trans ((lintegral_mono_set hincl).trans (hrel φ hχ hφ)))
  have hempty :
      (⋂ m : ℕ, (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂) ∩ aboveLevel F (m : ℝ)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    rw [Set.mem_iInter] at hg
    obtain ⟨B, hB⟩ :=
      (Set.finite_range fun w : InfinitePlace F => localHeight (archComponent F w (glArch (𝓞 F) F g))).bddAbove
    obtain ⟨m, hm⟩ := exists_nat_ge B
    obtain ⟨w, hw⟩ := (hg m).2
    exact not_lt.mpr (hB (Set.mem_range_self w)) (hm.trans_lt hw)
  have hT : Filter.Tendsto
      (fun m : ℕ => (T.card : ℝ≥0∞) * N₁ * (adelicGLHaar (Fin 2) (𝓞 F) F).withDensity (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
        ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂) ∩ aboveLevel F (m : ℝ)))
      Filter.atTop (nhds ((T.card : ℝ≥0∞) * N₁ * 0)) := by
    have h := tendsto_measure_iInter_atTop
      (μ := (adelicGLHaar (Fin 2) (𝓞 F) F).withDensity fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
      (fun m => (hmeas m).nullMeasurableSet) hanti ⟨0, hfin⟩
    simp only [hempty, measure_empty] at h
    exact ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hN₁))
  rw [mul_zero] at hT
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds hη)).exists
  refine ⟨⋃ t ∈ T, (· * t) '' (centreCutSiegelSet F c u d₁ d₂ ∩
    {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ l * m}), ?_, ?_, ?_, ?_⟩
  · exact Set.iUnion₂_mono fun t _ => Set.image_mono Set.inter_subset_left
  · exact (T.isCompact_biUnion fun t _ =>
      (isCompact_centreCutSiegelSet_inter_heightCap F hc hd₁).image (continuous_mul_const t)).closure_of_subset
      subset_rfl
  · exact (T.isCompact_biUnion fun t _ =>
      (isCompact_centreCutSiegelSet_inter_heightCap F hc hd₁).image (continuous_mul_const t)).measure_lt_top
  · refine Filter.eventually_of_mem hK1 fun y hy => ?_
    have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) \
        (⋃ t ∈ T, (· * t) '' (centreCutSiegelSet F c u d₁ d₂ ∩
          {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ l * m}))
        ⊆ ⋃ t ∈ T, (· * t) '' (centreCutSiegelSet F c u d₁ d₂ ∩ aboveLevel F (l * m)) := by
      rintro g ⟨hgW, hgD⟩
      obtain ⟨t, ht, s, hs, rfl⟩ := Set.mem_iUnion₂.1 hgW
      refine Set.mem_iUnion₂.2 ⟨t, ht, s, ⟨hs, ?_⟩, rfl⟩
      by_contra hcon
      simp only [aboveLevel, Set.mem_setOf_eq, not_exists, not_lt] at hcon
      exact hgD (Set.mem_iUnion₂.2 ⟨t, ht, s, ⟨hs, hcon⟩, rfl⟩)
    have hpiece : ∀ t ∈ T,
        ∫⁻ x in (· * t) '' (centreCutSiegelSet F c u d₁ d₂ ∩ aboveLevel F (l * m)), (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
          ≤ N₁ * (adelicGLHaar (Fin 2) (𝓞 F) F).withDensity (fun g => (‖φ g‖₊ : ℝ≥0∞) ^ 2)
            ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F (c / l) u d₁ d₂) ∩ aboveLevel F (m : ℝ)) := by
      intro t ht
      rw [setLIntegral_image_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ (g * y)‖₊ : ℝ≥0∞) ^ 2)
        ((measurableSet_centreCutSiegelSet c u d₁ d₂).inter (measurableSet_aboveLevel (l * m))) t,
        withDensity_apply _ (hmeas m)]
      simp only [mul_assoc]
      have hmem : t * y ∈ ⋃ t ∈ T, (t * ·) '' K := Set.mem_iUnion₂.2 ⟨t, ht, y, hy, rfl⟩
      refine (hcore (l * m) (t * y) hmem φ hφ hχ).trans (mul_le_mul_right (lintegral_mono_set ?_) _)
      intro g hg
      obtain ⟨w, hw⟩ := hg.2
      rw [mul_div_cancel_left₀ _ hl0] at hw
      exact ⟨hg.1, w, hw⟩
    refine (lintegral_mono_set hsub).trans ?_
    refine (setLIntegral_biUnion_finset_le (adelicGLHaar (Fin 2) (𝓞 F) F) (fun g => (‖φ (g * y)‖₊ : ℝ≥0∞) ^ 2)
      (fun t => (· * t) '' (centreCutSiegelSet F c u d₁ d₂ ∩ aboveLevel F (l * m))) T).trans ?_
    refine (Finset.sum_le_sum hpiece).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    exact hm.le

end Interface

end WindowMultiplicity

end MULTbodies

section PASSAGEweak

open MeasureTheory
open scoped ENNReal

namespace WeakTranslateClosure

variable {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}

private theorem toLp_sum_translates {f : G → ℂ} (hT : ∀ h : G, MemLp (fun z => f (z * h)) 2 μ)
    (s : Finset G) (l : G → ℂ) :
    ∃ hg : MemLp (fun y => ∑ h ∈ s, l h * f (y * h)) 2 μ,
      hg.toLp = ∑ h ∈ s, l h • (hT h).toLp := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    rw [Finset.sum_empty, ← MemLp.toLp_zero (μ := μ) (p := 2) (E := ℂ)]
    · exact (MemLp.toLp_eq_toLp_iff _ _).2 (Filter.Eventually.of_forall fun y => by simp)
    · exact MemLp.zero
  | insert a s ha ih =>
    obtain ⟨hg, hgl⟩ := ih
    have hterm : MemLp (fun y => l a * f (y * a)) 2 μ := (hT a).const_mul (l a)
    have hfun : (fun y => ∑ h ∈ insert a s, l h * f (y * h)) =
        fun y => l a * f (y * a) + ∑ h ∈ s, l h * f (y * h) := by
      funext y
      rw [Finset.sum_insert ha]
    refine ⟨hfun ▸ hterm.add hg, ?_⟩
    have hcongr : (hfun ▸ hterm.add hg : MemLp (fun y => ∑ h ∈ insert a s, l h * f (y * h)) 2 μ).toLp =
        (hterm.add hg).toLp :=
      (MemLp.toLp_eq_toLp_iff _ _).2
        (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply, Finset.sum_insert ha])
    have hsmul : hterm.toLp = l a • (hT a).toLp := by
      rw [← MemLp.toLp_const_smul]
      exact (MemLp.toLp_eq_toLp_iff _ _).2 (Filter.Eventually.of_forall fun y => rfl)
    rw [hcongr, MemLp.toLp_add hterm hg, Finset.sum_insert ha, hsmul, hgl]

private theorem exists_finset_lintegral_sub_sum_sq_lt_of_forall_inner_eq_zero {f : G → ℂ}
    (hT : ∀ h : G, MemLp (fun z => f (z * h)) 2 μ) {v : G → ℂ} (hv : MemLp v 2 μ)
    (horth : ∀ ψ : Lp ℂ 2 μ, (∀ h : G, (inner ℂ ψ ((hT h).toLp) : ℂ) = 0) → (inner ℂ ψ (hv.toLp) : ℂ) = 0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (s : Finset G) (l : G → ℂ), ∫⁻ y, (‖v y - ∑ h ∈ s, l h * f (y * h)‖₊ : ℝ≥0∞) ^ 2 ∂μ < ε := by
  classical
  set W : Submodule ℂ (Lp ℂ 2 μ) :=
    (Submodule.span ℂ (Set.range fun h : G => (hT h).toLp)).topologicalClosure with hW

  have hvW : hv.toLp ∈ W := by
    haveI : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    rw [← Submodule.orthogonal_orthogonal W, Submodule.mem_orthogonal]
    intro ψ hψ
    refine horth ψ fun h => ?_
    have hmem : (hT h).toLp ∈ W :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨h, rfl⟩)
    exact Submodule.inner_left_of_mem_orthogonal hmem hψ

  obtain ⟨r, hr0, hrε⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < ε := by
    rcases eq_or_ne ε ⊤ with hεtop | hεtop
    · exact ⟨1, one_pos, by simp [hεtop]⟩
    · refine ⟨ε.toReal / 2, half_pos (ENNReal.toReal_pos hε.ne' hεtop), ?_⟩
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hεtop]
      exact half_lt_self (ENNReal.toReal_pos hε.ne' hεtop)

  have hvcl : hv.toLp ∈ closure ((Submodule.span ℂ (Set.range fun h : G => (hT h).toLp) : Submodule ℂ _) :
      Set (Lp ℂ 2 μ)) := by
    first | exact hvW | simpa [hW, Submodule.topologicalClosure_coe] using hvW | simpa +zetaDelta [hW, Submodule.topologicalClosure_coe] using hvW
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.1 hvcl (Real.sqrt r) (Real.sqrt_pos.2 hr0)
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hw
  obtain ⟨hg, hgl⟩ := toLp_sum_translates hT c.support (fun h => c h)
  refine ⟨c.support, fun h => c h, ?_⟩

  have hsum : c.sum (fun h a => a • (hT h).toLp) = hg.toLp := by
    rw [hgl, Finsupp.sum]
  rw [hsum, dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp] at hdist
  have hfin : eLpNorm (v - fun y => ∑ h ∈ c.support, c h * f (y * h)) 2 μ ≠ ⊤ := (hv.sub hg).eLpNorm_ne_top
  have hlt : eLpNorm (v - fun y => ∑ h ∈ c.support, c h * f (y * h)) 2 μ < ENNReal.ofReal (Real.sqrt r) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 hdist

  have hsq := (ENNReal.pow_lt_pow_left_iff two_ne_zero).2 hlt
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr0.le] at hsq
  refine lt_of_le_of_lt (le_of_eq ?_) (hsq.trans hrε)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, one_div,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat, inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one]
  refine lintegral_congr fun y => ?_
  simp only [Pi.sub_apply, enorm_eq_nnnorm, ENNReal.rpow_two]

end WeakTranslateClosure

open NumberField MeasureTheory
open NumberField.AdelicHaar
open scoped ENNReal
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm"
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace WeakPassage

section Pairing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem integrable_mul_conj_mul {x y : α → ℂ} {wt : α → ℝ} (hx : MemLp x 2 μ)
    (hy : MemLp y 2 μ) (hwt : AEStronglyMeasurable wt μ) {C : ℝ} (hC : ∀ᵐ a ∂μ, ‖wt a‖ ≤ C) :
    Integrable (fun a => x a * (starRingEnd ℂ) (y a) * ((wt a : ℝ) : ℂ)) μ := by
  have hxa := hx.aestronglyMeasurable
  have hya := hy.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun a => x a * (starRingEnd ℂ) (y a) * ((wt a : ℝ) : ℂ)) μ :=
    (hxa.mul (Complex.continuous_conj.comp_aestronglyMeasurable hya)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hwt)
  have hx2 : Integrable (fun a => ‖x a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hxa).mp hx
  have hy2 : Integrable (fun a => ‖y a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hya).mp hy
  refine Integrable.mono' ((hx2.add hy2).const_mul (max C 0)) hmeas ?_
  filter_upwards [hC] with a ha
  simp only [Pi.add_apply]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real]
  have h2 : ‖x a‖ * ‖y a‖ ≤ ‖x a‖ ^ 2 + ‖y a‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x a‖ - ‖y a‖), norm_nonneg (x a), norm_nonneg (y a)]
  calc ‖x a‖ * ‖y a‖ * ‖wt a‖ ≤ (‖x a‖ ^ 2 + ‖y a‖ ^ 2) * max C 0 :=
        mul_le_mul h2 (ha.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = max C 0 * (‖x a‖ ^ 2 + ‖y a‖ ^ 2) := mul_comm _ _

private theorem integrable_norm_sq_mul {f : α → ℂ} {wt : α → ℝ} (hf : MemLp f 2 μ)
    (hwt : AEStronglyMeasurable wt μ) {C : ℝ} (hC : ∀ᵐ a ∂μ, ‖wt a‖ ≤ C) :
    Integrable (fun a => ‖f a‖ ^ 2 * wt a) μ := by
  have hf2 : Integrable (fun a => ‖f a‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  refine Integrable.mono' (hf2.const_mul (max C 0)) (hf2.aestronglyMeasurable.mul hwt) ?_
  filter_upwards [hC] with a ha
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖f a‖ ^ 2 * ‖wt a‖ ≤ ‖f a‖ ^ 2 * max C 0 :=
        mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (sq_nonneg _)
    _ = max C 0 * ‖f a‖ ^ 2 := mul_comm _ _

end Pairing

variable (K : Type) [Field K] [NumberField K]

private abbrev haarGL : Measure (AdelicGL2 (𝓞 K) K) :=
  adelicGLHaar (Fin 2) (𝓞 K) K

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology in
private theorem secondCountable_adelicGL2 : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact (Units.isInducing_embedProduct (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).secondCountableTopology

private theorem peterssonIntegral_rightConv_eq_integral [SigmaFinite (adelicGLHaar (Fin 2) (𝓞 K) K)] (s : ℝ)
    (S : Set (AdelicGL2 (𝓞 K) K))
    (ξ R F : AdelicGL2 (𝓞 K) K → ℂ) (g₀ : AdelicGL2 (𝓞 K) K)
    (hint : Integrable (Function.uncurry fun (g y : AdelicGL2 (𝓞 K) K) =>
        ξ g * (starRingEnd ℂ) (R (g * g₀ * y) * F y) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 K) K))) :
    peterssonIntegral K s S ξ (fun z => rightConv K R F (z * g₀)) =
      ∫ y, (starRingEnd ℂ) (F y) * peterssonIntegral K s S ξ (fun z => R (z * g₀ * y))
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  unfold peterssonIntegral
  simp only [rightConv_apply]
  have hinner : ∀ g : AdelicGL2 (𝓞 K) K,
      ξ g * (starRingEnd ℂ) (∫ y, R (g * g₀ * y) * F y ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ) =
        ∫ y, ξ g * (starRingEnd ℂ) (R (g * g₀ * y) * F y) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro g
    rw [← integral_conj, ← integral_const_mul, ← integral_mul_const]
  simp_rw [hinner]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [map_mul]
  ring

private theorem integrable_pairing_rightConv_integrand_window [SigmaFinite (haarGL K)]
    {D : Set (AdelicGL2 (𝓞 K) K)} (s : ℝ) {ξ R F : AdelicGL2 (𝓞 K) K → ℂ}
    (hξ : MemLp ξ 2 ((haarGL K).restrict D)) (hRc : Continuous R) (g₀ : AdelicGL2 (𝓞 K) K)
    (hRy : ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => R (z * g₀ * y)) 2 ((haarGL K).restrict D))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCle : ∀ y ∈ tsupport F, ∫ z in D, ‖R (z * g₀ * y)‖ ^ 2 ∂(haarGL K) ≤ C)
    (hwt_meas : AEStronglyMeasurable
      (fun z : AdelicGL2 (𝓞 K) K => NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s))
      ((haarGL K).restrict D))
    {Wb : ℝ} (hWb0 : 0 ≤ Wb)
    (hwt_bound : ∀ᵐ z ∂(haarGL K).restrict D,
      ‖NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s)‖ ≤ Wb)
    (hFc : Continuous F) (hFs : HasCompactSupport F) :
    Integrable (Function.uncurry fun (g y : AdelicGL2 (𝓞 K) K) =>
        ξ g * (starRingEnd ℂ) (R (g * g₀ * y) * F y) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  haveI := secondCountable_adelicGL2 K

  have hmeas : AEStronglyMeasurable (Function.uncurry fun (g y : AdelicGL2 (𝓞 K) K) =>
      ξ g * (starRingEnd ℂ) (R (g * g₀ * y) * F y) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    have h1 : AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => ξ p.1)
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) :=
      hξ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : Continuous (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        (starRingEnd ℂ) (R (p.1 * g₀ * p.2) * F p.2)) :=
      Complex.continuous_conj.comp
        ((hRc.comp ((continuous_fst.mul continuous_const).mul continuous_snd)).mul (hFc.comp continuous_snd))
    have h3 : AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det p.1) ^ (-s) : ℝ) : ℂ))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hwt_meas.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
    exact (h1.mul h2.aestronglyMeasurable).mul h3
  refine (integrable_prod_iff' hmeas).2 ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  ·
    have h := (integrable_mul_conj_mul hξ (hRy y) hwt_meas hwt_bound).mul_const ((starRingEnd ℂ) (F y))
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry_apply_pair, map_mul]
    ring
  ·
    have hnorm : ∀ z y : AdelicGL2 (𝓞 K) K,
        ‖ξ z * (starRingEnd ℂ) (R (z * g₀ * y) * F y) *
            ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s) : ℝ) : ℂ)‖ =
          ‖F y‖ * (‖ξ z‖ *
            (‖R (z * g₀ * y)‖ * ‖NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s)‖)) := by
      intro z y
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real]
      ring
    set A : ℝ := (∫ z in D, ‖ξ z‖ ^ (2 : ℝ) ∂(haarGL K)) ^ (1 / 2 : ℝ) with hA
    have hA0 : 0 ≤ A := Real.rpow_nonneg (integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _) _
    set K₀ : ℝ := A * (Wb ^ 2 * C) ^ (1 / 2 : ℝ) with hK₀
    have hK₀0 : 0 ≤ K₀ := mul_nonneg hA0 (Real.rpow_nonneg (mul_nonneg (sq_nonneg _) hC0) _)
    have hslice : ∀ y : AdelicGL2 (𝓞 K) K,
        ∫ z in D, ‖ξ z * (starRingEnd ℂ) (R (z * g₀ * y) * F y) *
            ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s) : ℝ) : ℂ)‖ ∂(haarGL K)
          ≤ ‖F y‖ * K₀ := by
      intro y
      simp only [hnorm]
      rw [integral_const_mul]
      by_cases hy : y ∈ tsupport F
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)

        have hG : MemLp (fun z => ‖R (z * g₀ * y)‖ *
            ‖NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s)‖) 2
            ((haarGL K).restrict D) := by
          refine ((hRy y).norm.const_mul Wb).of_le
            ((hRy y).aestronglyMeasurable.norm.mul hwt_meas.norm) (hwt_bound.mono fun z hz => ?_)
          rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
            Real.norm_of_nonneg (mul_nonneg hWb0 (norm_nonneg _)), mul_comm Wb]
          exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (haarGL K).restrict D) Real.HolderConjugate.two_two
          (Filter.Eventually.of_forall fun z => norm_nonneg (ξ z))
          (Filter.Eventually.of_forall fun z =>
            mul_nonneg (norm_nonneg (R (z * g₀ * y)))
              (norm_nonneg (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s))))
          (by simpa using hξ.norm) (by simpa using hG)
        refine hH.trans (mul_le_mul_of_nonneg_left ?_ hA0)
        refine Real.rpow_le_rpow (integral_nonneg fun z => Real.rpow_nonneg (mul_nonneg (norm_nonneg _)
          (norm_nonneg _)) _) ?_ (by norm_num)

        have hint : Integrable (fun z => ‖R (z * g₀ * y)‖ ^ 2 * Wb ^ 2) ((haarGL K).restrict D) :=
          integrable_norm_sq_mul (hRy y) aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ => le_rfl)
        calc ∫ z in D, (‖R (z * g₀ * y)‖ *
                ‖NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-s)‖) ^ (2 : ℝ) ∂(haarGL K)
            ≤ ∫ z in D, ‖R (z * g₀ * y)‖ ^ 2 * Wb ^ 2 ∂(haarGL K) := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => Real.rpow_nonneg
                (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _) hint (hwt_bound.mono fun z hz => ?_)
              simp only [Real.rpow_two, mul_pow]
              gcongr
          _ = Wb ^ 2 * ∫ z in D, ‖R (z * g₀ * y)‖ ^ 2 ∂(haarGL K) := by
              rw [integral_mul_const]
              ring
          _ ≤ Wb ^ 2 * C := mul_le_mul_of_nonneg_left (hCle y hy) (sq_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero, zero_mul, zero_mul]
    refine (((hFc.integrable_of_hasCompactSupport hFs).norm.mul_const K₀).mono' ?_
      (Filter.Eventually.of_forall fun y => ?_))
    · exact (hmeas.norm.prod_swap).integral_prod_right'
    · simp only [Function.uncurry_apply_pair]
      rw [Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
      exact hslice y

private theorem peterssonIntegral_rightConv_eq_zero_of_forall_translate [SigmaFinite (haarGL K)]
    {D : Set (AdelicGL2 (𝓞 K) K)} {ψ u F : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : MemLp ψ 2 ((haarGL K).restrict D)) (huc : Continuous u)
    (huy : ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => u (z * y)) 2 ((haarGL K).restrict D))
    {C : ℝ} (hC0 : 0 ≤ C) (hCle : ∀ y ∈ tsupport F, ∫ z in D, ‖u (z * y)‖ ^ 2 ∂(haarGL K) ≤ C)
    (hFc : Continuous F) (hFs : HasCompactSupport F)
    (horth : ∀ y : AdelicGL2 (𝓞 K) K, peterssonIntegral K 0 D ψ (fun z => u (z * y)) = 0) :
    peterssonIntegral K 0 D ψ (rightConv K u F) = 0 := by
  have hwt_meas : AEStronglyMeasurable
      (fun z : AdelicGL2 (𝓞 K) K =>
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-(0 : ℝ)))
      ((haarGL K).restrict D) := by
    simp only [neg_zero, Real.rpow_zero]
    exact aestronglyMeasurable_const
  have hwt_bound : ∀ᵐ z ∂(haarGL K).restrict D,
      ‖NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-(0 : ℝ))‖ ≤ 1 :=
    Filter.Eventually.of_forall fun z => by simp
  have hint := integrable_pairing_rightConv_integrand_window K 0 hψ huc 1
    (fun y => by simpa only [mul_one] using huy y) hC0 (fun y hy => by simpa only [mul_one] using hCle y hy)
    hwt_meas zero_le_one hwt_bound hFc hFs
  have h := peterssonIntegral_rightConv_eq_integral K 0 D ψ u F 1 hint
  simp only [mul_one] at h
  rw [h]
  simp only [horth, mul_zero, integral_zero]

section Bridge

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem inner_toLp_eq_integral {x y : α → ℂ} (hx : MemLp x 2 μ) (hy : MemLp y 2 μ) :
    (inner ℂ hx.toLp hy.toLp : ℂ) = ∫ a, (starRingEnd ℂ) (x a) * y a ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hx.coeFn_toLp, hy.coeFn_toLp] with a hxa hya
  rw [hxa, hya, RCLike.inner_apply']

private theorem norm_integral_conj_mul_le {x y : α → ℂ} (hx : MemLp x 2 μ) (hy : MemLp y 2 μ) :
    ‖∫ a, (starRingEnd ℂ) (x a) * y a ∂μ‖ ≤ (eLpNorm x 2 μ).toReal * (eLpNorm y 2 μ).toReal := by
  rw [← inner_toLp_eq_integral hx hy, ← Lp.norm_toLp x hx, ← Lp.norm_toLp y hy]
  exact norm_inner_le_norm _ _

private theorem toReal_eLpNorm_le_of_lintegral_le {f : α → ℂ} {η : ℝ} (hη : 0 ≤ η)
    (h : ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ ENNReal.ofReal (η ^ 2)) : (eLpNorm f 2 μ).toReal ≤ η := by
  have hsq : eLpNorm f 2 μ ^ 2 = ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, one_div,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat, inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one]
    refine lintegral_congr fun a => ?_
    simp only [enorm_eq_nnnorm, ENNReal.rpow_two]
  have hle : eLpNorm f 2 μ ≤ ENNReal.ofReal η := by
    by_contra hlt
    push Not at hlt
    have h2 := (ENNReal.pow_lt_pow_left_iff two_ne_zero).2 hlt
    rw [hsq, ← ENNReal.ofReal_pow hη] at h2
    exact lt_irrefl _ (h2.trans_le h)
  exact ENNReal.toReal_le_of_le_ofReal hη hle

private theorem integrable_mul_conj_one {x y : α → ℂ} (hx : MemLp x 2 μ) (hy : MemLp y 2 μ) :
    Integrable (fun a => x a * (starRingEnd ℂ) (y a)) μ := by
  have h := integrable_mul_conj_mul hx hy (wt := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (C := 1) (Filter.Eventually.of_forall fun _ => by simp)
  simpa only [Complex.ofReal_one, mul_one] using h

private theorem eq_zero_of_norm_le_mul {x : ℂ} {N : ℝ} (hN : 0 ≤ N) (h : ∀ θ : ℝ, 0 < θ → ‖x‖ ≤ N * θ) :
    x = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  have hN1 : 0 < N + 1 := by linarith
  refine (h (ε / (N + 1)) (div_pos hε hN1)).trans ?_
  rw [zero_add, mul_div_assoc', div_le_iff₀ hN1]
  nlinarith

end Bridge

private theorem peterssonIntegral_zero_eq (D : Set (AdelicGL2 (𝓞 K) K)) (x y : AdelicGL2 (𝓞 K) K → ℂ) :
    peterssonIntegral K 0 D x y = ∫ g in D, x g * (starRingEnd ℂ) (y g) ∂(haarGL K) := by
  unfold peterssonIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]

private theorem peterssonIntegral_zero_eq_conj_integral {D : Set (AdelicGL2 (𝓞 K) K)}
    (x y : AdelicGL2 (𝓞 K) K → ℂ) :
    peterssonIntegral K 0 D x y =
      (starRingEnd ℂ) (∫ g in D, (starRingEnd ℂ) (x g) * y g ∂(haarGL K)) := by
  rw [peterssonIntegral_zero_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [map_mul, Complex.conj_conj]

private theorem norm_peterssonIntegral_zero_le {D : Set (AdelicGL2 (𝓞 K) K)} {ψ v : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : MemLp ψ 2 ((haarGL K).restrict D)) (hv : MemLp v 2 ((haarGL K).restrict D)) :
    ‖peterssonIntegral K 0 D ψ v‖ ≤
      (eLpNorm ψ 2 ((haarGL K).restrict D)).toReal * (eLpNorm v 2 ((haarGL K).restrict D)).toReal := by
  rw [peterssonIntegral_zero_eq_conj_integral, Complex.norm_conj]
  exact norm_integral_conj_mul_le hψ hv

private theorem peterssonIntegral_zero_sub {D : Set (AdelicGL2 (𝓞 K) K)} {ψ a b : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : MemLp ψ 2 ((haarGL K).restrict D)) (ha : MemLp a 2 ((haarGL K).restrict D))
    (hb : MemLp b 2 ((haarGL K).restrict D)) :
    peterssonIntegral K 0 D ψ a - peterssonIntegral K 0 D ψ b = peterssonIntegral K 0 D ψ (a - b) := by
  simp only [peterssonIntegral_zero_eq]
  have hia := integrable_mul_conj_one hψ ha
  have hib := integrable_mul_conj_one hψ hb
  rw [← integral_sub hia hib]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Pi.sub_apply, map_sub]
  ring

private theorem peterssonIntegral_zero_sum {D : Set (AdelicGL2 (𝓞 K) K)} {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : MemLp ψ 2 ((haarGL K).restrict D)) {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (v : ι → AdelicGL2 (𝓞 K) K → ℂ) (hv : ∀ i ∈ t, MemLp (v i) 2 ((haarGL K).restrict D)) :
    peterssonIntegral K 0 D ψ (fun g => ∑ i ∈ t, c i * v i g) =
      ∑ i ∈ t, (starRingEnd ℂ) (c i) * peterssonIntegral K 0 D ψ (v i) := by
  simp only [peterssonIntegral_zero_eq]
  have hint : ∀ i ∈ t, Integrable (fun g => (starRingEnd ℂ) (c i) * (ψ g * (starRingEnd ℂ) (v i g)))
      ((haarGL K).restrict D) := fun i hi => (integrable_mul_conj_one hψ (hv i hi)).const_mul _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum t hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem peterssonIntegral_zero_eq_zero_of_weak [SigmaFinite (haarGL K)] {D : Set (AdelicGL2 (𝓞 K) K)}
    {ψ R R' : AdelicGL2 (𝓞 K) K → ℂ} (hψ : MemLp ψ 2 ((haarGL K).restrict D))
    (horth : ∀ y : AdelicGL2 (𝓞 K) K, peterssonIntegral K 0 D ψ (fun z => R (z * y)) = 0)
    (hR'c : Continuous R')
    (hR'y : ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => R' (z * y)) 2 ((haarGL K).restrict D))
    (hR'bdd : ∀ B : Set (AdelicGL2 (𝓞 K) K), IsCompact B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ B, ∫ z in D, ‖R' (z * y)‖ ^ 2 ∂(haarGL K) ≤ C)
    (hcont : Filter.Tendsto (fun y => ∫⁻ z in D, (‖R' (z * y) - R' z‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K))
      (nhds 1) (nhds 0))
    (hRc : Continuous R)
    (hRy : ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => R (z * y)) 2 ((haarGL K).restrict D))
    (hubdd : ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) (B : Set (AdelicGL2 (𝓞 K) K)),
      IsCompact B → ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ B, ∫ z in D, ‖∑ h ∈ s, l h * R (z * y * h)‖ ^ 2 ∂(haarGL K) ≤ C)
    {P : (AdelicGL2 (𝓞 K) K → ℂ) → Prop} (hPc : ∀ f, P f → Continuous f ∧ HasCompactSupport f)
    (hker : ∀ V ∈ nhds (1 : AdelicGL2 (𝓞 K) K), ∃ f : AdelicGL2 (𝓞 K) K → ℂ, P f ∧
      (∀ y, f y ≠ 0 → ∃ y' ∈ V, (fun z => R' (z * y)) = fun z => R' (z * y')) ∧
      ∫ y, f y ∂(haarGL K) = 1 ∧ ∫ y, ‖f y‖ ∂(haarGL K) ≤ 2)
    {A : Finset (AdelicGL2 (𝓞 K) K) → (AdelicGL2 (𝓞 K) K → ℂ) → ℝ≥0∞}
    (hA : ∀ ε : ℝ≥0∞, 0 < ε → ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ), A s l < ε)
    (hsoft : ∀ f, P f → MemLp (rightConv K R' f) 2 ((haarGL K).restrict D) ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        MemLp (rightConv K (fun g => ∑ h ∈ s, l h * R (g * h)) f) 2 ((haarGL K).restrict D) ∧
        ∫⁻ z in D, (‖rightConv K R' f z - rightConv K (fun g => ∑ h ∈ s, l h * R (g * h)) f z‖₊ : ℝ≥0∞) ^ 2
            ∂(haarGL K) ≤ C * A s l) :
    peterssonIntegral K 0 D ψ R' = 0 := by
  set N : ℝ := (eLpNorm ψ 2 ((haarGL K).restrict D)).toReal with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hR'mem : MemLp R' 2 ((haarGL K).restrict D) := by simpa only [mul_one] using hR'y 1

  have hpair : ∀ {v : AdelicGL2 (𝓞 K) K → ℂ} (hv : MemLp v 2 ((haarGL K).restrict D)) {η : ℝ}, 0 ≤ η →
      ∫⁻ z in D, (‖v z‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K) ≤ ENNReal.ofReal (η ^ 2) →
      ‖peterssonIntegral K 0 D ψ v‖ ≤ N * η := by
    intro v hv η hη hmass
    exact (norm_peterssonIntegral_zero_le K hψ hv).trans
      (mul_le_mul_of_nonneg_left (toReal_eLpNorm_le_of_lintegral_le hη hmass) hN0)

  have hconv_zero : ∀ f, P f → peterssonIntegral K 0 D ψ (rightConv K R' f) = 0 := by
    intro f hPf
    obtain ⟨hfc, hfs⟩ := hPc f hPf
    obtain ⟨hR'conv, C, hCtop, hsl⟩ := hsoft f hPf

    have hu_zero : ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        peterssonIntegral K 0 D ψ (rightConv K (fun g => ∑ h ∈ s, l h * R (g * h)) f) = 0 := by
      intro s l
      obtain ⟨Cu, hCu0, hCule⟩ := hubdd s l (tsupport f) hfs
      have huc : Continuous fun g => ∑ h ∈ s, l h * R (g * h) :=
        continuous_finsetSum s fun h _ => continuous_const.mul (hRc.comp (continuous_id.mul continuous_const))
      have huy : ∀ y : AdelicGL2 (𝓞 K) K,
          MemLp (fun z => ∑ h ∈ s, l h * R (z * y * h)) 2 ((haarGL K).restrict D) := by
        intro y
        refine memLp_finsetSum s fun h _ => ?_
        simpa only [mul_assoc] using (hRy (y * h)).const_mul (l h)
      have horth_u : ∀ y : AdelicGL2 (𝓞 K) K,
          peterssonIntegral K 0 D ψ (fun z => ∑ h ∈ s, l h * R (z * y * h)) = 0 := by
        intro y
        rw [peterssonIntegral_zero_sum K hψ s l (fun h z => R (z * y * h))
          (fun h _ => by simpa only [mul_assoc] using hRy (y * h))]
        refine Finset.sum_eq_zero fun h _ => ?_
        have h0 := horth (y * h)
        simp only [← mul_assoc] at h0
        rw [h0, mul_zero]
      exact peterssonIntegral_rightConv_eq_zero_of_forall_translate K hψ huc huy hCu0 hCule hfc hfs horth_u
    refine eq_zero_of_norm_le_mul hN0 fun θ hθ => ?_

    have hx0 : ENNReal.ofReal (θ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hC1 : C + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hCtop, ENNReal.one_ne_top⟩
    obtain ⟨s, l, hsl_small⟩ := hA (ENNReal.ofReal (θ ^ 2) / (C + 1)) (ENNReal.div_pos hx0 hC1)
    obtain ⟨huconv, hdiff⟩ := hsl s l
    have hmass : ∫⁻ z in D, (‖(rightConv K R' f - rightConv K (fun g => ∑ h ∈ s, l h * R (g * h)) f) z‖₊ :
        ℝ≥0∞) ^ 2 ∂(haarGL K) ≤ ENNReal.ofReal (θ ^ 2) := by
      simp only [Pi.sub_apply]
      calc _ ≤ C * A s l := hdiff
        _ ≤ C * (ENNReal.ofReal (θ ^ 2) / (C + 1)) := mul_le_mul_right hsl_small.le _
        _ ≤ (C + 1) * (ENNReal.ofReal (θ ^ 2) / (C + 1)) := mul_le_mul_left le_self_add _
        _ ≤ ENNReal.ofReal (θ ^ 2) := ENNReal.mul_div_le
    have hsplit := peterssonIntegral_zero_sub K hψ hR'conv huconv
    rw [hu_zero s l, sub_zero] at hsplit
    rw [hsplit]
    exact hpair (hR'conv.sub huconv) hθ.le hmass

  refine eq_zero_of_norm_le_mul (mul_nonneg zero_le_two hN0) fun η hη => ?_
  have hev : ∀ᶠ y in nhds (1 : AdelicGL2 (𝓞 K) K),
      ∫⁻ z in D, (‖R' (z * y) - R' z‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K) < ENNReal.ofReal (η ^ 2) :=
    hcont.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity)))
  obtain ⟨f, hPf, hnear, hint1, hnorm2⟩ := hker _ hev
  obtain ⟨hfc, hfs⟩ := hPc f hPf

  obtain ⟨CB, hCB0, hCBle⟩ := hR'bdd (tsupport f) hfs
  have hwt_meas : AEStronglyMeasurable
      (fun z : AdelicGL2 (𝓞 K) K =>
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-(0 : ℝ)))
      ((haarGL K).restrict D) := by
    simp only [neg_zero, Real.rpow_zero]
    exact aestronglyMeasurable_const
  have hwt_bound : ∀ᵐ z ∂(haarGL K).restrict D,
      ‖NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det z) ^ (-(0 : ℝ))‖ ≤ 1 :=
    Filter.Eventually.of_forall fun z => by simp
  have hint := integrable_pairing_rightConv_integrand_window K 0 hψ hR'c 1
    (fun y => by simpa only [mul_one] using hR'y y) hCB0 (fun y hy => by simpa only [mul_one] using hCBle y hy)
    hwt_meas zero_le_one hwt_bound hfc hfs
  have h981 := peterssonIntegral_rightConv_eq_integral K 0 D ψ R' f 1 hint
  simp only [mul_one] at h981

  have hslice : Integrable (fun y => (starRingEnd ℂ) (f y) * peterssonIntegral K 0 D ψ (fun z => R' (z * y)))
      (haarGL K) := by
    refine hint.integral_prod_right.congr (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [peterssonIntegral_zero_eq, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Function.uncurry_apply_pair, mul_one, map_mul, neg_zero, Real.rpow_zero, Complex.ofReal_one]
    ring
  have hconst : Integrable (fun y => (starRingEnd ℂ) (f y) * peterssonIntegral K 0 D ψ R') (haarGL K) :=
    (Complex.continuous_conj.comp hfc).integrable_of_hasCompactSupport (hfs.comp_left (map_zero _)) |>.mul_const _

  have hself : peterssonIntegral K 0 D ψ R' =
      ∫ y, (starRingEnd ℂ) (f y) * peterssonIntegral K 0 D ψ R' ∂(haarGL K) := by
    rw [integral_mul_const, integral_conj, hint1, map_one, one_mul]

  have hdiff : peterssonIntegral K 0 D ψ R' =
      ∫ y, (starRingEnd ℂ) (f y) *
        (peterssonIntegral K 0 D ψ R' - peterssonIntegral K 0 D ψ (fun z => R' (z * y))) ∂(haarGL K) := by
    conv_lhs => rw [← sub_zero (peterssonIntegral K 0 D ψ R'), ← hconv_zero f hPf, h981, hself]
    rw [← integral_sub hconst hslice]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring

  have hterm : ∀ y : AdelicGL2 (𝓞 K) K,
      ‖(starRingEnd ℂ) (f y) *
        (peterssonIntegral K 0 D ψ R' - peterssonIntegral K 0 D ψ (fun z => R' (z * y)))‖ ≤ ‖f y‖ * (N * η) := by
    intro y
    by_cases hfy : f y = 0
    · simp [hfy]
    obtain ⟨y', hy'V, hy'eq⟩ := hnear y hfy
    rw [norm_mul, Complex.norm_conj, hy'eq, norm_sub_rev,
      peterssonIntegral_zero_sub K hψ (hR'y y') (by simpa only [mul_one] using hR'y 1)]
    refine mul_le_mul_of_nonneg_left (hpair ((hR'y y').sub (by simpa only [mul_one] using hR'y 1)) hη.le ?_)
      (norm_nonneg _)
    simpa only [Pi.sub_apply] using (show y' ∈ _ from hy'V).le
  rw [hdiff]
  calc ‖∫ y, (starRingEnd ℂ) (f y) *
          (peterssonIntegral K 0 D ψ R' - peterssonIntegral K 0 D ψ (fun z => R' (z * y))) ∂(haarGL K)‖
      ≤ ∫ y, ‖f y‖ * (N * η) ∂(haarGL K) :=
        norm_integral_le_of_norm_le ((hfc.integrable_of_hasCompactSupport hfs).norm.mul_const _)
          (Filter.Eventually.of_forall hterm)
    _ = (∫ y, ‖f y‖ ∂(haarGL K)) * (N * η) := integral_mul_const _ _
    _ ≤ 2 * (N * η) := mul_le_mul_of_nonneg_right hnorm2 (by positivity)
    _ = 2 * N * η := by ring

end WeakPassage

namespace WeakPassage

variable (K : Type) [Field K] [NumberField K]

private theorem exists_finset_lintegral_lt_of_weak_data [SigmaFinite (haarGL K)] {D : Set (AdelicGL2 (𝓞 K) K)}
    {R R' : AdelicGL2 (𝓞 K) K → ℂ} (hRc : Continuous R)
    (hRy : ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => R (z * y)) 2 ((haarGL K).restrict D))
    (hR'c : Continuous R')
    (hR'y : ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => R' (z * y)) 2 ((haarGL K).restrict D))
    (hR'bdd : ∀ B : Set (AdelicGL2 (𝓞 K) K), IsCompact B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ B, ∫ z in D, ‖R' (z * y)‖ ^ 2 ∂(haarGL K) ≤ C)
    (hcont : Filter.Tendsto (fun y => ∫⁻ z in D, (‖R' (z * y) - R' z‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K))
      (nhds 1) (nhds 0))
    (hubdd : ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) (B : Set (AdelicGL2 (𝓞 K) K)),
      IsCompact B → ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ B, ∫ z in D, ‖∑ h ∈ s, l h * R (z * y * h)‖ ^ 2 ∂(haarGL K) ≤ C)
    {P : (AdelicGL2 (𝓞 K) K → ℂ) → Prop} (hPc : ∀ f, P f → Continuous f ∧ HasCompactSupport f)
    (hker : ∀ V ∈ nhds (1 : AdelicGL2 (𝓞 K) K), ∃ f : AdelicGL2 (𝓞 K) K → ℂ, P f ∧
      (∀ y, f y ≠ 0 → ∃ y' ∈ V, (fun z => R' (z * y)) = fun z => R' (z * y')) ∧
      ∫ y, f y ∂(haarGL K) = 1 ∧ ∫ y, ‖f y‖ ∂(haarGL K) ≤ 2)
    {A : Finset (AdelicGL2 (𝓞 K) K) → (AdelicGL2 (𝓞 K) K → ℂ) → ℝ≥0∞}
    (hA : ∀ ε : ℝ≥0∞, 0 < ε → ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ), A s l < ε)
    (hsoft : ∀ f, P f → MemLp (rightConv K R' f) 2 ((haarGL K).restrict D) ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        MemLp (rightConv K (fun g => ∑ h ∈ s, l h * R (g * h)) f) 2 ((haarGL K).restrict D) ∧
        ∫⁻ z in D, (‖rightConv K R' f z - rightConv K (fun g => ∑ h ∈ s, l h * R (g * h)) f z‖₊ : ℝ≥0∞) ^ 2
            ∂(haarGL K) ≤ C * A s l)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
      ∫⁻ y in D, (‖R' y - ∑ h ∈ s, l h * R (y * h)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε := by
  have hR'mem : MemLp R' 2 ((haarGL K).restrict D) := by simpa only [mul_one] using hR'y 1
  refine WeakTranslateClosure.exists_finset_lintegral_sub_sum_sq_lt_of_forall_inner_eq_zero hRy hR'mem ?_ ε hε
  intro Ψ hΨ

  have hψ : MemLp (⇑Ψ) 2 ((haarGL K).restrict D) := Lp.memLp Ψ
  have hΨeq : hψ.toLp = Ψ := Lp.toLp_coeFn Ψ hψ
  have hzero : ∀ {v : AdelicGL2 (𝓞 K) K → ℂ} (hv : MemLp v 2 ((haarGL K).restrict D)),
      (inner ℂ Ψ hv.toLp : ℂ) = 0 ↔ peterssonIntegral K 0 D (⇑Ψ) v = 0 := by
    intro v hv
    conv_lhs => rw [← hΨeq]
    rw [inner_toLp_eq_integral hψ hv, peterssonIntegral_zero_eq_conj_integral, map_eq_zero]
  have horth : ∀ y : AdelicGL2 (𝓞 K) K, peterssonIntegral K 0 D (⇑Ψ) (fun z => R (z * y)) = 0 :=
    fun y => (hzero (hRy y)).1 (hΨ y)
  exact (hzero hR'mem).2
    (peterssonIntegral_zero_eq_zero_of_weak K hψ horth hR'c hR'y hR'bdd hcont hRc hRy hubdd hPc hker hA hsoft)

end WeakPassage

section AdelicExt

open NumberField.AdelicLevel AdelicDock IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

private theorem adelicGL2_ext {x y : AdelicGL2 (𝓞 K) K} (harch : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K),
      finComponent (𝓞 K) K w (glFin (𝓞 K) K x) = finComponent (𝓞 K) K w (glFin (𝓞 K) K y)) : x = y := by
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K
  · ext i j
    have h0 := Units.val_inj.mpr harch
    have h := congrFun (congrFun h0 i) j
    first | exact h | simpa only [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply] using h | simpa +zetaDelta only [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply] using h
  · apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K
    intro w
    ext i j : 1
    have h0 := Units.val_inj.mpr (hfin w)
    have h := congrFun (congrFun h0 i) j
    first | exact h | simpa only [finComponent_apply, glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply] using h | simpa +zetaDelta only [finComponent_apply, glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply] using h

end AdelicExt

section KernelUnit

variable {K : Type} [Field K] [NumberField K]

section SmoothingKernels

open NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open scoped ENNReal ProbabilityTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm IsDedekindDomain LocalGL2 AdelicDock Filter Topology"
open AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

variable (K)

namespace RightConvRegularity

open scoped Classical

section Slice

private abbrev instNG : NormedAddCommGroup (mixedEmbedding.mixedSpace K) := inferInstance
attribute [local instance] instNG
private abbrev instNS : NormedSpace ℝ (mixedEmbedding.mixedSpace K) := inferInstance
attribute [local instance] instNS

omit [NumberField K] in
private theorem continuous_symm_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  refine continuous_pi fun v => ?_
  by_cases hv : v.IsReal
  · have h : (fun x : mixedEmbedding.mixedSpace K =>
          (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x v) =
        fun x => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (x.1 ⟨v, hv⟩) := by
      funext x
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      have hx := congrArg (fun p : mixedEmbedding.mixedSpace K => p.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply x)
      exact hx
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have h : (fun x : mixedEmbedding.mixedSpace K =>
          (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x v) =
        fun x => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm
          (x.2 ⟨v, hc⟩) := by
      funext x
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      have hx := congrArg (fun p : mixedEmbedding.mixedSpace K => p.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply x)
      exact hx
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

end Slice

end RightConvRegularity

attribute [local instance] RightConvRegularity.instNG RightConvRegularity.instNS

open scoped Classical in

private def IsSmoothingKernel (N : Ideal (𝓞 K)) (U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (F : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∧
    IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∧ U ≤ finiteLevelOne (𝓞 K) K N ∧
    ∃ fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa ∧
      ∀ y : AdelicGL2 (𝓞 K) K, F y = fa (glArch (𝓞 K) K y) * (if glFin (𝓞 K) K y ∈ U then 1 else 0)

private def archUnits : Set (mixedEmbedding.mixedSpace K) :=
  {z | IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z)}

variable {K}

section

variable (K)

open scoped Classical in

private theorem isFinTestFactor_indicator (U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (hUo : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))))
    (hUc : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :
    IsFinTestFactor K (fun k => if k ∈ U then (1 : ℂ) else 0) := by
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro k
    by_cases hk : k ∈ U
    · refine ⟨U, hUo, hk, fun k' hk' => ?_⟩
      have hk'' : k' ∈ U := hk'
      rw [if_pos hk'', if_pos hk]
    · refine ⟨(U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))ᶜ, hUc.isClosed.isOpen_compl, hk, fun k' hk' => ?_⟩
      have hk'' : k' ∉ U := hk'
      rw [if_neg hk'', if_neg hk]
  · refine HasCompactSupport.intro hUc fun k hk => ?_
    have hk' : k ∉ U := hk
    exact if_neg hk'

private theorem isFactorizableTestFn_of_isSmoothingKernel {N : Ideal (𝓞 K)}
    {U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))} {F : AdelicGL2 (𝓞 K) K → ℂ}
    (hF : IsSmoothingKernel K N U F) : IsFactorizableTestFn K F := by
  obtain ⟨hUo, hUc, -, fa, hfa, hFeq⟩ := hF
  exact ⟨fa, _, hfa, isFinTestFactor_indicator K U hUo hUc, hFeq⟩

end

section

variable (K)

omit [NumberField K] in
private theorem isUnit_of_mem_archUnits {z : mixedEmbedding.mixedSpace K} (hz : z ∈ archUnits K) : IsUnit z := by
  have h : IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z) := hz
  have h' := h.map (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  rwa [RingEquiv.apply_symm_apply] at h'

omit [NumberField K] in

private theorem coords_ne_zero_of_isUnit {z : mixedEmbedding.mixedSpace K} (hz : IsUnit z) :
    (∀ v, z.1 v ≠ 0) ∧ ∀ w, z.2 w ≠ 0 := by
  obtain ⟨h1, h2⟩ := Prod.isUnit_iff.1 hz
  exact ⟨fun v => (Pi.isUnit_iff.1 h1 v).ne_zero, fun w => (Pi.isUnit_iff.1 h2 w).ne_zero⟩

private def coordInv (z : mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  (fun v => (z.1 v)⁻¹, fun w => (z.2 w)⁻¹)

omit [NumberField K] in

private theorem ringInverse_eq_coordInv {z : mixedEmbedding.mixedSpace K} (hz : IsUnit z) :
    Ring.inverse z = coordInv K z := by
  obtain ⟨h1, h2⟩ := coords_ne_zero_of_isUnit K hz
  obtain ⟨u, rfl⟩ := hz
  rw [Ring.inverse_unit]
  refine Units.inv_eq_of_mul_eq_one_right (Prod.ext (funext fun v => ?_) (funext fun w => ?_))
  · exact mul_inv_cancel₀ (h1 v)
  · exact mul_inv_cancel₀ (h2 w)

omit [NumberField K] in
private theorem mem_archUnits_iff {z : mixedEmbedding.mixedSpace K} : z ∈ archUnits K ↔ IsUnit z :=
  ⟨isUnit_of_mem_archUnits K,
    fun hz => hz.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.toMonoidHom⟩

private theorem isOpen_setOf_isUnit : IsOpen {z : mixedEmbedding.mixedSpace K | IsUnit z} := by
  have hset : {z : mixedEmbedding.mixedSpace K | IsUnit z} =
      (⋂ v, {z : mixedEmbedding.mixedSpace K | z.1 v ≠ 0}) ∩ ⋂ w, {z : mixedEmbedding.mixedSpace K | z.2 w ≠ 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Prod.isUnit_iff, Pi.isUnit_iff,
      isUnit_iff_ne_zero]
  rw [hset]
  exact (isOpen_iInter_of_finite fun v =>
      isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const).inter
    (isOpen_iInter_of_finite fun w => isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)

open scoped Classical in

private theorem contDiffAt_ringInverse_of_isUnit {n : WithTop ℕ∞} {z : mixedEmbedding.mixedSpace K}
    (hz : IsUnit z) :
    ContDiffAt ℝ n (Ring.inverse : mixedEmbedding.mixedSpace K → mixedEmbedding.mixedSpace K) z := by
  obtain ⟨h1, h2⟩ := coords_ne_zero_of_isUnit K hz
  have hc : ContDiffAt ℝ n (fun u : mixedEmbedding.mixedSpace K =>
      ((fun v => (u.1 v)⁻¹, fun w => (u.2 w)⁻¹) : mixedEmbedding.mixedSpace K)) z := by
    refine ContDiffAt.prodMk (contDiffAt_pi.2 fun v => ?_) (contDiffAt_pi.2 fun w => ?_)
    · have hf : ContDiffAt ℝ n (fun u : mixedEmbedding.mixedSpace K => u.1 v) z :=
        ((ContinuousLinearMap.proj v : (_ → ℝ) →L[ℝ] ℝ).contDiff.comp contDiff_fst).contDiffAt
      exact (contDiffAt_inv ℝ (h1 v)).comp z hf
    · have hf : ContDiffAt ℝ n (fun u : mixedEmbedding.mixedSpace K => u.2 w) z :=
        ((ContinuousLinearMap.proj w : (_ → ℂ) →L[ℝ] ℂ).contDiff.comp contDiff_snd).contDiffAt
      exact (contDiffAt_inv ℝ (h2 w)).comp z hf
  refine hc.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem ((isOpen_setOf_isUnit K).mem_nhds hz) fun u hu => ?_)
  exact ringInverse_eq_coordInv K hu

private theorem continuousOn_ringInverse_archUnits :
    ContinuousOn (Ring.inverse : mixedEmbedding.mixedSpace K → mixedEmbedding.mixedSpace K) (archUnits K) :=
  fun _ hz =>
    (contDiffAt_ringInverse_of_isUnit K (n := 1) (isUnit_of_mem_archUnits K hz)).continuousAt.continuousWithinAt

private theorem isOpen_archUnits : IsOpen (archUnits K) := by
  have h : archUnits K = {z : mixedEmbedding.mixedSpace K | IsUnit z} := Set.ext fun _ => mem_archUnits_iff K
  rw [h]
  exact isOpen_setOf_isUnit K

end

section ArchInsertionNhds

variable (K)

private def archMatOfEntries (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.mapMatrix (Matrix.of E)

private theorem archMatOfEntries_apply (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) (i j : Fin 2) :
    archMatOfEntries K E i j = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (E i j) := rfl

private theorem continuous_archMatOfEntries : Continuous (archMatOfEntries K) := by
  refine continuous_matrix fun i j => ?_
  exact (RightConvRegularity.continuous_symm_ringEquiv_mixedSpace K).comp
    ((continuous_apply j).comp (continuous_apply i))

private def entriesDet (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  E 0 0 * E 1 1 - E 0 1 * E 1 0

private theorem continuous_entriesDet : Continuous (entriesDet K) := by
  unfold entriesDet
  fun_prop

private def entriesInv (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :
    Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K :=
  ![![E 1 1 * Ring.inverse (entriesDet K E), -(E 0 1 * Ring.inverse (entriesDet K E))],
    ![-(E 1 0 * Ring.inverse (entriesDet K E)), E 0 0 * Ring.inverse (entriesDet K E)]]

private def entriesUnits : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
  {E | entriesDet K E ∈ archUnits K}

private theorem isOpen_entriesUnits : IsOpen (entriesUnits K) :=
  (isOpen_archUnits K).preimage (continuous_entriesDet K)

private theorem continuousOn_entriesInv : ContinuousOn (entriesInv K) (entriesUnits K) := by
  have hinv : ContinuousOn (fun E => Ring.inverse (entriesDet K E)) (entriesUnits K) :=
    (continuousOn_ringInverse_archUnits K).comp (continuous_entriesDet K).continuousOn fun E hE => hE
  have h00 : Continuous fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => E 0 0 :=
    (continuous_apply (0 : Fin 2)).comp (continuous_apply (0 : Fin 2))
  have h01 : Continuous fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => E 0 1 :=
    (continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2))
  have h10 : Continuous fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => E 1 0 :=
    (continuous_apply (0 : Fin 2)).comp (continuous_apply (1 : Fin 2))
  have h11 : Continuous fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => E 1 1 :=
    (continuous_apply (1 : Fin 2)).comp (continuous_apply (1 : Fin 2))
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [entriesInv, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  · exact h11.continuousOn.mul hinv
  · exact (h01.continuousOn.mul hinv).neg
  · exact (h10.continuousOn.mul hinv).neg
  · exact h00.continuousOn.mul hinv

private theorem of_mul_of_entriesInv {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K} (hE : E ∈ entriesUnits K) :
    Matrix.of E * Matrix.of (entriesInv K E) = 1 ∧ Matrix.of (entriesInv K E) * Matrix.of E = 1 := by
  have hu : entriesDet K E * Ring.inverse (entriesDet K E) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_of_mem_archUnits K hE)
  have hd : entriesDet K E = E 0 0 * E 1 1 - E 0 1 * E 1 0 := rfl
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, entriesInv, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.one_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true, if_false,
      one_ne_zero, zero_ne_one]
  · linear_combination hu - Ring.inverse (entriesDet K E) * hd
  · ring1
  · ring1
  · linear_combination hu - Ring.inverse (entriesDet K E) * hd
  · linear_combination hu - Ring.inverse (entriesDet K E) * hd
  · ring1
  · ring1
  · linear_combination hu - Ring.inverse (entriesDet K E) * hd

private def archGLOfEntries (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) (hE : E ∈ entriesUnits K) :
    GL (Fin 2) (InfiniteAdeleRing K) where
  val := archMatOfEntries K E
  inv := archMatOfEntries K (entriesInv K E)
  val_inv := by
    unfold archMatOfEntries
    rw [← map_mul, (of_mul_of_entriesInv K hE).1, map_one]
  inv_val := by
    unfold archMatOfEntries
    rw [← map_mul, (of_mul_of_entriesInv K hE).2, map_one]

private theorem continuous_archGLOfEntries_restrict :
    Continuous fun E : entriesUnits K => archGLOfEntries K E.1 E.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_archMatOfEntries K).comp continuous_subtype_val
  · exact (continuous_archMatOfEntries K).comp (continuousOn_iff_continuous_restrict.1 (continuousOn_entriesInv K))

private theorem archEntries_mem_entriesUnits (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    archEntries K g ∈ entriesUnits K := by
  show IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (entriesDet K (archEntries K g)))
  have hdet : (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (entriesDet K (archEntries K g))
      = Matrix.det (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    simp only [entriesDet, archEntries_apply, map_sub, map_mul, RingEquiv.symm_apply_apply, Matrix.det_fin_two]
  rw [hdet]
  exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

private theorem archGLOfEntries_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    archGLOfEntries K (archEntries K g) (archEntries_mem_entriesUnits K g) = g := by
  ext i j
  simp only [archGLOfEntries, archMatOfEntries_apply, archEntries_apply, RingEquiv.symm_apply_apply]

open scoped Classical in

private noncomputable def archGLOfEntries' (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  if hE : E ∈ entriesUnits K then archGLOfEntries K E hE else 1

private theorem archGLOfEntries'_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    archGLOfEntries' K (archEntries K g) = g := by
  rw [archGLOfEntries', dif_pos (archEntries_mem_entriesUnits K g), archGLOfEntries_archEntries]

private theorem continuousAt_archGLOfEntries' {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ entriesUnits K) : ContinuousAt (archGLOfEntries' K) E := by
  have hcont : ContinuousOn (archGLOfEntries' K) (entriesUnits K) := by
    rw [continuousOn_iff_continuous_restrict]
    refine (continuous_archGLOfEntries_restrict K).congr fun F => ?_
    simp only [Set.restrict_apply, archGLOfEntries', dif_pos F.2]
  exact hcont.continuousAt ((isOpen_entriesUnits K).mem_nhds hE)

private def archInsert (g : GL (Fin 2) (InfiniteAdeleRing K)) : AdelicGL2 (𝓞 K) K where
  val := SiegelVolume.infMat K (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
  inv := SiegelVolume.infMat K
    ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
  val_inv := by rw [← SiegelVolume.infMat_mul, Units.mul_inv, SiegelVolume.infMat_one]
  inv_val := by rw [← SiegelVolume.infMat_mul, Units.inv_mul, SiegelVolume.infMat_one]

private theorem continuous_infMat : Continuous (SiegelVolume.infMat K) := by
  refine continuous_matrix fun i j => ?_
  simp only [SiegelVolume.infMat, Matrix.of_apply]
  exact ((continuous_apply j).comp (continuous_apply i)).prodMk continuous_const

private theorem continuous_archInsert : Continuous (archInsert K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_infMat K).comp Units.continuous_val
  · exact (continuous_infMat K).comp Units.continuous_coe_inv

private theorem archInsert_one : archInsert K 1 = 1 := by
  ext : 1
  simp only [archInsert, Units.val_one, SiegelVolume.infMat_one]

private theorem archInsert_glArch_of_glFin_eq_one {a : AdelicGL2 (𝓞 K) K} (ha : glFin (𝓞 K) K a = 1) :
    archInsert K (glArch (𝓞 K) K a) = a := by
  ext : 1
  show SiegelVolume.infMat K ((glArch (𝓞 K) K a : GL (Fin 2) (InfiniteAdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) = (a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  refine SiegelVolume.matrix_eq_of_arch_fin K ?_ ?_
  · rw [SiegelVolume.adeleArch_mapMatrix_infMat]
    rfl
  · rw [SiegelVolume.adeleFin_mapMatrix_infMat]
    have h := congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ha
    exact h.symm

private theorem exists_pos_forall_mem_of_mem_nhds_one {V : Set (AdelicGL2 (𝓞 K) K)}
    (hV : V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 →
      dist (archEntries K (glArch (𝓞 K) K a)) (archEntries K 1) < ε → a ∈ V := by
  have h1 : archInsert K (archGLOfEntries' K (archEntries K 1)) = 1 := by
    rw [archGLOfEntries'_archEntries, archInsert_one]
  have hcont : ContinuousAt (fun E => archInsert K (archGLOfEntries' K E)) (archEntries K 1) :=
    (continuous_archInsert K).continuousAt.comp (continuousAt_archGLOfEntries' K (archEntries_mem_entriesUnits K 1))
  have hpre : (fun E => archInsert K (archGLOfEntries' K E)) ⁻¹' V ∈ 𝓝 (archEntries K 1) := by
    refine hcont.preimage_mem_nhds ?_
    rw [h1]
    exact hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨ε, hε, fun a ha hdist => ?_⟩
  have hmem := hball hdist
  simp only [Set.mem_preimage, archGLOfEntries'_archEntries, archInsert_glArch_of_glFin_eq_one K ha] at hmem
  exact hmem

end ArchInsertionNhds

variable (K) in

private theorem exists_archTestFactor_of_pos {ε : ℝ} (hε : 0 < ε) :
    ∃ fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa ∧ (∀ g, ∃ r : ℝ, 0 ≤ r ∧ fa g = r) ∧
      fa 1 ≠ 0 ∧ ∀ g, fa g ≠ 0 → dist (archEntries K g) (archEntries K 1) < ε := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 (isOpen_entriesUnits K) _ (archEntries_mem_entriesUnits K 1)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min r ε / 2 := ⟨_, rfl⟩
  have hmin : 0 < min r ε := lt_min hr hε
  have hρpos : 0 < ρ := by rw [hρ]; exact half_pos hmin
  have hρr : ρ < r := by rw [hρ]; exact (half_lt_self hmin).trans_le (min_le_left _ _)
  have hρε : ρ < ε := by rw [hρ]; exact (half_lt_self hmin).trans_le (min_le_right _ _)
  let b : ContDiffBump (archEntries K 1) := ⟨ρ / 2, ρ, half_pos hρpos, half_lt_self hρpos⟩

  have hsupp : Function.support (⇑Complex.ofRealCLM ∘ ⇑b) ⊆ Function.support b := by
    intro E hE
    rw [Function.mem_support] at hE ⊢
    intro h0
    apply hE
    simp [h0]
  have htsupp : tsupport (⇑Complex.ofRealCLM ∘ ⇑b) ⊆ tsupport b := closure_mono hsupp
  have hc : HasCompactSupport (⇑Complex.ofRealCLM ∘ ⇑b) :=
    IsCompact.of_isClosed_subset b.hasCompactSupport isClosed_closure htsupp
  have hU : tsupport (⇑Complex.ofRealCLM ∘ ⇑b) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := by
    refine htsupp.trans ?_
    rw [b.tsupport_eq]
    refine (Metric.closedBall_subset_ball (show b.rOut < r from hρr)).trans (hrU.trans fun E hE => ?_)
    have hE' : entriesDet K E ∈ archUnits K := hE
    simpa [entriesDet, Matrix.det_fin_two] using isUnit_of_mem_archUnits K hE'
  have hfa : IsArchTestFactor K fun g => (⇑Complex.ofRealCLM ∘ ⇑b) (archEntries K g) :=
    isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det K _
      (Complex.ofRealCLM.contDiff.comp b.contDiff) hc hU
  refine ⟨fun g => (⇑Complex.ofRealCLM ∘ ⇑b) (archEntries K g), hfa, fun g => ⟨b (archEntries K g), b.nonneg, ?_⟩,
    ?_, fun g hg => ?_⟩
  · simp
  · have h1 : b (archEntries K 1) = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp [h1]
  · have hb : b (archEntries K g) ≠ 0 := by
      intro h0
      apply hg
      simp [h0]
    have hmem : archEntries K g ∈ Function.support b := Function.mem_support.2 hb
    rw [b.support_eq, Metric.mem_ball] at hmem
    exact hmem.trans hρε

open scoped Classical in

private theorem exists_isSmoothingKernel_of_mem_nhds_one {N : Ideal (𝓞 K)} (hN : N ≠ ⊥)
    {V : Set (AdelicGL2 (𝓞 K) K)} (hV : V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ F : AdelicGL2 (𝓞 K) K → ℂ, IsSmoothingKernel K N (finiteLevelOne (𝓞 K) K N) F ∧ Continuous F ∧
      HasCompactSupport F ∧ (∀ y, ∃ r : ℝ, 0 ≤ r ∧ F y = r) ∧ F 1 ≠ 0 ∧
        ∀ y, F y ≠ 0 → ∃ u ∈ finiteLevelOne (𝓞 K) K N, (finEmbed (𝓞 K) K u)⁻¹ * y ∈ V := by
  obtain ⟨ε, hε, hεV⟩ := exists_pos_forall_mem_of_mem_nhds_one K hV
  obtain ⟨fa, hfa, hfare, hfa1, hfasupp⟩ := exists_archTestFactor_of_pos K hε
  obtain ⟨F, hF⟩ : ∃ F : AdelicGL2 (𝓞 K) K → ℂ, F = fun y =>
      fa (glArch (𝓞 K) K y) * (if glFin (𝓞 K) K y ∈ finiteLevelOne (𝓞 K) K N then 1 else 0) := ⟨_, rfl⟩
  have hker : IsSmoothingKernel K N (finiteLevelOne (𝓞 K) K N) F := by
    unfold IsSmoothingKernel
    exact ⟨isOpen_finiteLevelOne (R := 𝓞 K) (K := K) (N := N) hN,
      isCompact_finiteLevelOne (R := 𝓞 K) (K := K) (N := N), le_rfl, fa, hfa, fun y => by rw [hF]⟩
  obtain ⟨hFc, hFs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K F
    (isFactorizableTestFn_of_isSmoothingKernel K hker)
  refine ⟨F, hker, hFc, hFs, fun y => ?_, ?_, fun y hy => ?_⟩
  · obtain ⟨r, hr0, hr⟩ := hfare (glArch (𝓞 K) K y)
    by_cases hu : glFin (𝓞 K) K y ∈ finiteLevelOne (𝓞 K) K N
    · exact ⟨r, hr0, by simp [hF, hu, hr]⟩
    · exact ⟨0, le_rfl, by simp [hF, hu]⟩
  · have h1 : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ finiteLevelOne (𝓞 K) K N := one_mem _
    simp only [hF, map_one, h1, if_true, mul_one]
    exact hfa1
  · have hu : glFin (𝓞 K) K y ∈ finiteLevelOne (𝓞 K) K N := by
      by_contra hu
      exact hy (by simp [hF, hu])
    have hfay : fa (glArch (𝓞 K) K y) ≠ 0 := by
      intro h0
      exact hy (by simp [hF, h0])
    refine ⟨glFin (𝓞 K) K y, hu, hεV _ ?_ ?_⟩
    · rw [map_mul, map_inv, glFin_finEmbed, inv_mul_cancel]
    · rw [map_mul, map_inv, glArch_finEmbed, inv_one, one_mul]
      exact hfasupp _ hfay

end SmoothingKernels

end KernelUnit

open NumberField.AdelicLevel AdelicDock IsDedekindDomain

namespace WeakPassage

section KernelAdapter

variable {K : Type} [Field K] [NumberField K]

private theorem finEmbed_mul_of_glFin_eq_one {y : AdelicGL2 (𝓞 K) K} (hy : glFin (𝓞 K) K y = 1)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    finEmbed (𝓞 K) K u * y = y * finEmbed (𝓞 K) K u := by
  apply adelicGL2_ext
  · simp only [map_mul, glArch_finEmbed, one_mul, mul_one]
  · intro w
    simp only [map_mul, glFin_finEmbed, hy, one_mul, mul_one]

private theorem isFactorizableTestFn_const_mul {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f) (c : ℂ) :
    IsFactorizableTestFn K (fun y => c * f y) := by
  obtain ⟨fa, ff, hfa, ⟨hffl, hffs⟩, hfeq⟩ := hf
  refine ⟨fa, fun x => c * ff x, hfa, ⟨hffl.comp (fun z => c * z), hffs.mul_left⟩, fun y => ?_⟩
  beta_reduce
  rw [hfeq y]; ring

private theorem integral_ne_zero_of_nonneg_of_apply_one_ne_zero {F : AdelicGL2 (𝓞 K) K → ℂ}
    (hFc : Continuous F) (hFs : HasCompactSupport F) (hFre : ∀ y, ∃ r : ℝ, 0 ≤ r ∧ F y = r) (hF1 : F 1 ≠ 0) :
    ∫ y, F y ∂(haarGL K) ≠ 0 := by
  choose r hr0 hFr using hFre
  have hFeq : F = fun y => ((r y : ℝ) : ℂ) := funext hFr
  have hrc : Continuous r := by
    have : Continuous fun y => (F y).re := Complex.continuous_re.comp hFc
    refine this.congr fun y => ?_
    simp only [hFr y, Complex.ofReal_re]
  have hrs : HasCompactSupport r := by
    refine hFs.mono fun y hy => ?_
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h; exact hy (by exact_mod_cast (hFr y).symm.trans h)
  simp only [hFeq]
  rw [integral_complex_ofReal]
  norm_cast
  refine ((integral_pos_iff_support_of_nonneg (μ := haarGL K) (f := r) hr0
    (hrc.integrable_of_hasCompactSupport hrs)).2 ?_).ne'
  refine (hrc.isOpen_support).measure_pos (haarGL K) ⟨1, ?_⟩
  simp only [Function.mem_support, ne_eq]
  intro h; apply hF1; rw [hFr 1, h, Complex.ofReal_zero]

private theorem integral_norm_normalised_le {F : AdelicGL2 (𝓞 K) K → ℂ}
    (hFre : ∀ y, ∃ r : ℝ, 0 ≤ r ∧ F y = r) (hI : ∫ y, F y ∂(haarGL K) ≠ 0) :
    ∫ y, ‖(∫ z, F z ∂(haarGL K))⁻¹ * F y‖ ∂(haarGL K) ≤ 2 := by
  choose r hr0 hFr using hFre
  have hFeq : F = fun y => ((r y : ℝ) : ℂ) := funext hFr
  subst hFeq
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr0 _)]
  rw [integral_const_mul, integral_complex_ofReal, Complex.norm_real]
  by_cases hint : Integrable r (haarGL K)
  · have hpos : 0 < ∫ y, r y ∂(haarGL K) := by
      rcases (integral_nonneg (μ := haarGL K) (f := r) hr0).lt_or_eq with h | h
      · exact h
      · exfalso; apply hI; beta_reduce; rw [integral_complex_ofReal, ← h, Complex.ofReal_zero]
    rw [Real.norm_of_nonneg hpos.le, inv_mul_cancel₀ hpos.ne']
    norm_num
  · rw [integral_undef hint]; simp

private theorem exists_kernel_of_levelInvariant {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) {R' : AdelicGL2 (𝓞 K) K → ℂ}
    (hlev : ∀ u ∈ finiteLevelOne (𝓞 K) K N, ∀ z, R' (z * finEmbed (𝓞 K) K u) = R' z)
    {V : Set (AdelicGL2 (𝓞 K) K)} (hV : V ∈ nhds (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      (IsFactorizableTestFn K f ∧ Continuous f ∧ HasCompactSupport f) ∧
      (∀ y, f y ≠ 0 → ∃ y' ∈ V, (fun z => R' (z * y)) = fun z => R' (z * y')) ∧
      ∫ y, f y ∂(haarGL K) = 1 ∧ ∫ y, ‖f y‖ ∂(haarGL K) ≤ 2 := by
  obtain ⟨F, hker, hFc, hFs, hFre, hF1, hFsupp⟩ := exists_isSmoothingKernel_of_mem_nhds_one hN hV
  have hI : ∫ y, F y ∂(haarGL K) ≠ 0 := integral_ne_zero_of_nonneg_of_apply_one_ne_zero hFc hFs hFre hF1
  refine ⟨fun y => (∫ z, F z ∂(haarGL K))⁻¹ * F y, ⟨?_, continuous_const.mul hFc, hFs.mul_left⟩,
    fun y hy => ?_, ?_, integral_norm_normalised_le hFre hI⟩
  · exact isFactorizableTestFn_const_mul (isFactorizableTestFn_of_isSmoothingKernel K hker) _
  · have hFy : F y ≠ 0 := fun h => hy (by simp only [h, mul_zero])
    obtain ⟨u, hu, hyV⟩ := hFsupp y hFy
    obtain ⟨-, -, -, fa, -, hFeq⟩ := hker
    have hyfin : glFin (𝓞 K) K y ∈ finiteLevelOne (𝓞 K) K N := by
      by_contra h
      exact hFy (by rw [hFeq y, if_neg h, mul_zero])
    refine ⟨(finEmbed (𝓞 K) K u)⁻¹ * y, hyV, funext fun z => ?_⟩

    have hb : glFin (𝓞 K) K ((finEmbed (𝓞 K) K u)⁻¹ * y) ∈ finiteLevelOne (𝓞 K) K N := by
      rw [map_mul, map_inv, glFin_finEmbed]
      exact mul_mem (inv_mem hu) hyfin
    have hsplit : y = (finEmbed (𝓞 K) K u)⁻¹ * y *
        finEmbed (𝓞 K) K ((glFin (𝓞 K) K ((finEmbed (𝓞 K) K u)⁻¹ * y))⁻¹ * u *
          glFin (𝓞 K) K ((finEmbed (𝓞 K) K u)⁻¹ * y)) := by
      apply adelicGL2_ext
      · simp only [map_mul, map_inv, glArch_finEmbed, inv_one, one_mul, mul_one]
      · intro w
        simp only [map_mul, map_inv, glFin_finEmbed]
        group
    show R' (z * y) = R' (z * ((finEmbed (𝓞 K) K u)⁻¹ * y))
    conv_lhs => rw [hsplit]
    rw [← mul_assoc]
    exact hlev _ (mul_mem (mul_mem (inv_mem hb) hu) hb) _
  · rw [integral_const_mul, inv_mul_cancel₀ hI]

end KernelAdapter

end WeakPassage

namespace WeakPassage

section MassAdapter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem eLpNorm_two_pow_two (f : α → ℂ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, one_div,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat, inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one]
  congr 1; funext x
  rw [← ENNReal.rpow_natCast, enorm_eq_nnnorm]; norm_num

private theorem memLp_of_lintegral_ne_top [TopologicalSpace α] [OpensMeasurableSpace α] {f : α → ℂ}
    (hf : Continuous f) {D : Set α} (hD : (∫⁻ x in D, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≠ ⊤) : MemLp f 2 (μ.restrict D) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [lt_top_iff_ne_top]
  intro htop
  apply hD
  rw [← eLpNorm_two_pow_two, htop, ENNReal.top_pow two_ne_zero]

private theorem lintegral_ne_top_of_memLp {f : α → ℂ} {D : Set α} (hf : MemLp f 2 (μ.restrict D)) :
    (∫⁻ x in D, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≠ ⊤ := by
  rw [← eLpNorm_two_pow_two]
  exact ENNReal.pow_ne_top hf.eLpNorm_ne_top

private theorem integral_norm_sq_eq_toReal [TopologicalSpace α] [OpensMeasurableSpace α] {f : α → ℂ}
    (hf : Continuous f) (D : Set α) :
    ∫ x in D, ‖f x‖ ^ 2 ∂μ = (∫⁻ x in D, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    ((hf.norm.fun_pow 2).aestronglyMeasurable)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

end MassAdapter

variable (K : Type) [Field K] [NumberField K]

private theorem translates_memLp_and_bdd_of_mass_comparison {D : Set (AdelicGL2 (𝓞 K) K)}
    {Q : (AdelicGL2 (𝓞 K) K → ℂ) → Prop}
    (hcmp : ∀ B : Set (AdelicGL2 (𝓞 K) K), IsCompact B → ∃ N : ℝ, ∀ y ∈ B, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Q φ →
      Continuous φ → ∫⁻ x in D, (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K) ≤
        ENNReal.ofReal N * ∫⁻ x in D, (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K))
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hQ : Q φ) (hφc : Continuous φ) (hφ : MemLp φ 2 ((haarGL K).restrict D)) :
    (∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => φ (z * y)) 2 ((haarGL K).restrict D)) ∧
      ∀ B : Set (AdelicGL2 (𝓞 K) K), IsCompact B → ∃ C : ℝ, 0 ≤ C ∧
        ∀ y ∈ B, ∫ z in D, ‖φ (z * y)‖ ^ 2 ∂(haarGL K) ≤ C := by
  have hmass := lintegral_ne_top_of_memLp hφ
  have hbound : ∀ B : Set (AdelicGL2 (𝓞 K) K), IsCompact B → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ y ∈ B, ∫⁻ x in D, (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K) ≤ M := by
    intro B hB
    obtain ⟨N, hN⟩ := hcmp B hB
    exact ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmass, fun y hy => hN y hy φ hQ hφc⟩
  refine ⟨fun y => ?_, fun B hB => ?_⟩
  · obtain ⟨M, hM, hle⟩ := hbound {y} isCompact_singleton
    exact memLp_of_lintegral_ne_top (hφc.comp (continuous_mul_const y)) (ne_top_of_le_ne_top hM (hle y rfl))
  · obtain ⟨M, hM, hle⟩ := hbound B hB
    refine ⟨M.toReal, ENNReal.toReal_nonneg, fun y hy => ?_⟩
    rw [integral_norm_sq_eq_toReal (f := fun z => φ (z * y)) (hφc.comp (continuous_mul_const y))]
    exact ENNReal.toReal_mono hM (hle y hy)

private theorem memLp_sum_translates {D : Set (AdelicGL2 (𝓞 K) K)} {R : AdelicGL2 (𝓞 K) K → ℂ}
    (hRy : ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun z => R (z * y)) 2 ((haarGL K).restrict D))
    (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) :
    MemLp (fun g => ∑ h ∈ s, l h * R (g * h)) 2 ((haarGL K).restrict D) :=
  memLp_finsetSum s fun h _ => (hRy h).const_mul (l h)

end WeakPassage

end PASSAGEweak

section Holes

variable {K : Type} [Field K] [NumberField K]

private abbrev plainW (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂

private abbrev ampleW (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ

private abbrev pinsW (W : Set (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K W (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K)

private abbrev massW (W : Set (AdelicGL2 (𝓞 K) K)) (R R' : AdelicGL2 (𝓞 K) K → ℂ) (s : Finset (AdelicGL2 (𝓞 K) K))
    (l : AdelicGL2 (𝓞 K) K → ℂ) : ℝ≥0∞ :=
  ∫⁻ y in W, (‖R' y - ∑ h ∈ s, l h * R (y * h)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)

private abbrev ApproxW (W : Set (AdelicGL2 (𝓞 K) K)) (R R' : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ), massW W R R' s l < ε

private theorem pos_of_coversModCentre (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hcov : CoversModCentre K (plainW c u d₁ d₂ T)) : 0 < d₂ := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨γ, z, hmem⟩ := hcov 1
  obtain ⟨x, -, g, hg, -⟩ := Set.mem_iUnion₂.mp hmem
  exact lt_of_lt_of_le (archDetNorm_pos w g) (((mem_centreCutSiegelSet_iff (F := K)).mp hg).2.2.2 w).2

private theorem plainW_mono_lower (c u d₁ d₁' d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (h : d₁ ≤ d₁') :
    plainW c u d₁' d₂ T ⊆ plainW c u d₁ d₂ T := by
  refine Set.iUnion₂_mono fun x _ => Set.image_mono fun g hg => ?_
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (mem_centreCutSiegelSet_iff (F := K)).mp hg
  exact (mem_centreCutSiegelSet_iff (F := K)).mpr ⟨h₁, h₂, h₃, fun w => ⟨le_trans h (h₄ w).1, (h₄ w).2⟩⟩

private theorem plainW_mono_unipotent (c u u' d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (h : |u| ≤ u') :
    plainW c u d₁ d₂ T ⊆ plainW c u' d₁ d₂ T := by
  refine Set.iUnion₂_mono fun x _ => Set.image_mono fun g hg => ?_
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (mem_centreCutSiegelSet_iff (F := K)).mp hg
  have hu : u ^ 2 ≤ u' ^ 2 := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
  exact (mem_centreCutSiegelSet_iff (F := K)).mpr ⟨h₁, h₂, fun w => le_trans (h₃ w) hu, h₄⟩

private theorem ampleW_subset_plainW (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ampleW c u d₁ d₂ κ T ⊆ plainW c u d₁ d₂ T :=
  Set.iUnion₂_mono fun _ _ => Set.image_mono (centreCutSiegelSetAmple_subset (F := K) c u d₁ d₂ κ)

private theorem ApproxW.mono {W W' : Set (AdelicGL2 (𝓞 K) K)} (h : W ⊆ W') {R R' : AdelicGL2 (𝓞 K) K → ℂ}
    (hW' : ApproxW W' R R') : ApproxW W R R' := fun ε hε =>
  let ⟨s, l, hsl⟩ := hW' ε hε
  ⟨s, l, lt_of_le_of_lt (lintegral_mono_set h) hsl⟩

private def IsCoveringParameter (K : Type) [Field K] [NumberField K] (u : ℝ) : Prop :=
  ∀ x : (w : InfinitePlace K) → w.Completion, ∃ ξ : 𝓞 K, ∀ w : InfinitePlace K,
    ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ u

private theorem IsCoveringParameter.mono {u u' : ℝ} (h : IsCoveringParameter K u) (huu' : u ≤ u') :
    IsCoveringParameter K u' := by
  intro x
  obtain ⟨ξ, hξ⟩ := h x
  exact ⟨ξ, fun w => (hξ w).trans huu'⟩

section SoftVolScope

open NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm AutomorphicForm.SmoothCusp AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open scoped ENNReal ProbabilityTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm IsDedekindDomain Filter Topology"

attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel

namespace FundamentalDomainSlab

open scoped Pointwise ENNReal

section FDAction

variable {H α : Type*} [Group H] [MulAction H α] [MeasurableSpace α] [MeasurableConstSMul H α]
  [Countable H] {ν : Measure α} [SMulInvariantMeasure H α ν]

private theorem setLIntegral_fd_le_of_cover {S E : Set α} (hS : IsFundamentalDomain H S ν)
    (hcov : S ⊆ ⋃ γ : H, (γ • ·) ⁻¹' E) (F : α → ℝ≥0∞) (hF : ∀ (γ : H) (w : α), F (γ • w) = F w) :
    ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in E, F w ∂ν := by
  calc ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in ⋃ γ : H, S ∩ (γ • ·) ⁻¹' E, F w ∂ν := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp (hcov hw)
        exact Set.mem_iUnion.mpr ⟨γ, hw, hγ⟩
    _ ≤ ∑' γ : H, ∫⁻ w in S ∩ (γ • ·) ⁻¹' E, F w ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : H, ∫⁻ w in γ • S ∩ E, F w ∂ν := by
        refine tsum_congr fun γ => ?_
        have hpre : (fun w : α => γ • w) ⁻¹' (γ • S ∩ E) = S ∩ (γ • ·) ⁻¹' E := by
          rw [Set.preimage_inter, Set.preimage_smul, inv_smul_smul]
        rw [← (measurePreserving_smul γ ν).setLIntegral_comp_preimage_emb
          (measurableEmbedding_const_smul γ) F (γ • S ∩ E), hpre]
        simp_rw [hF]
    _ = ∫⁻ w in E, F w ∂ν := by
        rw [hS.setLIntegral_eq_tsum F E]
        exact tsum_congr fun γ => by rw [Set.inter_comm]

end FDAction

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

private theorem smulInvariantMeasure_restrict (Γ : Subgroup G) [MeasurableConstSMul ↥Γ G]
    (μ : Measure G) [SMulInvariantMeasure ↥Γ G μ] {T : Set G} (hT : MeasurableSet T)
    (hΓT : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' T = T) :
    SMulInvariantMeasure ↥Γ G (μ.restrict T) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓT γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hT)

variable [MeasurableMul G]

private theorem isFundamentalDomain_image_mul_right (Γ : Subgroup G) (μ : Measure G)
    [μ.IsMulRightInvariant] {S T T' : Set G} (hS : IsFundamentalDomain ↥Γ S (μ.restrict T))
    (g : G) (hTT' : (fun w : G => w * g⁻¹) ⁻¹' T = T') :
    IsFundamentalDomain ↥Γ ((fun w : G => w * g) '' S) (μ.restrict T') := by
  have hmp : MeasurePreserving (fun w : G => w * g⁻¹) (μ.restrict T') (μ.restrict T) := by
    rw [← hTT']
    exact (measurePreserving_mul_right μ g⁻¹).restrict_preimage_emb (measurableEmbedding_mulRight g⁻¹) T
  have h := hS.image_of_equiv (ν := μ.restrict T') (Equiv.mulRight g)
    (by simpa using hmp.quasiMeasurePreserving) (Equiv.refl _)
    (fun γ w => show (γ : G) * w * g = (γ : G) * (w * g) from mul_assoc _ _ _)
  simpa using h

private theorem setLIntegral_biUnion_translates_le (μ : Measure G) [μ.IsMulLeftInvariant]
    {D : Set G} (F : G → ℝ≥0∞) {ι : Type*} (I : Finset ι) (b : ι → G) (k : ι → ℝ≥0∞)
    (hk : ∀ i, k i ≠ ∞) (hFb : ∀ (i : ι) (w : G), F (b i * w) = k i * F w) :
    ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ ≤ ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := by
  have hpiece : ∀ i, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ = k i * ∫⁻ w in D, F w ∂μ := by
    intro i
    rw [← (measurePreserving_mul_left μ (b i)).setLIntegral_comp_emb (measurableEmbedding_mulLeft (b i)) F D]
    simp_rw [hFb]
    exact lintegral_const_mul' (k i) _ (hk i)
  calc ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ
      ≤ ∫⁻ w in ⋃ i : ↥I, (fun w => b i * w) '' D, F w ∂μ := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hw⟩
    _ ≤ ∑' i : ↥I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := by
        rw [tsum_fintype, Finset.sum_coe_sort I fun i => ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ]
    _ = ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := Finset.sum_congr rfl fun i _ => hpiece i

private theorem memLp_comp_mul_right (μ : Measure G) [μ.IsMulRightInvariant] {S : Set G}
    {f : G → ℂ} (h : G) (hf : MemLp f 2 (μ.restrict ((fun w => w * h) '' S))) :
    MemLp (fun z => f (z * h)) 2 (μ.restrict S) :=
  hf.comp_measurePreserving
    ((measurePreserving_mul_right μ h).restrict_image_emb (measurableEmbedding_mulRight h) S)

end Group

section Pairing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem memLp_two_of_lintegral {f : α → ℂ} (h1 : AEStronglyMeasurable f μ)
    (h2 : ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞) : MemLp f 2 μ := by
  refine ⟨h1, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mpr ?_⟩
  simpa only [ENNReal.toReal_ofNat] using h2

private theorem lintegral_lt_top_of_memLp_two {f : α → ℂ} (hf : MemLp f 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mp hf.2
  simpa only [ENNReal.toReal_ofNat] using h

end Pairing

end FundamentalDomainSlab

section
variable (K)

namespace CompactSlabComparison

open FundamentalDomainSlab NumberField.TateGlobal

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

variable {K}

private abbrev detNorm (g : AdelicGL2 (𝓞 K) K) : ℝ :=
  NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)

variable (K) in

private abbrev detSlab (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

variable (K) in

private abbrev haarGL : Measure (AdelicGL2 (𝓞 K) K) :=
  adelicGLHaar (Fin 2) (𝓞 K) K

variable (K) in

private abbrev rationalPoints : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (globalPoints (𝓞 K) K).range

private scoped instance instCountableField : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

private scoped instance instCountableRationalPoints : Countable ↥(rationalPoints K) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (GL (Fin 2) K) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable

private theorem detNorm_pos (g : AdelicGL2 (𝓞 K) K) : 0 < detNorm g := ideleNorm_pos _

private theorem detNorm_mul (g h : AdelicGL2 (𝓞 K) K) : detNorm (g * h) = detNorm g * detNorm h := by
  show ideleNorm K _ = _
  rw [map_mul, ideleNorm_mul]

private theorem detNorm_globalPoints_mul (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    detNorm (globalPoints (𝓞 K) K γ * g) = detNorm g := by
  rw [detNorm_mul]
  show ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)) * detNorm g = detNorm g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

private theorem detNorm_subtype_mul (γ : ↥(rationalPoints K)) (g : AdelicGL2 (𝓞 K) K) :
    detNorm ((γ : AdelicGL2 (𝓞 K) K) * g) = detNorm g := by
  obtain ⟨_, γ', rfl⟩ := γ
  exact detNorm_globalPoints_mul γ' g

private theorem detNorm_one : detNorm (1 : AdelicGL2 (𝓞 K) K) = 1 := by
  show ideleNorm K (Matrix.GeneralLinearGroup.det 1) = 1
  rw [map_one]
  unfold ideleNorm
  rw [map_one, NNReal.coe_one]

private theorem detNorm_inv (g : AdelicGL2 (𝓞 K) K) : detNorm g⁻¹ = (detNorm g)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← detNorm_mul, mul_inv_cancel, detNorm_one])

private theorem subtype_mul_mem_detSlab (γ : ↥(rationalPoints K)) {a b : ℝ} {g : AdelicGL2 (𝓞 K) K}
    (hg : g ∈ detSlab K a b) : (γ : AdelicGL2 (𝓞 K) K) * g ∈ detSlab K a b := by
  show detNorm ((γ : AdelicGL2 (𝓞 K) K) * g) ∈ Set.Icc a b
  rw [detNorm_subtype_mul]
  exact hg

private theorem measurableSet_detSlab (a b : ℝ) : MeasurableSet (detSlab K a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K a b

private theorem preimage_subtype_mul_detSlab (γ : ↥(rationalPoints K)) (a b : ℝ) :
    (fun w : AdelicGL2 (𝓞 K) K => (γ : AdelicGL2 (𝓞 K) K) * w) ⁻¹' detSlab K a b = detSlab K a b := by
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [show ideleNorm K (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 K) K) * w)) = detNorm w from
    detNorm_subtype_mul γ w]

private theorem preimage_mul_right_detSlab (g : AdelicGL2 (𝓞 K) K) {a b : ℝ} :
    (fun w : AdelicGL2 (𝓞 K) K => w * g⁻¹) ⁻¹' detSlab K a b = detSlab K (a * detNorm g) (b * detNorm g) := by
  ext w
  have h1 : ideleNorm K (Matrix.GeneralLinearGroup.det (w * g⁻¹)) = detNorm w / detNorm g := by
    rw [div_eq_mul_inv, ← detNorm_inv g]
    exact detNorm_mul w g⁻¹
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
  rw [h1, le_div_iff₀ (detNorm_pos g), div_le_iff₀ (detNorm_pos g)]

private theorem image_mul_right_subset_detSlab {S : Set (AdelicGL2 (𝓞 K) K)} {a b : ℝ} (hS : S ⊆ detSlab K a b)
    (g : AdelicGL2 (𝓞 K) K) : (fun w => w * g) '' S ⊆ detSlab K (a * detNorm g) (b * detNorm g) := by
  rintro _ ⟨w, hw, rfl⟩
  have h := hS hw
  show detNorm (w * g) ∈ Set.Icc (a * detNorm g) (b * detNorm g)
  rw [detNorm_mul]
  exact ⟨mul_le_mul_of_nonneg_right h.1 (detNorm_pos g).le, mul_le_mul_of_nonneg_right h.2 (detNorm_pos g).le⟩

private theorem smulInvariantMeasure_detSlab (a b : ℝ) :
    SMulInvariantMeasure ↥(rationalPoints K) (AdelicGL2 (𝓞 K) K) ((haarGL K).restrict (detSlab K a b)) :=
  smulInvariantMeasure_restrict (rationalPoints K) (haarGL K) (measurableSet_detSlab a b)
    (fun γ => preimage_subtype_mul_detSlab γ a b)

private def IsCoveredBy (D : Set (AdelicGL2 (𝓞 K) K)) (N : Finset (AdeleRing (𝓞 K) K)ˣ)
    (X : Set (AdelicGL2 (𝓞 K) K)) : Prop :=
  ∀ g ∈ X, ∃ γ : GL (Fin 2) K, ∃ n ∈ N,
    (centralScalar (𝓞 K) K n)⁻¹ * (globalPoints (𝓞 K) K γ * g) ∈ D

private theorem isCoveredBy_detSlab_of_forall {D : Set (AdelicGL2 (𝓞 K) K)} {a b : ℝ}
    {N : Finset (AdeleRing (𝓞 K) K)ˣ}
    (h : ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) K, ∃ n ∈ N,
          globalPoints (𝓞 K) K γ * g ∈ (· * centralScalar (𝓞 K) K n) '' D) :
    IsCoveredBy D N (detSlab K a b) := by
  intro g hg
  obtain ⟨γ, n, hn, y, hy, hyn⟩ := h g hg
  refine ⟨γ, n, hn, ?_⟩
  rw [← hyn]
  show (centralScalar (𝓞 K) K n)⁻¹ * (y * centralScalar (𝓞 K) K n) ∈ D
  rw [mul_centralScalar_comm n y, inv_mul_cancel_left]
  exact hy

private theorem memLp_of_isCoveredBy {D S : Set (AdelicGL2 (𝓞 K) K)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 K) K)ˣ}
    {f : AdelicGL2 (𝓞 K) K → ℂ} {χ : (AdeleRing (𝓞 K) K)ˣ → ℂ} (hf : Continuous f)
    (hmem : MemLp f 2 ((haarGL K).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) K) (w : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (w : AdelicGL2 (𝓞 K) K), f (centralScalar (𝓞 K) K n * w) = χ n * f w)
    (hS : IsFundamentalDomain ↥(rationalPoints K) S ((haarGL K).restrict (detSlab K a b))) (hSs : S ⊆ detSlab K a b)
    (hX : IsCoveredBy D N (detSlab K a b)) : MemLp f 2 ((haarGL K).restrict S) := by
  have hcov' : ∀ g ∈ detSlab K a b, ∃ γ : ↥(rationalPoints K), ∃ n ∈ N,
      (centralScalar (𝓞 K) K n)⁻¹ * ((γ : AdelicGL2 (𝓞 K) K) * g) ∈ D := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g hg
    exact ⟨⟨globalPoints (𝓞 K) K γ, γ, rfl⟩, n, hn, h⟩
  have h2 : ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) < ∞ := by
    haveI := smulInvariantMeasure_detSlab (K := K) a b
    have hcovE : S ⊆ ⋃ γ : ↥(rationalPoints K), (γ • ·) ⁻¹'
        ((⋃ n ∈ N, (fun w => centralScalar (𝓞 K) K n * w) '' D) ∩ detSlab K a b) := fun g hg => by
      obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
      refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨n, hn, _, h, mul_inv_cancel_left _ _⟩, ?_⟩
      exact subtype_mul_mem_detSlab γ (hSs hg)
    have hF : ∀ (γ : ↥(rationalPoints K)) (w : AdelicGL2 (𝓞 K) K), ‖f (γ • w)‖ₑ ^ (2 : ℝ) = ‖f w‖ₑ ^ (2 : ℝ) := by
      rintro ⟨_, γ, rfl⟩ w
      show ‖f (globalPoints (𝓞 K) K γ * w)‖ₑ ^ (2 : ℝ) = _
      rw [hΓ]
    have hD : ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) < ∞ := lintegral_lt_top_of_memLp_two hmem
    calc ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K)
        = ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂((haarGL K).restrict (detSlab K a b)) := by
          rw [Measure.restrict_restrict_of_subset hSs]
      _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 K) K n * w) '' D) ∩ detSlab K a b,
            ‖f w‖ₑ ^ (2 : ℝ) ∂((haarGL K).restrict (detSlab K a b)) :=
          setLIntegral_fd_le_of_cover hS hcovE _ hF
      _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 K) K n * w) '' D, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) :=
          lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
      _ ≤ ∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) :=
          setLIntegral_biUnion_translates_le (haarGL K) _ N (fun n => centralScalar (𝓞 K) K n)
            (fun n => ‖χ n‖ₑ ^ (2 : ℝ)) (fun n => ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
            (fun n w => by rw [hZ, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)])
      _ < ∞ := by
          refine ENNReal.sum_lt_top.mpr fun n _ => ENNReal.mul_lt_top ?_ hD
          exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
  exact memLp_two_of_lintegral hf.aestronglyMeasurable h2

private theorem memLp_translate_of_cover [(haarGL K).IsMulRightInvariant] {D S : Set (AdelicGL2 (𝓞 K) K)}
    {α β : ℝ} (hα : 0 < α) {f : AdelicGL2 (𝓞 K) K → ℂ} {χ : (AdeleRing (𝓞 K) K)ˣ → ℂ} (hf : Continuous f)
    (hmem : MemLp f 2 ((haarGL K).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) K) (w : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (w : AdelicGL2 (𝓞 K) K), f (centralScalar (𝓞 K) K n * w) = χ n * f w)
    (hS : IsFundamentalDomain ↥(rationalPoints K) S ((haarGL K).restrict (detSlab K α β))) (hSs : S ⊆ detSlab K α β)
    (hcov : ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 K) K)ˣ, IsCoveredBy D N (detSlab K a b))
    (h : AdelicGL2 (𝓞 K) K) : MemLp (fun z => f (z * h)) 2 ((haarGL K).restrict S) := by
  obtain ⟨N, hN⟩ := hcov (α * detNorm h) (β * detNorm h) (mul_pos hα (detNorm_pos h))
  refine memLp_comp_mul_right (haarGL K) h ?_
  exact memLp_of_isCoveredBy hf hmem hΓ hZ
    (isFundamentalDomain_image_mul_right (rationalPoints K) (haarGL K) hS h (preimage_mul_right_detSlab h))
    (image_mul_right_subset_detSlab hSs h) hN

private def centralValue {D : Set (AdelicGL2 (𝓞 K) K)} {U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)}
    {gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K} {B : Set (AdeleRing (𝓞 K) K)}
    {Φ : HeckeEigensystem K ℂ} (R : SmoothCuspRealizationAt K (productionPinsOf K D U gen B) Φ)
    (n : (AdeleRing (𝓞 K) K)ˣ) : ℂ :=
  ((R.centralChar ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)

private theorem realization_laws {D : Set (AdelicGL2 (𝓞 K) K)} {U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)}
    {gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K} {B : Set (AdeleRing (𝓞 K) K)}
    {Φ : HeckeEigensystem K ℂ} (R : SmoothCuspRealizationAt K (productionPinsOf K D U gen B) Φ) :
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), R.toFun (globalPoints (𝓞 K) K γ * g) = R.toFun g) ∧
    (∀ (n : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      R.toFun (centralScalar (𝓞 K) K n * g) = centralValue R n * R.toFun g) ∧
    MemLp R.toFun 2 ((haarGL K).restrict D) := by
  have h : LsXiMemberAt (𝓞 K) K (haarGL K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) R.centralChar D R.toFun :=
    R.smoothCusp.1.1
  rw [lsXiMemberAt_iff] at h
  exact ⟨h.1.left_invariant, fun n g => h.1.central_transform ⟨n, Subgroup.mem_top n⟩ g, h.2⟩

end CompactSlabComparison
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

open CompactSlabComparison FundamentalDomainSlab in
private theorem lintegral_enorm_sq_le_of_isCoveredBy {D S : Set (AdelicGL2 (𝓞 K) K)} {a b : ℝ}
    {N : Finset (AdeleRing (𝓞 K) K)ˣ} {f : AdelicGL2 (𝓞 K) K → ℂ} {χ : (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hΓ : ∀ (γ : GL (Fin 2) K) (w : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (w : AdelicGL2 (𝓞 K) K), f (centralScalar (𝓞 K) K n * w) = χ n * f w)
    (hS : IsFundamentalDomain ↥(rationalPoints K) S ((haarGL K).restrict (detSlab K a b))) (hSs : S ⊆ detSlab K a b)
    (hX : IsCoveredBy D N (detSlab K a b)) :
    ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K)
      ≤ (∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ)) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) := by
  haveI := smulInvariantMeasure_detSlab (K := K) a b
  have hcovE : S ⊆ ⋃ γ : ↥(rationalPoints K), (γ • ·) ⁻¹'
      ((⋃ n ∈ N, (fun w => centralScalar (𝓞 K) K n * w) '' D) ∩ detSlab K a b) := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g (hSs hg)
    refine Set.mem_iUnion.mpr ⟨⟨globalPoints (𝓞 K) K γ, γ, rfl⟩, Set.mem_iUnion₂.mpr ⟨n, hn, _, h, ?_⟩, ?_⟩
    · exact mul_inv_cancel_left _ _
    · exact subtype_mul_mem_detSlab ⟨globalPoints (𝓞 K) K γ, γ, rfl⟩ (hSs hg)
  have hF : ∀ (γ : ↥(rationalPoints K)) (w : AdelicGL2 (𝓞 K) K), ‖f (γ • w)‖ₑ ^ (2 : ℝ) = ‖f w‖ₑ ^ (2 : ℝ) := by
    rintro ⟨_, γ, rfl⟩ w
    show ‖f (globalPoints (𝓞 K) K γ * w)‖ₑ ^ (2 : ℝ) = _
    rw [hΓ]
  calc ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K)
      = ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂((haarGL K).restrict (detSlab K a b)) := by
        rw [Measure.restrict_restrict_of_subset hSs]
    _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 K) K n * w) '' D) ∩ detSlab K a b,
          ‖f w‖ₑ ^ (2 : ℝ) ∂((haarGL K).restrict (detSlab K a b)) :=
        setLIntegral_fd_le_of_cover hS hcovE _ hF
    _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 K) K n * w) '' D, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
    _ ≤ ∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) :=
        setLIntegral_biUnion_translates_le (haarGL K) _ N (fun n => centralScalar (𝓞 K) K n)
          (fun n => ‖χ n‖ₑ ^ (2 : ℝ)) (fun n => ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
          (fun n w => by rw [hZ, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)])
    _ = (∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ)) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(haarGL K) := by
        rw [Finset.sum_mul]

section

open scoped ProbabilityTheory

private theorem integrable_constantTermIntegrand_of_continuous {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (g : AdelicGL2 (𝓞 K) K) :
    Integrable (constantTermIntegrand unipotentGL2 f g) ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) := by
  haveI : IsProbabilityMeasure ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) := isProbabilityMeasure_cond_adelicBox K
  obtain ⟨C₀, hC₀, hbox⟩ := exists_isCompact_adelicBox_subset K
  have hcont : Continuous (constantTermIntegrand unipotentGL2 f g) :=
    hf.comp (continuous_unipotentGL2.mul continuous_const)
  obtain ⟨M, hM⟩ := hC₀.exists_bound_of_continuousOn hcont.continuousOn
  refine (integrable_const M).mono' hcont.aestronglyMeasurable ?_
  exact (ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox K)).mono fun x hx => hM x (hbox hx)

private theorem isCuspidalFn_sub {φ₁ φ₂ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (hc₁ : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ₁)
    (hc₂ : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ₂) :
    IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 (fun z => φ₁ z - φ₂ z) := by
  intro g
  have e₁ := hc₁ g
  have e₂ := hc₂ g
  simp only [constantTerm] at e₁ e₂ ⊢
  have hsub : constantTermIntegrand unipotentGL2 (fun z => φ₁ z - φ₂ z) g =
      fun q => constantTermIntegrand unipotentGL2 φ₁ g q - constantTermIntegrand unipotentGL2 φ₂ g q := rfl
  rw [hsub, integral_sub (integrable_constantTermIntegrand_of_continuous h₁ g)
    (integrable_constantTermIntegrand_of_continuous h₂ g), e₁, e₂, sub_zero]

private theorem rightConv_sub_apply {φ₁ φ₂ F : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (hFc : Continuous F) (hFs : HasCompactSupport F) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K (fun z => φ₁ z - φ₂ z) F g = rightConv K φ₁ F g - rightConv K φ₂ F g := by
  simp only [rightConv_apply, sub_mul]
  refine integral_sub ?_ ?_
  · exact ((h₁.comp (continuous_const.mul continuous_id)).mul hFc).integrable_of_hasCompactSupport hFs.mul_left
  · exact ((h₂.comp (continuous_const.mul continuous_id)).mul hFc).integrable_of_hasCompactSupport hFs.mul_left

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section SumTranslates

open scoped ProbabilityTheory

private theorem sumTranslates_globalPoints_mul {R : AdelicGL2 (𝓞 K) K → ℂ}
    (hΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), R (globalPoints (𝓞 K) K γ * g) = R g)
    (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    ∑ h ∈ s, l h * R (globalPoints (𝓞 K) K γ * g * h) = ∑ h ∈ s, l h * R (g * h) :=
  Finset.sum_congr rfl fun h _ => by rw [mul_assoc, hΓ]

private theorem sumTranslates_centralScalar_mul {R : AdelicGL2 (𝓞 K) K → ℂ} {χ : (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hZ : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), R (centralScalar (𝓞 K) K n * g) = χ n * R g)
    (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) (n : (AdeleRing (𝓞 K) K)ˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    ∑ h ∈ s, l h * R (centralScalar (𝓞 K) K n * g * h) = χ n * ∑ h ∈ s, l h * R (g * h) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by rw [mul_assoc, hZ]; ring

private theorem continuous_sumTranslates {R : AdelicGL2 (𝓞 K) K → ℂ} (hR : Continuous R)
    (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) :
    Continuous fun g : AdelicGL2 (𝓞 K) K => ∑ h ∈ s, l h * R (g * h) :=
  continuous_finsetSum s fun h _ => continuous_const.mul (hR.comp (continuous_mul_const h))

private theorem isCuspidalFn_sumTranslates {R : AdelicGL2 (𝓞 K) K → ℂ} (hRc : Continuous R)
    (hcusp : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 R)
    (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) :
    IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2
      fun g : AdelicGL2 (𝓞 K) K => ∑ h ∈ s, l h * R (g * h) := by
  intro g
  have hint : ∀ h ∈ s, Integrable (fun q => l h * constantTermIntegrand unipotentGL2 R (g * h) q)
      ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) :=
    fun h _ => (integrable_constantTermIntegrand_of_continuous hRc (g * h)).const_mul (l h)
  have hfun : constantTermIntegrand unipotentGL2 (fun g : AdelicGL2 (𝓞 K) K => ∑ h ∈ s, l h * R (g * h)) g =
      fun q => ∑ h ∈ s, l h * constantTermIntegrand unipotentGL2 R (g * h) q := by
    funext q
    simp only [constantTermIntegrand, mul_assoc]
  simp only [constantTerm] at hcusp ⊢
  rw [hfun, integral_finsetSum s hint]
  refine Finset.sum_eq_zero fun h _ => ?_
  have hz := hcusp (g * h)
  unfold constantTerm at hz
  rw [integral_const_mul, hz, mul_zero]

end SumTranslates
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

open CompactSlabComparison FundamentalDomainSlab in

private theorem memLp_sumTranslates_of_cover [(haarGL K).IsMulRightInvariant] {D S : Set (AdelicGL2 (𝓞 K) K)}
    {α β : ℝ} (hα : 0 < α) {R : AdelicGL2 (𝓞 K) K → ℂ} {χ : (AdeleRing (𝓞 K) K)ˣ → ℂ} (hRc : Continuous R)
    (hmem : MemLp R 2 ((haarGL K).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) K) (w : AdelicGL2 (𝓞 K) K), R (globalPoints (𝓞 K) K γ * w) = R w)
    (hZ : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (w : AdelicGL2 (𝓞 K) K), R (centralScalar (𝓞 K) K n * w) = χ n * R w)
    (hS : IsFundamentalDomain ↥(rationalPoints K) S ((haarGL K).restrict (detSlab K α β)))
    (hSs : S ⊆ detSlab K α β)
    (hcov : ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 K) K)ˣ, IsCoveredBy D N (detSlab K a b))
    (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) :
    MemLp (fun g : AdelicGL2 (𝓞 K) K => ∑ h ∈ s, l h * R (g * h)) 2 ((haarGL K).restrict S) :=
  memLp_finsetSum s fun h _ => (memLp_translate_of_cover hα hRc hmem hΓ hZ hS hSs hcov h).const_mul (l h)

private theorem eLpNorm_two_sq {X : Type*} [MeasurableSpace X] (μ : Measure X) (φ : X → ℂ) :
    eLpNorm φ 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖φ x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_mul]
  norm_num

private theorem coe_nnnorm_pow_two_eq (z : ℂ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ‖z‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, enorm_eq_nnnorm]

private theorem measure_plainW_lt_top [(adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant] (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    adelicGLHaar (Fin 2) (𝓞 K) K (plainW c u d₁ d₂ T) < ⊤ := by
  refine (measure_biUnion_finset_le (μ := adelicGLHaar (Fin 2) (𝓞 K) K) T _).trans_lt
    (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  rw [Set.image_mul_right, measure_preimage_mul_right]
  exact SiegelVolume.measure_centreCutSiegelSet_lt_top (adelicGLHaar (Fin 2) (𝓞 K) K) hc u hd₁ d₂

private theorem measurableSet_plainW (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    MeasurableSet (plainW c u d₁ d₂ T) :=
  T.measurableSet_biUnion fun x _ => by
    rw [Set.image_mul_right]
    exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const x⁻¹)

open CompactSlabComparison FundamentalDomainSlab in

private theorem memLp_rightConv_and_exists_forall_lintegral_rightConv_sub_le_mul_massW_ample
    (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (plainW c u d₁ d₂ T)) (hamp : CoversModCentre K (ampleW c u d₁ d₂ κ T))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ'.toRawCentral R')
    (hω : R.centralChar = R'.centralChar) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (hfc : Continuous f) (hfs : HasCompactSupport f) :
    MemLp (rightConv K R'.toFun f) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u d₁ d₂ T)) ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        MemLp (rightConv K (fun g => ∑ h ∈ s, l h * R.toFun (g * h)) f) 2
            ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u d₁ d₂ T)) ∧
          ∫⁻ y in plainW c u d₁ d₂ T,
              (‖rightConv K R'.toFun f y - rightConv K (fun g => ∑ h ∈ s, l h * R.toFun (g * h)) f y‖₊ : ℝ≥0∞) ^ 2
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
            C * massW (ampleW c u d₁ d₂ κ T) R.toFun R'.toFun s l := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  have _ := hcov

  obtain ⟨hRΓ, hRZ, hRD⟩ := realization_laws R
  obtain ⟨hR'Γ, hR'Z, hR'D⟩ := realization_laws R'
  have hRZ' : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      R.toFun (centralScalar (𝓞 K) K n * g) = centralValue R' n * R.toFun g := by
    intro n g
    rw [hRZ n g]
    simp only [centralValue, hω]
  have hRc : Continuous R.toFun := hR
  have hR'c : Continuous R'.toFun := hR'
  have hRcusp : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 R.toFun := R.smoothCusp.1.2
  have hR'cusp : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 R'.toFun :=
    R'.smoothCusp.1.2

  have hcovN :=
    exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple K c u d₁ d₂ κ T hd hamp
  have hsub : ampleW c u d₁ d₂ κ T ⊆ plainW c u d₁ d₂ T :=
    Set.iUnion₂_mono fun x _ => Set.image_mono (centreCutSiegelSetAmple_subset c u d₁ d₂ κ)
  have hcovP : ∀ a b : ℝ, 0 < a →
      ∃ N : Finset (AdeleRing (𝓞 K) K)ˣ, IsCoveredBy (plainW c u d₁ d₂ T) N (detSlab K a b) := by
    intro a b ha
    obtain ⟨N, hN⟩ := hcovN a b ha
    refine ⟨N, fun g hg => ?_⟩
    obtain ⟨γ, n, hn, h⟩ := isCoveredBy_detSlab_of_forall hN g hg
    exact ⟨γ, n, hn, hsub h⟩

  obtain ⟨S, hSs, hS⟩ := exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  obtain ⟨N, hN⟩ := hcovN 1 2 one_pos
  have hXamp : IsCoveredBy (ampleW c u d₁ d₂ κ T) N (detSlab K 1 2) := isCoveredBy_detSlab_of_forall hN
  obtain ⟨C₀, hC₀⟩ :=
    exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
      K R'.centralChar f hf c u d₁ d₂ T hc hd₁ 1 2 two_pos one_lt_two S hS
  have hvol := measure_plainW_lt_top c u d₁ d₂ T hc hd₁

  have hmass : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar φ →
      IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ → Continuous φ →
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S) →
      MemLp (rightConv K φ f) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u d₁ d₂ T)) ∧
        ∫⁻ y in plainW c u d₁ d₂ T, ‖rightConv K φ f y‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
          adelicGLHaar (Fin 2) (𝓞 K) K (plainW c u d₁ d₂ T) * (ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) *
            ∫⁻ w in S, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    intro φ hlsxi hcusp hφc hφS
    have hpt : ∀ y ∈ plainW c u d₁ d₂ T, ‖rightConv K φ f y‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) *
          ∫⁻ w in S, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      intro y hy
      have h1 := hC₀ φ hlsxi hcusp hφc hφS y hy
      have h2 : ‖rightConv K φ f y‖ₑ ≤ ENNReal.ofReal (max C₀ 0) *
          eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_toReal hφS.eLpNorm_ne_top,
          ← ENNReal.ofReal_mul (le_max_right _ _)]
        exact ENNReal.ofReal_le_ofReal (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg))
      calc ‖rightConv K φ f y‖ₑ ^ (2 : ℝ)
          ≤ (ENNReal.ofReal (max C₀ 0) * eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S)) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow h2 (by norm_num)
        _ = ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) * ∫⁻ w in S, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), eLpNorm_two_sq]
    have hint : ∫⁻ y in plainW c u d₁ d₂ T, ‖rightConv K φ f y‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
        adelicGLHaar (Fin 2) (𝓞 K) K (plainW c u d₁ d₂ T) * (ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) *
          ∫⁻ w in S, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
      refine (setLIntegral_mono' (measurableSet_plainW c u d₁ d₂ T) hpt).trans ?_
      rw [setLIntegral_const, mul_comm]
    refine ⟨?_, hint⟩
    have hconv : Continuous (rightConv K φ f) :=
      (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K φ hφc f hf).1
    refine memLp_two_of_lintegral hconv.aestronglyMeasurable (hint.trans_lt ?_)
    refine ENNReal.mul_lt_top hvol (ENNReal.mul_lt_top ?_ (lintegral_lt_top_of_memLp_two hφS))
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

  have hR'S : MemLp R'.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S) := by
    simpa using memLp_translate_of_cover one_pos hR'c hR'D hR'Γ hR'Z hS hSs hcovP 1
  have hR'lsxi : IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar R'.toFun := ⟨hR'Γ, fun z g => hR'Z z g⟩
  have huΓ : ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
      IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar fun g => ∑ h ∈ s, l h * R.toFun (g * h) :=
    fun s l => ⟨fun γ g => sumTranslates_globalPoints_mul hRΓ s l γ g,
      fun z g => sumTranslates_centralScalar_mul hRZ' s l z g⟩
  have huS : ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
      MemLp (fun g => ∑ h ∈ s, l h * R.toFun (g * h)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S) :=
    fun s l => memLp_sumTranslates_of_cover one_pos hRc hRD hRΓ hRZ' hS hSs hcovP s l
  refine ⟨(hmass R'.toFun hR'lsxi hR'cusp hR'c hR'S).1, adelicGLHaar (Fin 2) (𝓞 K) K (plainW c u d₁ d₂ T) *
    (ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) * ∑ n ∈ N, ‖centralValue R' n‖ₑ ^ (2 : ℝ)), ?_, fun s l => ?_⟩
  · refine ENNReal.mul_ne_top hvol.ne (ENNReal.mul_ne_top ?_ ?_)
    · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
    · exact (ENNReal.sum_lt_top.mpr fun n _ => ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top).ne
  have huc := continuous_sumTranslates hRc s l
  refine ⟨(hmass _ (huΓ s l) (isCuspidalFn_sumTranslates hRc hRcusp s l) huc (huS s l)).1, ?_⟩

  set φ : AdelicGL2 (𝓞 K) K → ℂ := fun z => R'.toFun z - ∑ h ∈ s, l h * R.toFun (z * h) with hφ
  have hφΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g := by
    intro γ g
    simp only [hφ, hR'Γ, sumTranslates_globalPoints_mul hRΓ]
  have hφZ : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      φ (centralScalar (𝓞 K) K n * g) = centralValue R' n * φ g := by
    intro n g
    simp only [hφ, hR'Z, sumTranslates_centralScalar_mul hRZ', mul_sub]
  have hφlsxi : IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar φ := ⟨hφΓ, fun z g => hφZ z g⟩
  have hφcusp : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ :=
    isCuspidalFn_sub hR'c huc hR'cusp (isCuspidalFn_sumTranslates hRc hRcusp s l)
  have hφc : Continuous φ := hR'c.sub huc
  have hφS : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S) := hR'S.sub (huS s l)
  have hφamp := lintegral_enorm_sq_le_of_isCoveredBy hφΓ hφZ hS hSs hXamp
  have hsplit : ∀ y : AdelicGL2 (𝓞 K) K,
      (‖rightConv K R'.toFun f y - rightConv K (fun g => ∑ h ∈ s, l h * R.toFun (g * h)) f y‖₊ : ℝ≥0∞) ^ 2 =
        ‖rightConv K φ f y‖ₑ ^ (2 : ℝ) := by
    intro y
    rw [coe_nnnorm_pow_two_eq, ← rightConv_sub_apply hR'c huc hfc hfs y]
  have hmassW : massW (ampleW c u d₁ d₂ κ T) R.toFun R'.toFun s l =
      ∫⁻ w in ampleW c u d₁ d₂ κ T, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    simp only [massW, hφ, coe_nnnorm_pow_two_eq]
  simp only [hsplit, hmassW]
  calc ∫⁻ y in plainW c u d₁ d₂ T, ‖rightConv K φ f y‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ adelicGLHaar (Fin 2) (𝓞 K) K (plainW c u d₁ d₂ T) * (ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) *
          ∫⁻ w in S, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := (hmass φ hφlsxi hφcusp hφc hφS).2
    _ ≤ adelicGLHaar (Fin 2) (𝓞 K) K (plainW c u d₁ d₂ T) * (ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) *
          ((∑ n ∈ N, ‖centralValue R' n‖ₑ ^ (2 : ℝ)) *
            ∫⁻ w in ampleW c u d₁ d₂ κ T, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) :=
        mul_le_mul_right (mul_le_mul_right hφamp _) _
    _ = adelicGLHaar (Fin 2) (𝓞 K) K (plainW c u d₁ d₂ T) *
          (ENNReal.ofReal (max C₀ 0) ^ (2 : ℝ) * ∑ n ∈ N, ‖centralValue R' n‖ₑ ^ (2 : ℝ)) *
            ∫⁻ w in ampleW c u d₁ d₂ κ T, ‖φ w‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        ring

end SoftVolScope
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section SigmaFiniteHaar

variable (K)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology in
private theorem secondCountable_adelicGL2 : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact (Units.isInducing_embedProduct (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).secondCountableTopology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdeleRing.secondCountableTopology in
private theorem sigmaFinite_adelicGLHaar : SigmaFinite (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := secondCountable_adelicGL2 K
  infer_instance

end SigmaFiniteHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

open CompactSlabComparison AdelicDock in

private theorem approxW_of_approxW_ample_of_pos (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (hd₁ : 0 < d₁) (hd : d₁ < d₂) (hκ : 1 ≤ κ) (hwide : IsCoveringParameter K u)
    (hcov : CoversModCentre K (plainW c u d₁ d₂ T))
    (hamp : CoversModCentre K (ampleW c u d₁ d₂ κ T)) (Θ Θ' : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ'.toRawCentral R')
    (hω : R.centralChar = R'.centralChar) (happrox : ApproxW (ampleW c u d₁ d₂ κ T) R.toFun R'.toFun) :
    ApproxW (plainW c u d₁ d₂ T) R.toFun R'.toFun := by
  intro ε hε
  have hlawsR := realization_laws R
  obtain ⟨hRΓ, hRZ, hRD⟩ := hlawsR
  have hlawsR' := realization_laws R'
  obtain ⟨hR'Γ, hR'Z, hR'D⟩ := hlawsR'
  have hRc : Continuous R.toFun := hR
  have hR'c : Continuous R'.toFun := hR'
  haveI : SigmaFinite (haarGL K) := sigmaFinite_adelicGLHaar K

  have hRZ' : ∀ (n : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      R.toFun (centralScalar (𝓞 K) K n * g) = centralValue R' n * R.toFun g := by
    intro n g
    rw [hRZ n g]
    simp only [centralValue, hω]
  have hRlsxi : IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar R.toFun := ⟨hRΓ, fun z g => hRZ' z g⟩
  have hR'lsxi : IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar R'.toFun := ⟨hR'Γ, fun z g => hR'Z z g⟩
  have hulsxi : ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
      IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar fun g => ∑ h ∈ s, l h * R.toFun (g * h) :=
    fun s l => ⟨sumTranslates_globalPoints_mul hRΓ s l, fun z g => sumTranslates_centralScalar_mul hRZ' s l z g⟩

  have hcmp : ∀ B : Set (AdelicGL2 (𝓞 K) K), IsCompact B → ∃ N : ℝ, ∀ y ∈ B, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar φ → Continuous φ →
        ∫⁻ x in plainW c u d₁ d₂ T, (‖φ (x * y)‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K) ≤
          ENNReal.ofReal N * ∫⁻ x in plainW c u d₁ d₂ T, (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K) :=
    fun B hB =>
      WindowMultiplicity.translates_le_mul_of_coveringParameter (F := K) c u d₁ d₂ T hc hd₁ hd hwide hcov
        R'.centralChar hB
  obtain ⟨hRy, -⟩ :=
    WeakPassage.translates_memLp_and_bdd_of_mass_comparison (K := K) (D := plainW c u d₁ d₂ T) hcmp hRlsxi hRc hRD
  obtain ⟨hR'y, hR'bdd⟩ :=
    WeakPassage.translates_memLp_and_bdd_of_mass_comparison (K := K) (D := plainW c u d₁ d₂ T) hcmp hR'lsxi hR'c
      hR'D
  have hubdd : ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ) (B : Set (AdelicGL2 (𝓞 K) K)),
      IsCompact B → ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ B,
        ∫ z in plainW c u d₁ d₂ T, ‖∑ h ∈ s, l h * R.toFun (z * y * h)‖ ^ 2 ∂(haarGL K) ≤ C := by
    intro s l B hB
    have hu := WeakPassage.translates_memLp_and_bdd_of_mass_comparison (K := K) (D := plainW c u d₁ d₂ T) hcmp
      (hulsxi s l) (continuous_sumTranslates hRc s l) (WeakPassage.memLp_sum_translates (K := K) hRy s l)
    exact hu.2 B hB

  have hcont : Filter.Tendsto
      (fun y => ∫⁻ z in plainW c u d₁ d₂ T, (‖R'.toFun (z * y) - R'.toFun z‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K))
      (nhds 1) (nhds 0) := by
    have hmass : ∫⁻ x in plainW c u d₁ d₂ T, (‖R'.toFun x‖₊ : ℝ≥0∞) ^ 2 ∂(haarGL K) < ⊤ :=
      (WeakPassage.lintegral_ne_top_of_memLp hR'D).lt_top
    have htail := WindowMultiplicity.exists_tail_le_of_coveringParameter (F := K) c u d₁ d₂ T hc hd₁ hd hwide hcov
      R'.centralChar R'.toFun hR'c hR'lsxi hmass
    have h := TranslationContinuity.tendsto_setLIntegral_nnnorm_translate_sub_translate_sq (haarGL K) hR'c
      (plainW c u d₁ d₂ T) 1 htail
    simpa only [mul_one] using h

  have hlev : ∀ k ∈ finiteLevelOne (𝓞 K) K Θ'.toRawCentral.level, ∀ z : AdelicGL2 (𝓞 K) K,
      R'.toFun (z * finEmbed (𝓞 K) K k) = R'.toFun z := by
    intro k hk z
    exact R'.level_invariant z _ ⟨(finEmbed_mem_levelOne_iff (𝓞 K) K k).mpr hk,
      (mem_finiteAdelicGL2Subgroup_iff K _).mpr (glArch_finEmbed (𝓞 K) K k)⟩

  exact WeakPassage.exists_finset_lintegral_lt_of_weak_data (K := K) hRc hRy hR'c hR'y hR'bdd hcont hubdd
    (P := fun f => IsFactorizableTestFn K f ∧ Continuous f ∧ HasCompactSupport f)
    (fun _ hf => ⟨hf.2.1, hf.2.2⟩)
    (fun V hV => WeakPassage.exists_kernel_of_levelInvariant (K := K) Θ'.toRawCentral.level_ne_bot hlev hV)
    (A := fun s l => massW (ampleW c u d₁ d₂ κ T) R.toFun R'.toFun s l) happrox
    (fun f hf =>
      memLp_rightConv_and_exists_forall_lintegral_rightConv_sub_le_mul_massW_ample c u d₁ d₂ κ T hc hd₁ hd hcov
        hamp Θ Θ' R hR R' hR' hω f hf.1 hf.2.1 hf.2.2)
    ε hε

section CentralUnits

variable (v₀ : InfinitePlace K) (a : (v₀.Completion)ˣ)

private abbrev centralUnitAt : AdelicGL2 (𝓞 K) K := centralScalar (𝓞 K) K (archCentralUnit K v₀ a)

private abbrev unitComponent (w : InfinitePlace K) : w.Completion :=
  ((archCentralUnit K v₀ a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w

private theorem unitComponent_ne_zero (w : InfinitePlace K) : unitComponent v₀ a w ≠ 0 :=
  archCentralUnit_fst_ne_zero v₀ a w

private theorem archComponent_centralUnitAt_apply (w : InfinitePlace K) (i j : Fin 2) :
    (archComponent K w (glArch (𝓞 K) K (centralUnitAt v₀ a)) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then unitComponent v₀ a w else 0 := by
  rw [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

private theorem archComponent_centralUnitAt_mul (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (centralUnitAt v₀ a * g))
      = archComponent K w (glArch (𝓞 K) K (centralUnitAt v₀ a)) * archComponent K w (glArch (𝓞 K) K g) := by
  rw [map_mul, map_mul]

private theorem localHeight_centralUnitAt_mul (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (centralUnitAt v₀ a * g)))
      = localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [archComponent_centralUnitAt_mul]
  have hs := archComponent_centralUnitAt_apply v₀ a w
  exact localHeight_scalar_entries_mul (unitComponent_ne_zero v₀ a w) (by rw [hs]; simp) (by rw [hs]; simp)
    (by rw [hs]; simp) (by rw [hs]; simp) _

private theorem xWindowSq_centralUnitAt_mul (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    xWindowSq (archComponent K w (glArch (𝓞 K) K (centralUnitAt v₀ a * g)))
      = xWindowSq (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [archComponent_centralUnitAt_mul]
  have hs := archComponent_centralUnitAt_apply v₀ a w
  exact xWindowSq_scalar_entries_mul (unitComponent_ne_zero v₀ a w) (by rw [hs]; simp) (by rw [hs]; simp)
    (by rw [hs]; simp) (by rw [hs]; simp) _

private theorem glFin_centralUnitAt_mul (g : AdelicGL2 (𝓞 K) K) :
    glFin (𝓞 K) K (centralUnitAt v₀ a * g) = glFin (𝓞 K) K g := by
  rw [map_mul, glFin_scalar_eq_one K (archCentralUnit_snd v₀ a) (centralScalar_apply_eq _ 0)
    (centralScalar_apply_ne _ (by decide)) (centralScalar_apply_ne _ (by decide)) (centralScalar_apply_eq _ 1),
    one_mul]

private theorem archDetNorm_centralUnitAt_mul (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (centralUnitAt v₀ a * g)
      = ‖unitComponent v₀ a w‖ * ‖unitComponent v₀ a w‖ * archDetNorm w g := by
  unfold archDetNorm
  rw [archComponent_centralUnitAt_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  have hs := archComponent_centralUnitAt_apply v₀ a w
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

private theorem archDetNorm_centralUnitAt_mul_self (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm v₀ (centralUnitAt v₀ a * g) = ‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖ * archDetNorm v₀ g := by
  rw [archDetNorm_centralUnitAt_mul]
  simp only [unitComponent, archCentralUnit_fst_self]

private theorem archDetNorm_centralUnitAt_mul_of_ne {w : InfinitePlace K} (hw : w ≠ v₀) (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (centralUnitAt v₀ a * g) = archDetNorm w g := by
  rw [archDetNorm_centralUnitAt_mul]
  simp only [unitComponent, archCentralUnit_fst_of_ne v₀ a hw, norm_one, one_mul]

end CentralUnits
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section ShellWindows

variable (K)

private def shellSet (c u : ℝ) (lo : InfinitePlace K → ℝ) (d₂ : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K ∧
    (∀ w : InfinitePlace K, c ≤ localHeight (archComponent K w (glArch (𝓞 K) K g))) ∧
    (∀ w : InfinitePlace K, xWindowSq (archComponent K w (glArch (𝓞 K) K g)) ≤ u ^ 2) ∧
    ∀ w : InfinitePlace K, archDetNorm w g ∈ Set.Icc (lo w) d₂}

private theorem shellSet_const (c u d₁ d₂ : ℝ) :
    shellSet K c u (fun _ => d₁) d₂ = centreCutSiegelSet K c u d₁ d₂ := by
  ext g
  exact (mem_centreCutSiegelSet_iff (F := K)).symm

variable {K}

private theorem centralUnitAt_mul_mem_shellSet (v₀ : InfinitePlace K) (a : (v₀.Completion)ˣ) {c u d₂ : ℝ}
    {lo lo' : InfinitePlace K → ℝ} {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ shellSet K c u lo d₂)
    (hlo : ∀ w, w ≠ v₀ → lo' w = lo w)
    (hv₀ : ‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖ * archDetNorm v₀ g ∈ Set.Icc (lo' v₀) d₂) :
    centralUnitAt v₀ a * g ∈ shellSet K c u lo' d₂ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hg
  refine ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rwa [glFin_centralUnitAt_mul]
  · rw [localHeight_centralUnitAt_mul]; exact h₂ w
  · rw [xWindowSq_centralUnitAt_mul]; exact h₃ w
  · by_cases hw : w = v₀
    · subst hw
      rwa [archDetNorm_centralUnitAt_mul_self]
    · rw [archDetNorm_centralUnitAt_mul_of_ne v₀ a hw, hlo w hw]
      exact h₄ w

end ShellWindows
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section MassIdentity

private theorem measurableSet_shellSet (c u : ℝ) (lo : InfinitePlace K → ℝ) (d₂ : ℝ) :
    MeasurableSet (shellSet K c u lo d₂) := by
  have hK : IsOpen {g : AdelicGL2 (𝓞 K) K | glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K} :=
    (isOpen_finiteLevelZero (R := 𝓞 K) (K := K) (N := ⊤) (by simp)).preimage (continuous_glFin (𝓞 K) K)
  have hfloor : ∀ w : InfinitePlace K,
      IsClosed {g : AdelicGL2 (𝓞 K) K | c ≤ localHeight (archComponent K w (glArch (𝓞 K) K g))} := fun w =>
    isClosed_le continuous_const
      ((continuous_localHeight).comp ((continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K)))
  have hwin : ∀ w : InfinitePlace K,
      IsClosed {g : AdelicGL2 (𝓞 K) K | xWindowSq (archComponent K w (glArch (𝓞 K) K g)) ≤ u ^ 2} := fun w =>
    isClosed_le ((continuous_xWindowSq).comp ((continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K)))
      continuous_const
  have hdet : ∀ w : InfinitePlace K, IsClosed {g : AdelicGL2 (𝓞 K) K | archDetNorm w g ∈ Set.Icc (lo w) d₂} :=
    fun w => isClosed_Icc.preimage (continuous_archDetNorm w)
  have : shellSet K c u lo d₂ =
      {g | glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K} ∩
      ((⋂ w : InfinitePlace K, {g | c ≤ localHeight (archComponent K w (glArch (𝓞 K) K g))}) ∩
       ((⋂ w : InfinitePlace K, {g | xWindowSq (archComponent K w (glArch (𝓞 K) K g)) ≤ u ^ 2}) ∩
        (⋂ w : InfinitePlace K, {g | archDetNorm w g ∈ Set.Icc (lo w) d₂}))) := by
    ext g
    simp only [shellSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  exact hK.measurableSet.inter (((isClosed_iInter hfloor).measurableSet).inter
    (((isClosed_iInter hwin).measurableSet).inter ((isClosed_iInter hdet).measurableSet)))

private theorem measurableSet_inter_archDetNorm_lt {X : Set (AdelicGL2 (𝓞 K) K)} (hX : MeasurableSet X)
    (v₀ : InfinitePlace K) (β : ℝ) : MeasurableSet (X ∩ {g | archDetNorm v₀ g < β}) :=
  hX.inter ((isOpen_Iio.preimage (continuous_archDetNorm v₀)).measurableSet)

private theorem setLIntegral_nnnorm_sq_le_of_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] {z : G} {ω : ℂ} (hω : ω ≠ 0) {φ : G → ℂ} (hφm : Measurable φ)
    (hφ : ∀ y, φ (z * y) = ω * φ y) {X Y : Set G} (hY : MeasurableSet Y) (hXY : ∀ y ∈ X, z * y ∈ Y) :
    ∫⁻ y in X, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ ((‖ω‖₊ : ℝ≥0∞) ^ 2)⁻¹ * ∫⁻ y in Y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  set F : G → ℝ≥0∞ := fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2 with hF
  have hFm : Measurable F := (hφm.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hω2 : (‖ω‖₊ : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using hω)
  have hω2' : (‖ω‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top

  have hpt : ∀ y ∈ X, F y ≤ ((‖ω‖₊ : ℝ≥0∞) ^ 2)⁻¹ * Y.indicator F (z * y) := by
    intro y hy
    rw [Set.indicator_of_mem (hXY y hy)]
    have : F (z * y) = (‖ω‖₊ : ℝ≥0∞) ^ 2 * F y := by
      simp only [hF, hφ y, nnnorm_mul, ENNReal.coe_mul, mul_pow]
    rw [this, ← mul_assoc, ENNReal.inv_mul_cancel hω2 hω2', one_mul]
  calc ∫⁻ y in X, F y ∂μ
      ≤ ∫⁻ y in X, ((‖ω‖₊ : ℝ≥0∞) ^ 2)⁻¹ * Y.indicator F (z * y) ∂μ :=
        setLIntegral_mono ((hFm.indicator hY).comp (measurable_const_mul z) |>.const_mul _) hpt
    _ ≤ ∫⁻ y, ((‖ω‖₊ : ℝ≥0∞) ^ 2)⁻¹ * Y.indicator F (z * y) ∂μ := setLIntegral_le_lintegral _ _
    _ = ((‖ω‖₊ : ℝ≥0∞) ^ 2)⁻¹ * ∫⁻ y, Y.indicator F (z * y) ∂μ :=
        lintegral_const_mul _ ((hFm.indicator hY).comp (measurable_const_mul z))
    _ = ((‖ω‖₊ : ℝ≥0∞) ^ 2)⁻¹ * ∫⁻ y, Y.indicator F y ∂μ := by rw [lintegral_mul_left_eq_self (Y.indicator F) z]
    _ = ((‖ω‖₊ : ℝ≥0∞) ^ 2)⁻¹ * ∫⁻ y in Y, F y ∂μ := by rw [lintegral_indicator hY]

end MassIdentity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section OnePlace

variable (v₀ : InfinitePlace K)

omit [NumberField K] in
private theorem two_ne_zero_completion : (2 : v₀.Completion) ≠ 0 := by
  intro h
  have h2 := norm_two_completion (F := K) v₀
  rw [h, norm_zero] at h2
  norm_num at h2

private abbrev twoUnit : (v₀.Completion)ˣ := Units.mk0 (2 : v₀.Completion) (two_ne_zero_completion v₀)

private abbrev scaler : AdelicGL2 (𝓞 K) K := centralUnitAt v₀ (twoUnit v₀)

private theorem archDetNorm_scaler_mul (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm v₀ (scaler v₀ * g) = 4 * archDetNorm v₀ g := by
  rw [archDetNorm_centralUnitAt_mul_self, Units.val_mk0, norm_two_completion]
  norm_num

private theorem scaler_pow_mul (j : ℕ) (g : AdelicGL2 (𝓞 K) K) :
    glFin (𝓞 K) K (scaler v₀ ^ j * g) = glFin (𝓞 K) K g ∧
    (∀ w : InfinitePlace K, localHeight (archComponent K w (glArch (𝓞 K) K (scaler v₀ ^ j * g)))
        = localHeight (archComponent K w (glArch (𝓞 K) K g))) ∧
    (∀ w : InfinitePlace K, xWindowSq (archComponent K w (glArch (𝓞 K) K (scaler v₀ ^ j * g)))
        = xWindowSq (archComponent K w (glArch (𝓞 K) K g))) ∧
    (∀ w : InfinitePlace K, w ≠ v₀ → archDetNorm w (scaler v₀ ^ j * g) = archDetNorm w g) ∧
    archDetNorm v₀ (scaler v₀ ^ j * g) = 4 ^ j * archDetNorm v₀ g := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ih
    have hstep : scaler v₀ ^ (j + 1) * g = scaler v₀ * (scaler v₀ ^ j * g) := by
      rw [pow_succ', mul_assoc]
    rw [hstep]
    refine ⟨?_, fun w => ?_, fun w => ?_, fun w hw => ?_, ?_⟩
    · rw [glFin_centralUnitAt_mul, h₁]
    · rw [localHeight_centralUnitAt_mul, h₂ w]
    · rw [xWindowSq_centralUnitAt_mul, h₃ w]
    · rw [archDetNorm_centralUnitAt_mul_of_ne _ _ hw, h₄ w hw]
    · rw [archDetNorm_scaler_mul, h₅, pow_succ]
      ring

private theorem central_law_pow {ψ : AdelicGL2 (𝓞 K) K → ℂ} {ω₀ : ℂ} (hψ : ∀ y, ψ (scaler v₀ * y) = ω₀ * ψ y) (j : ℕ)
    (y : AdelicGL2 (𝓞 K) K) : ψ (scaler v₀ ^ j * y) = ω₀ ^ j * ψ y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, hψ, ih, pow_succ', mul_assoc]

open scoped Classical in

private def shell (c u : ℝ) (lo : InfinitePlace K → ℝ) (d₁ d₂ : ℝ) (k : ℕ) : Set (AdelicGL2 (𝓞 K) K) :=
  shellSet K c u (Function.update lo v₀ d₁) d₂ ∩
    {g | d₂ / 4 ≤ 4 ^ (k + 1) * archDetNorm v₀ g ∧ 4 ^ (k + 1) * archDetNorm v₀ g < d₂}

open scoped Classical in
private theorem measurableSet_shell (c u : ℝ) (lo : InfinitePlace K → ℝ) (d₁ d₂ : ℝ) (k : ℕ) :
    MeasurableSet (shell v₀ c u lo d₁ d₂ k) := by
  refine (measurableSet_shellSet c u _ d₂).inter ?_
  have hc : Continuous fun g : AdelicGL2 (𝓞 K) K => (4 : ℝ) ^ (k + 1) * archDetNorm v₀ g :=
    continuous_const.mul (continuous_archDetNorm v₀)
  exact ((isClosed_le continuous_const hc).measurableSet).inter ((isOpen_lt hc continuous_const).measurableSet)

open scoped Classical in

private theorem shellSet_update_subset (c u : ℝ) (lo : InfinitePlace K → ℝ) {d₁ d₂ : ℝ} (hlo : lo v₀ = d₂ / 4) :
    shellSet K c u (Function.update lo v₀ d₁) d₂ ⊆ shellSet K c u lo d₂ ∪ ⋃ k : ℕ, shell v₀ c u lo d₁ d₂ k := by
  intro g hg
  have hg' := hg
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hg'
  set t := archDetNorm v₀ g with ht
  have htpos : 0 < t := archDetNorm_pos v₀ g
  have htop : t ≤ d₂ := by
    have := h₄ v₀
    rw [Function.update_self] at this
    exact this.2
  by_cases hbig : d₂ / 4 ≤ t
  · left
    refine ⟨h₁, h₂, h₃, fun w => ?_⟩
    by_cases hw : w = v₀
    · subst hw
      exact ⟨hlo ▸ hbig, htop⟩
    · have := h₄ w
      rwa [Function.update_of_ne hw] at this
  · right
    push Not at hbig

    have hex : ∃ n : ℕ, d₂ / 4 ≤ 4 ^ n * t := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (d₂ / 4 / t) (by norm_num : (1 : ℝ) < 4)
      exact ⟨n, ((div_lt_iff₀ htpos).mp hn).le⟩
    classical
    let n := Nat.find hex
    have hn : d₂ / 4 ≤ 4 ^ n * t := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      have : d₂ / 4 ≤ 4 ^ n * t := hn
      rw [h0, pow_zero, one_mul] at this
      exact absurd this (not_le.mpr hbig)
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hmin : ¬ d₂ / 4 ≤ 4 ^ k * t := Nat.find_min hex (by omega)
    push Not at hmin
    refine Set.mem_iUnion.mpr ⟨k, hg, ?_, ?_⟩
    · rw [← hk]; exact hn
    · rw [pow_succ]
      linarith

open scoped Classical in

private theorem scaler_pow_mul_mem_of_mem_shell (c u : ℝ) (lo : InfinitePlace K → ℝ) {d₁ d₂ : ℝ}
    (hlo : lo v₀ = d₂ / 4) {k : ℕ} {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ shell v₀ c u lo d₁ d₂ k) :
    scaler v₀ ^ (k + 1) * g ∈ shellSet K c u lo d₂ := by
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hlow, hhigh⟩ := hg
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := scaler_pow_mul v₀ (k + 1) g
  refine ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [e₁]; exact h₁
  · rw [e₂ w]; exact h₂ w
  · rw [e₃ w]; exact h₃ w
  · by_cases hw : w = v₀
    · subst hw
      rw [e₅, hlo]
      exact ⟨hlow, hhigh.le⟩
    · rw [e₄ w hw]
      have := h₄ w
      rwa [Function.update_of_ne hw] at this

private abbrev stepRatio (ω₀ : ℂ) : ℝ≥0∞ := ((‖ω₀‖₊ : ℝ≥0∞) ^ 2)⁻¹

private abbrev stepConst (ω₀ : ℂ) : ℝ≥0∞ := 1 + ∑' k : ℕ, stepRatio ω₀ ^ (k + 1)

private theorem stepRatio_lt_one {ω₀ : ℂ} (hω₀ : 1 < (‖ω₀‖₊ : ℝ≥0∞)) : stepRatio ω₀ < 1 :=
  ENNReal.inv_lt_one.mpr (one_lt_pow₀ hω₀ two_ne_zero)

private theorem stepConst_ne_top {ω₀ : ℂ} (hω₀ : 1 < (‖ω₀‖₊ : ℝ≥0∞)) : stepConst ω₀ ≠ ⊤ := by
  have hr := stepRatio_lt_one hω₀
  rw [stepConst, ENNReal.tsum_geometric_add_one]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hr.ne_top ?_⟩
  exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hr).ne'

open scoped Classical in

private theorem mass_shell_le (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsMulLeftInvariant] (c u : ℝ)
    (lo : InfinitePlace K → ℝ) {d₁ d₂ : ℝ} (hlo : lo v₀ = d₂ / 4) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψm : Measurable ψ)
    {ω₀ : ℂ} (hω₀ : ω₀ ≠ 0) (hψ : ∀ y, ψ (scaler v₀ * y) = ω₀ * ψ y) (k : ℕ) :
    ∫⁻ y in shell v₀ c u lo d₁ d₂ k, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ stepRatio ω₀ ^ (k + 1) * ∫⁻ y in shellSet K c u lo d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := setLIntegral_nnnorm_sq_le_of_mul_left (X := shell v₀ c u lo d₁ d₂ k) μ (pow_ne_zero (k + 1) hω₀) hψm
    (central_law_pow v₀ hψ (k + 1))
    (measurableSet_shellSet c u lo d₂) (fun y hy => scaler_pow_mul_mem_of_mem_shell v₀ c u lo hlo hy)
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [stepRatio, nnnorm_pow, ENNReal.coe_pow, ← pow_mul, ← ENNReal.inv_pow, ← pow_mul, mul_comm (k + 1) 2]

open scoped Classical in

private theorem mass_shellSet_update_le (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsMulLeftInvariant] (c u : ℝ)
    (lo : InfinitePlace K → ℝ) (d₁ : ℝ) {d₂ : ℝ} (hlo : lo v₀ = d₂ / 4) {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hψm : Measurable ψ) {ω₀ : ℂ} (hω₀ : ω₀ ≠ 0) (hψ : ∀ y, ψ (scaler v₀ * y) = ω₀ * ψ y) :
    ∫⁻ y in shellSet K c u (Function.update lo v₀ d₁) d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ stepConst ω₀ * ∫⁻ y in shellSet K c u lo d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  set F : AdelicGL2 (𝓞 K) K → ℝ≥0∞ := fun y => (‖ψ y‖₊ : ℝ≥0∞) ^ 2 with hF
  set M := ∫⁻ y in shellSet K c u lo d₂, F y ∂μ with hM
  calc ∫⁻ y in shellSet K c u (Function.update lo v₀ d₁) d₂, F y ∂μ
      ≤ ∫⁻ y in shellSet K c u lo d₂ ∪ ⋃ k : ℕ, shell v₀ c u lo d₁ d₂ k, F y ∂μ :=
        lintegral_mono_set (shellSet_update_subset v₀ c u lo hlo)
    _ ≤ M + ∫⁻ y in ⋃ k : ℕ, shell v₀ c u lo d₁ d₂ k, F y ∂μ := lintegral_union_le _ _ _
    _ ≤ M + ∑' k : ℕ, ∫⁻ y in shell v₀ c u lo d₁ d₂ k, F y ∂μ := by
        gcongr
        exact lintegral_iUnion_le _ _
    _ ≤ M + ∑' k : ℕ, stepRatio ω₀ ^ (k + 1) * M := by
        gcongr with k
        exact mass_shell_le v₀ μ c u lo hlo hψm hω₀ hψ k
    _ = stepConst ω₀ * M := by
        rw [ENNReal.tsum_mul_right, stepConst, add_mul, one_mul]

end OnePlace
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section AllPlaces

open scoped Classical in

private theorem mass_shellSet_le_prod_mul (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsMulLeftInvariant] (c u d₁ : ℝ)
    (d₂ : ℝ) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψm : Measurable ψ) (ω : InfinitePlace K → ℂ) (hω : ∀ v, ω v ≠ 0)
    (hψ : ∀ v y, ψ (scaler v * y) = ω v * ψ y) (S : Finset (InfinitePlace K)) :
    ∫⁻ y in shellSet K c u (fun w => if w ∈ S then d₁ else d₂ / 4) d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ (∏ v ∈ S, stepConst (ω v)) * ∫⁻ y in shellSet K c u (fun _ => d₂ / 4) d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hv ih =>
    have hupd : (fun w => if w ∈ insert v S then d₁ else d₂ / 4)
        = Function.update (fun w => if w ∈ S then d₁ else d₂ / 4) v d₁ := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp
      · simp [hw]
    have hlo : (fun w => if w ∈ S then d₁ else d₂ / 4) v = d₂ / 4 := by simp [hv]
    rw [hupd, Finset.prod_insert hv, mul_assoc]
    calc ∫⁻ y in shellSet K c u (Function.update (fun w => if w ∈ S then d₁ else d₂ / 4) v d₁) d₂,
            (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ
        ≤ stepConst (ω v) * ∫⁻ y in shellSet K c u (fun w => if w ∈ S then d₁ else d₂ / 4) d₂,
            (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ :=
          mass_shellSet_update_le v μ c u _ d₁ hlo hψm (hω v) (hψ v)
      _ ≤ stepConst (ω v) * ((∏ w ∈ S, stepConst (ω w)) *
            ∫⁻ y in shellSet K c u (fun _ => d₂ / 4) d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂μ) := by gcongr

open scoped Classical in

private theorem mass_centreCut_le_prod_mul (c u d₁ d₂ : ℝ) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψm : Measurable ψ)
    (ω : InfinitePlace K → ℂ) (hω : ∀ v, ω v ≠ 0) (hψ : ∀ v y, ψ (scaler v * y) = ω v * ψ y) :
    ∫⁻ y in centreCutSiegelSet K c u d₁ d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ (∏ v, stepConst (ω v)) *
        ∫⁻ y in centreCutSiegelSet K c u (d₂ / 4) d₂, (‖ψ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have h := mass_shellSet_le_prod_mul (adelicGLHaar (Fin 2) (𝓞 K) K) c u d₁ d₂ hψm ω hω hψ Finset.univ
  simpa only [Finset.mem_univ, if_true, shellSet_const] using h

end AllPlaces
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section Translates

private theorem setLIntegral_image_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulRightInvariant] (F : G → ℝ≥0∞) {S : Set G} (hS : MeasurableSet S) (x : G) :
    ∫⁻ y in (· * x) '' S, F y ∂μ = ∫⁻ y in S, F (y * x) ∂μ := by
  have hpre : MeasurableSet ((· * x⁻¹) ⁻¹' S) := hS.preimage (measurable_mul_const x⁻¹)
  rw [Set.image_mul_right, ← lintegral_indicator hpre, ← lintegral_indicator hS,
    ← lintegral_mul_right_eq_self (((· * x⁻¹) ⁻¹' S).indicator F) x]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · have hy' : y * x ∈ (· * x⁻¹) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']
  · have hy' : y * x ∉ (· * x⁻¹) ⁻¹' S := by simpa [Set.mem_preimage] using hy
    simp [Set.indicator, hy, hy']

private theorem setLIntegral_biUnion_finset_le {G : Type} [MeasurableSpace G] (μ : Measure G) (F : G → ℝ≥0∞)
    (S : G → Set G) (T : Finset G) : ∫⁻ y in ⋃ x ∈ T, S x, F y ∂μ ≤ ∑ x ∈ T, ∫⁻ y in S x, F y ∂μ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (by gcongr)

end Translates
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

private theorem exists_massW_le_mul_massW_quarter (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂) (hcov : CoversModCentre K (plainW c u d₁ d₂ T))
    (Θ Θ' : HeckeEigensystem K ℂ) (R : SmoothCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Θ'.toRawCentral R')
    (hω : R.centralChar = R'.centralChar) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
      massW (plainW c u d₁ d₂ T) R.toFun R'.toFun s l ≤ C * massW (plainW c u (d₂ / 4) d₂ T) R.toFun R'.toFun s l := by
  classical
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K

  have hRfun : IsLsXiFunction (𝓞 K) K ⊤ R.centralChar R.toFun :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp R.smoothCusp.1.1).1
  have hR'fun : IsLsXiFunction (𝓞 K) K ⊤ R'.centralChar R'.toFun :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp R'.smoothCusp.1.1).1

  let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
    { toFun := fun z => R.centralChar ⟨z, Subgroup.mem_top z⟩
      map_one' := R.centralChar.map_one
      map_mul' := fun a b => R.centralChar.map_mul ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩ }
  set ω : InfinitePlace K → ℂ := fun v => ((χ (archCentralUnit K v (twoUnit v)) : ℂˣ) : ℂ) with hωdef
  have hωne : ∀ v, ω v ≠ 0 := fun v => Units.ne_zero _
  have hlawR : ∀ v y, R.toFun (scaler v * y) = ω v * R.toFun y := fun v y =>
    hRfun.central_transform ⟨archCentralUnit K v (twoUnit v), Subgroup.mem_top _⟩ y
  have hlawR' : ∀ v y, R'.toFun (scaler v * y) = ω v * R'.toFun y := fun v y => by
    have h := hR'fun.central_transform ⟨archCentralUnit K v (twoUnit v), Subgroup.mem_top _⟩ y
    rw [← hω] at h
    exact h

  have hωbig : ∀ v, 1 < (‖ω v‖₊ : ℝ≥0∞) := by
    intro v
    have hlt := norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre K c u d₁ d₂ T hd₁ hd₂ hcov R.toFun hR
      R.exists_ne_zero hRfun.left_invariant χ (fun z g => hRfun.central_transform ⟨z, Subgroup.mem_top z⟩ g)
      (memLp_toFun R) v (twoUnit v)⁻¹
      (by rw [Units.val_inv_eq_inv_val, norm_inv, Units.val_mk0, norm_two_completion]; norm_num)
    have hinv : archCentralUnit K v (twoUnit v)⁻¹ = (archCentralUnit K v (twoUnit v))⁻¹ := Units.ext rfl
    rw [hinv, map_inv, Units.val_inv_eq_inv_val, norm_inv] at hlt
    have hpos : 0 < ‖((χ (archCentralUnit K v (twoUnit v)) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
    have h1 : 1 < ‖ω v‖ := (inv_lt_one₀ hpos).mp hlt
    exact ENNReal.one_lt_coe_iff.mpr (by exact_mod_cast h1)

  refine ⟨(T.card : ℝ≥0∞) * ∏ v, stepConst (ω v),
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.prod_ne_top fun v _ => stepConst_ne_top (hωbig v)), ?_⟩
  intro s l

  set g : AdelicGL2 (𝓞 K) K → ℂ := fun y => R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h) with hgdef
  have hRc : Continuous R.toFun := hR
  have hR'c : Continuous R'.toFun := hR'
  have hgm : Measurable g :=
    hR'c.measurable.sub
      (Finset.measurable_sum s fun h _ => measurable_const.mul (hRc.measurable.comp (measurable_mul_const h)))
  have hglaw : ∀ v y, g (scaler v * y) = ω v * g y := by
    intro v y
    simp only [hgdef]
    rw [hlawR', mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [mul_assoc (scaler v), hlawR]
    ring

  have hper : ∀ x ∈ T,
      ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        ≤ (∏ v, stepConst (ω v)) * massW (plainW c u (d₂ / 4) d₂ T) R.toFun R'.toFun s l := by
    intro x hx
    have hψm : Measurable fun y => g (y * x) := hgm.comp (measurable_mul_const x)
    have hψlaw : ∀ v y, (fun y => g (y * x)) (scaler v * y) = ω v * (fun y => g (y * x)) y := fun v y => by
      simp only
      rw [mul_assoc, hglaw]
    calc ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        = ∫⁻ y in centreCutSiegelSet K c u d₁ d₂, (‖g (y * x)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          setLIntegral_image_mul_right _ _ (measurableSet_centreCutSiegelSet c u d₁ d₂) x
      _ ≤ (∏ v, stepConst (ω v)) *
            ∫⁻ y in centreCutSiegelSet K c u (d₂ / 4) d₂, (‖g (y * x)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          mass_centreCut_le_prod_mul c u d₁ d₂ hψm ω hωne hψlaw
      _ = (∏ v, stepConst (ω v)) *
            ∫⁻ y in (· * x) '' centreCutSiegelSet K c u (d₂ / 4) d₂, (‖g y‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          rw [setLIntegral_image_mul_right _ _ (measurableSet_centreCutSiegelSet c u (d₂ / 4) d₂) x]
      _ ≤ (∏ v, stepConst (ω v)) * massW (plainW c u (d₂ / 4) d₂ T) R.toFun R'.toFun s l := by
          gcongr
          exact lintegral_mono_set
            (Set.subset_iUnion₂ (s := fun x (_ : x ∈ T) => (· * x) '' centreCutSiegelSet K c u (d₂ / 4) d₂) x hx)
  calc massW (plainW c u d₁ d₂ T) R.toFun R'.toFun s l
      ≤ ∑ x ∈ T, ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g y‖₊ : ℝ≥0∞) ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        setLIntegral_biUnion_finset_le _ _ _ T
    _ ≤ ∑ _x ∈ T, (∏ v, stepConst (ω v)) * massW (plainW c u (d₂ / 4) d₂ T) R.toFun R'.toFun s l :=
        Finset.sum_le_sum hper
    _ = ((T.card : ℝ≥0∞) * ∏ v, stepConst (ω v)) * massW (plainW c u (d₂ / 4) d₂ T) R.toFun R'.toFun s l := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

section LatticeBox

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
private theorem norm_algebraMap_completion_eq (w : InfinitePlace F) (x : F) :
    ‖algebraMap F w.Completion x‖ = w x := by
  have he : algebraMap F w.Completion x = ((WithAbs.equiv w.1).symm x : w.Completion) := rfl
  rw [he, InfinitePlace.Completion.norm_coe]
  rfl

private theorem finite_setOf_forall_norm_le (B : ℝ) :
    {η : 𝓞 F | ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (η : F)‖ ≤ B}.Finite := by
  have hfin := Embeddings.finite_of_norm_le F ℂ B
  refine (hfin.preimage (f := fun η : 𝓞 F => (η : F)) ?_).subset ?_
  · intro a _ b _ hab
    exact RingOfIntegers.ext hab
  · intro η hη
    refine ⟨RingOfIntegers.isIntegral_coe η, fun φ => ?_⟩
    have h := hη (InfinitePlace.mk φ)
    rwa [norm_algebraMap_completion_eq, InfinitePlace.apply] at h

end LatticeBox
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section Moves

open Matrix AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

private def upperGL (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, t]
    (by rw [Matrix.det_fin_two_of]; simp [ha, ht])

omit [NumberField K] in
private theorem upperGL_apply_zero_zero (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 0 0 = a := rfl

omit [NumberField K] in
private theorem upperGL_apply_zero_one (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 0 1 = b := rfl

omit [NumberField K] in
private theorem upperGL_apply_one_zero (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := rfl

omit [NumberField K] in
private theorem upperGL_apply_one_one (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht : Matrix (Fin 2) (Fin 2) K) 1 1 = t := rfl

private theorem archComponent_globalPoints_upperGL_entries (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0)
    (ht : t ≠ 0) :
    let s : GL (Fin 2) w.Completion :=
      archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht)))
    (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (a : w.Completion) ∧
      (s : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = (b : w.Completion) ∧
      (s : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 ∧
      (s : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (t : w.Completion) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [archComponent_globalPoints_apply]
  · rfl
  · rfl
  · rw [upperGL_apply_one_zero]; exact NumberField.InfinitePlace.Completion.coe_zero (K := K) (v := w)
  · rfl

omit [NumberField K] in
private theorem coe_completion_ne_zero (w : InfinitePlace K) {t : K} (ht : t ≠ 0) : (t : w.Completion) ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [norm_coe_completion, norm_zero] at this
  exact ht (of_not_not ((w.pos_iff.not).mp (not_lt.mpr this.le)))

private theorem archComponent_globalPoints_mul (w : InfinitePlace K) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ * g))
      = archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K γ))
          * archComponent K w (glArch (𝓞 K) K g) := by
  rw [map_mul, map_mul]

private theorem localHeight_globalPoints_upperGL_mul (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    localHeight (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht) * g)))
      = w a / w t * localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  obtain ⟨h00, -, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a b t ha ht
  rw [archComponent_globalPoints_mul,
    localHeight_upper_entries_mul (coe_completion_ne_zero w ht) h00 h10 h11, norm_coe_completion,
    norm_coe_completion]

private theorem xWindowSq_globalPoints_diag_mul (w : InfinitePlace K) (a t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    xWindowSq (archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a 0 t ha ht) * g)))
      = (w a / w t) ^ 2 * xWindowSq (archComponent K w (glArch (𝓞 K) K g)) := by
  obtain ⟨h00, h01, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a 0 t ha ht
  rw [archComponent_globalPoints_mul,
    xWindowSq_diag_entries_mul (coe_completion_ne_zero w ht) h00 (by rw [h01]; exact NumberField.InfinitePlace.Completion.coe_zero (K := K) (v := w))
      h10 h11,
    norm_coe_completion, norm_coe_completion]

private theorem archDetNorm_globalPoints_upperGL_mul (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (globalPoints (𝓞 K) K (upperGL a b t ha ht) * g) = w a * w t * archDetNorm w g := by
  obtain ⟨h00, -, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a b t ha ht
  unfold archDetNorm
  rw [archComponent_globalPoints_mul, det_upper_entries_mul h00 h10 h11, norm_mul, norm_mul, norm_coe_completion,
    norm_coe_completion]

open scoped Classical in

private noncomputable def placeEmb (w : InfinitePlace K) : w.Completion →+* ℂ :=
  if hw : w.IsReal then Complex.ofRealHom.comp (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)
  else InfinitePlace.Completion.extensionEmbedding w

omit [NumberField K] in
private theorem norm_placeEmb (w : InfinitePlace K) (x : w.Completion) : ‖placeEmb w x‖ = ‖x‖ := by
  unfold placeEmb
  split_ifs with hw
  · rw [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

private noncomputable def xAtP (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  xCoord (((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) w.Completion).map (placeEmb w))

private theorem xWindowSq_eq_norm_xAtP_sq (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    xWindowSq (archComponent K w (glArch (𝓞 K) K g)) = ‖xAtP w g‖ ^ 2 :=
  xWindowSq_eq_norm_xCoord_map_sq (placeEmb w) (norm_placeEmb w) _

private theorem xAtP_globalPoints_upperGL_mul (w : InfinitePlace K) (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) :
    xAtP w (globalPoints (𝓞 K) K (upperGL a b t ha ht) * g)
      = placeEmb w a / placeEmb w t * xAtP w g + placeEmb w b / placeEmb w t := by
  obtain ⟨h00, h01, h10, h11⟩ := archComponent_globalPoints_upperGL_entries w a b t ha ht
  set φ := placeEmb w
  set s : GL (Fin 2) w.Completion :=
    archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht))) with hs
  set h : GL (Fin 2) w.Completion := archComponent K w (glArch (𝓞 K) K g) with hh
  have hφt : φ (t : w.Completion) ≠ 0 := (map_ne_zero φ).mpr (coe_completion_ne_zero w ht)
  have hlaw := xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ s) (a := φ (a : w.Completion))
    (b := φ (b : w.Completion)) (t := φ (t : w.Completion)) hφt
    (by rw [coe_map, Matrix.map_apply, h00]) (by rw [coe_map, Matrix.map_apply, h01])
    (by rw [coe_map, Matrix.map_apply, h10, map_zero]) (by rw [coe_map, Matrix.map_apply, h11])
    (Matrix.GeneralLinearGroup.map φ h)
  unfold xAtP
  rw [archComponent_globalPoints_mul, ← hs, ← hh, ← coe_map, ← coe_map, ← map_mul, coe_map, ← coe_map] at *
  rw [map_mul (archComponent K w)]
  exact hlaw

private theorem exists_placeEmb_eq_xAtP (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) :
    ∃ x : w.Completion, placeEmb w x = xAtP w g := by
  by_cases hw : w.IsReal
  ·
    have hsurj : Function.Surjective (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw).surjective
    have hreal : ∀ z : w.Completion,
        placeEmb w z = ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hw z : ℝ) : ℂ) := by
      intro z; simp only [placeEmb, dif_pos hw, RingHom.comp_apply, Complex.ofRealHom_eq_coe]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = xAtP w g := by
      refine ⟨(xAtP w g).re, ?_⟩
      unfold xAtP xCoord
      simp only [hreal, Matrix.map_apply]
      apply Complex.ext <;>
        simp [Complex.ofReal_re, Complex.ofReal_im, -InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    obtain ⟨x, hx⟩ := hsurj r
    exact ⟨x, by rw [hreal, hx, hr]⟩
  · have hsurj : Function.Surjective (InfinitePlace.Completion.extensionEmbedding w) :=
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    obtain ⟨x, hx⟩ := hsurj (xAtP w g)
    exact ⟨x, by simp only [placeEmb, dif_neg hw]; exact hx⟩

private theorem algebraMap_mem_integralFiniteAdeles (a : 𝓞 K) :
    algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K a)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  intro v
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one a

private theorem glFin_globalPoints_upperGL_entries_mem (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (hai : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hbi : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) b ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hti : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) t ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (i j : Fin 2) :
    ((glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht)) :
          GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [glFin_globalPoints_apply]
  fin_cases i <;> fin_cases j
  · exact hai
  · exact hbi
  · show algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (0 : K) ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K
    rw [map_zero]; exact AdelicLevel.zero_mem_integralFiniteAdeles
  · exact hti

omit [NumberField K] in

private theorem upperGL_inv (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperGL a b t ha ht)⁻¹ = upperGL a⁻¹ (-b / (a * t)) t⁻¹ (inv_ne_zero ha) (inv_ne_zero ht) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two, ha, ht] <;>
    field_simp <;> ring

private theorem glFin_globalPoints_upperGL_mem (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (hai : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hbi : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) b ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hti : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) t ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hai' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) a⁻¹ ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hbi' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (-b / (a * t))
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hti' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) t⁻¹ ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL a b t ha ht)) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨glFin_globalPoints_upperGL_entries_mem a b t ha ht hai hbi hti, fun i j => ?_⟩
  rw [← map_inv, ← map_inv, upperGL_inv]
  exact glFin_globalPoints_upperGL_entries_mem _ _ _ _ _ hai' hbi' hti' i j

private theorem algebraMap_zero_mem :
    algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (0 : K) ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [map_zero]; exact AdelicLevel.zero_mem_integralFiniteAdeles

omit [NumberField K] in
private theorem algebraMap_units_inv_eq (ε : (𝓞 K)ˣ) :
    (algebraMap (𝓞 K) K (ε : 𝓞 K))⁻¹ = algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) :=
  inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])

private theorem algebraMap_units_inv_mem (ε : (𝓞 K)ˣ) :
    algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K (ε : 𝓞 K))⁻¹
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [algebraMap_units_inv_eq]; exact algebraMap_mem_integralFiniteAdeles _

private theorem glFin_globalPoints_diagUnits_mem (ε ε' : (𝓞 K)ˣ) :
    glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL (algebraMap (𝓞 K) K ε) 0 (algebraMap (𝓞 K) K ε')
        (RingOfIntegers.coe_ne_zero_iff.mpr ε.ne_zero) (RingOfIntegers.coe_ne_zero_iff.mpr ε'.ne_zero)))
      ∈ finiteIntegralGL2 (𝓞 K) K := by
  have hai : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_mem_integralFiniteAdeles _
  have hti : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε')
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_mem_integralFiniteAdeles _
  have hai' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε)⁻¹
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_units_inv_mem _
  have hti' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ε')⁻¹
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := algebraMap_units_inv_mem _
  have hbi' : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
      (-(0 : K) / (algebraMap (𝓞 K) K ε * algebraMap (𝓞 K) K ε')) ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [neg_zero, zero_div]; exact algebraMap_zero_mem
  exact glFin_globalPoints_upperGL_mem _ _ _ _ _ hai algebraMap_zero_mem hti hai' hbi' hti'

private theorem glFin_globalPoints_shift_mem (ξ : 𝓞 K) :
    glFin (𝓞 K) K (globalPoints (𝓞 K) K (upperGL 1 (algebraMap (𝓞 K) K ξ) 1 one_ne_zero one_ne_zero))
      ∈ finiteIntegralGL2 (𝓞 K) K := by
  have h1 : algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (1 : K)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [map_one]; exact AdelicLevel.one_mem_integralFiniteAdeles
  refine glFin_globalPoints_upperGL_mem _ _ _ _ _ h1 (algebraMap_mem_integralFiniteAdeles ξ) h1 (by rwa [inv_one])
    ?_ (by rwa [inv_one])
  rw [mul_one, div_one, ← map_neg]
  exact algebraMap_mem_integralFiniteAdeles (-ξ)

end Moves
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

section Relaxation

open AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

private noncomputable def shiftPt (ξ : 𝓞 K) : AdelicGL2 (𝓞 K) K :=
  globalPoints (𝓞 K) K (upperGL 1 (algebraMap (𝓞 K) K ξ) 1 one_ne_zero one_ne_zero)

omit [NumberField K] in
private theorem norm_algebraMap_eq_norm_coe (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = ‖(x : w.Completion)‖ := rfl

private theorem shiftPt_neg_mul_mem_centreCutSiegelSet {c u u' d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 K) K}
    (hg : g ∈ centreCutSiegelSet K c u' d₁ d₂) {x : (w : InfinitePlace K) → w.Completion}
    (hx : ∀ w, placeEmb w (x w) = xAtP w g) {ξ : 𝓞 K}
    (hξ : ∀ w : InfinitePlace K, ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ u) :
    shiftPt (-ξ) * g ∈ centreCutSiegelSet K c u d₁ d₂ := by
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  obtain ⟨hfin, hfloor, hwin, hdet⟩ := hg
  refine ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [map_mul]
    exact Subgroup.mul_mem _ (glFin_globalPoints_shift_mem (-ξ)) hfin
  · rw [shiftPt, localHeight_globalPoints_upperGL_mul, map_one, div_one, one_mul]
    exact hfloor w
  · have h1 : placeEmb w ((1 : K) : w.Completion) = 1 := by
      rw [show ((1 : K) : w.Completion) = 1 from rfl, map_one]
    have e : ((algebraMap (𝓞 K) K (-ξ) : K) : w.Completion) = -(algebraMap K w.Completion (ξ : K)) := by
      rw [map_neg, ← NumberField.InfinitePlace.Completion.algebraMap_apply, map_neg]
    rw [xWindowSq_eq_norm_xAtP_sq, shiftPt, xAtP_globalPoints_upperGL_mul, h1, div_one, div_one, one_mul,
      ← hx w, ← map_add, norm_placeEmb, e, ← sub_eq_add_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (hξ w) 2
  · rw [shiftPt, archDetNorm_globalPoints_upperGL_mul, map_one, one_mul, one_mul]
    exact hdet w

private theorem shiftPt_mul_shiftPt_neg (ξ : 𝓞 K) : shiftPt ξ * shiftPt (-ξ) = 1 := by
  unfold shiftPt
  rw [← map_mul]
  convert map_one (globalPoints (𝓞 K) K) using 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two]

private theorem norm_le_of_mem_centreCutSiegelSet {c u' d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 K) K}
    (hg : g ∈ centreCutSiegelSet K c u' d₁ d₂) (hu' : 0 ≤ u') {x : (w : InfinitePlace K) → w.Completion}
    (hx : ∀ w, placeEmb w (x w) = xAtP w g) (w : InfinitePlace K) : ‖x w‖ ≤ u' := by
  have h := (mem_centreCutSiegelSet_iff.mp hg).2.2.1 w
  rw [xWindowSq_eq_norm_xAtP_sq, ← hx w, norm_placeEmb] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hu' two_ne_zero).mp h

private noncomputable def integerBox (B : ℝ) : Finset (𝓞 K) :=
  (finite_setOf_forall_norm_le (F := K) B).toFinset

private theorem mem_integerBox {B : ℝ} {η : 𝓞 K} :
    η ∈ integerBox (K := K) B ↔ ∀ w : InfinitePlace K, ‖algebraMap K w.Completion (η : K)‖ ≤ B := by
  simp [integerBox]

private theorem plainW_subset_biUnion (c u u' d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hu : IsCoveringParameter K u) (huu' : u ≤ u') :
    plainW c u' d₁ d₂ T ⊆
      ⋃ ξ ∈ integerBox (K := K) (u + u'),
        {h | h ∈ plainW c u' d₁ d₂ T ∧ shiftPt (-ξ) * h ∈ plainW c u d₁ d₂ T} := by
  intro h hh
  have hh' := hh
  simp only [plainW, Set.mem_iUnion, Set.mem_image, exists_prop] at hh'
  obtain ⟨t, ht, g, hg, rfl⟩ := hh'

  choose x hx using fun w => exists_placeEmb_eq_xAtP w g
  obtain ⟨ξ, hξ⟩ := hu x
  have hu0 : 0 ≤ u := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    exact le_trans (norm_nonneg _) (hξ w)
  have hu'0 : 0 ≤ u' := le_trans hu0 huu'
  refine Set.mem_iUnion₂.mpr ⟨ξ, ?_, hh, ?_⟩
  · refine mem_integerBox.mpr fun w => ?_
    calc ‖algebraMap K w.Completion (ξ : K)‖
        = ‖x w - (x w - algebraMap K w.Completion (ξ : K))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x w‖ + ‖x w - algebraMap K w.Completion (ξ : K)‖ := norm_sub_le _ _
      _ ≤ u' + u := add_le_add (norm_le_of_mem_centreCutSiegelSet hg hu'0 hx w) (hξ w)
      _ = u + u' := add_comm _ _
  · simp only [plainW, Set.mem_iUnion, Set.mem_image, exists_prop]
    exact ⟨t, ht, shiftPt (-ξ) * g, shiftPt_neg_mul_mem_centreCutSiegelSet hg hx hξ, mul_assoc _ _ _⟩

private theorem measurableSet_plainW_relax (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    MeasurableSet (plainW c u d₁ d₂ T) := by
  refine Finset.measurableSet_biUnion T fun t _ => ?_
  rw [Set.image_mul_right]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const t⁻¹)

private theorem lintegral_plainW_le_count_mul (c u u' d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hu : IsCoveringParameter K u) (huu' : u ≤ u') {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφm : Measurable φ)
    (hφ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g) :
    ∫⁻ y in plainW c u' d₁ d₂ T, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ (((integerBox (K := K) (u + u')).card : ℝ≥0∞)) *
          ∫⁻ y in plainW c u d₁ d₂ T, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K
  set Z := integerBox (K := K) (u + u') with hZ
  set S : 𝓞 K → Set (AdelicGL2 (𝓞 K) K) :=
    fun ξ => {h | h ∈ plainW c u' d₁ d₂ T ∧ shiftPt (-ξ) * h ∈ plainW c u d₁ d₂ T} with hS
  have hcover := plainW_subset_biUnion c u u' d₁ d₂ T hu huu'
  have hcover' : plainW c u' d₁ d₂ T ⊆ ⋃ ξ : Z, S ξ := fun h hh => by
    obtain ⟨ξ, hξZ, hξ⟩ := Set.mem_iUnion₂.mp (hcover hh)
    exact Set.mem_iUnion.mpr ⟨⟨ξ, hξZ⟩, hξ⟩
  calc ∫⁻ y in plainW c u' d₁ d₂ T, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ ∫⁻ y in ⋃ ξ : Z, S ξ, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := lintegral_mono_set hcover'
    _ ≤ ∑' ξ : Z, ∫⁻ y in S ξ, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := lintegral_iUnion_le _ _
    _ = ∑ ξ : Z, ∫⁻ y in S ξ, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := tsum_fintype _
    _ ≤ ∑ _ξ : Z, ∫⁻ y in plainW c u d₁ d₂ T, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        have hinv : ∀ y, φ (shiftPt (-(ξ : 𝓞 K)) * y) = (1 : ℂ) * φ y := fun y => by
          rw [one_mul]; exact hφ _ y
        have h := setLIntegral_nnnorm_sq_le_of_mul_left μ (z := shiftPt (-(ξ : 𝓞 K))) (ω := (1 : ℂ)) one_ne_zero
          hφm hinv (measurableSet_plainW_relax c u d₁ d₂ T) (fun y (hy : y ∈ S ξ) => hy.2)
        simpa using h
    _ = (((integerBox (K := K) (u + u')).card : ℝ≥0∞)) *
          ∫⁻ y in plainW c u d₁ d₂ T, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

private theorem toFun_globalPoints_mul {pins : CarrierPins K} {Φ : HeckeEigensystem K ℂ}
    (R : SmoothCuspRealizationAt K pins Φ) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    R.toFun (globalPoints (𝓞 K) K γ * g) = R.toFun g := by
  obtain ⟨hls, -⟩ := R.smoothCusp.1.1
  exact hls.left_invariant γ g

private theorem memLp_plainW_of_memLp_plainW_of_le (c u u' d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hu : IsCoveringParameter K u) (huu' : u ≤ u') {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφc : Continuous φ)
    (hφ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (hφn : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u d₁ d₂ T))) :
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u' d₁ d₂ T)) := by
  refine WeakPassage.memLp_of_lintegral_ne_top hφc (ne_top_of_le_ne_top ?_
    (lintegral_plainW_le_count_mul c u u' d₁ d₂ T hu huu' hφc.measurable hφ))
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (WeakPassage.lintegral_ne_top_of_memLp hφn)

end Relaxation
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

private theorem memLp_relax_of_covering (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (_hc : 0 < c)
    (_hd₁ : 0 < d₁) (_hd : d₁ < d₂) (hu : IsCoveringParameter K u)
    (_hcov : CoversModCentre K (plainW c u d₁ d₂ T)) {Φ : HeckeEigensystem K ℂ}
    (R : SmoothCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Φ)
    (hR : IsGenuineCuspRealizationAt K (pinsW (plainW c u d₁ d₂ T)) Φ R) (u' : ℝ) (huu' : u ≤ u') :
    MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u' d₁ d₂ T)) := by
  exact memLp_plainW_of_memLp_plainW_of_le c u u' d₁ d₂ T hu huu' hR (toFun_globalPoints_mul R) (memLp_toFun R)

end Holes
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison"

private theorem passage_frame
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hc : 0 < c)
    (hu : ∀ x : (w : InfinitePlace K) → w.Completion, ∃ ξ : 𝓞 K, ∀ w : InfinitePlace K,
      ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ u)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    ∃ u' d₁' κ : ℝ, 0 < d₁' ∧ d₁' < d₂ ∧ 1 ≤ κ ∧
      CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ) ∧
      (∃ Rκ : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ.toRawCentral Rκ ∧ Rκ.toFun = R.toFun) ∧
      (∃ R'κ : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ'.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ'.toRawCentral R'κ ∧ R'κ.toFun = R'.toFun) ∧
      ((∀ δ : ℝ≥0∞, 0 < δ →
          ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ,
                (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < δ) →
        ∀ ε : ℝ≥0∞, 0 < ε →
          ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
                (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε) := by

  have hω : R.centralChar = R'.centralChar :=
    SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite K _ Θ Θ' hΘ R hR R' hR'

  have hd₂ : 0 < d₂ := pos_of_coversModCentre c u d₁ d₂ T hcov
  obtain ⟨d₁', hd₁'pos, hle, hlt, hcmp⟩ : ∃ d₁' : ℝ, 0 < d₁' ∧ d₁ ≤ d₁' ∧ d₁' < d₂ ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        massW (plainW c u d₁ d₂ T) R.toFun R'.toFun s l ≤ C * massW (plainW c u d₁' d₂ T) R.toFun R'.toFun s l := by
    rcases lt_or_ge 0 d₁ with hpos | hnonpos
    · exact ⟨d₁, hpos, le_rfl, hd, 1, ENNReal.one_ne_top, fun s l => by rw [one_mul]⟩
    · exact ⟨d₂ / 4, by linarith, by linarith, by linarith,
        exists_massW_le_mul_massW_quarter c u d₁ d₂ T hnonpos hd₂ hcov Θ Θ' R hR R' hR' hω⟩

  have hcov' : CoversModCentre K (plainW c u (d₁') d₂ T) :=
    (coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre K c u d₁ d₂ _ T hle hlt hcov Θ
      ⟨R, hR⟩).1

  obtain ⟨κ, R₀, hκ, -, hamp⟩ := exists_coversModCentre_centreCutSiegelSetAmple K
  set uf : ℝ := max |u| R₀
  have huf : |u| ≤ uf := le_max_left _ _
  have hR₀f : R₀ ≤ uf := le_max_right _ _
  have huuf : u ≤ uf := le_trans (le_abs_self u) huf
  have hwf : IsCoveringParameter K uf := IsCoveringParameter.mono hu huuf
  have hmaxf : max uf R₀ = uf := max_eq_left hR₀f
  have hwide := plainW_mono_unipotent c u uf (d₁') d₂ T huf
  have hcovf : CoversModCentre K (plainW c uf (d₁') d₂ T) := hcov'.mono hwide
  have hampcov : CoversModCentre K (ampleW c uf (d₁') d₂ κ T) := by
    have h := hamp c uf _ d₂ T hcovf
    rwa [hmaxf] at h

  have hsub := plainW_mono_lower c u d₁ _ d₂ T hle
  have hRn : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u (d₁') d₂ T)) :=
    (memLp_toFun R).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hR'n : MemLp R'.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c u (d₁') d₂ T)) :=
    (memLp_toFun R').mono_measure (Measure.restrict_mono hsub le_rfl)

  have hRf : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c uf (d₁') d₂ T)) :=
    memLp_relax_of_covering c u _ d₂ T hc hd₁'pos hlt hu hcov' (transport R hRn)
      (isGenuine_transport R hR hRn) uf huuf
  have hR'f : MemLp R'.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW c uf (d₁') d₂ T)) :=
    memLp_relax_of_covering c u _ d₂ T hc hd₁'pos hlt hu hcov' (transport R' hR'n)
      (isGenuine_transport R' hR' hR'n) uf huuf

  have hRa : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (ampleW c uf (d₁') d₂ κ T)) :=
    hRf.mono_measure (Measure.restrict_mono (ampleW_subset_plainW c uf _ d₂ κ T) le_rfl)
  have hR'a : MemLp R'.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (ampleW c uf (d₁') d₂ κ T)) :=
    hR'f.mono_measure (Measure.restrict_mono (ampleW_subset_plainW c uf _ d₂ κ T) le_rfl)
  refine ⟨uf, d₁', κ, hd₁'pos, hlt, hκ, hampcov, exists_transport R hR hRa, exists_transport R' hR' hR'a,
    ?_⟩

  intro hδ ε hε
  obtain ⟨C, hC, hmass⟩ := hcmp
  have hwideapprox : ApproxW (plainW c uf (d₁') d₂ T) R.toFun R'.toFun :=
    approxW_of_approxW_ample_of_pos c uf _ d₂ κ T hc hd₁'pos hlt hκ hwf hcovf hampcov Θ Θ'
      (transport R hRf) (isGenuine_transport R hR hRf) (transport R' hR'f) (isGenuine_transport R' hR' hR'f) hω hδ
  have hnarrow : ApproxW (plainW c u (d₁') d₂ T) R.toFun R'.toFun := hwideapprox.mono hwide
  obtain ⟨s, l, hsl⟩ :=
    hnarrow (ε / (C + 1)) (ENNReal.div_pos hε.ne' (ENNReal.add_ne_top.mpr ⟨hC, ENNReal.one_ne_top⟩))
  refine ⟨s, l, lt_of_le_of_lt (hmass s l) ?_⟩
  calc C * massW (plainW c u (d₁') d₂ T) R.toFun R'.toFun s l
      ≤ (C + 1) * massW (plainW c u (d₁') d₂ T) R.toFun R'.toFun s l :=
        mul_le_mul_left le_self_add _
    _ < ε := by rw [mul_comm]; exact ENNReal.mul_lt_of_lt_div hsl

end AutomorphicForm.WindowPassage
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage.CompactSlabComparison P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.AutomorphicForm.WindowPassage"

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hc : 0 < c)
    (hu : ∀ x : (w : InfinitePlace K) → w.Completion, ∃ ξ : 𝓞 K, ∀ w : InfinitePlace K,
      ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ u)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    ∃ u' d₁' κ : ℝ, 0 < d₁' ∧ d₁' < d₂ ∧ 1 ≤ κ ∧
      CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ) ∧
      (∃ Rκ : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ.toRawCentral Rκ ∧ Rκ.toFun = R.toFun) ∧
      (∃ R'κ : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ'.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ'.toRawCentral R'κ ∧ R'κ.toFun = R'.toFun) ∧
      ((∀ δ : ℝ≥0∞, 0 < δ →
          ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ,
                (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < δ) →
        ∀ ε : ℝ≥0∞, 0 < ε →
          ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
                (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε) :=
  AutomorphicForm.WindowPassage.passage_frame K c u d₁ d₂ T hd hc hu hcov Θ Θ' hΘ R hR R' hR'

end S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre (solution)
