-- Prove2me | solution 1 for AutomorphicForm.integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6ce4d189-4cba-5075-b5ca-b020a9aafecb

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

import Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_HaarQuotient
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates"
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

open scoped ENNReal Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 finiteAdelicGL2Subgroup isClosed_finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe unipotentGL2Hom localAt continuous_localAt"
namespace MassR5
p2m_open "AutomorphicForm"

open MeasureTheory HaarQuotient
open scoped ENNReal

section LevelOneOpen

namespace IntegralUnits

open Matrix NumberField

variable {F : Type*} [Field F] (O : ValuationSubring F)

def IsIntegralUnit (k : GL (Fin 2) F) : Prop :=
  (∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O) ∧ ∀ i j, ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O

variable {O}

theorem isOpen_setOf_isIntegralUnit [TopologicalSpace F] [IsTopologicalRing F] (hO : IsOpen (O : Set F)) :
    IsOpen {k : GL (Fin 2) F | IsIntegralUnit O k} := by
  have h1 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := fun i j =>
    hO.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} :=
    fun i j => hO.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have hset : {k : GL (Fin 2) F | IsIntegralUnit O k} =
      (⋂ i, ⋂ j, {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O}) ∩
        ⋂ i, ⋂ j, {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := by
    ext k
    simp only [IsIntegralUnit, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

end IntegralUnits

namespace LevelOne

open IsDedekindDomain AdelicDock IntegralUnits

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun h => h.integral, fun h => ⟨h, ?_, ?_⟩⟩
  · rw [AdelicLevel.idealBound_top]
    have := h 1 0
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  · rw [AdelicLevel.idealBound_top]
    have := sub_mem (h 1 1) (one_mem (v.adicCompletionIntegers ℚ))
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ ↔ IsIntegralUnit (v.adicCompletionIntegers ℚ) k := by
  rw [mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff]
  exact Iff.rfl

theorem isOpen_localLevelOne_top :
    IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  have hset : ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) =
        {k : GL (Fin 2) (v.adicCompletion ℚ) | IsIntegralUnit (v.adicCompletionIntegers ℚ) k} := by
    ext k
    exact mem_localLevelOne_top_iff v k
  rw [hset]
  exact isOpen_setOf_isIntegralUnit ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v)

end LevelOne

end LevelOneOpen

namespace DensNorm

open scoped Pointwise

section Norm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SigmaCompactSpace G] [WeaklyLocallyCompactSpace G]
  (H : Subgroup G) (μH : Measure H)

def coeff (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem weight_eq (g : G) :
    weight H μH g = ∑' n : ℕ,
      coeff H μH n * (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  unfold HaarQuotient.weight
  rw [dif_pos ⟨inferInstance, inferInstance⟩]
  rfl

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem coeff_le (n : ℕ) : coeff H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n :=
  mul_le_of_le_one_right (by simp) (ENNReal.inv_le_one.mpr le_self_add)

theorem lintegral_term_le [μH.IsMulRightInvariant] (n : ℕ) (g : G) :
    ∫⁻ x : H, coeff H μH n *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) ∂μH ≤
      (2⁻¹ : ℝ≥0∞) ^ n := by
  set E : Set G := CompactExhaustion.choice G (n + 1) with hE
  set U : Set H := {x : H | (x : G) * g ∈ interior E} with hU
  have hUmeas : MeasurableSet U :=
    (isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)).measurableSet
  have hfun : (fun x : H => coeff H μH n * (interior E).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g)) =
      fun x : H => U.indicator (fun _ => coeff H μH n) x := by
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (show (x : G) * g ∈ interior E from hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (x : G) * g ∉ interior E from hx)]
  rw [hfun, lintegral_indicator_const hUmeas]

  by_cases hne : U = ∅
  · simp [hne]
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hsub : U ⊆ (fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by
    intro x hx
    refine ⟨(x : G) * g, interior_subset hx, ((x₀ : G) * g)⁻¹, Set.inv_mem_inv.mpr (interior_subset hx₀), ?_⟩
    simp [mul_assoc]
  calc coeff H μH n * μH U ≤ coeff H μH n * μH ((fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹))) :=
        mul_le_mul_right (measure_mono hsub) _
    _ = coeff H μH n * μH (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by rw [measure_preimage_mul_right]
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
        unfold coeff
        rw [mul_assoc]
        refine mul_le_of_le_one_right (by simp) ?_
        rw [← hE, ← ENNReal.div_eq_inv_mul]
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)

theorem measurable_term (n : ℕ) (g : G) :
    Measurable fun x : H => coeff H μH n *
      (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) :=
  measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet).comp
    (measurable_subtype_coe.mul_const g))

theorem lintegral_weight_mul_ne_top [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ ⊤ := by
  simp_rw [weight_eq H μH]
  rw [lintegral_tsum fun n => (measurable_term H μH n g).aemeasurable]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => lintegral_term_le H μH n g)
  rw [ENNReal.tsum_geometric]
  simp

theorem lintegral_weight_mul_ne_zero [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ 0 := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hg : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  set U : Set H := {x : H | (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)} with hU
  have hUopen : IsOpen U := isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)
  have hU1 : (1 : H) ∈ U := by
    show ((1 : H) : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)
    simpa using hg

  have hcompact : IsCompact (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)) :=
    (hH.isClosedEmbedding_subtypeVal).isCompact_preimage
      (((CompactExhaustion.choice G).isCompact (n + 1)).mul ((CompactExhaustion.choice G).isCompact (n + 1)).inv)
  have hcoeff : coeff H μH n ≠ 0 := by
    unfold coeff
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.mpr ?_)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hcompact.measure_lt_top.ne⟩

  have hterm : coeff H μH n * μH U ≤ ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH := by
    rw [← lintegral_indicator_const hUopen.measurableSet]
    refine lintegral_mono fun x => ?_
    rw [weight_eq H μH]
    refine le_trans ?_ (ENNReal.le_tsum n)
    by_cases hx : x ∈ U
    · have hxg : (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) := hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxg]
    · simp [Set.indicator_of_notMem hx]
  refine ne_of_gt (lt_of_lt_of_le ?_ hterm)
  exact ENNReal.mul_pos hcoeff (hUopen.measure_pos μH ⟨1, hU1⟩).ne'

omit [IsTopologicalGroup G] [BorelSpace G] in

theorem weight_ne_top (g : G) : weight H μH g ≠ ⊤ := by
  rw [weight_eq]
  refine ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ?_ ?_
  · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    exact ENNReal.inv_ne_top.mpr (by simp)
  · refine ENNReal.tsum_le_tsum fun n => ?_
    refine le_trans (mul_le_of_le_one_right (by simp) ?_) (coeff_le H μH n)
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) g |>.trans le_rfl

theorem density_ne_top [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) : density H μH g ≠ ⊤ :=
  ENNReal.div_ne_top (weight_ne_top H μH g) (lintegral_weight_mul_ne_zero H μH hH g)

end Norm

end DensNorm

theorem countable_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) := by
  have hI : Set.Countable (Set.univ : Set (Ideal (𝓞 K))) := by
    have : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := by
      ext I; simp
    rw [this]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOf_absNorm_eq n).countable)
  haveI : Countable (Ideal (𝓞 K)) := Set.countable_univ_iff.mp hI
  exact (Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h))

section Pos

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SigmaCompactSpace G] [WeaklyLocallyCompactSpace G]
  (H : Subgroup G) (μH : Measure H)

theorem weight_pos [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) : weight H μH g ≠ 0 := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hg : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  have hcompact : IsCompact (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)) :=
    (hH.isClosedEmbedding_subtypeVal).isCompact_preimage
      (((CompactExhaustion.choice G).isCompact (n + 1)).mul ((CompactExhaustion.choice G).isCompact (n + 1)).inv)
  have hcoeff : DensNorm.coeff H μH n ≠ 0 := by
    unfold DensNorm.coeff
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.mpr ?_)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hcompact.measure_lt_top.ne⟩
  rw [DensNorm.weight_eq H μH]
  refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum n))
  rw [Set.indicator_of_mem hg, mul_one]
  exact pos_iff_ne_zero.mpr hcoeff

theorem density_pos [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (hH : IsClosed (H : Set G)) (g : G) :
    density H μH g ≠ 0 := by
  unfold HaarQuotient.density
  exact (ENNReal.div_pos_iff.mpr ⟨weight_pos H μH hH g, DensNorm.lintegral_weight_mul_ne_top H μH g⟩).ne'

end Pos

theorem isClopen_ball (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    IsClopen {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(n : ℤ))} := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  set a : p.adicCompletion ℚ := (((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation ℚ p)).symm π :
    WithVal (IsDedekindDomain.HeightOneSpectrum.valuation ℚ p)) : p.adicCompletion ℚ) ^ n with ha
  have hva : Valued.v a = WithZero.exp (-(n : ℤ)) := by
    rw [ha, map_pow, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul]
    simp
  have ha0 : Valued.v.restrict a ≠ 0 := by
    intro h
    have : Valued.v a = 0 := by
      have := (Valuation.restrict_le_iff Valued.v (x := a) (y := 0)).mp (by rw [h]; exact zero_le')
      simpa using this
    rw [hva] at this
    exact WithZero.coe_ne_zero this
  have hset : {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(n : ℤ))} =
      {x | Valued.v.restrict x ≤ Valued.v.restrict a} := by
    ext x; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hva]
  rw [hset]
  exact Valued.isClopen_closedBall _ ha0

theorem isMulRightInvariant_of_comm {H : Type*} [Group H] [MeasurableSpace H] (μ : Measure H)
    [μ.IsMulLeftInvariant] (hcomm : ∀ a b : H, a * b = b * a) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (fun x : H => x * g) = fun x : H => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g

theorem range_mul_comm {M G : Type*} [CommGroup M] [Group G] (φ : M →* G) (a b : φ.range) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem subgroupOf_mul_comm {G : Type*} [Group G] (H K : Subgroup G) (hcomm : ∀ a b : H, a * b = b * a)
    (a b : H.subgroupOf K) : a * b = b * a := by
  apply Subtype.ext
  apply Subtype.ext
  have ha : ((a : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp a.2
  have hb : ((b : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp b.2
  have := congrArg Subtype.val (hcomm ⟨_, ha⟩ ⟨_, hb⟩)
  simpa using this

section U
variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]
omit [TopologicalSpace R] [T2Space R] in
theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | Units.val g 0 0 = 1 ∧ Units.val g 1 0 = 0 ∧ Units.val g 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change Units.val (unipotentGL2 y.toAdd) 0 0 = 1 ∧ Units.val (unipotentGL2 y.toAdd) 1 0 = 0 ∧
      Units.val (unipotentGL2 y.toAdd) 1 1 = 1
    simp [unipotentGL2]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (Units.val g 0 1), ?_⟩
    change unipotentGL2 (Units.val g 0 1) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : Continuous fun g : GL (Fin 2) R => Units.val g := Units.continuous_val
  exact (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))
end U

theorem locallyCompactSpace_generalLinearGroup {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] : LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) A ≃ₜ
      (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ).symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

theorem measurable_lintegral_weight_mul [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable fun g : G => ∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH := by
  have hm : Measurable fun p : H × G => HaarQuotient.weight H μH ((p.1 : G) * p.2) :=
    (measurable_weight H μH).comp ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  exact hm.lintegral_prod_left

theorem measurable_density [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] (H : Subgroup G)
    (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  unfold HaarQuotient.density
  exact (measurable_weight H μH).div (measurable_lintegral_weight_mul H μH)

end Density

end AutomorphicForm.MassR5

end

namespace MassR5Defs

def bigcellP (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : finiteAdelicGL2Subgroup ℚ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k'

def boxP (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ) (g : finiteAdelicGL2Subgroup ℚ) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
      Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
      Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
          WithZero.exp (-(mS p : ℤ)) ∧
      Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
          WithZero.exp (-(mS p : ℤ)))

end MassR5Defs

scoped instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := AutomorphicForm.MassR5.countable_heightOneSpectrum ℚ

namespace MassR5Defs
open AutomorphicForm.MassR5 MeasureTheory

theorem hNloc  : ∀ (n : RSCarrier.finUnipotent) (v : HeightOneSpectrum (𝓞 ℚ)),
    localAt ℚ v ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
      (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range := by
  intro n v
  obtain ⟨y, hy⟩ := Subgroup.mem_subgroupOf.mp n.2
  have e : ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 y.toAdd := by rw [← hy]; rfl
  refine ⟨Multiplicative.ofAdd ((y.toAdd).2 v), ?_⟩
  rw [e]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((unipotentGL2 ((y.toAdd).2 v) : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _) i j =
    ((((unipotentGL2 y.toAdd : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem hNrow  : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ) (j : Fin 2),
    ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j =
      ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j := by
  intro n g j
  obtain ⟨y, hy⟩ := Subgroup.mem_subgroupOf.mp n.2
  have e : ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 y.toAdd := by rw [← hy]; rfl
  rw [Subgroup.coe_mul, Units.val_mul, e, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem hcellN (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
    bigcellP S ((n : finiteAdelicGL2Subgroup ℚ) * g) ↔ bigcellP S g := by
  intro n g
  have key : ∀ v, ∀ (m : GL (Fin 2) (v.adicCompletion ℚ)), m ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range →
      ∀ x : GL (Fin 2) (v.adicCompletion ℚ),
      ((∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, m * x = n' * k') ↔
        (∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n' * k')) := by
    intro v m hm x
    constructor
    · rintro ⟨n', hn', k', hk', h⟩
      exact ⟨m⁻¹ * n', mul_mem (inv_mem hm) hn', k', hk', by rw [mul_assoc, ← h, inv_mul_cancel_left]⟩
    · rintro ⟨n', hn', k', hk', h⟩
      exact ⟨m * n', mul_mem hm hn', k', hk', by rw [h, mul_assoc]⟩
  simp only [bigcellP, Subgroup.coe_mul, map_mul]
  exact forall₂_congr fun v _ => key v _ (hNloc n v) _

theorem hboxN (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ) : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
    boxP S mS ((n : finiteAdelicGL2Subgroup ℚ) * g) ↔ boxP S mS g := by
  intro n g; simp only [boxP, hNrow n g]

theorem hent  : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 2), Continuous fun g : finiteAdelicGL2Subgroup ℚ =>
    ((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p := fun p j =>
  (RestrictedProduct.continuous_eval p).comp (continuous_snd.comp
    ((Units.continuous_val.matrix_elem 1 j).comp continuous_subtype_val))

theorem hcellm (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : MeasurableSet {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g} := by
  have : {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g} = ⋂ v : HeightOneSpectrum (𝓞 ℚ), {g : finiteAdelicGL2Subgroup ℚ | v ∉ S →
      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ ((AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range :
        Set (GL (Fin 2) (v.adicCompletion ℚ))) * (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ)))} := by
    ext g
    simp only [bigcellP, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_mul, SetLike.mem_coe]
    refine forall₂_congr fun v _ => ⟨fun ⟨n, hn, k, hk, h⟩ => ⟨n, hn, k, hk, h.symm⟩, fun ⟨n, hn, k, hk, h⟩ => ⟨n, hn, k, hk, h.symm⟩⟩
  rw [this]
  refine MeasurableSet.iInter fun v => ?_
  by_cases hv : v ∈ S
  · have : {g : finiteAdelicGL2Subgroup ℚ | v ∉ S → localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈
        ((AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Set (GL (Fin 2) (v.adicCompletion ℚ))) *
          (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ)))} = Set.univ := by
      ext g; simp [hv]
    rw [this]; exact MeasurableSet.univ
  · have : {g : finiteAdelicGL2Subgroup ℚ | v ∉ S → localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈
        ((AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Set (GL (Fin 2) (v.adicCompletion ℚ))) *
          (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ)))} =
        ((fun g : finiteAdelicGL2Subgroup ℚ => localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) ⁻¹'
          (((AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Set (GL (Fin 2) (v.adicCompletion ℚ))) *
            (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))))) := by
      ext g; simp [hv]
    rw [this]
    exact ((LevelOne.isOpen_localLevelOne_top v).mul_left.preimage
      ((continuous_localAt (K := ℚ) (v := v)).comp continuous_subtype_val)).measurableSet

theorem hball  : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (f : finiteAdelicGL2Subgroup ℚ → p.adicCompletion ℚ),
    Continuous f → MeasurableSet {g | Valued.v (f g) ≤ WithZero.exp (-(n : ℤ))} := fun p n f hf =>
  ((isClopen_ball p n).preimage hf).isOpen.measurableSet

theorem hboxm (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ) : MeasurableSet {g : finiteAdelicGL2Subgroup ℚ | boxP S mS g} := by
  have e : {g : finiteAdelicGL2Subgroup ℚ | boxP S mS g} =
      (⋂ p : HeightOneSpectrum (𝓞 ℚ), ⋂ j : Fin 2, {g : finiteAdelicGL2Subgroup ℚ | p ∉ S →
        Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ WithZero.exp (-((0 : ℕ) : ℤ))}) ∩
      ⋂ p ∈ S, ({g : finiteAdelicGL2Subgroup ℚ | Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
          WithZero.exp (-(mS p : ℤ))} ∩
        {g : finiteAdelicGL2Subgroup ℚ | Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
          WithZero.exp (-(mS p : ℤ))}) := by
    ext g
    simp only [boxP, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun p j hp => h1 p hp j, fun p hp => h2 p hp⟩, fun ⟨h1, h2⟩ => ⟨fun p hp j => h1 p j hp, fun p hp => h2 p hp⟩⟩
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun p => MeasurableSet.iInter fun j => ?_)
    (Finset.measurableSet_biInter S fun p _ => ?_)
  · by_cases hp : p ∈ S
    · have : {g : finiteAdelicGL2Subgroup ℚ | p ∉ S →
          Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤
            WithZero.exp (-((0 : ℕ) : ℤ))} = Set.univ := by ext g; simp [hp]
      rw [this]; exact MeasurableSet.univ
    · have : {g : finiteAdelicGL2Subgroup ℚ | p ∉ S →
          Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤
            WithZero.exp (-((0 : ℕ) : ℤ))} =
          {g : finiteAdelicGL2Subgroup ℚ | Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤
            WithZero.exp (-((0 : ℕ) : ℤ))} := by ext g; simp [hp]
      rw [this]; exact hball p 0 _ (hent p j)
  · exact (hball p (mS p) _ (hent p 0)).inter (hball p (mS p) _ ((hent p 1).sub continuous_const))

end MassR5Defs

open AutomorphicForm.MassR5 MassR5Defs in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hmS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S → 1 ≤ mS p)
    (hWm : Measurable Wf₁)
    (hWN : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf₁ ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf₁ g‖)
    (hWU : ∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
      ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf₁ (g * u) = Wf₁ g)
    (hW1 : Wf₁ 1 ≠ 0)
    (hCpt : ∃ Cpt : Set (finiteAdelicGL2Subgroup ℚ), IsCompact Cpt ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf₁ g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) :
    (∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
        Integrable ({g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ))))}.indicator
            fun g : finiteAdelicGL2Subgroup ℚ => (Complex.normSq (Wf₁ g) : ℂ))
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin)) ∧
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin))
          {g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) ∧ Wf₁ g ≠ 0} ≠ 0) := by
  classical

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo ℚ
  haveI : SecondCountableTopology (finiteAdelicGL2Subgroup ℚ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (AdelicGL2 (𝓞 ℚ) ℚ) := locallyCompactSpace_generalLinearGroup
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := (isClosed_finiteAdelicGL2Subgroup ℚ).locallyCompactSpace
  haveI : BorelSpace (finiteAdelicGL2Subgroup ℚ) := Subtype.borelSpace _
  obtain ⟨Cpt, hCptc, hmain⟩ := hCpt
  obtain ⟨U, hUo, hU⟩ := hWU

  let ind : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun a =>
    if h : a ∈ finiteAdelicGL2Subgroup ℚ then (if boxP S mS ⟨a, h⟩ ∧ Wf₁ ⟨a, h⟩ ≠ 0 then 1 else 0) else 0
  have hind : ∀ g : finiteAdelicGL2Subgroup ℚ, ind g = if boxP S mS g ∧ Wf₁ g ≠ 0 then 1 else 0 := by
    intro g; simp only [ind, dif_pos g.2]
  obtain ⟨K', hK'c, hsub⟩ :=
    LanglandsTunnell.RankinSelberg.exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul S ind ind
      ⟨Cpt, 1, hCptc, fun g => by rw [hind]; split_ifs <;> simp, fun g hcell hne => by
        rw [hind] at hne
        have hb : boxP S mS g ∧ Wf₁ g ≠ 0 := by by_contra h; rw [if_neg h] at hne; exact hne (mul_zero _)
        exact hmain g hcell hb.2 hb.1⟩

  have hcont : Continuous Wf₁ := by
    refine (IsLocallyConstant.iff_eventually_eq Wf₁).mpr (fun g => ?_) |>.continuous
    have hopen : IsOpen ({g} * (U : Set (finiteAdelicGL2Subgroup ℚ))) := hUo.mul_left
    have hmem : g ∈ ({g} * (U : Set (finiteAdelicGL2Subgroup ℚ))) := Set.mem_mul.mpr ⟨g, rfl, 1, U.one_mem, mul_one g⟩
    filter_upwards [hopen.mem_nhds hmem] with y hy
    obtain ⟨g', rfl, u, hu, rfl⟩ := Set.mem_mul.mp hy
    exact hU _ _ hu
  obtain ⟨M, hM⟩ := hK'c.exists_bound_of_continuousOn hcont.continuousOn
  have hbound : ∀ g : finiteAdelicGL2Subgroup ℚ, bigcellP S g → boxP S mS g → Wf₁ g ≠ 0 → ‖Wf₁ g‖ ≤ M := by
    intro g hcell hbox hne
    have hg : g ∈ {g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
            localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k) ∧ ind g * ind g ≠ 0} := by
      refine ⟨hcell, ?_⟩
      rw [hind, if_pos ⟨hbox, hne⟩]; norm_num
    obtain ⟨n, hn, k, hk, hnk⟩ := Set.mem_mul.mp (hsub hg)
    rw [← hnk, hWN ⟨n, hn⟩ k]
    exact hM k hk
  have hcutm : MeasurableSet {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} := by
    rw [Set.setOf_and]; exact (hcellm S).inter (hboxm S mS)

  have hzz : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  intro μf _ μNFin _

  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      W₁ g = if bigcellP S g ∧ boxP S mS g then Wf₁ g else 0 :=
    ⟨fun a => if h : a ∈ finiteAdelicGL2Subgroup ℚ then (if bigcellP S ⟨a, h⟩ ∧ boxP S mS ⟨a, h⟩ then Wf₁ ⟨a, h⟩ else 0) else 0,
      fun g => by simp only [dif_pos g.2]⟩
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      F₁ g = (starRingEnd ℂ) (Wf₁ g) :=
    ⟨fun a => if h : a ∈ finiteAdelicGL2Subgroup ℚ then (starRingEnd ℂ) (Wf₁ ⟨a, h⟩) else 0, fun g => by simp only [dif_pos g.2]⟩
  have hWF : ∀ g : finiteAdelicGL2Subgroup ℚ, W₁ g * F₁ g =
      {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g}.indicator (fun g => ((Complex.normSq (Wf₁ g) : ℝ) : ℂ)) g := by
    intro g
    rw [hW₁, hF₁]
    by_cases hc : bigcellP S g ∧ boxP S mS g
    · rw [if_pos hc, Set.indicator_of_mem (show g ∈ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc),
        Complex.mul_conj]
    · rw [if_neg hc, zero_mul,
        Set.indicator_of_notMem (show g ∉ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc)]
  have hmeasI : Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
      {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g}.indicator (fun g => ((Complex.normSq (Wf₁ g) : ℝ) : ℂ)) g :=
    (Complex.measurable_ofReal.comp (Complex.continuous_normSq.measurable.comp hWm)).indicator hcutm
  have hm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W₁ g * F₁ g := by
    have : (fun g : finiteAdelicGL2Subgroup ℚ => W₁ g * F₁ g) =
        {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g}.indicator (fun g => ((Complex.normSq (Wf₁ g) : ℝ) : ℂ)) :=
      funext hWF
    rw [this]; exact hmeasI
  have hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W₁ ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F₁ ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W₁ (g : AdelicGL2 (𝓞 ℚ) ℚ) * F₁ (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
    intro n g
    rw [hWF, hWF]
    by_cases hc : bigcellP S g ∧ boxP S mS g
    · have hc' : bigcellP S ((n : finiteAdelicGL2Subgroup ℚ) * g) ∧ boxP S mS ((n : finiteAdelicGL2Subgroup ℚ) * g) :=
        ⟨(hcellN S n g).mpr hc.1, (hboxN S mS n g).mpr hc.2⟩
      rw [Set.indicator_of_mem (show _ ∈ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc'),
        Set.indicator_of_mem (show g ∈ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc),
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hWN n g]
    · have hc' : ¬ (bigcellP S ((n : finiteAdelicGL2Subgroup ℚ) * g) ∧ boxP S mS ((n : finiteAdelicGL2Subgroup ℚ) * g)) := fun h =>
        hc ⟨(hcellN S n g).mp h.1, (hboxN S mS n g).mp h.2⟩
      rw [Set.indicator_of_notMem (show _ ∉ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc'),
        Set.indicator_of_notMem (show g ∉ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc)]
  have hsupp : ∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ, ‖W₁ g * F₁ g‖ ≤ B₀) ∧
      ∀ g : finiteAdelicGL2Subgroup ℚ,
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
            ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
        W₁ g * F₁ g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
            ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
              localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ) := by
    refine ⟨Cpt, M ^ 2, hCptc, fun g => ?_, fun g hcell hne => ?_⟩
    · rw [hWF]
      by_cases hc : bigcellP S g ∧ boxP S mS g
      · rw [Set.indicator_of_mem (show g ∈ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc),
          Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
        by_cases hz : Wf₁ g = 0
        · rw [hz, norm_zero, zero_pow two_ne_zero]; positivity
        · exact pow_le_pow_left₀ (norm_nonneg _) (hbound g hc.1 hc.2 hz) 2
      · rw [Set.indicator_of_notMem (show g ∉ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc), norm_zero]
        positivity
    · rw [hWF] at hne
      have hc : bigcellP S g ∧ boxP S mS g := by
        by_contra h
        exact hne (Set.indicator_of_notMem (show g ∉ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from h) _)
      rw [Set.indicator_of_mem (show g ∈ {g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g} from hc)] at hne
      have hz : Wf₁ g ≠ 0 := by
        intro h; apply hne; rw [h]; simp
      exact hmain g hcell hz hc.2
  have hfin := LanglandsTunnell.RankinSelberg.lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support
    μf μNFin S W₁ F₁ hm hinv hsupp 0

  have hintegrand : ∀ g : finiteAdelicGL2Subgroup ℚ,
      ‖{g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                    localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W₁ g) g *
          {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                    localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F₁ g) g‖ₑ *
        ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (0 : ℝ)) =
      ‖{g : finiteAdelicGL2Subgroup ℚ | bigcellP S g ∧ boxP S mS g}.indicator (fun g => ((Complex.normSq (Wf₁ g) : ℝ) : ℂ)) g‖ₑ := by
    intro g
    rw [Real.rpow_zero, ENNReal.ofReal_one, mul_one]
    by_cases hcell : bigcellP S g
    · have hcellU := hcell
      simp only [bigcellP] at hcellU
      congr 1
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_pos hcellU, if_pos hcellU, hWF g]
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    · have hcellU := hcell
      simp only [bigcellP] at hcellU
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg hcellU, zero_mul, if_neg (fun h => hcell h.1)]
  simp_rw [hintegrand] at hfin
  refine ⟨⟨hmeasI.aestronglyMeasurable, hfin⟩, ?_⟩

  haveI : μNFin.IsMulRightInvariant :=
    isMulRightInvariant_of_comm μNFin (subgroupOf_mul_comm _ _ (range_mul_comm _))
  have hNclosed : IsClosed ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) := by
    rw [Subgroup.coe_subgroupOf]
    exact (isClosed_range_unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).preimage continuous_subtype_val
  set O : Set (finiteAdelicGL2Subgroup ℚ) := ((U : Set (finiteAdelicGL2Subgroup ℚ)) ∩
      ((↑) : finiteAdelicGL2Subgroup ℚ → AdelicGL2 (𝓞 ℚ) ℚ) ⁻¹'
        ((NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ ⊤ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ))) ∩
      ⋂ p ∈ S, ({g : finiteAdelicGL2Subgroup ℚ | Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
            WithZero.exp (-(mS p : ℤ))} ∩
          {g : finiteAdelicGL2Subgroup ℚ | Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
            WithZero.exp (-(mS p : ℤ))}) with hO
  have hOo : IsOpen O := by
    refine ((hUo.inter ((NumberField.AdelicLevel.isOpen_levelOne (𝓞 ℚ) ℚ (N := ⊤) top_ne_bot).preimage
      continuous_subtype_val)).inter (isOpen_biInter_finset fun p _ => ?_))
    exact (((isClopen_ball p (mS p)).preimage (hent p 0)).isOpen).inter
      (((isClopen_ball p (mS p)).preimage ((hent p 1).sub continuous_const)).isOpen)
  have h1O : (1 : finiteAdelicGL2Subgroup ℚ) ∈ O := by
    refine ⟨⟨U.one_mem, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, OneMemClass.coe_one]; exact one_mem _
    · simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, OneMemClass.coe_one, Units.val_one,
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.one_apply_eq]
      intro p _
      refine ⟨?_, ?_⟩
      · show Valued.v ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) p) ≤ _
        rw [show ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) p) = 0 from rfl, map_zero]; exact zero_le'
      · show Valued.v ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) p - 1) ≤ _
        rw [show ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) p) = 1 from rfl, sub_self, map_zero]; exact zero_le'
  have hOsub : O ⊆ {g : finiteAdelicGL2Subgroup ℚ | (bigcellP S g ∧ boxP S mS g) ∧ Wf₁ g ≠ 0} := by
    intro g hg
    obtain ⟨⟨hgU, hgL⟩, hgB⟩ := hg
    have hlev : (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ ⊤ := hgL
    rw [NumberField.AdelicLevel.mem_levelOne_iff, NumberField.AdelicLevel.mem_finiteLevelOne_iff] at hlev
    obtain ⟨hl1, hl2⟩ := hlev
    have hint : ∀ (i j : Fin 2) (v : HeightOneSpectrum (𝓞 ℚ)),
        ((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v ∈ v.adicCompletionIntegers ℚ :=
      fun i j v => hl1.integral i j v
    have hint' : ∀ (i j : Fin 2) (v : HeightOneSpectrum (𝓞 ℚ)),
        (((((g⁻¹ : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v ∈
          v.adicCompletionIntegers ℚ := by
      intro i j v
      have := hl2.integral i j v
      rwa [← map_inv] at this
    have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
      intro v
      rw [LevelOne.mem_localLevelOne_top_iff]
      refine ⟨fun i j => hint i j v, fun i j => ?_⟩
      rw [← map_inv, ← Subgroup.coe_inv]
      exact hint' i j v
    have hgB' := Set.mem_iInter₂.mp hgB
    refine ⟨⟨fun v _ => ⟨1, one_mem _, _, hloc v, (one_mul _).symm⟩, fun p _ j => ?_, fun p hp => ?_⟩, ?_⟩
    · exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := p)).mp (hint 1 j p)
    · exact hgB' p hp
    · rw [← one_mul g, hU 1 g hgU]; exact hW1
  have hOmeas : MeasurableSet O := hOo.measurableSet
  have hmassEq : {g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) ∧ Wf₁ g ≠ 0} =
      {g : finiteAdelicGL2Subgroup ℚ | (bigcellP S g ∧ boxP S mS g) ∧ Wf₁ g ≠ 0} := by
    ext g; simp only [Set.mem_setOf_eq, bigcellP, boxP, and_assoc]
  rw [hmassEq]
  intro hzero
  have hO0 : (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) O = 0 :=
    measure_mono_null hOsub hzero
  haveI : SigmaCompactSpace RSCarrier.finUnipotent := hNclosed.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  rw [MeasureTheory.withDensity_apply _ hOmeas] at hO0
  have hρm : Measurable (HaarQuotient.density RSCarrier.finUnipotent μNFin) := measurable_density _ μNFin
  rw [MeasureTheory.lintegral_eq_zero_iff hρm] at hO0
  have hpos : ∀ g, HaarQuotient.density RSCarrier.finUnipotent μNFin g ≠ 0 := density_pos _ μNFin hNclosed
  have : (μf.restrict O) Set.univ = 0 := by
    have h := (Filter.EventuallyEq.symm hO0)
    have : ∀ᵐ g ∂(μf.restrict O), False := by
      filter_upwards [hO0] with g hg
      exact hpos g hg
    simpa [Filter.eventually_false_iff_eq_bot, ae_eq_bot] using this
  rw [Measure.restrict_apply_univ] at this
  exact absurd this (hOo.measure_pos μf ⟨1, h1O⟩).ne'

#print axioms solution

end S_AutomorphicForm_integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat
end P2MW
export P2MW.S_AutomorphicForm_integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat (solution)
