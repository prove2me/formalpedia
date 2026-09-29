-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e8ccce82-c471-5e06-a33b-e4e0f4984a60

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicHaar AutomorphicForm MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace CompactSquareMass

open NumberField.TateGlobal NumberField.AdelicVolume AutomorphicForm.SiegelCovering
open scoped ProbabilityTheory Pointwise

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

variable (K : Type) [Field K] [NumberField K]

private abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

variable {K}

private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

variable (K)

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

private def sq (φ : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ := (‖φ y‖₊ : ℝ≥0∞) ^ 2

variable {K}

private theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

private theorem normDet_central (c : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K c * x)) =
      ideleNorm K c ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, det_centralScalar, pow_two, ideleNorm_mul, pow_two]

private theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

omit [NumberField K] in

private theorem exists_completion_norm_eq (w : InfinitePlace K) (s : ℝ) (hs : 0 ≤ s) :
    ∃ a : w.Completion, ‖a‖ = s := by
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw s
    refine ⟨a, ?_⟩
    have h1 : (InfinitePlace.Completion.extensionEmbedding w a : ℂ) = (s : ℂ) := by
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, ha]
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw (s : ℂ)
    refine ⟨a, ?_⟩
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]

private theorem exists_ideleNorm_eq (t : ℝ) (ht : 0 < t) : ∃ c : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K c = t := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨a, ha⟩ := exists_completion_norm_eq w (t ^ ((w.mult : ℝ)⁻¹)) (Real.rpow_nonneg ht.le _)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact (Real.rpow_pos_of_pos ht _).ne ha
  refine ⟨archCentralUnit K w (Units.mk0 a ha0), ?_⟩
  unfold ideleNorm
  rw [AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one K _ (archCentralUnit_snd w _),
    Finset.prod_eq_single w (fun v _ hv => by rw [archCentralUnit_fst_of_ne w _ hv, norm_one, one_pow])
      (fun h => (h (Finset.mem_univ w)).elim),
    archCentralUnit_fst_self]
  show ‖a‖ ^ w.mult = t
  rw [ha, Real.rpow_inv_natCast_pow ht.le InfinitePlace.mult_ne_zero]

private theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

private theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

private theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, normDet_global]
  exact Iff.rfl

private scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

private theorem smulInvariant_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ slab K α β =
      (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ slab K α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, slab_Γ_stable]
  rw [hset, measure_preimage_mul]

private theorem countable_K : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_Γ : Countable (Γ K) := by
  haveI := countable_K (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) := Units.val_injective.countable
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

private theorem central_comm (c : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    X * centralScalar (𝓞 K) K c = centralScalar (𝓞 K) K c * X :=
  AutomorphicForm.SiegelCovering.mul_centralScalar_comm c X

private theorem measurable_sq (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) : Measurable (sq K φ) :=
  (measurable_coe_nnreal_ennreal.comp hφ.measurable.nnnorm).pow_const 2

private theorem shifts (a b α β : ℝ) (ha : 0 < a) (hβ : 0 < β) (hαβ : α < β) :
    ∃ Zs : Finset (AdeleRing (𝓞 K) K)ˣ, ∀ r ∈ Set.Icc a b, ∃ z ∈ Zs,
      ideleNorm K z ^ 2 * r ∈ Set.Icc α β := by
  classical

  set θ : ℝ := max (α / β) (1 / 2) with hθ
  have hθ_half : (1 / 2 : ℝ) ≤ θ := le_max_right _ _
  have hθ_pos : 0 < θ := by linarith
  have hθ_lt : θ < 1 := max_lt ((div_lt_one hβ).2 hαβ) (by norm_num)
  have hαθ : α ≤ θ * β := by
    have h : α / β ≤ θ := le_max_left _ _
    calc α = α / β * β := (div_mul_cancel₀ α hβ.ne').symm
      _ ≤ θ * β := mul_le_mul_of_nonneg_right h hβ.le

  have hs_pos : ∀ k : ℕ, 0 < θ ^ k * (β / a) := fun k => mul_pos (pow_pos hθ_pos k) (div_pos hβ ha)
  have hz : ∀ k : ℕ, ∃ z : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K z = Real.sqrt (θ ^ k * (β / a)) :=
    fun k => exists_ideleNorm_eq _ (Real.sqrt_pos.2 (hs_pos k))
  choose z hz using hz

  obtain ⟨N, hN⟩ : ∃ N : ℕ, θ ^ N * (b / a) ≤ 1 := by
    rcases le_or_gt b 0 with hb | hb
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact (div_nonpos_iff.2 (Or.inr ⟨hb, ha.le⟩)).trans zero_le_one
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ha hb) hθ_lt
      refine ⟨N, ?_⟩
      have h := mul_le_mul_of_nonneg_right hN.le (div_pos hb ha).le
      rwa [div_mul_div_comm, mul_comm b a, div_self (mul_pos ha hb).ne'] at h
  refine ⟨(Finset.range (N + 1)).image z, fun r hr => ?_⟩
  obtain ⟨har, hrb⟩ := hr
  set t : ℝ := r / a with ht
  have ht_one : 1 ≤ t := (one_le_div ha).2 har
  have ht_le : t ≤ b / a := div_le_div_of_nonneg_right hrb ha.le

  have hex : ∃ k : ℕ, θ ^ k * t ≤ 1 :=
    ⟨N, (mul_le_mul_of_nonneg_left ht_le (pow_pos hθ_pos N).le).trans hN⟩
  set k : ℕ := Nat.find hex with hk
  have hk_spec : θ ^ k * t ≤ 1 := Nat.find_spec hex
  have hk_le : k ≤ N := Nat.find_min' hex ((mul_le_mul_of_nonneg_left ht_le (pow_pos hθ_pos N).le).trans hN)
  have hk_lower : θ ≤ θ ^ k * t := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero, one_mul]
      exact hθ_lt.le.trans ht_one
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hkpos).symm⟩
      have hjlt : j < k := by omega
      have hmin : ¬ θ ^ j * t ≤ 1 := Nat.find_min hex (hk ▸ hjlt)
      rw [not_le] at hmin
      calc θ = θ * 1 := (mul_one θ).symm
        _ ≤ θ * (θ ^ j * t) := mul_le_mul_of_nonneg_left hmin.le hθ_pos.le
        _ = θ ^ k * t := by rw [hj, pow_succ, mul_comm (θ ^ j) θ, mul_assoc]
  refine ⟨z k, Finset.mem_image_of_mem z (Finset.mem_range.2 (Nat.lt_succ_of_le hk_le)), ?_⟩
  rw [hz k, Real.sq_sqrt (hs_pos k).le]
  have hval : θ ^ k * (β / a) * r = β * (θ ^ k * t) := by
    rw [ht]; ring
  rw [hval]
  constructor
  · calc α ≤ θ * β := hαθ
      _ = β * θ := mul_comm _ _
      _ ≤ β * (θ ^ k * t) := mul_le_mul_of_nonneg_left hk_lower hβ.le
  · calc β * (θ ^ k * t) ≤ β * 1 := mul_le_mul_of_nonneg_left hk_spec hβ.le
      _ = β := mul_one β

private theorem transfer (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Set (AdelicGL2 (𝓞 K) K)) :
    ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, sq K φ y ∂(μ K) =
      ENNReal.ofReal ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖⁻¹) ^ 2) * ∫⁻ y in S, sq K φ y ∂(μ K) := by
  have hmp : MeasurePreserving (fun y : AdelicGL2 (𝓞 K) K => centralScalar (𝓞 K) K z * y) (μ K) (μ K) :=
    measurePreserving_mul_left (μ K) _
  have hemb : MeasurableEmbedding (fun y : AdelicGL2 (𝓞 K) K => centralScalar (𝓞 K) K z * y) :=
    (MeasurableEquiv.mulLeft (centralScalar (𝓞 K) K z)).measurableEmbedding
  have hv : (0 : ℝ) < ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  set c : ℝ≥0∞ := (‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 (Units.ne_zero _)))
  have hctop : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hpt : ∀ y : AdelicGL2 (𝓞 K) K, sq K φ (centralScalar (𝓞 K) K z * y) = c * sq K φ y := by
    intro y
    simp only [sq, hφ.central_transform ⟨z, Subgroup.mem_top z⟩ y, nnnorm_mul, ENNReal.coe_mul, mul_pow, hc]
  have hconst : ENNReal.ofReal ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖⁻¹) ^ 2) = c⁻¹ := by
    rw [ENNReal.ofReal_pow (inv_nonneg.2 hv.le), ENNReal.ofReal_inv_of_pos hv, ← coe_nnnorm,
      ENNReal.ofReal_coe_nnreal, hc, ENNReal.inv_pow]
  have hS := hmp.setLIntegral_comp_preimage_emb hemb (sq K φ) S
  rw [hconst, ← hS]
  calc ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, sq K φ y ∂(μ K)
      = ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, c⁻¹ * (c * sq K φ y) ∂(μ K) := by
        refine lintegral_congr fun y => ?_
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ = c⁻¹ * ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, c * sq K φ y ∂(μ K) :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0)
    _ = c⁻¹ * ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, sq K φ (centralScalar (𝓞 K) K z * y)
          ∂(μ K) := by
        simp_rw [hpt]

private theorem unfold (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφΓ : ∀ (γ : Γ K) (y : AdelicGL2 (𝓞 K) K), φ (γ • y) = φ y)
    (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E) (hE : E ⊆ slab K α β) (n : ℕ)
    (hn : ∀ y : AdelicGL2 (𝓞 K) K, ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard ≤ n) :
    ∫⁻ y in E, sq K φ y ∂(μ K) ≤ (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
  haveI := countable_Γ (K := K)
  haveI := smulInvariant_restrict_slab (K := K) α β
  have hsqΓ : ∀ (γ : Γ K) (y : AdelicGL2 (𝓞 K) K), sq K φ (γ⁻¹ • y) = sq K φ y := by
    intro γ y
    simp only [sq, hφΓ]

  have hE' : ∫⁻ y in E, sq K φ y ∂(μ K) = ∫⁻ y in E, sq K φ y ∂((μ K).restrict (slab K α β)) := by
    rw [Measure.restrict_restrict' (slab_measurable α β), Set.inter_eq_left.2 hE]
  have hΦ' : ∫⁻ y in Φ₀, sq K φ y ∂((μ K).restrict (slab K α β)) ≤ ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
    rw [Measure.restrict_restrict' (slab_measurable α β)]
    exact lintegral_mono_set Set.inter_subset_left
  rw [hE']
  calc ∫⁻ y in E, sq K φ y ∂((μ K).restrict (slab K α β))
      = ∑' γ : Γ K, ∫⁻ y in γ • E ∩ Φ₀, sq K φ (γ⁻¹ • y) ∂((μ K).restrict (slab K α β)) :=
        hΦ₀.setLIntegral_eq_tsum' _ E
    _ = ∑' γ : Γ K, ∫⁻ y in Φ₀, (γ • E).indicator (fun _ => (1 : ℝ≥0∞)) y * sq K φ y
          ∂((μ K).restrict (slab K α β)) := by
        refine tsum_congr fun γ => ?_
        simp_rw [hsqΓ]
        rw [← Measure.restrict_restrict (hEm.const_smul γ), ← lintegral_indicator (hEm.const_smul γ)]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ γ • E <;> simp [Set.indicator, hy]
    _ = ∫⁻ y in Φ₀, (∑' γ : Γ K, (γ • E).indicator (fun _ => (1 : ℝ≥0∞)) y) * sq K φ y
          ∂((μ K).restrict (slab K α β)) := by
        rw [← lintegral_tsum]
        · simp_rw [ENNReal.tsum_mul_right]
        · intro γ
          exact ((measurable_const.indicator (hEm.const_smul γ)).mul (measurable_sq φ hφc)).aemeasurable
    _ ≤ ∫⁻ y in Φ₀, (n : ℝ≥0∞) * sq K φ y ∂((μ K).restrict (slab K α β)) := by
        refine lintegral_mono fun y => ?_
        gcongr
        have h1 : ∑' γ : ({γ : Γ K | y ∈ γ • E} : Set (Γ K)), (1 : ℝ≥0∞) =
            ∑' γ : Γ K, (γ • E).indicator (fun _ => (1 : ℝ≥0∞)) y :=
          (tsum_subtype ({γ : Γ K | y ∈ γ • E} : Set (Γ K)) fun _ => (1 : ℝ≥0∞)).trans
            (tsum_congr fun γ => by by_cases hγ : y ∈ γ • E <;> simp [Set.indicator, hγ])
        rw [← h1, ENNReal.tsum_set_one]
        calc (({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard : ℝ≥0∞)
            ≤ ((n : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 (hn y)
          _ = (n : ℝ≥0∞) := ENat.toENNReal_coe n
    _ = (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂((μ K).restrict (slab K α β)) := lintegral_const_mul _ (measurable_sq φ hφc)
    _ ≤ (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by gcongr

private theorem globalPoints_entry (δ : Matrix.GeneralLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((globalPoints (𝓞 K) K δ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      = algebraMap K (AdeleRing (𝓞 K) K) ((δ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

private theorem finite_setOf_mem_of_isCompact {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ({γ : Γ K | (γ : AdelicGL2 (𝓞 K) K) ∈ E} : Set (Γ K)).Finite := by

  have hfin : ∀ i j : Fin 2, ({q : K | algebraMap K (AdeleRing (𝓞 K) K) q ∈
      (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) '' E} : Set K).Finite :=
    fun i j =>
      NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K
        (hE.image (Units.continuous_val.matrix_elem i j))

  have hT : (Set.pi Set.univ fun i : Fin 2 => Set.pi Set.univ fun j : Fin 2 =>
      algebraMap K (AdeleRing (𝓞 K) K) '' {q : K | algebraMap K (AdeleRing (𝓞 K) K) q ∈
        (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) '' E} :
          Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => (hfin i j).image _
  refine Set.Finite.of_finite_image (f := fun γ : Γ K =>
    ((γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) (hT.subset ?_) ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨δ, hδ⟩ := Γ_smul_eq γ
    intro i _ j _
    refine ⟨(δ : Matrix (Fin 2) (Fin 2) K) i j, ⟨(γ : AdelicGL2 (𝓞 K) K), hγ, ?_⟩, ?_⟩
    · show ((γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = _
      rw [hδ, globalPoints_entry]
    · show _ = ((γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      rw [hδ, globalPoints_entry]
  · intro γ _ γ' _ h
    exact Subtype.ext (Units.ext h)

private theorem exists_forall_encard_le_of_isCompact {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ∃ n : ℕ, ∀ y : AdelicGL2 (𝓞 K) K, ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard ≤ n := by
  have hEE : IsCompact (Set.image2 (fun e e' : AdelicGL2 (𝓞 K) K => e * e'⁻¹) E E) := by
    rw [← Set.image_prod]
    exact (hE.prod hE).image (continuous_fst.mul continuous_snd.inv)
  have hS := finite_setOf_mem_of_isCompact hEE
  refine ⟨hS.toFinset.card, fun y => ?_⟩
  rcases ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.encard_empty]
    exact zero_le
  obtain ⟨e₀, he₀, hγ₀e₀⟩ := hγ₀
  beta_reduce at hγ₀e₀
  rw [Γ_smul] at hγ₀e₀
  calc ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard
      = ((fun γ : Γ K => γ₀⁻¹ * γ) '' {γ : Γ K | y ∈ γ • E}).encard :=
        (Set.InjOn.encard_image fun _ _ _ _ h => mul_left_cancel h).symm
    _ ≤ ({γ : Γ K | (γ : AdelicGL2 (𝓞 K) K) ∈
          Set.image2 (fun e e' : AdelicGL2 (𝓞 K) K => e * e'⁻¹) E E} : Set (Γ K)).encard := by
        refine Set.encard_le_encard ?_
        rintro _ ⟨γ, hγ, rfl⟩
        obtain ⟨e, he, hγe⟩ := hγ
        beta_reduce at hγe
        rw [Γ_smul] at hγe
        have h : (γ₀ : AdelicGL2 (𝓞 K) K) * e₀ = (γ : AdelicGL2 (𝓞 K) K) * e := hγ₀e₀.trans hγe.symm
        refine ⟨e₀, he₀, e, he, ?_⟩
        show e₀ * e⁻¹ = ((γ₀⁻¹ * γ : Γ K) : AdelicGL2 (𝓞 K) K)
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        calc e₀ * e⁻¹ = (γ₀ : AdelicGL2 (𝓞 K) K)⁻¹ * ((γ₀ : AdelicGL2 (𝓞 K) K) * e₀) * e⁻¹ := by group
          _ = (γ₀ : AdelicGL2 (𝓞 K) K)⁻¹ * ((γ : AdelicGL2 (𝓞 K) K) * e) * e⁻¹ := by rw [h]
          _ = (γ₀ : AdelicGL2 (𝓞 K) K)⁻¹ * (γ : AdelicGL2 (𝓞 K) K) := by group
    _ = hS.toFinset.card := hS.encard_eq_coe_toFinset_card

private theorem detRange_of_isCompact {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ∃ a b : ℝ, 0 < a ∧ ∀ y ∈ E, ideleNorm K (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc a b := by
  rcases E.eq_empty_or_nonempty with hEe | hEne
  · exact ⟨1, 1, one_pos, fun y hy => (by rw [hEe] at hy; exact hy.elim)⟩
  obtain ⟨ymin, -, hmin⟩ := hE.exists_isMinOn hEne (continuous_ideleNorm_det K).continuousOn
  obtain ⟨ymax, -, hmax⟩ := hE.exists_isMaxOn hEne (continuous_ideleNorm_det K).continuousOn
  exact ⟨_, _, ideleNorm_pos (Matrix.GeneralLinearGroup.det ymin), fun y hy => ⟨hmin hy, hmax hy⟩⟩

private theorem compact_mass_bound (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (α β : ℝ) (hβ : 0 < β)
    (hαβ : α < β) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
      ∫⁻ y in E, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        ≤ ENNReal.ofReal N * ∫⁻ y in Φ₀, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨a, b, ha, hab⟩ := detRange_of_isCompact hE
  obtain ⟨Zs, hZs⟩ := shifts (K := K) a b α β ha hβ hαβ
  obtain ⟨n, hn⟩ := exists_forall_encard_le_of_isCompact hE
  set w : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun z => (‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖⁻¹) ^ 2 with hw
  have hw_nonneg : ∀ z, 0 ≤ w z := fun z => sq_nonneg _
  refine ⟨(∑ z ∈ Zs, w z) * n, fun φ hφ hφc => ?_⟩
  have hφΓ : ∀ (γ : Γ K) (y : AdelicGL2 (𝓞 K) K), φ (γ • y) = φ y := by
    intro γ y
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hφ.left_invariant]

  set piece : (AdeleRing (𝓞 K) K)ˣ → Set (AdelicGL2 (𝓞 K) K) := fun z =>
    E ∩ {y | ideleNorm K z ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc α β} with hpiece
  have hpiece_meas : ∀ z, MeasurableSet (piece z) := fun z =>
    hE.isClosed.measurableSet.inter
      (measurableSet_Icc.preimage ((continuous_ideleNorm_det K).const_mul _).measurable)
  have hcover : E ⊆ ⋃ z : Zs, piece z := by
    intro y hy
    obtain ⟨z, hz, hzr⟩ := hZs _ (hab y hy)
    exact Set.mem_iUnion.2 ⟨⟨z, hz⟩, hy, hzr⟩

  set shifted : (AdeleRing (𝓞 K) K)ˣ → Set (AdelicGL2 (𝓞 K) K) := fun z =>
    (fun y => centralScalar (𝓞 K) K z * y) '' piece z with hshifted
  have hshifted_meas : ∀ z, MeasurableSet (shifted z) := fun z =>
    (MeasurableEquiv.mulLeft (centralScalar (𝓞 K) K z)).measurableSet_image.2 (hpiece_meas z)
  have hshifted_slab : ∀ z, shifted z ⊆ slab K α β := by
    rintro z _ ⟨y, ⟨-, hy⟩, rfl⟩
    show ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * y)) ∈ Set.Icc α β
    rw [normDet_central]
    exact hy
  have hshifted_count : ∀ z y, ({γ : Γ K | y ∈ γ • shifted z} : Set (Γ K)).encard ≤ n := by
    intro z y
    refine (Set.encard_le_encard ?_).trans (hn ((centralScalar (𝓞 K) K z)⁻¹ * y))
    rintro γ ⟨y₀, ⟨y₁, ⟨hy₁, -⟩, rfl⟩, rfl⟩
    refine ⟨y₁, hy₁, ?_⟩
    beta_reduce
    rw [Γ_smul, Γ_smul, ← mul_assoc (γ : AdelicGL2 (𝓞 K) K), central_comm, mul_assoc, inv_mul_cancel_left]

  have hpiece_bound : ∀ z, ∫⁻ y in piece z, sq K φ y ∂(μ K) ≤
      ENNReal.ofReal (w z) * ((n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)) := by
    intro z
    calc ∫⁻ y in piece z, sq K φ y ∂(μ K)
        ≤ ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' shifted z, sq K φ y ∂(μ K) :=
          lintegral_mono_set (Set.subset_preimage_image _ _)
      _ = ENNReal.ofReal (w z) * ∫⁻ y in shifted z, sq K φ y ∂(μ K) := transfer χ φ hφ z _
      _ ≤ ENNReal.ofReal (w z) * ((n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)) := by
          gcongr
          exact unfold α β Φ₀ hΦ₀ φ hφc hφΓ (shifted z) (hshifted_meas z) (hshifted_slab z) n (hshifted_count z)

  show ∫⁻ y in E, sq K φ y ∂(μ K) ≤ ENNReal.ofReal ((∑ z ∈ Zs, w z) * n) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)
  calc ∫⁻ y in E, sq K φ y ∂(μ K)
      ≤ ∫⁻ y in ⋃ z : Zs, piece z, sq K φ y ∂(μ K) := lintegral_mono_set hcover
    _ ≤ ∑' z : Zs, ∫⁻ y in piece z, sq K φ y ∂(μ K) := lintegral_iUnion_le _ _
    _ = ∑ z : Zs, ∫⁻ y in piece z, sq K φ y ∂(μ K) := tsum_fintype _
    _ ≤ ∑ z : Zs, ENNReal.ofReal (w z) * ((n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)) :=
        Finset.sum_le_sum fun z _ => hpiece_bound z
    _ = (∑ z : Zs, ENNReal.ofReal (w z)) * (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
        rw [← Finset.sum_mul, mul_assoc]
    _ = ENNReal.ofReal ((∑ z ∈ Zs, w z) * n) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
        rw [← Finset.sum_coe_sort Zs w, ENNReal.ofReal_mul (Finset.sum_nonneg fun (z : Zs) _ => hw_nonneg z),
          ENNReal.ofReal_sum_of_nonneg fun (z : Zs) _ => hw_nonneg z, ENNReal.ofReal_natCast]

end CompactSquareMass
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain.CompactSquareMass"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain.CompactSquareMass"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∫⁻ y in C, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal N * ∫⁻ y in Φ₀, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  CompactSquareMass.compact_mass_bound χ α β hβ hαβ Φ₀ hΦ₀ hC

end S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain (solution)
