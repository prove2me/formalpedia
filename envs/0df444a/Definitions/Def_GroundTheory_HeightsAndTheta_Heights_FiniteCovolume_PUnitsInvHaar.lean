-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnitsInvHaar
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnitsInvHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:29.150521+00:00
-- url     : https://prove2.me/theorems/8ce8b004-826b-45ef-a9d1-03f074f5e2d0
-- title:
--   PUnits Inv Haar
-- statement:
--   Definitions and structural lemmas for PUnits Inv Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnitsInvHaar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnitsInvHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Measure Set
open scoped ENNReal NNReal
noncomputable section
namespace UnitsInvHaar
variable {I : Type*} [Fintype I]
def invSqWeight (b : I → ℂ) : ℝ≥0∞ := ∏ i, ‖b i‖ₑ⁻¹ ^ 2
def weightedVolume (I : Type*) [Fintype I] : Measure (I → ℂ) :=
  (volume : Measure (I → ℂ)).withDensity invSqWeight
def invUnits (b : I → ℂ) : I → ℂˣ := fun i => if h : b i = 0 then 1 else (Units.mk0 (b i) h)⁻¹
def invHaar (I : Type*) [Fintype I] : Measure (I → ℂˣ) := (weightedVolume I).map invUnits
def scaleMap (t : I → ℂˣ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) :=
  LinearMap.pi fun i => (Algebra.lmul ℝ ℂ (t i : ℂ)).comp (LinearMap.proj i)
omit [Fintype I] in
theorem scaleMap_apply (t : I → ℂˣ) (b : I → ℂ) (i : I) : scaleMap t b i = (t i : ℂ) * b i := by
  simp [scaleMap]
theorem det_scaleMap (t : I → ℂˣ) :
    LinearMap.det (scaleMap t) = ∏ i, Complex.normSq (t i : ℂ) := by
  rw [scaleMap, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply]
theorem measurable_to_units {α : Type*} [MeasurableSpace α] {f : α → ℂˣ}
    (hf : Measurable fun x => (f x : ℂ)) : Measurable f := by
  rintro _ ⟨t, ht, rfl⟩
  exact hf ht
theorem measurable_invSqWeight : Measurable (invSqWeight : (I → ℂ) → ℝ≥0∞) :=
  Finset.measurable_prod _ fun i _ => ((measurable_pi_apply i).enorm.inv).pow_const 2
omit [Fintype I] in
theorem measurable_invUnits : Measurable (invUnits : (I → ℂ) → I → ℂˣ) := by
  refine measurable_pi_lambda _ fun i => measurable_to_units ?_
  have : (fun b : I → ℂ => ((invUnits b i : ℂˣ) : ℂ)) = fun b => if b i = 0 then 1 else (b i)⁻¹ := by
    funext b
    by_cases h : b i = 0 <;> simp [invUnits, h]
  rw [this]
  exact Measurable.ite ((measurableSet_singleton 0).preimage (measurable_pi_apply i))
    measurable_const (measurable_pi_apply i).inv
theorem ae_ne_zero : ∀ᵐ b ∂(volume : Measure (I → ℂ)), ∀ i, b i ≠ 0 := by
  have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  exact ae_all_iff.2 fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : I => (volume : Measure ℂ)) (i := i)).eventually h0
theorem ae_ne_zero_weighted : ∀ᵐ b ∂(weightedVolume I), ∀ i, b i ≠ 0 :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_ne_zero
theorem map_scaleMap (t : I → ℂˣ) : (weightedVolume I).map (scaleMap t) = weightedVolume I := by
  have hL : Measurable (scaleMap t) := (scaleMap t).continuous_of_finiteDimensional.measurable
  have hDpos : 0 < ∏ i, Complex.normSq (t i : ℂ) :=
    Finset.prod_pos fun i _ => Complex.normSq_pos.2 (t i).ne_zero
  have hD : LinearMap.det (scaleMap t) ≠ 0 := by rw [det_scaleMap]; exact hDpos.ne'
  set κ : ℝ≥0∞ := ∏ i, ‖(t i : ℂ)‖ₑ ^ 2 with hκdef
  have hκ0 : κ ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (enorm_ne_zero.2 (t i).ne_zero)
  have hκtop : κ ≠ ⊤ := ENNReal.prod_ne_top fun i _ => ENNReal.pow_ne_top enorm_ne_top
  have hκD : ENNReal.ofReal (∏ i, Complex.normSq (t i : ℂ)) = κ := by
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ => Complex.normSq_nonneg _]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hκ : κ * ENNReal.ofReal |(LinearMap.det (scaleMap t))⁻¹| = 1 := by
    rw [det_scaleMap, abs_of_pos (inv_pos.2 hDpos), ENNReal.ofReal_inv_of_pos hDpos, hκD,
      ENNReal.mul_inv_cancel hκ0 hκtop]
  have hW : ∀ b, invSqWeight b = κ * invSqWeight (scaleMap t b) := by
    intro b
    rw [invSqWeight, invSqWeight, hκdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h0 : ‖(t i : ℂ)‖ₑ ≠ 0 := enorm_ne_zero.2 (t i).ne_zero
    rw [scaleMap_apply, enorm_mul, ENNReal.mul_inv (Or.inl h0) (Or.inl enorm_ne_top), mul_pow,
      ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel h0 enorm_ne_top, one_pow, one_mul]
  ext s hs
  rw [map_apply hL hs, weightedVolume, withDensity_apply _ (hL hs), withDensity_apply _ hs,
    ← lintegral_indicator (hL hs), ← lintegral_indicator hs]
  have hind : (scaleMap t ⁻¹' s).indicator invSqWeight =
      fun b => κ * s.indicator invSqWeight (scaleMap t b) := by
    funext b
    by_cases hb : scaleMap t b ∈ s
    · rw [indicator_of_mem (show b ∈ scaleMap t ⁻¹' s from hb), indicator_of_mem hb, hW]
    · rw [indicator_of_notMem (show b ∉ scaleMap t ⁻¹' s from hb), indicator_of_notMem hb, mul_zero]
  have hm : Measurable (s.indicator (invSqWeight : (I → ℂ) → ℝ≥0∞)) :=
    measurable_invSqWeight.indicator hs
  rw [hind]
  beta_reduce
  rw [lintegral_const_mul _ (f := fun b => s.indicator invSqWeight (scaleMap t b)) (hm.comp hL),
    ← lintegral_map hm hL,
    map_linearMap_addHaar_eq_smul_addHaar _ hD, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    hκ, one_mul]
instance : IsMulLeftInvariant (invHaar I) := by
  refine ⟨fun s => ?_⟩
  have hL : Measurable (scaleMap s⁻¹) := (scaleMap s⁻¹).continuous_of_finiteDimensional.measurable
  have hae : (fun x => s * x) ∘ invUnits =ᵐ[weightedVolume I] invUnits ∘ scaleMap s⁻¹ := by
    filter_upwards [ae_ne_zero_weighted] with b hb
    funext i
    have hsb : scaleMap s⁻¹ b i ≠ 0 := by
      rw [scaleMap_apply]; exact mul_ne_zero (s⁻¹ i).ne_zero (hb i)
    simp only [Function.comp, invUnits, Pi.mul_apply, dif_neg (hb i), dif_neg hsb]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, scaleMap_apply, Pi.inv_apply,
      mul_inv, inv_inv]
  rw [invHaar, map_map (measurable_const_mul s) measurable_invUnits, map_congr hae,
    ← map_map measurable_invUnits hL, map_scaleMap]
instance : IsFiniteMeasureOnCompacts (invHaar I) := by
  refine ⟨fun K hK => ?_⟩
  let φ : (I → ℂˣ) → ℝ := fun a => ∑ i, (‖(a i : ℂ)‖ + ‖(((a i)⁻¹ : ℂˣ) : ℂ)‖)
  have hφ : Continuous φ := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (Units.continuous_val.comp (continuous_apply i)).norm.add
      (Units.continuous_val.comp ((continuous_apply i).inv)).norm
  obtain ⟨R₀, hR₀⟩ := (hK.image hφ).bddAbove
  set R := max R₀ 0
  have hbd : ∀ a ∈ K, ∀ i, ‖(a i : ℂ)‖ ≤ R ∧ ‖(((a i)⁻¹ : ℂˣ) : ℂ)‖ ≤ R := by
    intro a ha i
    have h1 : φ a ≤ R₀ := hR₀ ⟨a, ha, rfl⟩
    have h2 : ‖(a i : ℂ)‖ + ‖(((a i)⁻¹ : ℂˣ) : ℂ)‖ ≤ φ a :=
      Finset.single_le_sum (f := fun j => ‖(a j : ℂ)‖ + ‖(((a j)⁻¹ : ℂˣ) : ℂ)‖)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have := le_max_left R₀ 0
    constructor <;> linarith [norm_nonneg (a i : ℂ), norm_nonneg (((a i)⁻¹ : ℂˣ) : ℂ)]
  have hR : 0 ≤ R := le_max_right _ _
  set C : ℝ≥0∞ := ∏ _i : I, ENNReal.ofReal R ^ 2
  have hKm : MeasurableSet (invUnits ⁻¹' K : Set (I → ℂ)) :=
    measurable_invUnits hK.isClosed.measurableSet
  rw [invHaar, map_apply measurable_invUnits hK.isClosed.measurableSet, weightedVolume,
    withDensity_apply _ hKm, ← lintegral_indicator hKm]
  have hle : ∀ᵐ b ∂(volume : Measure (I → ℂ)),
      (invUnits ⁻¹' K).indicator invSqWeight b ≤ (Metric.closedBall 0 R).indicator (fun _ => C) b := by
    filter_upwards [ae_ne_zero] with b hb
    by_cases hbK : invUnits b ∈ K
    · have hval : ∀ i, ((invUnits b i : ℂˣ) : ℂ) = (b i)⁻¹ := fun i => by simp [invUnits, hb i]
      have hval' : ∀ i, (((invUnits b i)⁻¹ : ℂˣ) : ℂ) = b i := fun i => by simp [invUnits, hb i]
      have hball : b ∈ Metric.closedBall (0 : I → ℂ) R := by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
        intro i
        rw [← hval' i]
        exact (hbd _ hbK i).2
      rw [indicator_of_mem (show b ∈ invUnits ⁻¹' K from hbK), indicator_of_mem hball, invSqWeight]
      refine Finset.prod_le_prod' fun i _ => ?_
      gcongr
      rw [← enorm_inv (hb i), ← hval i, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbd _ hbK i).1
    · rw [indicator_of_notMem (show b ∉ invUnits ⁻¹' K from hbK)]
      exact bot_le
  refine (lintegral_mono_ae hle).trans_lt ?_
  rw [lintegral_indicator_const measurableSet_closedBall]
  exact ENNReal.mul_lt_top (ENNReal.prod_ne_top fun i _ => ENNReal.pow_ne_top ENNReal.ofReal_ne_top).lt_top
    measure_closedBall_lt_top
end UnitsInvHaar
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


