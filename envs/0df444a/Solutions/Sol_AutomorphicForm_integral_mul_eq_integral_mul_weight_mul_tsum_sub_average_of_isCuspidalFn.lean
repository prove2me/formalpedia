-- Prove2me | solution 1 for AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5d95a986-76b9-5e9b-88b2-3d720c4a5ac8

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn

open NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm MeasureTheory
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

namespace CuspidalUnfolding

open scoped ENNReal
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private scoped instance countable_ideal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  exact hsurj.countable

private scoped instance countable_heightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R] [Countable R] :
    Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := fun v w h => HeightOneSpectrum.ext h
  exact hinj.countable

variable (K : Type) [Field K] [NumberField K]

private scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private scoped instance countable_ringOfIntegers : Countable (𝓞 K) :=
  Function.Injective.countable (RingOfIntegers.coe_injective (K := K))

open scoped RestrictedProduct in
private scoped instance secondCountable_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometry_toCompletion (v := v)).isEmbedding.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

private scoped instance secondCountable_gl : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 K) K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

private theorem regular_adelicAddHaar : (adelicAddHaar (𝓞 K) K).Regular := by
  unfold adelicAddHaar
  exact Measure.regular_addHaarMeasure

attribute [local instance] regular_adelicAddHaar

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G₂" => GL (Fin 2) (AdeleRing (𝓞 K) K)
local notation "ι" => algebraMap K (AdeleRing (𝓞 K) K)
local notation "μG" => adelicGLHaar (Fin 2) (𝓞 K) K
local notation "μA" => adelicAddHaar (𝓞 K) K

private theorem unip_inv (t : 𝔸) : (unipotentGL2 t)⁻¹ = unipotentGL2 (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

private theorem unip_neg_mul_unip_mul (t : 𝔸) (y : G₂) : unipotentGL2 (-t) * (unipotentGL2 t * y) = y := by
  rw [← mul_assoc, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, one_mul]

private theorem unip_mul_unip_neg_mul (t : 𝔸) (y : G₂) : unipotentGL2 t * (unipotentGL2 (-t) * y) = y := by
  rw [← mul_assoc, ← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero, one_mul]

private theorem unipK_neg_mul (β : K) (y : G₂) : unipotentGL2 (ι (-β)) * (unipotentGL2 (ι β) * y) = y := by
  rw [map_neg]
  exact unip_neg_mul_unip_mul K _ y

private theorem continuous_unip : Continuous (fun t : 𝔸 => unipotentGL2 t) := by
  have hval : Continuous (fun t : 𝔸 => ((unipotentGL2 t : G₂) : Matrix (Fin 2) (Fin 2) 𝔸)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [unip_inv]
  exact hval.comp continuous_neg

private theorem continuous_entry : Continuous (fun g : G₂ => ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1)) :=
  Units.continuous_val.matrix_elem 0 1

private theorem entry_unip (t : 𝔸) : ((unipotentGL2 t : G₂) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = t := by
  simp [unipotentGL2_coe]

private theorem finite_setOf_unip_mul_mem {C : Set G₂} (hC : IsCompact C) (y : G₂) :
    {β : K | unipotentGL2 (ι β) * y ∈ C}.Finite := by
  have hD : IsCompact ((fun g : G₂ => ((g * y⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1) '' C) :=
    hC.image ((continuous_entry K).comp (continuous_mul_const y⁻¹))
  refine (NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hD).subset fun β hβ => ?_
  refine ⟨unipotentGL2 (ι β) * y, hβ, ?_⟩
  show ((unipotentGL2 (ι β) * y * y⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = ι β
  rw [mul_inv_cancel_right, entry_unip]

private theorem isCompact_translates {S : Set 𝔸} (hS : IsCompact S) (x : G₂) {T : Set G₂} (hT : IsCompact T) :
    IsCompact (Set.image2 (fun (t : 𝔸) (c : G₂) => unipotentGL2 t * x * c) S T) := by
  have hcont : Continuous (fun p : 𝔸 × G₂ => unipotentGL2 p.1 * x * p.2) :=
    (((continuous_unip K).comp continuous_fst).mul continuous_const).mul continuous_snd
  rw [← Set.image_prod]
  exact (hS.prod hT).image hcont

private theorem isCompact_closure_box : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private theorem tsum_weight_neg (w : G₂ → ℝ) (z : G₂) :
    ∑' β : K, w (unipotentGL2 (ι (-β)) * z) = ∑' β : K, w (unipotentGL2 (ι β) * z) :=
  (Equiv.neg K).tsum_eq (fun β : K => w (unipotentGL2 (ι β) * z))

private theorem tsum_ofReal_weight_neg_eq_one (w : G₂ → ℝ) (hw0 : ∀ y, 0 ≤ w y) {z : G₂}
    (h1 : ∑' β : K, w (unipotentGL2 (ι β) * z) = 1) :
    ∑' β : K, ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) = 1 := by
  have hsum : Summable fun β : K => w (unipotentGL2 (ι β) * z) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h1
    exact zero_ne_one h1
  have hre : ∑' β : K, ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z))
      = ∑' β : K, ENNReal.ofReal (w (unipotentGL2 (ι β) * z)) :=
    (Equiv.neg K).tsum_eq (fun β : K => ENNReal.ofReal (w (unipotentGL2 (ι β) * z)))
  rw [hre, ← ENNReal.ofReal_tsum_of_nonneg (fun β => hw0 _) hsum, h1, ENNReal.ofReal_one]

private theorem tsum_coe_weight_neg_eq_one (w : G₂ → ℝ) {z : G₂}
    (h1 : ∑' β : K, w (unipotentGL2 (ι β) * z) = 1) :
    ∑' β : K, ((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_tsum, tsum_weight_neg K w z, h1, Complex.ofReal_one]

private theorem tsum_lintegral_weight_neg_mul (Ψ : G₂ → ℝ≥0∞) (hΨ : AEMeasurable Ψ μG)
    (w : G₂ → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ y, Ψ y ≠ 0 → ∑' β : K, w (unipotentGL2 (ι β) * y) = 1) :
    ∑' β : K, ∫⁻ z, ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) * Ψ z ∂μG = ∫⁻ z, Ψ z ∂μG := by
  have hweβ : ∀ β : K, Measurable fun z : G₂ => ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) := fun β =>
    hw.ennreal_ofReal.comp (measurable_const_mul _)
  rw [← lintegral_tsum fun β => (hweβ β).aemeasurable.fun_mul hΨ]
  refine lintegral_congr fun z => ?_
  rw [ENNReal.tsum_mul_right]
  by_cases hz : Ψ z = 0
  · simp [hz]
  · rw [tsum_ofReal_weight_neg_eq_one K w hw0 (hw1 z hz), one_mul]

private theorem lintegral_weight_mul_tsum (Ψ : G₂ → ℝ≥0∞) (hΨ : AEMeasurable Ψ μG)
    (w : G₂ → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ y, Ψ y ≠ 0 → ∑' β : K, w (unipotentGL2 (ι β) * y) = 1) :
    ∫⁻ y, ENNReal.ofReal (w y) * ∑' β : K, Ψ (unipotentGL2 (ι β) * y) ∂μG = ∫⁻ y, Ψ y ∂μG := by
  have hΨβ : ∀ β : K, AEMeasurable (fun y : G₂ => Ψ (unipotentGL2 (ι β) * y)) μG := fun β =>
    hΨ.comp_quasiMeasurePreserving (measurePreserving_mul_left μG (unipotentGL2 (ι β))).quasiMeasurePreserving
  have hwe : Measurable fun y : G₂ => ENNReal.ofReal (w y) := hw.ennreal_ofReal
  calc ∫⁻ y, ENNReal.ofReal (w y) * ∑' β : K, Ψ (unipotentGL2 (ι β) * y) ∂μG
      = ∫⁻ y, ∑' β : K, ENNReal.ofReal (w y) * Ψ (unipotentGL2 (ι β) * y) ∂μG := by
        refine lintegral_congr fun y => ?_
        rw [ENNReal.tsum_mul_left]
    _ = ∑' β : K, ∫⁻ y, ENNReal.ofReal (w y) * Ψ (unipotentGL2 (ι β) * y) ∂μG :=
        lintegral_tsum fun β => hwe.aemeasurable.mul (hΨβ β)
    _ = ∑' β : K, ∫⁻ z, ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) * Ψ z ∂μG := by
        refine tsum_congr fun β => ?_
        rw [← lintegral_mul_left_eq_self (fun z => ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) * Ψ z)
          (unipotentGL2 (ι β))]
        refine lintegral_congr fun y => ?_
        simp only [unipK_neg_mul]
    _ = ∫⁻ z, Ψ z ∂μG := tsum_lintegral_weight_neg_mul K Ψ hΨ w hw hw0 hw1

private theorem enorm_coe_mul {r : ℝ} (hr : 0 ≤ r) (c : ℂ) : ‖(r : ℂ) * c‖ₑ = ENNReal.ofReal r * ‖c‖ₑ := by
  rw [enorm_mul, ← ofReal_norm (r : ℂ), Complex.norm_real, Real.norm_of_nonneg hr]

private theorem tsum_integral_coe_weight_mul (h : G₂ → ℂ) (hint : Integrable h μG)
    (w : G₂ → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ y, h y ≠ 0 → ∑' β : K, w (unipotentGL2 (ι β) * y) = 1) :
    ∑' β : K, ∫ y, ((w y : ℝ) : ℂ) * h (unipotentGL2 (ι β) * y) ∂μG = ∫ y, h y ∂μG := by
  have hwc : ∀ β : K, Measurable fun z : G₂ => ((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) := fun β =>
    Complex.measurable_ofReal.comp (hw.comp (measurable_const_mul _))
  have hAE : ∀ β : K, AEStronglyMeasurable (fun z : G₂ => ((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) * h z) μG :=
    fun β => (hwc β).aestronglyMeasurable.mul hint.aestronglyMeasurable
  have hfin : ∑' β : K, ∫⁻ z, ‖((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) * h z‖ₑ ∂μG ≠ ∞ := by
    have hterm : ∀ β : K, ∫⁻ z, ‖((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) * h z‖ₑ ∂μG
        = ∫⁻ z, ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) * ‖h z‖ₑ ∂μG := fun β =>
      lintegral_congr fun z => enorm_coe_mul (hw0 _) _
    rw [tsum_congr hterm, tsum_lintegral_weight_neg_mul K (fun z => ‖h z‖ₑ) hint.aestronglyMeasurable.enorm w hw hw0
      (fun y hy => hw1 y (by simpa using hy))]
    have hfi := hint.hasFiniteIntegral
    unfold HasFiniteIntegral at hfi
    exact hfi.ne
  calc ∑' β : K, ∫ y, ((w y : ℝ) : ℂ) * h (unipotentGL2 (ι β) * y) ∂μG
      = ∑' β : K, ∫ z, ((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) * h z ∂μG := by
        refine tsum_congr fun β => ?_
        rw [← integral_mul_left_eq_self (fun z => ((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) * h z)
          (unipotentGL2 (ι β))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [unipK_neg_mul]
    _ = ∫ z, ∑' β : K, ((w (unipotentGL2 (ι (-β)) * z) : ℝ) : ℂ) * h z ∂μG := (integral_tsum hAE hfin).symm
    _ = ∫ z, h z ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        rw [tsum_mul_right]
        by_cases hz : h z = 0
        · simp [hz]
        · rw [tsum_coe_weight_neg_eq_one K w (hw1 z hz), one_mul]

private theorem integral_coe_weight_mul_tsum (h : G₂ → ℂ) (hint : Integrable h μG)
    (w : G₂ → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ y, h y ≠ 0 → ∑' β : K, w (unipotentGL2 (ι β) * y) = 1) :
    ∫ y, ((w y : ℝ) : ℂ) * ∑' β : K, h (unipotentGL2 (ι β) * y) ∂μG = ∫ y, h y ∂μG := by
  have hwm : Measurable fun y : G₂ => ((w y : ℝ) : ℂ) := Complex.measurable_ofReal.comp hw
  have hhβ : ∀ β : K, AEStronglyMeasurable (fun y : G₂ => h (unipotentGL2 (ι β) * y)) μG := fun β =>
    hint.aestronglyMeasurable.comp_measurePreserving (measurePreserving_mul_left μG _)
  have hAE : ∀ β : K, AEStronglyMeasurable (fun y : G₂ => ((w y : ℝ) : ℂ) * h (unipotentGL2 (ι β) * y)) μG :=
    fun β => hwm.aestronglyMeasurable.mul (hhβ β)
  have hfin : ∑' β : K, ∫⁻ y, ‖((w y : ℝ) : ℂ) * h (unipotentGL2 (ι β) * y)‖ₑ ∂μG ≠ ∞ := by
    have hterm : ∀ β : K, ∫⁻ y, ‖((w y : ℝ) : ℂ) * h (unipotentGL2 (ι β) * y)‖ₑ ∂μG
        = ∫⁻ z, ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) * ‖h z‖ₑ ∂μG := by
      intro β
      rw [← lintegral_mul_left_eq_self (fun z => ENNReal.ofReal (w (unipotentGL2 (ι (-β)) * z)) * ‖h z‖ₑ)
        (unipotentGL2 (ι β))]
      refine lintegral_congr fun y => ?_
      rw [enorm_coe_mul (hw0 y)]
      simp only [unipK_neg_mul]
    rw [tsum_congr hterm, tsum_lintegral_weight_neg_mul K (fun z => ‖h z‖ₑ) hint.aestronglyMeasurable.enorm w hw hw0
      (fun y hy => hw1 y (by simpa using hy))]
    have hfi := hint.hasFiniteIntegral
    unfold HasFiniteIntegral at hfi
    exact hfi.ne
  calc ∫ y, ((w y : ℝ) : ℂ) * ∑' β : K, h (unipotentGL2 (ι β) * y) ∂μG
      = ∫ y, ∑' β : K, ((w y : ℝ) : ℂ) * h (unipotentGL2 (ι β) * y) ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        dsimp only
        rw [tsum_mul_left]
    _ = ∑' β : K, ∫ y, ((w y : ℝ) : ℂ) * h (unipotentGL2 (ι β) * y) ∂μG := integral_tsum hAE hfin
    _ = ∫ y, h y ∂μG := tsum_integral_coe_weight_mul K h hint w hw hw0 hw1

private theorem integrable_coe_weight_mul_tsum (h : G₂ → ℂ) (hint : Integrable h μG)
    (hfin : ∀ y, {β : K | h (unipotentGL2 (ι β) * y) ≠ 0}.Finite)
    (w : G₂ → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ y, h y ≠ 0 → ∑' β : K, w (unipotentGL2 (ι β) * y) = 1) :
    Integrable (fun y => ((w y : ℝ) : ℂ) * ∑' β : K, h (unipotentGL2 (ι β) * y)) μG := by
  have hwm : Measurable fun y : G₂ => ((w y : ℝ) : ℂ) := Complex.measurable_ofReal.comp hw
  have hhβ : ∀ β : K, AEStronglyMeasurable (fun y : G₂ => h (unipotentGL2 (ι β) * y)) μG := fun β =>
    hint.aestronglyMeasurable.comp_measurePreserving (measurePreserving_mul_left μG _)
  have hsum : AEStronglyMeasurable (fun y : G₂ => ∑' β : K, h (unipotentGL2 (ι β) * y)) μG :=
    AEStronglyMeasurable.tsum hhβ
  refine ⟨hwm.aestronglyMeasurable.mul hsum, ?_⟩
  have hcore := lintegral_weight_mul_tsum K (fun z => ‖h z‖ₑ) hint.aestronglyMeasurable.enorm w hw hw0
    (fun y hy => hw1 y (by simpa using hy))
  have hle : ∀ y, ‖((w y : ℝ) : ℂ) * ∑' β : K, h (unipotentGL2 (ι β) * y)‖ₑ
      ≤ ENNReal.ofReal (w y) * ∑' β : K, ‖h (unipotentGL2 (ι β) * y)‖ₑ := by
    intro y
    rw [enorm_coe_mul (hw0 y)]
    refine mul_le_mul_right ?_ _
    have hs : Summable fun β : K => ‖h (unipotentGL2 (ι β) * y)‖ := by
      refine summable_of_ne_finset_zero (s := (hfin y).toFinset) fun β hβ => ?_
      rw [norm_eq_zero]
      simpa using hβ
    calc ‖∑' β : K, h (unipotentGL2 (ι β) * y)‖ₑ
        = ENNReal.ofReal ‖∑' β : K, h (unipotentGL2 (ι β) * y)‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑' β : K, ‖h (unipotentGL2 (ι β) * y)‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hs)
      _ = ∑' β : K, ENNReal.ofReal ‖h (unipotentGL2 (ι β) * y)‖ :=
          ENNReal.ofReal_tsum_of_nonneg (fun β => norm_nonneg _) hs
      _ = ∑' β : K, ‖h (unipotentGL2 (ι β) * y)‖ₑ := tsum_congr fun β => ofReal_norm _
  have hfi := hint.hasFiniteIntegral
  unfold HasFiniteIntegral at hfi ⊢
  calc ∫⁻ y, ‖((w y : ℝ) : ℂ) * ∑' β : K, h (unipotentGL2 (ι β) * y)‖ₑ ∂μG
      ≤ ∫⁻ y, ENNReal.ofReal (w y) * ∑' β : K, ‖h (unipotentGL2 (ι β) * y)‖ₑ ∂μG := lintegral_mono hle
    _ = ∫⁻ y, ‖h y‖ₑ ∂μG := hcore
    _ < ∞ := hfi

private noncomputable def boxAvg (f : G₂ → ℂ) (x z : G₂) : ℂ :=
  ∫ b in adelicBox K, f (x⁻¹ * unipotentGL2 (-b) * z) ∂μA

private theorem integral_unip_eq_tsum_boxAvg (f : G₂ → ℂ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (x y : G₂) :
    ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂μA = ∑' β : K, boxAvg K f x (unipotentGL2 (ι β) * y) := by
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 K) K) :=
    (Set.countable_range (algebraMap K (AdeleRing (𝓞 K) K))).to_subtype
  have hFc : Continuous (fun t : 𝔸 => f (x⁻¹ * unipotentGL2 (-t) * y)) :=
    hf.comp ((continuous_const.mul ((continuous_unip K).comp continuous_neg)).mul continuous_const)
  have hFs : HasCompactSupport (fun t : 𝔸 => f (x⁻¹ * unipotentGL2 (-t) * y)) := by
    have hcont : Continuous (fun g : G₂ => -(((x * g * y⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1)) :=
      ((continuous_entry K).comp ((continuous_const.mul continuous_id).mul continuous_const)).neg
    refine HasCompactSupport.of_support_subset_isCompact (IsCompact.image hfs hcont) fun t ht => ?_
    refine ⟨x⁻¹ * unipotentGL2 (-t) * y, subset_tsupport f ht, ?_⟩
    show -(((x * (x⁻¹ * unipotentGL2 (-t) * y) * y⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1) = t
    rw [mul_assoc x⁻¹, mul_inv_cancel_left, mul_inv_cancel_right, entry_unip, neg_neg]
  have hFi : Integrable (fun t : 𝔸 => f (x⁻¹ * unipotentGL2 (-t) * y)) μA :=
    hFc.integrable_of_hasCompactSupport hFs
  have hneg : ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂μA = ∫ t, f (x⁻¹ * unipotentGL2 (-t) * y) ∂μA := by
    rw [← integral_neg_eq_self (fun t : 𝔸 => f (x⁻¹ * unipotentGL2 (-t) * y)) μA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
  let e : K ≃ AdeleRing.principalSubgroup (𝓞 K) K :=
    Equiv.ofBijective (fun β => ⟨ι β, ⟨β, rfl⟩⟩)
      ⟨fun β₁ β₂ hβ => NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val hβ),
        by rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩⟩
  calc ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂μA
      = ∫ t, f (x⁻¹ * unipotentGL2 (-t) * y) ∂μA := hneg
    _ = ∑' γ : AdeleRing.principalSubgroup (𝓞 K) K,
          ∫ b in adelicBox K, f (x⁻¹ * unipotentGL2 (-(γ +ᵥ b)) * y) ∂μA :=
        (isAddFundamentalDomain_adelicBox_adelicAddHaar K).integral_eq_tsum''
          (fun t : 𝔸 => f (x⁻¹ * unipotentGL2 (-t) * y)) hFi
    _ = ∑' β : K, ∫ b in adelicBox K, f (x⁻¹ * unipotentGL2 (-(ι β + b)) * y) ∂μA :=
        (e.tsum_eq (fun γ : AdeleRing.principalSubgroup (𝓞 K) K =>
          ∫ b in adelicBox K, f (x⁻¹ * unipotentGL2 (-(γ +ᵥ b)) * y) ∂μA)).symm
    _ = ∑' β : K, boxAvg K f x (unipotentGL2 (ι (-β)) * y) := by
        refine tsum_congr fun β => ?_
        unfold boxAvg
        refine setIntegral_congr_fun (measurableSet_adelicBox K) fun b _ => ?_
        rw [neg_add, add_comm, map_neg, unipotentGL2_add]
        simp only [mul_assoc]
    _ = ∑' β : K, boxAvg K f x (unipotentGL2 (ι β) * y) :=
        (Equiv.neg K).tsum_eq (fun β : K => boxAvg K f x (unipotentGL2 (ι β) * y))

private theorem stronglyMeasurable_boxAvg (f : G₂ → ℂ) (hf : Continuous f) (x : G₂) :
    StronglyMeasurable (boxAvg K f x) := by
  have hcont : Continuous (Function.uncurry fun (z : G₂) (b : 𝔸) => f (x⁻¹ * unipotentGL2 (-b) * z)) := by
    have hn := continuous_unip K
    show Continuous (fun p : G₂ × 𝔸 => f (x⁻¹ * unipotentGL2 (-p.2) * p.1))
    exact hf.comp (by fun_prop)
  unfold boxAvg
  exact hcont.stronglyMeasurable.integral_prod_right

private theorem exists_norm_boxAvg_le (f : G₂ → ℂ) (hf : Continuous f) (hfs : HasCompactSupport f) (x : G₂) :
    ∃ B : ℝ, ∀ z, ‖boxAvg K f x z‖ ≤ B := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨C * (adelicAddHaar (𝓞 K) K).real (adelicBox K), fun z => ?_⟩
  exact norm_setIntegral_le_of_norm_le_const (adelicAddHaar_adelicBox_lt_top K) fun b _ => hC _

private theorem boxAvg_eq_zero_of_notMem (f : G₂ → ℂ) (x z : G₂)
    (hz : z ∉ Set.image2 (fun (t : 𝔸) (c : G₂) => unipotentGL2 t * x * c) (closure (adelicBox K)) (tsupport f)) :
    boxAvg K f x z = 0 := by
  unfold boxAvg
  refine setIntegral_eq_zero_of_forall_eq_zero fun b hb => ?_
  by_contra hne
  have hc : x⁻¹ * unipotentGL2 (-b) * z ∈ tsupport f := subset_tsupport f hne
  have hmem := Set.mem_image2_of_mem (f := fun (t : 𝔸) (c : G₂) => unipotentGL2 t * x * c) (subset_closure hb) hc
  beta_reduce at hmem
  rw [mul_assoc, mul_assoc x⁻¹, mul_inv_cancel_left, unip_mul_unip_neg_mul] at hmem
  exact hz hmem

private theorem setIntegral_box_eq_zero (φ : G₂ → ℂ)
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ) (z : G₂) :
    ∫ b in adelicBox K, φ (unipotentGL2 b * z) ∂μA = 0 := by
  have h := hφc z
  unfold constantTerm constantTermIntegrand at h
  rw [ProbabilityTheory.cond, integral_smul_measure] at h
  rcases smul_eq_zero.mp h with h0 | h0
  · exfalso
    rw [ENNReal.toReal_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact ENNReal.inv_ne_zero.mpr (adelicAddHaar_adelicBox_lt_top K).ne h0
    · exact ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos K).ne' h0
  · exact h0

private theorem integral_mul_boxAvg_eq_zero (φ f : G₂ → ℂ) (x : G₂)
    (hφi : LocallyIntegrable φ μG)
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    ∫ z, φ z * boxAvg K f x z ∂μG = 0 := by
  set R := Set.image2 (fun (t : 𝔸) (c : G₂) => unipotentGL2 t * x * c) (closure (adelicBox K)) (tsupport f)
    with hRdef
  have hR : IsCompact R := isCompact_translates K (isCompact_closure_box K) x hfs
  have hφR : Integrable (R.indicator φ) μG :=
    (hφi.integrableOn_isCompact hR).integrable_indicator hR.isClosed.measurableSet
  have h1 : ∀ z, φ z * boxAvg K f x z = R.indicator φ z * boxAvg K f x z := by
    intro z
    by_cases hz : z ∈ R
    · rw [Set.indicator_of_mem hz]
    · rw [boxAvg_eq_zero_of_notMem K f x z hz, mul_zero, mul_zero]
  haveI : IsFiniteMeasure ((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact adelicAddHaar_adelicBox_lt_top K⟩
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfs
  have hn := continuous_unip K
  set Θ : 𝔸 × G₂ → ℂ := fun p => R.indicator φ p.2 * f (x⁻¹ * unipotentGL2 (-p.1) * p.2) with hΘ
  have hΘi : Integrable Θ (((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) := by
    have h2 : Integrable (fun p : 𝔸 × G₂ => (fun _ : 𝔸 => (1 : ℂ)) p.1 * R.indicator φ p.2)
        (((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) :=
      (integrable_const (1 : ℂ)).mul_prod hφR
    have h3 : AEStronglyMeasurable (fun p : 𝔸 × G₂ => f (x⁻¹ * unipotentGL2 (-p.1) * p.2))
        (((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) :=
      (hf.comp (by fun_prop)).aestronglyMeasurable
    refine (h2.mul_bdd h3 (Filter.Eventually.of_forall fun p => hCf _)).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [hΘ, one_mul]
  have hS : MeasurePreserving (fun p : 𝔸 × G₂ => (p.1, unipotentGL2 p.1 * p.2))
      (((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG)
      (((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) := by
    refine (MeasurePreserving.id _).skew_product (g := fun (b : 𝔸) (z : G₂) => unipotentGL2 b * z) ?_
      (Filter.Eventually.of_forall fun b => map_mul_left_eq_self μG (unipotentGL2 b))
    show Measurable (fun p : 𝔸 × G₂ => unipotentGL2 p.1 * p.2)
    exact (by fun_prop : Continuous (fun p : 𝔸 × G₂ => unipotentGL2 p.1 * p.2)).measurable
  have hcomp : ∫ p, Θ p ∂(((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG)
      = ∫ p, Θ (p.1, unipotentGL2 p.1 * p.2) ∂(((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) := by
    have h := integral_map (f := Θ) hS.measurable.aemeasurable (by rw [hS.map_eq]; exact hΘi.aestronglyMeasurable)
    rw [hS.map_eq] at h
    exact h
  have hL : ∫ p, Θ p ∂(((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG)
      = ∫ z, R.indicator φ z * boxAvg K f x z ∂μG := by
    rw [integral_prod_symm _ hΘi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hΘ]
    unfold boxAvg
    exact integral_const_mul _ _
  have hΘS : Integrable (fun p : 𝔸 × G₂ => Θ (p.1, unipotentGL2 p.1 * p.2))
      (((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) :=
    (hS.integrable_comp hΘi.aestronglyMeasurable).mpr hΘi
  have hRhs : ∫ p, Θ (p.1, unipotentGL2 p.1 * p.2)
      ∂(((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) = 0 := by
    rw [integral_prod_symm _ hΘS]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)).trans (integral_zero _ _)
    simp only [hΘ]
    by_cases hz : f (x⁻¹ * z) = 0
    · refine setIntegral_eq_zero_of_forall_eq_zero fun b _ => ?_
      rw [mul_assoc x⁻¹, unip_neg_mul_unip_mul, hz, mul_zero]
    · have hc : x⁻¹ * z ∈ tsupport f := subset_tsupport f hz
      have hmem : ∀ b ∈ adelicBox K, unipotentGL2 b * z ∈ R := fun b hb => by
        have hm := Set.mem_image2_of_mem (f := fun (t : 𝔸) (c : G₂) => unipotentGL2 t * x * c) (subset_closure hb) hc
        beta_reduce at hm
        rwa [mul_assoc, mul_inv_cancel_left] at hm
      calc ∫ b in adelicBox K,
              R.indicator φ (unipotentGL2 b * z) * f (x⁻¹ * unipotentGL2 (-b) * (unipotentGL2 b * z)) ∂μA
          = ∫ b in adelicBox K, φ (unipotentGL2 b * z) * f (x⁻¹ * z) ∂μA := by
            refine setIntegral_congr_fun (measurableSet_adelicBox K) fun b hb => ?_
            beta_reduce
            rw [Set.indicator_of_mem (hmem b hb), mul_assoc x⁻¹, unip_neg_mul_unip_mul]
        _ = (∫ b in adelicBox K, φ (unipotentGL2 b * z) ∂μA) * f (x⁻¹ * z) := integral_mul_const _ _
        _ = 0 := by rw [setIntegral_box_eq_zero K φ hφc z, zero_mul]
  calc ∫ z, φ z * boxAvg K f x z ∂μG
      = ∫ z, R.indicator φ z * boxAvg K f x z ∂μG := integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∫ p, Θ p ∂(((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) := hL.symm
    _ = ∫ p, Θ (p.1, unipotentGL2 p.1 * p.2) ∂(((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)).prod μG) := hcomp
    _ = 0 := hRhs

private theorem integrable_mul_of_bounded_support (φ : G₂ → ℂ) (hφi : LocallyIntegrable φ μG)
    (ψ : G₂ → ℂ) (hψ : AEStronglyMeasurable ψ μG) {S : Set G₂} (hS : IsCompact S)
    (hsupp : ∀ z, z ∉ S → ψ z = 0) {B : ℝ} (hB : ∀ z, ‖ψ z‖ ≤ B) :
    Integrable (fun z => φ z * ψ z) μG := by
  have hind : Integrable (S.indicator φ) μG :=
    (hφi.integrableOn_isCompact hS).integrable_indicator hS.isClosed.measurableSet
  refine (hind.mul_bdd hψ (Filter.Eventually.of_forall hB)).congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S
  · simp only [Set.indicator_of_mem hz]
  · simp only [Set.indicator_of_notMem hz, hsupp z hz, mul_zero]

private theorem finite_and_measurable_and_integrable
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    (∀ y, Set.Finite {β : K |
        f (x⁻¹ * (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y)) ≠ 0})
    ∧ Measurable (fun y => f (x⁻¹ * y))
    ∧ Integrable (fun y => φ y * f (x⁻¹ * y)) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hS : IsCompact ((fun c : G₂ => x * c) '' tsupport f) :=
    IsCompact.image hfs (continuous_const.mul continuous_id)
  have hslice : Continuous (fun y : G₂ => f (x⁻¹ * y)) := hf.comp (continuous_const.mul continuous_id)
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨fun y => ?_, hslice.measurable, ?_⟩
  · refine (finite_setOf_unip_mul_mem K hS y).subset fun β hβ => ?_
    exact ⟨x⁻¹ * (unipotentGL2 (ι β) * y), subset_tsupport f hβ, mul_inv_cancel_left x _⟩
  · refine integrable_mul_of_bounded_support K φ hφi _ hslice.aestronglyMeasurable hS (fun z hz => ?_) (fun z => hCf _)
    by_contra hne
    exact hz ⟨x⁻¹ * z, subset_tsupport f hne, mul_inv_cancel_left x z⟩

private theorem integral_mul_eq_integral_mul_weight_mul_tsum
    (φ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ)
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hg : Measurable g)
    (hgl : ∀ y, Set.Finite {β : K | g (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) ≠ 0})
    (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ y, g y ≠ 0 →
      ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = 1)
    (hint : Integrable (fun y => φ y * g y) (adelicGLHaar (Fin 2) (𝓞 K) K)) :
    ∫ y, φ y * g y ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ y, φ y * (w y : ℂ) *
          (∑' β : K, g (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have _ := hg
  have _ := hgl
  have h := integral_coe_weight_mul_tsum K (fun y => φ y * g y) hint w hw hw0
    (fun y hy => hw1 y (fun h0 => hy (by simp only [h0, mul_zero])))
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  simp only [hφN]
  rw [tsum_mul_left]
  ring

private theorem integrable_and_integral_mul_weight_mul_average_eq_zero
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ)
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)), c ∈ tsupport f →
      ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) *
        (unipotentGL2 t * x * c)) = 1) :
    Integrable (fun y => φ y * (w y : ℂ) *
        (∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y)))
        (adelicGLHaar (Fin 2) (𝓞 K) K)
    ∧ Integrable (fun y => φ y * (w y : ℂ) *
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
          ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)))
        (adelicGLHaar (Fin 2) (𝓞 K) K)
    ∧ ∫ y, φ y * (w y : ℂ) *
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
          ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  obtain ⟨hfin₁, -, hint₁⟩ := finite_and_measurable_and_integrable K φ f x hφi hf hfs

  have hn₁ : ∀ y, φ y * f (x⁻¹ * y) ≠ 0 → ∑' β : K, w (unipotentGL2 (ι β) * y) = 1 := by
    intro y hy
    have hfy : f (x⁻¹ * y) ≠ 0 := fun h0 => hy (by rw [h0, mul_zero])
    have h := hw1 0 (x⁻¹ * y) (subset_tsupport f hfy)
    simpa only [unipotentGL2_zero, one_mul, mul_inv_cancel_left] using h
  have hfin₁' : ∀ y, {β : K | φ (unipotentGL2 (ι β) * y) * f (x⁻¹ * (unipotentGL2 (ι β) * y)) ≠ 0}.Finite := by
    intro y
    refine (hfin₁ y).subset fun β hβ => ?_
    exact fun h0 => hβ (by rw [h0, mul_zero])
  have hI₁ : Integrable (fun y => ((w y : ℝ) : ℂ) *
      ∑' β : K, φ (unipotentGL2 (ι β) * y) * f (x⁻¹ * (unipotentGL2 (ι β) * y))) μG :=
    integrable_coe_weight_mul_tsum K (fun y => φ y * f (x⁻¹ * y)) hint₁ hfin₁' w hw hw0 hn₁
  have e₁ : ∀ y, ((w y : ℝ) : ℂ) * (∑' β : K, φ (unipotentGL2 (ι β) * y) * f (x⁻¹ * (unipotentGL2 (ι β) * y)))
      = φ y * (w y : ℂ) * (∑' β : K, f (x⁻¹ * unipotentGL2 (ι β) * y)) := by
    intro y
    simp only [hφN, mul_assoc]
    rw [tsum_mul_left]
    ring

  have hP0 : ∀ y, ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂μA = ∑' β : K, boxAvg K f x (unipotentGL2 (ι β) * y) :=
    integral_unip_eq_tsum_boxAvg K f hf hfs x
  have hR : IsCompact (Set.image2 (fun (t : 𝔸) (c : G₂) => unipotentGL2 t * x * c) (closure (adelicBox K))
      (tsupport f)) := isCompact_translates K (isCompact_closure_box K) x hfs
  obtain ⟨B, hB⟩ := exists_norm_boxAvg_le K f hf hfs x
  have hint₂ : Integrable (fun z => φ z * boxAvg K f x z) μG :=
    integrable_mul_of_bounded_support K φ hφi _ (stronglyMeasurable_boxAvg K f hf x).aestronglyMeasurable hR
      (fun z hz => boxAvg_eq_zero_of_notMem K f x z hz) hB
  have hn₂ : ∀ y, φ y * boxAvg K f x y ≠ 0 → ∑' β : K, w (unipotentGL2 (ι β) * y) = 1 := by
    intro y hy
    have hAy : boxAvg K f x y ≠ 0 := fun h0 => hy (by rw [h0, mul_zero])
    have hyR : y ∈ Set.image2 (fun (t : 𝔸) (c : G₂) => unipotentGL2 t * x * c) (closure (adelicBox K))
        (tsupport f) := by
      by_contra h
      exact hAy (boxAvg_eq_zero_of_notMem K f x y h)
    obtain ⟨t, -, c, hc, rfl⟩ := hyR
    exact hw1 t c hc
  have hfin₂ : ∀ y, {β : K | φ (unipotentGL2 (ι β) * y) * boxAvg K f x (unipotentGL2 (ι β) * y) ≠ 0}.Finite := by
    intro y
    refine (finite_setOf_unip_mul_mem K hR y).subset fun β hβ => ?_
    by_contra h
    exact hβ (by rw [boxAvg_eq_zero_of_notMem K f x _ h, mul_zero])
  have hI₂ : Integrable (fun y => ((w y : ℝ) : ℂ) *
      ∑' β : K, φ (unipotentGL2 (ι β) * y) * boxAvg K f x (unipotentGL2 (ι β) * y)) μG :=
    integrable_coe_weight_mul_tsum K (fun z => φ z * boxAvg K f x z) hint₂ hfin₂ w hw hw0 hn₂
  have hJ₂ : ∫ y, ((w y : ℝ) : ℂ) *
      ∑' β : K, φ (unipotentGL2 (ι β) * y) * boxAvg K f x (unipotentGL2 (ι β) * y) ∂μG
      = ∫ z, φ z * boxAvg K f x z ∂μG :=
    integral_coe_weight_mul_tsum K (fun z => φ z * boxAvg K f x z) hint₂ w hw hw0 hn₂
  have hvan := integral_mul_boxAvg_eq_zero K φ f x hφi hφc hf hfs
  have e₂ : ∀ y, φ y * (w y : ℂ) *
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
          ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
      = (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
          (((w y : ℝ) : ℂ) *
            ∑' β : K, φ (unipotentGL2 (ι β) * y) * boxAvg K f x (unipotentGL2 (ι β) * y)) := by
    intro y
    rw [hP0 y]
    simp only [hφN]
    rw [tsum_mul_left]
    ring
  refine ⟨hI₁.congr (Filter.Eventually.of_forall e₁), ?_, ?_⟩
  · exact (hI₂.const_mul _).congr (Filter.Eventually.of_forall fun y => (e₂ y).symm)
  · refine (integral_congr_ae (Filter.Eventually.of_forall e₂)).trans ?_
    rw [integral_const_mul, hJ₂, hvan, mul_zero]

end CuspidalUnfolding
p2m_reactivate "P2MW.S_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn.CuspidalUnfolding"

open CuspidalUnfolding in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)), c ∈ tsupport f →
      ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) *
        (unipotentGL2 t * x * c)) = 1) :
    ∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ y, φ y * (w y : ℂ) *
          ((∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
            - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨hfin, hgm, hint⟩ := finite_and_measurable_and_integrable K φ f x hφi hf hfs
  obtain ⟨hIP, hIP0, hvan⟩ :=
    integrable_and_integral_mul_weight_mul_average_eq_zero K φ f x w hφN hφi hφc hf hfs hw hw0 hw1
  have hw1' : ∀ y, f (x⁻¹ * y) ≠ 0 →
      ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = 1 := by
    intro y hy
    have hmem : x⁻¹ * y ∈ tsupport f := subset_tsupport _ (Function.mem_support.mpr hy)
    have := hw1 0 (x⁻¹ * y) hmem
    simpa [unipotentGL2_zero, mul_inv_cancel_left] using this
  have hunf := integral_mul_eq_integral_mul_weight_mul_tsum K φ (fun y => f (x⁻¹ * y)) w hφN
    hgm hfin hw hw0 hw1' hint
  simp only [mul_assoc] at hunf hIP hIP0 hvan ⊢
  rw [hunf]
  have hsplit := integral_sub hIP hIP0
  rw [hvan, sub_zero] at hsplit
  rw [← hsplit]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  ring

end S_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn (solution)
