-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5b509055-c83d-5c18-8b26-a1348bedafb5

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
import Theorems.Thm_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory

open scoped ENNReal NNReal
open NumberField.AdelicVolume

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace MovingRegionSquareMass

variable (K : Type) [Field K] [NumberField K]

local notation "G𝔸" => GL (Fin 2) (AdeleRing (𝓞 K) K)
local notation "Z𝔸" => GL (Fin 1) (AdeleRing (𝓞 K) K)
local notation "𝔸" => AdeleRing (𝓞 K) K

private abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

variable {K}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

section Geometry

open Set

variable (K)

private def region (x : G𝔸) (C : Set G𝔸) : Set G𝔸 :=
  Set.image2 (fun (t : 𝔸) (c : G𝔸) => unipotentGL2 t * x * c) (closure (adelicBox K)) C

private def cen : Z𝔸 →* G𝔸 :=
  (centralScalar (𝓞 K) K).comp Matrix.GeneralLinearGroup.det

private theorem fst_apply_ne_zero (t : (𝔸)ˣ) (w : InfinitePlace K) : (t : 𝔸).1 w ≠ 0 := by
  intro h0
  have h1 : ((t : 𝔸) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)).1 w = (1 : 𝔸).1 w := by rw [Units.mul_inv]
  have h2 : ((t : 𝔸) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)).1 w = (t : 𝔸).1 w * ((t⁻¹ : (𝔸)ˣ) : 𝔸).1 w := rfl
  rw [h2, h0, zero_mul] at h1
  exact zero_ne_one h1

private theorem archComponent_centralScalar_apply (t : (𝔸)ˣ) (w : InfinitePlace K) (i j : Fin 2) :
    ((archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K t)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j = if i = j then (t : 𝔸).1 w else 0 := by
  rw [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

private theorem continuous_unip : Continuous (fun t : 𝔸 => unipotentGL2 t) := by
  have hval : Continuous (fun t : 𝔸 => ((unipotentGL2 t : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have hinv : ∀ t : 𝔸, (unipotentGL2 t)⁻¹ = unipotentGL2 (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  simp only [hinv]
  exact hval.comp continuous_neg

private theorem isCompact_closure_box : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private theorem REGION (x : G𝔸) {C : Set G𝔸} (hC : IsCompact C) :
    IsCompact (region K x C) ∧ MeasurableSet (region K x C) := by
  have hcont : Continuous (fun p : 𝔸 × G𝔸 => unipotentGL2 p.1 * x * p.2) :=
    (((continuous_unip K).comp continuous_fst).mul continuous_const).mul continuous_snd
  have hcpt : IsCompact (region K x C) := by
    rw [region, ← Set.image_prod]
    exact ((isCompact_closure_box K).prod hC).image hcont
  exact ⟨hcpt, hcpt.isClosed.measurableSet⟩

private theorem cen_scalar (t : (𝔸)ˣ) :
    cen K (Matrix.GeneralLinearGroup.scalar (Fin 1) t) = centralScalar (𝓞 K) K t := by
  show centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) t))
    = centralScalar (𝓞 K) K t
  congr 1
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  simp

private theorem globalPoints_scalar (k : Kˣ) :
    globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) k)
      = centralScalar (𝓞 K) K (Units.map (algebraMap K (𝔸)) k) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [centralScalar_val, Matrix.diagonal_apply]
  show algebraMap K (𝔸) (Matrix.scalar (Fin 2) (k : K) i j) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem cen_mul_eq (z : Z𝔸) (X : G𝔸) : cen K z * X = X * cen K z :=
  (mul_centralScalar_comm (Matrix.GeneralLinearGroup.det z) X).symm

private theorem exists_isCompact_adeles (r : ℝ) {B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)}
    (hB : IsCompact B) :
    ∃ A : Set 𝔸, IsCompact A ∧ ∀ y : 𝔸, (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) → y.2 ∈ B → y ∈ A := by
  have hball : ∀ w : InfinitePlace K,
      IsCompact (InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall (0 : ℂ) r) :=
    fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall 0 r)
  refine ⟨(Set.pi Set.univ fun w : InfinitePlace K =>
      InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall (0 : ℂ) r) ×ˢ B,
    (isCompact_univ_pi hball).prod hB, fun y hy₁ hy₂ => ⟨?_, hy₂⟩⟩
  refine Set.mem_univ_pi.mpr fun w => ?_
  rw [Set.mem_preimage, mem_closedBall_zero_iff, SiegelCoordinates.norm_extensionEmbedding]
  exact hy₁ w

private theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : G𝔸 → (𝔸)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : G𝔸 => ((Matrix.GeneralLinearGroup.det g : (𝔸)ˣ) : 𝔸)
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_val.matrix_det
  · show Continuous fun g : G𝔸 => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (𝔸)ˣ) : 𝔸)
    simp only [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_coe_inv.matrix_det

private theorem unip_inv (s : 𝔸) : (unipotentGL2 s : G𝔸)⁻¹ = unipotentGL2 (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

section Local

variable {L : Type*} [NormedField L]

private def entryNormSq (M : Matrix (Fin 2) (Fin 2) L) : ℝ :=
  ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2

private theorem entryNormSq_nonneg (M : Matrix (Fin 2) (Fin 2) L) : 0 ≤ entryNormSq M := by
  unfold entryNormSq
  positivity

private theorem rowNormSq_mul_le (M N : Matrix (Fin 2) (Fin 2) L) (i : Fin 2) :
    ‖(M * N) i 0‖ ^ 2 + ‖(M * N) i 1‖ ^ 2 ≤ (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * entryNormSq N := by
  have h : ∀ j : Fin 2, ‖(M * N) i j‖ ^ 2
      ≤ (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * (‖N 0 j‖ ^ 2 + ‖N 1 j‖ ^ 2) := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : ‖M i 0 * N 0 j + M i 1 * N 1 j‖ ≤ ‖M i 0‖ * ‖N 0 j‖ + ‖M i 1‖ * ‖N 1 j‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    nlinarith [sq_nonneg (‖M i 0‖ * ‖N 1 j‖ - ‖M i 1‖ * ‖N 0 j‖), norm_nonneg (M i 0),
      norm_nonneg (M i 1), norm_nonneg (N 0 j), norm_nonneg (N 1 j)]
  calc ‖(M * N) i 0‖ ^ 2 + ‖(M * N) i 1‖ ^ 2
      ≤ (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * (‖N 0 0‖ ^ 2 + ‖N 1 0‖ ^ 2)
        + (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * (‖N 0 1‖ ^ 2 + ‖N 1 1‖ ^ 2) := add_le_add (h 0) (h 1)
    _ = (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * entryNormSq N := by
        unfold entryNormSq
        ring

private def transFactor (k : GL (Fin 2) L) : ℝ :=
  entryNormSq (k : Matrix (Fin 2) (Fin 2) L) / ‖(k : Matrix (Fin 2) (Fin 2) L).det‖

private theorem aux_ineq {dg dk Rg Rgk E : ℝ} (hdk : 0 < dk) (hRg : 0 < Rg) (hRgk : 0 < Rgk)
    (hdg : 0 ≤ dg) (hle : Rgk ≤ Rg * E) : dg / Rg ≤ E / dk * (dg * dk / Rgk) := by
  rw [div_mul_div_comm, div_le_div_iff₀ hRg (mul_pos hdk hRgk)]
  have h := mul_le_mul_of_nonneg_left hle (mul_nonneg hdg hdk.le)
  calc dg * (dk * Rgk) = dg * dk * Rgk := by ring
    _ ≤ dg * dk * (Rg * E) := h
    _ = E * (dg * dk) * Rg := by ring

private theorem localHeight_le_transFactor_mul (g k : GL (Fin 2) L) :
    localHeight g ≤ transFactor k * localHeight (g * k) := by
  have hRg := rowNormSq_pos g
  have hRgk := rowNormSq_pos (g * k)
  rw [Units.val_mul] at hRgk
  have hdk : 0 < ‖(k : Matrix (Fin 2) (Fin 2) L).det‖ :=
    norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero
  unfold localHeight transFactor
  rw [Units.val_mul, Matrix.det_mul, norm_mul]
  exact aux_ineq hdk hRg hRgk (norm_nonneg _) (rowNormSq_mul_le _ _ 1)

private theorem continuous_transFactor : Continuous (transFactor : GL (Fin 2) L → ℝ) := by
  have hc : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) L => ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hnum : Continuous fun k : GL (Fin 2) L => entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := by
    unfold entryNormSq
    exact ((((hc 0 0).pow 2).add ((hc 0 1).pow 2)).add ((hc 1 0).pow 2)).add ((hc 1 1).pow 2)
  have hdet : Continuous fun k : GL (Fin 2) L => ‖(k : Matrix (Fin 2) (Fin 2) L).det‖ :=
    (Units.continuous_val.matrix_det).norm
  exact hnum.div hdet fun k => (norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero).ne'

private def ratioFactor (k : GL (Fin 2) L) : ℝ :=
  entryNormSq (k : Matrix (Fin 2) (Fin 2) L) * entryNormSq ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)

private theorem continuous_ratioFactor : Continuous (ratioFactor : GL (Fin 2) L → ℝ) := by
  have hc : ∀ i j : Fin 2,
      Continuous fun k : GL (Fin 2) L => ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ ^ 2 :=
    fun i j => ((Units.continuous_val.matrix_elem i j).norm).pow 2
  have hc' : ∀ i j : Fin 2,
      Continuous fun k : GL (Fin 2) L => ‖((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖ ^ 2 :=
    fun i j => ((Units.continuous_coe_inv.matrix_elem i j).norm).pow 2
  unfold ratioFactor entryNormSq
  exact ((((hc 0 0).add (hc 0 1)).add (hc 1 0)).add (hc 1 1)).mul
    ((((hc' 0 0).add (hc' 0 1)).add (hc' 1 0)).add (hc' 1 1))

private theorem transFactor_nonneg (k : GL (Fin 2) L) : 0 ≤ transFactor k :=
  div_nonneg (entryNormSq_nonneg _) (norm_nonneg _)

private theorem ratioFactor_nonneg (k : GL (Fin 2) L) : 0 ≤ ratioFactor k :=
  mul_nonneg (entryNormSq_nonneg _) (entryNormSq_nonneg _)

private def ratio (g : GL (Fin 2) L) : ℝ :=
  topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L)

private theorem ratio_eq (g : GL (Fin 2) L) : ratio g = xWindowSq g + localHeight g ^ 2 := by
  simp only [ratio, xWindowSq]
  ring

private theorem topNormSq_nonneg' (M : Matrix (Fin 2) (Fin 2) L) : 0 ≤ topNormSq M := by
  unfold topNormSq
  positivity

private theorem ratio_nonneg (g : GL (Fin 2) L) : 0 ≤ ratio g :=
  div_nonneg (topNormSq_nonneg' _) (rowNormSq_pos g).le

private theorem ratio_mul_le (g k : GL (Fin 2) L) : ratio (g * k) ≤ ratioFactor k * ratio g := by
  have hrg := rowNormSq_pos g
  have hrgk := rowNormSq_pos (g * k)
  have htop : topNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_mul]
    exact rowNormSq_mul_le _ _ 0
  have hrow : rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
      ≤ rowNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        * entryNormSq ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
    have hg : (g : Matrix (Fin 2) (Fin 2) L) = ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        * ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
      rw [← Units.val_mul, mul_inv_cancel_right]
    calc rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
        = rowNormSq (((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
            * ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) := by rw [← hg]
      _ ≤ _ := rowNormSq_mul_le _ _ 1
  have hdiv : 0 ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L) :=
    div_nonneg (topNormSq_nonneg' _) hrg.le
  unfold ratio ratioFactor
  rw [div_le_iff₀ hrgk]
  calc topNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := htop
    _ = topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
          * rowNormSq (g : Matrix (Fin 2) (Fin 2) L) * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := by
        rw [div_mul_cancel₀ _ hrg.ne']
    _ ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
          * (rowNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
            * entryNormSq ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))
          * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrow hdiv) (entryNormSq_nonneg _)
    _ = _ := by ring

private theorem ratio_unip_mul_le (b : L) (g : GL (Fin 2) L) :
    ratio (unipotentGL2 b * g) ≤ 2 * ratio g + 2 * ‖b‖ ^ 2 := by
  have hrg := rowNormSq_pos g
  have hrow : rowNormSq ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) L) := by
    rw [rowNormSq_scalar_entries_mul (z := (1 : L)) (by rw [unipotentGL2_coe]; rfl)
      (by rw [unipotentGL2_coe]; rfl) g, norm_one, one_pow, one_mul]
  have h0 : ∀ j : Fin 2, ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 j
      = (g : Matrix (Fin 2) (Fin 2) L) 0 j + b * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
    intro j
    rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
    simp
  have hsq : ∀ u v : L, ‖u + b * v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * (‖b‖ ^ 2 * ‖v‖ ^ 2) := by
    intro u v
    have h1 : ‖u + b * v‖ ≤ ‖u‖ + ‖b‖ * ‖v‖ := by
      rw [← norm_mul]
      exact norm_add_le _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖u‖ - ‖b‖ * ‖v‖)]
  have htop : topNormSq ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      ≤ 2 * topNormSq (g : Matrix (Fin 2) (Fin 2) L)
        + 2 * ‖b‖ ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) L) := by
    unfold topNormSq rowNormSq
    rw [h0 0, h0 1]
    nlinarith [hsq ((g : Matrix (Fin 2) (Fin 2) L) 0 0) ((g : Matrix (Fin 2) (Fin 2) L) 1 0),
      hsq ((g : Matrix (Fin 2) (Fin 2) L) 0 1) ((g : Matrix (Fin 2) (Fin 2) L) 1 1)]
  unfold ratio
  rw [hrow, div_le_iff₀ hrg]
  calc topNormSq ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ≤ _ := htop
    _ = (2 * (topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L))
          + 2 * ‖b‖ ^ 2) * rowNormSq (g : Matrix (Fin 2) (Fin 2) L) := by
        field_simp

private theorem localHeight_unip_mul (b : L) (g : GL (Fin 2) L) :
    localHeight (unipotentGL2 b * g) = localHeight g := by
  rw [SiegelCoordinates.localHeight_upper_entries_mul (a := (1 : L)) (t := (1 : L)) one_ne_zero
    (by rw [unipotentGL2_coe]; rfl) (by rw [unipotentGL2_coe]; rfl) (by rw [unipotentGL2_coe]; rfl) g,
    norm_one, div_one, one_mul]

private theorem local_bounds {q β' r : L} (hr : r ≠ 0) (D S X Y M : GL (Fin 2) L)
    (hD00 : (D : Matrix (Fin 2) (Fin 2) L) 0 0 = q) (hD01 : (D : Matrix (Fin 2) (Fin 2) L) 0 1 = β')
    (hD10 : (D : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hD11 : (D : Matrix (Fin 2) (Fin 2) L) 1 1 = 1)
    (hS : ∀ i j, (S : Matrix (Fin 2) (Fin 2) L) i j = if i = j then r else 0)
    (hXY : localHeight X = localHeight Y) (h : D * Y = S * (X * M)) :
    ‖q‖ ≤ transFactor (M⁻¹ : GL (Fin 2) L)
      ∧ ‖β'‖ ^ 2 ≤ 2 * (ratioFactor M * ratio X) + 2 * ‖q‖ ^ 2 * ratio Y := by
  have hY := localHeight_pos Y
  have hSmul : localHeight (S * (X * M)) = localHeight (X * M) :=
    localHeight_scalar_entries_mul hr (hS 0 0) (by rw [hS]; rfl) (by rw [hS]; rfl) (hS 1 1) (X * M)
  constructor
  · have h1 : localHeight (D * Y) = ‖q‖ / ‖(1 : L)‖ * localHeight Y :=
      SiegelCoordinates.localHeight_upper_entries_mul one_ne_zero hD00 hD10 hD11 Y
    rw [norm_one, div_one] at h1
    have h2 : localHeight (X * M) ≤ transFactor (M⁻¹ : GL (Fin 2) L) * localHeight Y := by
      have := localHeight_le_transFactor_mul (X * M) M⁻¹
      rwa [mul_inv_cancel_right, hXY] at this
    have h3 : ‖q‖ * localHeight Y ≤ transFactor (M⁻¹ : GL (Fin 2) L) * localHeight Y := by
      rw [← h1, h, hSmul]
      exact h2
    exact le_of_mul_le_mul_right h3 hY
  ·
    set P : GL (Fin 2) L := X * M with hP
    have hmat : (D : Matrix (Fin 2) (Fin 2) L) * (Y : Matrix (Fin 2) (Fin 2) L)
        = (S : Matrix (Fin 2) (Fin 2) L) * (P : Matrix (Fin 2) (Fin 2) L) := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    have hSP : ∀ i j : Fin 2, ((S : Matrix (Fin 2) (Fin 2) L) * (P : Matrix (Fin 2) (Fin 2) L)) i j
        = r * (P : Matrix (Fin 2) (Fin 2) L) i j := by
      intro i j
      rw [Matrix.mul_apply, Fin.sum_univ_two, hS, hS]
      fin_cases i <;> simp
    have htopEq : ∀ j : Fin 2, q * (Y : Matrix (Fin 2) (Fin 2) L) 0 j + β' * (Y : Matrix (Fin 2) (Fin 2) L) 1 j
        = r * (P : Matrix (Fin 2) (Fin 2) L) 0 j := by
      intro j
      rw [← hSP, ← hmat, Matrix.mul_apply, Fin.sum_univ_two, hD00, hD01]
    have hbotEq : ∀ j : Fin 2, (Y : Matrix (Fin 2) (Fin 2) L) 1 j = r * (P : Matrix (Fin 2) (Fin 2) L) 1 j := by
      intro j
      rw [← hSP, ← hmat, Matrix.mul_apply, Fin.sum_univ_two, hD10, hD11, zero_mul, one_mul, zero_add]

    have hrowY : rowNormSq (Y : Matrix (Fin 2) (Fin 2) L) = ‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L) := by
      unfold rowNormSq
      rw [hbotEq 0, hbotEq 1, norm_mul, norm_mul]
      ring

    have hper : ∀ j : Fin 2, ‖β'‖ ^ 2 * ‖(Y : Matrix (Fin 2) (Fin 2) L) 1 j‖ ^ 2
        ≤ 2 * (‖r‖ ^ 2 * ‖(P : Matrix (Fin 2) (Fin 2) L) 0 j‖ ^ 2)
          + 2 * (‖q‖ ^ 2 * ‖(Y : Matrix (Fin 2) (Fin 2) L) 0 j‖ ^ 2) := by
      intro j
      have e : β' * (Y : Matrix (Fin 2) (Fin 2) L) 1 j
          = r * (P : Matrix (Fin 2) (Fin 2) L) 0 j - q * (Y : Matrix (Fin 2) (Fin 2) L) 0 j := by
        rw [← htopEq j]
        ring
      have h1 : ‖β' * (Y : Matrix (Fin 2) (Fin 2) L) 1 j‖
          ≤ ‖r‖ * ‖(P : Matrix (Fin 2) (Fin 2) L) 0 j‖ + ‖q‖ * ‖(Y : Matrix (Fin 2) (Fin 2) L) 0 j‖ := by
        rw [e, ← norm_mul, ← norm_mul]
        exact norm_sub_le _ _
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [norm_mul, mul_pow] at h2
      nlinarith [sq_nonneg (‖r‖ * ‖(P : Matrix (Fin 2) (Fin 2) L) 0 j‖ - ‖q‖ * ‖(Y : Matrix (Fin 2) (Fin 2) L) 0 j‖)]
    have hsum : ‖β'‖ ^ 2 * rowNormSq (Y : Matrix (Fin 2) (Fin 2) L)
        ≤ 2 * (‖r‖ ^ 2 * topNormSq (P : Matrix (Fin 2) (Fin 2) L))
          + 2 * (‖q‖ ^ 2 * topNormSq (Y : Matrix (Fin 2) (Fin 2) L)) := by
      unfold rowNormSq topNormSq
      nlinarith [hper 0, hper 1]
    have hrP := rowNormSq_pos P
    have hrY := rowNormSq_pos Y
    have hrn : (0 : ℝ) < ‖r‖ ^ 2 := by positivity

    have hβ : ‖β'‖ ^ 2 ≤ 2 * ratio P + 2 * ‖q‖ ^ 2 * ratio Y := by
      unfold ratio
      rw [hrowY] at hsum hrY
      have key : ‖β'‖ ^ 2 * (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L))
          ≤ (2 * (topNormSq (P : Matrix (Fin 2) (Fin 2) L) / rowNormSq (P : Matrix (Fin 2) (Fin 2) L))
            + 2 * ‖q‖ ^ 2 * (topNormSq (Y : Matrix (Fin 2) (Fin 2) L)
              / (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L))))
            * (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L)) := by
        rw [add_mul, mul_assoc (2 * ‖q‖ ^ 2), div_mul_cancel₀ _ hrY.ne']
        calc ‖β'‖ ^ 2 * (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L)) ≤ _ := hsum
          _ = _ := by
            field_simp
      rw [hrowY]
      exact le_of_mul_le_mul_right key hrY
    calc ‖β'‖ ^ 2 ≤ 2 * ratio P + 2 * ‖q‖ ^ 2 * ratio Y := hβ
      _ ≤ 2 * (ratioFactor M * ratio X) + 2 * ‖q‖ ^ 2 * ratio Y := by
        have := ratio_mul_le X M
        rw [← hP] at this
        linarith

end Local

private def diffSet (C : Set G𝔸) : Set G𝔸 :=
  Set.image2 (fun c c' : G𝔸 => c * c'⁻¹) C C

private theorem isCompact_diffSet {C : Set G𝔸} (hC : IsCompact C) : IsCompact (diffSet K C) := by
  unfold diffSet
  rw [← Set.image_prod]
  exact (hC.prod hC).image (continuous_fst.mul continuous_snd.inv)

private def Linked (C : Set G𝔸) (x : G𝔸) (δ : GL (Fin 2) K) : Prop :=
  ∃ (b b₀ : 𝔸) (ρ : Z𝔸) (M : G𝔸), b ∈ closure (adelicBox K) ∧ b₀ ∈ closure (adelicBox K) ∧ M ∈ diffSet K C ∧
    globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x) = cen K ρ * (unipotentGL2 b * x) * M

private def upper (q β' : K) (hq : q ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![q, β'; 0, 1] (by rw [Matrix.det_fin_two_of]; simp [hq])

omit [NumberField K] in
private theorem upper_coe (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) = !![q, β'; 0, 1] := rfl

omit [NumberField K] in
private theorem upper_apply_zero_zero (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 0 0 = q := rfl

omit [NumberField K] in
private theorem upper_apply_zero_one (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 0 1 = β' := rfl

omit [NumberField K] in
private theorem upper_apply_one_zero (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := rfl

omit [NumberField K] in
private theorem upper_apply_one_one (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := rfl

private theorem linked_of_scalar_mul {C : Set G𝔸} {x : G𝔸} {δ : GL (Fin 2) K} (s : Kˣ)
    (h : Linked K C x (Matrix.GeneralLinearGroup.scalar (Fin 2) s * δ)) : Linked K C x δ := by
  obtain ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ := h
  refine ⟨b, b₀, (Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap K (𝔸)) s))⁻¹ * ρ, M,
    hb, hb₀, hM, ?_⟩
  rw [map_mul, globalPoints_scalar] at heq
  rw [map_mul, map_inv, cen_scalar]
  simp only [mul_assoc] at heq ⊢
  rw [← heq, inv_mul_cancel_left]

private def ac (w : InfinitePlace K) (g : G𝔸) : GL (Fin 2) w.Completion :=
  archComponent K w (glArch (𝓞 K) K g)

private theorem ac_mul (w : InfinitePlace K) (g h : G𝔸) : ac K w (g * h) = ac K w g * ac K w h := by
  unfold ac
  rw [map_mul, map_mul]

private theorem ac_apply (w : InfinitePlace K) (g : G𝔸) (i j : Fin 2) :
    (ac K w g : Matrix (Fin 2) (Fin 2) w.Completion) i j = ((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w :=
  rfl

private theorem ac_globalPoints_apply (w : InfinitePlace K) (γ : GL (Fin 2) K) (i j : Fin 2) :
    (ac K w (globalPoints (𝓞 K) K γ) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = ((γ : Matrix (Fin 2) (Fin 2) K) i j : w.Completion) :=
  rfl

private theorem ac_cen_apply (w : InfinitePlace K) (ρ : Z𝔸) (i j : Fin 2) :
    (ac K w (cen K ρ) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then ((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸).1 w else 0 :=
  archComponent_centralScalar_apply K (Matrix.GeneralLinearGroup.det ρ) w i j

private theorem ac_unip (w : InfinitePlace K) (b : 𝔸) : ac K w (unipotentGL2 b) = unipotentGL2 (b.1 w) := by
  ext i j
  rw [ac_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem linked_arch {C : Set G𝔸} {x : G𝔸} {q β' : K} (hq : q ≠ 0)
    (h : Linked K C x (upper K q β' hq)) (w : InfinitePlace K) :
    ∃ M ∈ diffSet K C, ∃ b ∈ closure (adelicBox K), ∃ b₀ ∈ closure (adelicBox K),
      ‖(q : w.Completion)‖ ≤ transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion)
        ∧ ‖(β' : w.Completion)‖ ^ 2
          ≤ 2 * (ratioFactor (ac K w M) * (2 * ratio (ac K w x) + 2 * ‖b.1 w‖ ^ 2))
            + 2 * ‖(q : w.Completion)‖ ^ 2 * (2 * ratio (ac K w x) + 2 * ‖b₀.1 w‖ ^ 2) := by
  obtain ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ := h
  refine ⟨M, hM, b, hb, b₀, hb₀, ?_⟩
  have heqw := congrArg (ac K w) heq
  rw [ac_mul, ac_mul, ac_mul, ac_mul, ac_mul, ac_unip, ac_unip, mul_assoc] at heqw
  have hXY : localHeight (unipotentGL2 (b.1 w) * ac K w x) = localHeight (unipotentGL2 (b₀.1 w) * ac K w x) := by
    rw [localHeight_unip_mul, localHeight_unip_mul]
  obtain ⟨h1, h2⟩ := local_bounds (q := (q : w.Completion)) (β' := (β' : w.Completion))
    (fst_apply_ne_zero K (Matrix.GeneralLinearGroup.det ρ) w) _ _ _ _ _
    (ac_globalPoints_apply K w _ 0 0) (ac_globalPoints_apply K w _ 0 1)
    (by rw [ac_globalPoints_apply, upper_apply_one_zero]; first | exact NumberField.InfinitePlace.Completion.ext (by simp) | simp)
    (by rw [ac_globalPoints_apply, upper_apply_one_one]; first | exact NumberField.InfinitePlace.Completion.ext (by simp) | simp)
    (ac_cen_apply K w ρ) hXY heqw
  refine ⟨h1, h2.trans ?_⟩
  have hrf := ratioFactor_nonneg (ac K w M)
  have hb1 := mul_le_mul_of_nonneg_left (ratio_unip_mul_le (b.1 w) (ac K w x)) hrf
  have hq2 : (0 : ℝ) ≤ ‖(q : w.Completion)‖ ^ 2 := by positivity
  have hb2 := mul_le_mul_of_nonneg_left (ratio_unip_mul_le (b₀.1 w) (ac K w x)) hq2
  linarith

private theorem snd_mem_of_mem_closure_box {b : 𝔸} (hb : b ∈ closure (adelicBox K)) :
    b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hcl : IsClosed {y : 𝔸 | y.2 ∈ AdelicBox.integralFiniteAdeles (𝓞 K) K} :=
    (AdelicBox.isClosed_integralFiniteAdeles K).preimage continuous_snd
  exact closure_minimal (fun y hy => hy.2) hcl hb

private theorem glFin_unip_mem {b : 𝔸} (hb : b ∈ closure (adelicBox K)) :
    glFin (𝓞 K) K (unipotentGL2 b) ∈ finiteIntegralGL2 (𝓞 K) K := by
  have h2 := snd_mem_of_mem_closure_box K hb
  have hneg : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles h2
  rw [mem_finiteIntegralGL2_iff, ← map_inv, unip_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact h2
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hneg
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles

private theorem isCompact_finiteIntegralGL2' :
    IsCompact (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))) := by
  have : (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)))
      = {g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) |
          (∀ i j, (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
            ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) ∧
          ∀ i j, ((g⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
            ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K} :=
    Set.ext fun g => mem_finiteIntegralGL2_iff
  rw [this]
  exact isCompact_setOf_integral (𝓞 K) K

private def finBox (C : Set G𝔸) : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :=
  Set.image2
    (fun (p : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
        × GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
      (m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) => p.1 * m * p.2⁻¹)
    ((finiteIntegralGL2 (𝓞 K) K : Set _) ×ˢ (finiteIntegralGL2 (𝓞 K) K : Set _))
    (glFin (𝓞 K) K '' diffSet K C)

private theorem isCompact_finBox {C : Set G𝔸} (hC : IsCompact C) : IsCompact (finBox K C) := by
  unfold finBox
  rw [← Set.image_prod]
  refine (((isCompact_finiteIntegralGL2' K).prod (isCompact_finiteIntegralGL2' K)).prod
    ((isCompact_diffSet K hC).image (continuous_glFin (𝓞 K) K))).image ?_
  exact ((continuous_fst.comp continuous_fst).mul continuous_snd).mul
    (continuous_snd.comp continuous_fst).inv

private def finConf (C : Set G𝔸) (j : Fin 2) : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
  (fun N : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) =>
    ((N⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1
      * (N : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 0 j) '' finBox K C

private theorem isCompact_finConf {C : Set G𝔸} (hC : IsCompact C) (j : Fin 2) : IsCompact (finConf K C j) :=
  (isCompact_finBox K hC).image
    ((Units.continuous_coe_inv.matrix_elem 1 1).mul (Units.continuous_val.matrix_elem 0 j))

omit [NumberField K] in
private theorem upper_inv_apply_one_one {q β' : K} (hq : q ≠ 0) :
    (((upper K q β' hq)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  rw [Matrix.coe_units_inv, upper_coe, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two_of,
    Matrix.smul_apply, Matrix.of_apply]
  simp [Ring.inverse_eq_inv', hq]

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    (glFin (𝓞 K) K (globalPoints (𝓞 K) K γ) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
      = algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) :=
  rfl

private theorem glFin_cen_apply (ρ : Z𝔸) (i j : Fin 2) :
    (glFin (𝓞 K) K (cen K ρ) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
      = if i = j then ((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸).2 else 0 := by
  rw [glFin_apply]
  show ((centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det ρ) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = _
  rw [centralScalar_val, Matrix.diagonal_apply]
  split_ifs <;> rfl

private theorem linked_fin {C : Set G𝔸} {x : G𝔸} (hx : glFin (𝓞 K) K x ∈ finiteIntegralGL2 (𝓞 K) K)
    {q β' : K} (hq : q ≠ 0) (h : Linked K C x (upper K q β' hq)) :
    (algebraMap K (𝔸) q).2 ∈ finConf K C 0 ∧ (algebraMap K (𝔸) β').2 ∈ finConf K C 1 := by
  obtain ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ := h
  set δ := upper K q β' hq with hδ
  set N : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
    (glFin (𝓞 K) K (unipotentGL2 b) * glFin (𝓞 K) K x) * glFin (𝓞 K) K M
      * (glFin (𝓞 K) K (unipotentGL2 b₀) * glFin (𝓞 K) K x)⁻¹ with hN
  have hNmem : N ∈ finBox K C := by
    refine Set.mem_image2_of_mem
      (a := (glFin (𝓞 K) K (unipotentGL2 b) * glFin (𝓞 K) K x, glFin (𝓞 K) K (unipotentGL2 b₀) * glFin (𝓞 K) K x))
      ⟨Subgroup.mul_mem _ (glFin_unip_mem K hb) hx, Subgroup.mul_mem _ (glFin_unip_mem K hb₀) hx⟩
      (Set.mem_image_of_mem _ hM)

  have hsplit : glFin (𝓞 K) K (globalPoints (𝓞 K) K δ) * (glFin (𝓞 K) K (unipotentGL2 b₀) * glFin (𝓞 K) K x)
      = glFin (𝓞 K) K (cen K ρ) * (glFin (𝓞 K) K (unipotentGL2 b) * glFin (𝓞 K) K x) * glFin (𝓞 K) K M := by
    have := congrArg (glFin (𝓞 K) K) heq
    simpa only [map_mul] using this
  have hfin : glFin (𝓞 K) K (globalPoints (𝓞 K) K δ) = glFin (𝓞 K) K (cen K ρ) * N := by
    rw [eq_mul_inv_of_mul_eq hsplit, hN]
    simp only [mul_assoc]
  set r : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K := ((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸).2 with hr
  have hentry : ∀ i j : Fin 2,
      algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) ((δ : Matrix (Fin 2) (Fin 2) K) i j)
        = r * (N : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j := by
    intro i j
    rw [← glFin_globalPoints_apply, hfin, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, glFin_cen_apply,
      glFin_cen_apply]
    fin_cases i <;> simp [hr]

  have hinv : r = ((N⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1 := by
    have h1 : (glFin (𝓞 K) K (globalPoints (𝓞 K) K δ))⁻¹ = N⁻¹ * glFin (𝓞 K) K (cen K ρ⁻¹) := by
      rw [hfin, mul_inv_rev, map_inv, map_inv]
    have h2 := congrArg (fun g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) =>
      (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1) h1
    beta_reduce at h2
    rw [← map_inv, ← map_inv, glFin_globalPoints_apply, hδ, upper_inv_apply_one_one, map_one, Units.val_mul,
      Matrix.mul_apply, Fin.sum_univ_two, glFin_cen_apply, glFin_cen_apply,
      if_neg (show ¬ ((0 : Fin 2) = 1) by decide), if_pos rfl, mul_zero, zero_add] at h2

    have hrr : r * ((Matrix.GeneralLinearGroup.det ρ⁻¹ : (𝔸)ˣ) : 𝔸).2 = 1 := by
      rw [hr, map_inv]
      show (((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸)
        * (((Matrix.GeneralLinearGroup.det ρ)⁻¹ : (𝔸)ˣ) : 𝔸)).2 = 1
      rw [Units.mul_inv]
      rfl
    calc r = r * (((N⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1
            * ((Matrix.GeneralLinearGroup.det ρ⁻¹ : (𝔸)ˣ) : 𝔸).2) := by rw [← h2, mul_one]
      _ = _ := by rw [mul_comm _ (((Matrix.GeneralLinearGroup.det ρ⁻¹ : (𝔸)ˣ) : 𝔸).2), ← mul_assoc, hrr, one_mul]
  refine ⟨⟨N, hNmem, ?_⟩, ⟨N, hNmem, ?_⟩⟩
  · beta_reduce
    rw [← hinv, ← hentry 0 0, hδ, upper_apply_zero_zero]
    rfl
  · beta_reduce
    rw [← hinv, ← hentry 0 1, hδ, upper_apply_zero_one]
    rfl

private theorem archHeight_eq_prod (g : G𝔸) :
    archHeight K (glArch (𝓞 K) K g) = ∏ w : InfinitePlace K, localHeight (ac K w g) ^ w.mult :=
  rfl

private theorem archHeight_unip_mul (b : 𝔸) (x : G𝔸) :
    archHeight K (glArch (𝓞 K) K (unipotentGL2 b * x)) = archHeight K (glArch (𝓞 K) K x) := by
  rw [archHeight_eq_prod, archHeight_eq_prod]
  exact Finset.prod_congr rfl fun w _ => by rw [ac_mul, ac_unip, localHeight_unip_mul]

private theorem exists_forall_linked_upper {C : Set G𝔸} (hC : IsCompact C) :
    ∃ T₁ : ℝ, ∀ x : G𝔸, glFin (𝓞 K) K x ∈ finiteIntegralGL2 (𝓞 K) K →
      T₁ < archHeight K (glArch (𝓞 K) K x) → ∀ δ : GL (Fin 2) K, Linked K C x δ →
        (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  obtain ⟨T₀, hT₀⟩ :=
    AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
      K (isCompact_diffSet K hC)
  refine ⟨T₀, fun x hx hT δ ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ => ?_⟩
  have hxb : glFin (𝓞 K) K (unipotentGL2 b * x) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul]
    exact Subgroup.mul_mem _ (glFin_unip_mem K hb) hx
  have hxb₀ : glFin (𝓞 K) K (unipotentGL2 b₀ * x) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul]
    exact Subgroup.mul_mem _ (glFin_unip_mem K hb₀) hx
  refine hT₀ (unipotentGL2 b * x) (unipotentGL2 b₀ * x) hxb hxb₀ (by rwa [archHeight_unip_mul])
    (by rwa [archHeight_unip_mul]) δ (Matrix.GeneralLinearGroup.det ρ⁻¹) ?_
  have h₁ : (unipotentGL2 b * x)⁻¹ * globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x) = cen K ρ * M := by
    rw [mul_assoc, heq, cen_mul_eq, mul_assoc (unipotentGL2 b * x), inv_mul_cancel_left]
  have h₂ : (unipotentGL2 b * x)⁻¹ * globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x)
      * centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det ρ⁻¹) = M := by
    rw [h₁, show centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det ρ⁻¹) = cen K ρ⁻¹ from rfl, cen_mul_eq,
      mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [h₂]
  exact hM

private theorem exists_factor_bound {C : Set G𝔸} (hC : IsCompact C) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ M ∈ diffSet K C, ∀ w : InfinitePlace K,
      transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion) ≤ κ ∧ ratioFactor (ac K w M) ≤ κ := by
  have hcont : Continuous fun M : G𝔸 => ∑ w : InfinitePlace K,
      (transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion) + ratioFactor (ac K w M)) := by
    refine continuous_finsetSum _ fun w _ => ?_
    have hac : Continuous (ac K w) := (continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K)
    exact (continuous_transFactor.comp hac.inv).add (continuous_ratioFactor.comp hac)
  obtain ⟨κ, hκ⟩ := (isCompact_diffSet K hC).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max κ 0, le_max_right _ _, fun M hM w => ?_⟩
  have hterm : ∀ v : InfinitePlace K,
      0 ≤ transFactor ((ac K v M)⁻¹ : GL (Fin 2) v.Completion) + ratioFactor (ac K v M) :=
    fun v => add_nonneg (transFactor_nonneg _) (ratioFactor_nonneg _)
  have hle : transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion) + ratioFactor (ac K w M) ≤ κ := by
    refine le_trans (Finset.single_le_sum (fun v _ => hterm v) (Finset.mem_univ w)) ?_
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hκ M hM))
  exact ⟨(le_add_of_nonneg_right (ratioFactor_nonneg _)).trans (hle.trans (le_max_left _ _)),
    (le_add_of_nonneg_left (transFactor_nonneg _)).trans (hle.trans (le_max_left _ _))⟩

private theorem exists_box_bound :
    ∃ rB : ℝ, 0 ≤ rB ∧ ∀ b ∈ closure (adelicBox K), ∀ w : InfinitePlace K, ‖b.1 w‖ ^ 2 ≤ rB := by
  have hcont : Continuous fun b : 𝔸 => ∑ w : InfinitePlace K, ‖b.1 w‖ ^ 2 :=
    continuous_finsetSum _ fun w _ => (((continuous_archEval K w).comp continuous_fst).norm).pow 2
  obtain ⟨r, hr⟩ := (isCompact_closure_box K).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max r 0, le_max_right _ _, fun b hb w => ?_⟩
  refine le_trans (Finset.single_le_sum (f := fun v : InfinitePlace K => ‖b.1 v‖ ^ 2)
    (fun v _ => by positivity) (Finset.mem_univ w)) ?_
  exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hr b hb))).trans (le_max_left _ _)

omit [NumberField K] in

private theorem diag_ne_zero {δ : GL (Fin 2) K} (h10 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (δ : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 ∧ (δ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  have hdet : (δ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnits_det_units δ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

omit [NumberField K] in

private theorem eq_scalar_mul_upper {δ : GL (Fin 2) K} (h10 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ (diag_ne_zero K h10).2)
      * upper K ((δ : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1)
          ((δ : Matrix (Fin 2) (Fin 2) K) 0 1 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1)
          (div_ne_zero (diag_ne_zero K h10).1 (diag_ne_zero K h10).2) := by
  obtain ⟨-, hd⟩ := diag_ne_zero K h10
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul]
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ (diag_ne_zero K h10).2) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) ((δ : Matrix (Fin 2) (Fin 2) K) 1 1) := rfl
  rw [hs, upper_coe, Matrix.scalar_apply, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [h10] <;> field_simp

private theorem exists_prod_max_pow_le {c' : ℝ} (hc' : 0 < c') {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    ∃ (κ₀ : ℝ) (A : ℕ), 0 ≤ κ₀ ∧ ∀ x : G𝔸, (∀ w : InfinitePlace K, c' ≤ localHeight (ac K w x)) →
      1 ≤ archHeight K (glArch (𝓞 K) K x) →
        ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult
          ≤ κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A := by
  set d : ℕ := ∑ w : InfinitePlace K, w.mult with hd
  set cm : ℝ := min 1 c' with hcm
  have hcm0 : 0 < cm := lt_min one_pos hc'
  have hcm1 : cm ≤ 1 := min_le_left _ _
  have hcd0 : 0 < cm ^ d := pow_pos hcm0 d
  have hcd1 : cm ^ d ≤ 1 := pow_le_one₀ hcm0.le hcm1
  refine ⟨((1 + r₁ + r₂) / (cm ^ d) ^ 2) ^ d, 2 * d, by positivity, fun x hfloor hH => ?_⟩
  set H : ℝ := archHeight K (glArch (𝓞 K) K x) with hHdef

  have hloc : ∀ w : InfinitePlace K, localHeight (ac K w x) ^ w.mult ≤ H / cm ^ d := by
    intro w
    classical
    rw [le_div_iff₀ hcd0, hHdef, archHeight_eq_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (localHeight_pos _).le _)
    calc cm ^ d ≤ cm ^ ∑ v ∈ Finset.univ.erase w, v.mult :=
          pow_le_pow_of_le_one hcm0.le hcm1 (Finset.sum_le_sum_of_subset (Finset.erase_subset w Finset.univ))
      _ = ∏ v ∈ Finset.univ.erase w, cm ^ v.mult := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ v ∈ Finset.univ.erase w, localHeight (ac K v x) ^ v.mult :=
          Finset.prod_le_prod (fun v _ => pow_nonneg hcm0.le _) fun v _ =>
            pow_le_pow_left₀ hcm0.le ((min_le_right _ _).trans (hfloor v)) _
  have hHc1 : 1 ≤ H / cm ^ d := by
    rw [le_div_iff₀ hcd0, one_mul]
    exact hcd1.trans hH

  have hsq : ∀ w : InfinitePlace K, localHeight (ac K w x) ^ 2 ≤ (H / cm ^ d) ^ 2 := by
    intro w
    have hpos := localHeight_pos (ac K w x)
    rcases le_or_gt (localHeight (ac K w x)) 1 with h1 | h1
    · calc localHeight (ac K w x) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hpos.le h1 2
        _ ≤ (H / cm ^ d) ^ 2 := pow_le_pow_left₀ zero_le_one hHc1 2
    · have h2 : localHeight (ac K w x) ≤ localHeight (ac K w x) ^ w.mult :=
        le_self_pow₀ h1.le (InfinitePlace.mult_ne_zero)
      exact pow_le_pow_left₀ hpos.le (h2.trans (hloc w)) 2
  have hmax : ∀ w : InfinitePlace K,
      max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ≤ (1 + r₁ + r₂) * (H / cm ^ d) ^ 2 := by
    intro w
    have hq := hsq w
    have hHc2 : 1 ≤ (H / cm ^ d) ^ 2 := one_le_pow₀ hHc1
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hq hr₂, mul_le_mul_of_nonneg_left hHc2 hr₁]
  calc ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult
      ≤ ∏ w : InfinitePlace K, ((1 + r₁ + r₂) * (H / cm ^ d) ^ 2) ^ w.mult :=
        Finset.prod_le_prod (fun w _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun w _ =>
          pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (hmax w) _
    _ = ((1 + r₁ + r₂) * (H / cm ^ d) ^ 2) ^ d := Finset.prod_pow_eq_pow_sum _ _ _
    _ = ((1 + r₁ + r₂) / (cm ^ d) ^ 2) ^ d * H ^ (2 * d) := by
        rw [pow_mul, ← mul_pow, div_pow]
        congr 1
        ring

private theorem radius_arith {Q B RF R b b₀ κ u' rB H : ℝ} (hκ0 : 0 ≤ κ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hb0 : 0 ≤ b) (hb₀0 : 0 ≤ b₀) (hQκ : Q ≤ κ) (hRFκ : RF ≤ κ) (hratio : R ≤ u' ^ 2 + H ^ 2)
    (hb : b ≤ rB) (hb₀ : b₀ ≤ rB) (hβ : B ^ 2 ≤ 2 * (RF * (2 * R + 2 * b)) + 2 * Q ^ 2 * (2 * R + 2 * b₀)) :
    B ≤ (2 * κ + 2 * κ ^ 2) * (2 * u' ^ 2 + 2 * rB) + 1 + 2 * (2 * κ + 2 * κ ^ 2) * H ^ 2 := by
  set X : ℝ := 2 * u' ^ 2 + 2 * rB + 2 * H ^ 2 with hX
  have hin : 2 * R + 2 * b ≤ X := by rw [hX]; linarith
  have hin₀ : 2 * R + 2 * b₀ ≤ X := by rw [hX]; linarith
  have hnn : 0 ≤ 2 * R + 2 * b := by positivity
  have hnn₀ : 0 ≤ 2 * R + 2 * b₀ := by positivity
  have hQsq : Q ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hQ hQκ 2
  have h1 : RF * (2 * R + 2 * b) ≤ κ * X := mul_le_mul hRFκ hin hnn hκ0
  have h2 : Q ^ 2 * (2 * R + 2 * b₀) ≤ κ ^ 2 * X := mul_le_mul hQsq hin₀ hnn₀ (by positivity)
  have hβX : B ^ 2 ≤ (2 * κ + 2 * κ ^ 2) * X := by linarith [h1, h2, hβ]
  have hBle : B ≤ B ^ 2 + 1 := by nlinarith [sq_nonneg (B - 1 / 2)]
  have hexp : (2 * κ + 2 * κ ^ 2) * X
      = (2 * κ + 2 * κ ^ 2) * (2 * u' ^ 2 + 2 * rB) + 2 * (2 * κ + 2 * κ ^ 2) * H ^ 2 := by
    rw [hX]; ring
  linarith [hβX, hBle, hexp]

private theorem det_globalPoints (γ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)
      = Units.map (algebraMap K (𝔸)) (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Geometry

open NumberField.TateGlobal
open scoped Pointwise

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

private theorem det_unipotentGL2' (t : AdeleRing (𝓞 K) K) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 t) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

private theorem ideleNorm_one' : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  have h := ideleNorm_mul (F := K) 1 1
  rw [mul_one] at h
  exact mul_right_cancel₀ (ideleNorm_pos (F := K) 1).ne' (h.symm.trans (one_mul _).symm)

private theorem normDet_siegel (c' u' d₁' d₂' : ℝ) (hd₁' : 0 < d₁') {x : AdelicGL2 (𝓞 K) K}
    (hx : x ∈ centreCutSiegelSet K c' u' d₁' d₂') :
    ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈
      Set.Icc (d₁' ^ (∑ w : InfinitePlace K, w.mult)) (d₂' ^ (∑ w : InfinitePlace K, w.mult)) := by
  rw [mem_centreCutSiegelSet_iff] at hx
  obtain ⟨hfin, -, -, hdet⟩ := hx
  rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult K x hfin, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum]
  constructor
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg hd₁'.le _)
      fun w _ => pow_le_pow_left₀ hd₁'.le (hdet w).1 _
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w x).le _)
      fun w _ => pow_le_pow_left₀ (archDetNorm_pos w x).le (hdet w).2 _

private theorem detRange {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hd₁' : 0 < d₁') :
    ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂', ∀ y ∈ region K x C,
      ideleNorm K (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc a b := by
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, 1, one_pos, fun x _ y hy => ?_⟩
    rw [region, hCe, Set.image2_empty_right] at hy
    exact hy.elim
  obtain ⟨cmin, -, hmin⟩ := hC.exists_isMinOn hCne (continuous_ideleNorm_det K).continuousOn
  obtain ⟨cmax, -, hmax⟩ := hC.exists_isMaxOn hCne (continuous_ideleNorm_det K).continuousOn
  refine ⟨d₁' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det cmin),
    d₂' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det cmax),
    mul_pos (pow_pos hd₁' _) (ideleNorm_pos _), fun x hx y hy => ?_⟩
  rw [region] at hy
  obtain ⟨t, -, c, hc, rfl⟩ := hy
  have hxdet := normDet_siegel (K := K) c' u' d₁' d₂' hd₁' hx
  rw [normDet_mul, normDet_mul, det_unipotentGL2', ideleNorm_one', one_mul]
  constructor
  · exact mul_le_mul hxdet.1 (hmin hc) (ideleNorm_pos _).le (ideleNorm_pos _).le
  · exact mul_le_mul hxdet.2 (hmax hc) (ideleNorm_pos _).le
      ((pow_pos hd₁' _).le.trans (hxdet.1.trans hxdet.2))

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

private def PLinked (C : Set (AdelicGL2 (𝓞 K) K)) (x : AdelicGL2 (𝓞 K) K) (δ : GL (Fin 2) K) : Prop :=
  ∃ r ∈ region K x C, globalPoints (𝓞 K) K δ * r ∈ region K x C

private theorem PLinked.toLinked {C : Set (AdelicGL2 (𝓞 K) K)} {x : AdelicGL2 (𝓞 K) K} {δ : GL (Fin 2) K}
    (h : PLinked C x δ) : Linked K C x δ := by
  obtain ⟨r, ⟨b₀, hb₀, c₀, hc₀, rfl⟩, b, hb, c, hc, heq⟩ := h
  refine ⟨b, b₀, 1, c * c₀⁻¹, hb, hb₀, Set.mem_image2_of_mem hc hc₀, ?_⟩
  calc globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x)
      = globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x * c₀) * c₀⁻¹ := by group
    _ = unipotentGL2 b * x * c * c₀⁻¹ := by rw [← heq]
    _ = cen K 1 * (unipotentGL2 b * x) * (c * c₀⁻¹) := by rw [map_one, one_mul, mul_assoc]

private theorem PLinked.exists_det_eq {C : Set (AdelicGL2 (𝓞 K) K)} {x : AdelicGL2 (𝓞 K) K}
    {δ : GL (Fin 2) K} (h : PLinked C x δ) :
    ∃ M ∈ diffSet K C, Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K δ) = Matrix.GeneralLinearGroup.det M := by
  obtain ⟨r, ⟨b₀, -, c₀, hc₀, rfl⟩, b, -, c, hc, heq⟩ := h
  have h1 := congrArg (fun g : AdelicGL2 (𝓞 K) K => Matrix.GeneralLinearGroup.det g) heq
  simp only [map_mul, det_unipotentGL2', one_mul] at h1

  rw [mul_left_comm] at h1
  have h2 := mul_left_cancel h1
  refine ⟨c * c₀⁻¹, Set.mem_image2_of_mem hc hc₀, ?_⟩
  rw [map_mul, map_inv, h2, mul_inv_cancel_right]

private theorem encard_carriers_le (C : Set (AdelicGL2 (𝓞 K) K)) (x y : AdelicGL2 (𝓞 K) K) :
    ({γ : Γ K | y ∈ γ • region K x C} : Set (Γ K)).encard ≤
      ({δ : GL (Fin 2) K | PLinked C x δ} : Set (GL (Fin 2) K)).encard := by
  rcases ({γ : Γ K | y ∈ γ • region K x C} : Set (Γ K)).eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.encard_empty]
    exact zero_le
  obtain ⟨r₀, hr₀, hγ₀r₀⟩ := hγ₀
  beta_reduce at hγ₀r₀
  have hrep : ∀ γ : Γ K, ∃ δ : GL (Fin 2) K,
      globalPoints (𝓞 K) K δ = ((γ⁻¹ * γ₀ : Γ K) : AdelicGL2 (𝓞 K) K) :=
    fun γ => MonoidHom.mem_range.1 (γ⁻¹ * γ₀).2
  choose f hf using hrep
  refine Set.encard_le_encard_of_injOn (f := f) ?_ ?_
  · intro γ hγ
    obtain ⟨r, hr, hγr⟩ := hγ
    beta_reduce at hγr
    refine ⟨r₀, hr₀, ?_⟩
    rw [hf, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← Γ_smul, hγ₀r₀, ← hγr, Γ_smul, inv_mul_cancel_left]
    exact hr
  · intro γ _ γ' _ hγγ'
    have h := congrArg (globalPoints (𝓞 K) K) hγγ'
    rw [hf, hf] at h
    have h' : (γ⁻¹ * γ₀ : Γ K) = γ'⁻¹ * γ₀ := Subtype.ext h
    simpa using h'

private theorem count {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') :
    ∃ (T₁ : ℝ) (A : ℕ) (c₅ : ℝ), 0 ≤ c₅ ∧ ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
      T₁ < archHeight K (glArch (𝓞 K) K x) → ∀ y : AdelicGL2 (𝓞 K) K,
        ({γ : Γ K | y ∈ γ • region K x C} : Set (Γ K)).encard ≤
          ⌊c₅ * archHeight K (glArch (𝓞 K) K x) ^ A⌋₊ := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_forall_linked_upper K hC
  obtain ⟨κ, hκ0, hκ⟩ := exists_factor_bound K hC
  obtain ⟨rB, hrB0, hrB⟩ := exists_box_bound K
  obtain ⟨Aq, hAq, hAqmem⟩ := exists_isCompact_adeles K κ (isCompact_finConf K hC 0)
  have hQfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hAq
  obtain ⟨Qfin, hQfin_def⟩ : ∃ Q : Finset K, Q = hQfin.toFinset := ⟨_, rfl⟩
  obtain ⟨Mb, hMb⟩ :=
    NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact K (isCompact_finConf K hC 1)

  obtain ⟨D, hD⟩ : ∃ D : Set (AdeleRing (𝓞 K) K), D = ⋃ q ∈ Qfin, (fun M : AdelicGL2 (𝓞 K) K =>
    algebraMap K (AdeleRing (𝓞 K) K) q⁻¹ * (Matrix.GeneralLinearGroup.det M : AdeleRing (𝓞 K) K)) '' diffSet K C :=
    ⟨_, rfl⟩
  have hDc : IsCompact D := by
    rw [hD]
    refine Qfin.isCompact_biUnion fun q _ => (isCompact_diffSet K hC).image ?_
    exact continuous_const.mul (Units.continuous_val.comp (continuous_det K))
  have hF₂ := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hDc
  obtain ⟨S₂, hS₂⟩ : ∃ S : Finset K, S = hF₂.toFinset.biUnion fun t => (Polynomial.nthRoots 2 t).toFinset :=
    ⟨_, rfl⟩

  obtain ⟨cκ, hcκ⟩ : ∃ c : ℝ, c = 2 * κ + 2 * κ ^ 2 := ⟨_, rfl⟩
  have hcκ0 : 0 ≤ cκ := by rw [hcκ]; positivity
  obtain ⟨r₁, hr₁⟩ : ∃ r : ℝ, r = cκ * (2 * u' ^ 2 + 2 * rB) + 1 := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r : ℝ, r = 2 * cκ := ⟨_, rfl⟩
  have hr₁0 : 0 ≤ r₁ := by rw [hr₁]; positivity
  have hr₂0 : 0 ≤ r₂ := by rw [hr₂]; positivity
  obtain ⟨κ₀, A, hκ₀, hpoly⟩ := exists_prod_max_pow_le K hc' hr₁0 hr₂0
  refine ⟨max T₀ 1, A, (S₂.card : ℝ) * Qfin.card * (max Mb 0 * κ₀),
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (le_max_right _ _) hκ₀),
    fun x hxS hT y => ?_⟩
  obtain ⟨hxint, hxfloor, hxwin, -⟩ := mem_centreCutSiegelSet_iff.mp hxS
  have hT₀x : T₀ < archHeight K (glArch (𝓞 K) K x) := (le_max_left _ _).trans_lt hT
  have hH1 : 1 ≤ archHeight K (glArch (𝓞 K) K x) := ((le_max_right _ _).trans_lt hT).le
  have hupper := hT₀ x hxint hT₀x
  obtain ⟨s, hs_mem, hs_card⟩ := hMb 0 fun w => r₁ + r₂ * localHeight (ac K w x) ^ 2

  have hQs : ∀ (q β' : K) (hq : q ≠ 0), Linked K C x (upper K q β' hq) → q ∈ Qfin ∧ β' ∈ s := by
    intro q β' hq hl
    obtain ⟨hqfin, hβfin⟩ := linked_fin K hxint hq hl
    have harch : ∀ w : InfinitePlace K,
        ‖(q : w.Completion)‖ ≤ κ ∧ ‖(β' : w.Completion)‖ ≤ r₁ + r₂ * localHeight (ac K w x) ^ 2 := by
      intro w
      obtain ⟨M, hM, b, hb, b₀, hb₀, hqw, hβw⟩ := linked_arch K hq hl w
      obtain ⟨hMt, hMr⟩ := hκ M hM w
      have hratio : ratio (ac K w x) ≤ u' ^ 2 + localHeight (ac K w x) ^ 2 := by
        rw [ratio_eq]
        exact add_le_add (hxwin w) le_rfl
      refine ⟨hqw.trans hMt, ?_⟩
      rw [hr₁, hr₂, hcκ]
      exact radius_arith hκ0 (norm_nonneg _) (ratio_nonneg _) (by positivity) (by positivity)
        (hqw.trans hMt) hMr hratio (hrB b hb w) (hrB b₀ hb₀ w) hβw
    constructor
    · rw [hQfin_def, Set.Finite.mem_toFinset]
      exact hAqmem _ (fun w => (harch w).1) hqfin
    · refine hs_mem β' ?_ fun w => ?_
      · rw [sub_zero]
        exact hβfin
      · rw [sub_zero]
        exact (harch w).2

  have hcoords : ∀ δ : GL (Fin 2) K, PLinked C x δ →
      (δ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ S₂ ∧
        (δ : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ Qfin ∧
        (δ : Matrix (Fin 2) (Fin 2) K) 0 1 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ s := by
    intro δ hδ
    have hL := hδ.toLinked
    have h10 := hupper δ hL
    obtain ⟨hq0, hd0⟩ := diag_ne_zero K h10
    have hL' := hL
    rw [eq_scalar_mul_upper K h10] at hL'
    obtain ⟨hqQ, hβs⟩ := hQs _ _ _ (linked_of_scalar_mul K _ hL')
    refine ⟨?_, hqQ, hβs⟩

    obtain ⟨M, hM, hdet⟩ := hδ.exists_det_eq
    have hval : algebraMap K (AdeleRing (𝓞 K) K) ((δ : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2) =
        algebraMap K (AdeleRing (𝓞 K) K)
            ((δ : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹ *
          (Matrix.GeneralLinearGroup.det M : AdeleRing (𝓞 K) K) := by
      have hdetδ : (Matrix.GeneralLinearGroup.det M : AdeleRing (𝓞 K) K) =
          algebraMap K (AdeleRing (𝓞 K) K)
            ((δ : Matrix (Fin 2) (Fin 2) K) 0 0 * (δ : Matrix (Fin 2) (Fin 2) K) 1 1) := by
        rw [← hdet, det_globalPoints, Units.coe_map, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply,
          Matrix.det_fin_two, h10, mul_zero, sub_zero]
      rw [hdetδ, ← map_mul]
      congr 1
      field_simp
    have hmemD : algebraMap K (AdeleRing (𝓞 K) K) ((δ : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2) ∈ D := by
      rw [hD, hval]
      exact Set.mem_biUnion hqQ ⟨M, hM, rfl⟩
    rw [hS₂, Finset.mem_biUnion]
    exact ⟨_, hF₂.mem_toFinset.2 hmemD, Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots two_pos).2 rfl)⟩

  obtain ⟨g, hg⟩ : ∃ g : K × K × K → GL (Fin 2) K, g = fun p =>
      if h : p.1 ≠ 0 ∧ p.2.1 ≠ 0 then
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 p.1 h.1) * upper K p.2.1 p.2.2 h.2
      else 1 :=
    ⟨_, rfl⟩
  have hsub : {δ : GL (Fin 2) K | PLinked C x δ} ⊆
      g '' ((S₂ ×ˢ Qfin ×ˢ s : Finset (K × K × K)) : Set (K × K × K)) := by
    intro δ hδ
    have h10 := hupper δ hδ.toLinked
    obtain ⟨hq0, hd0⟩ := diag_ne_zero K h10
    obtain ⟨h₁, h₂, h₃⟩ := hcoords δ hδ
    refine ⟨((δ : Matrix (Fin 2) (Fin 2) K) 1 1,
      (δ : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1,
      (δ : Matrix (Fin 2) (Fin 2) K) 0 1 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1), ?_, ?_⟩
    · exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨h₁, Finset.mem_product.2 ⟨h₂, h₃⟩⟩)
    · rw [hg]
      dsimp only
      rw [dif_pos ⟨hd0, div_ne_zero hq0 hd0⟩]
      exact (eq_scalar_mul_upper K h10).symm

  have hs_le : (s.card : ℝ) ≤ max Mb 0 * (κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A) := by
    refine hs_card.trans ?_
    have hprod := hpoly x (fun w => hxfloor w) hH1
    have hprod0 : 0 ≤ ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult :=
      Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
    calc Mb * ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult
        ≤ max Mb 0 * ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hprod0
      _ ≤ max Mb 0 * (κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A) :=
          mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
  have hreal : (((S₂ ×ˢ Qfin ×ˢ s : Finset (K × K × K)).card : ℕ) : ℝ) ≤
      (S₂.card : ℝ) * Qfin.card * (max Mb 0 * κ₀) * archHeight K (glArch (𝓞 K) K x) ^ A := by
    rw [Finset.card_product, Finset.card_product]
    push_cast
    calc (S₂.card : ℝ) * ((Qfin.card : ℝ) * s.card)
        ≤ (S₂.card : ℝ) * ((Qfin.card : ℝ) * (max Mb 0 * (κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A))) := by
          gcongr
      _ = (S₂.card : ℝ) * Qfin.card * (max Mb 0 * κ₀) * archHeight K (glArch (𝓞 K) K x) ^ A := by ring
  calc ({γ : Γ K | y ∈ γ • region K x C} : Set (Γ K)).encard
      ≤ ({δ : GL (Fin 2) K | PLinked C x δ} : Set (GL (Fin 2) K)).encard := encard_carriers_le C x y
    _ ≤ (g '' ((S₂ ×ˢ Qfin ×ˢ s : Finset (K × K × K)) : Set (K × K × K))).encard := Set.encard_le_encard hsub
    _ ≤ (((S₂ ×ˢ Qfin ×ˢ s : Finset (K × K × K)) : Set (K × K × K))).encard := Set.encard_image_le _ _
    _ = ((S₂ ×ˢ Qfin ×ˢ s : Finset (K × K × K)).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (⌊(S₂.card : ℝ) * Qfin.card * (max Mb 0 * κ₀) * archHeight K (glArch (𝓞 K) K x) ^ A⌋₊ : ℕ∞) := by
        exact_mod_cast Nat.le_floor hreal

end MovingRegionSquareMass
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain.MovingRegionSquareMass"

open NumberField.TateGlobal
open scoped Pointwise

open MovingRegionSquareMass in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁')
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ (T₁ : ℝ) (A : ℕ) (M : ℝ), ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
          T₁ < archHeight K (glArch (𝓞 K) K x) →
            ∫⁻ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
              unipotentGL2 t * x * c) (closure (adelicBox K)) C,
                (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
              ≤ ENNReal.ofReal (M * archHeight K (glArch (𝓞 K) K x) ^ A) *
                ∫⁻ y in Φ₀, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨a, b, ha, hab⟩ := detRange (K := K) hC c' u' d₁' d₂' hd₁'
  obtain ⟨Zs, hZs⟩ := shifts (K := K) a b α β ha hβ hαβ
  obtain ⟨T₁, A, c₅, hc₅, hcount⟩ := count (K := K) hC c' u' d₁' d₂' hc'

  set w : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun z => (‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖⁻¹) ^ 2 with hw
  have hw_nonneg : ∀ z, 0 ≤ w z := fun z => sq_nonneg _
  refine ⟨max T₁ 0, A, (∑ z ∈ Zs, w z) * c₅, fun φ hφ hφc x hx hT => ?_⟩
  have hT₁ : T₁ < archHeight K (glArch (𝓞 K) K x) := (le_max_left _ _).trans_lt hT
  have hH : 0 ≤ archHeight K (glArch (𝓞 K) K x) := ((le_max_right _ _).trans_lt hT).le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊c₅ * archHeight K (glArch (𝓞 K) K x) ^ A⌋₊ := ⟨_, rfl⟩
  have hφΓ : ∀ (γ : Γ K) (y : AdelicGL2 (𝓞 K) K), φ (γ • y) = φ y := by
    intro γ y
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hφ.left_invariant]

  set piece : (AdeleRing (𝓞 K) K)ˣ → Set (AdelicGL2 (𝓞 K) K) := fun z =>
    region K x C ∩ {y | ideleNorm K z ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc α β} with hpiece
  have hpiece_meas : ∀ z, MeasurableSet (piece z) := fun z =>
    (REGION K x hC).2.inter
      (measurableSet_Icc.preimage ((continuous_ideleNorm_det K).const_mul _).measurable)
  have hcover : region K x C ⊆ ⋃ z : Zs, piece z := by
    intro y hy
    obtain ⟨z, hz, hzr⟩ := hZs _ (hab x hx y hy)
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
    rw [hn]
    refine (Set.encard_le_encard ?_).trans (hcount x hx hT₁ ((centralScalar (𝓞 K) K z)⁻¹ * y))
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

  have hn_le : (n : ℝ≥0∞) ≤ ENNReal.ofReal (c₅ * archHeight K (glArch (𝓞 K) K x) ^ A) := by
    rw [hn, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Nat.floor_le (mul_nonneg hc₅ (pow_nonneg hH A)))

  show ∫⁻ y in region K x C, sq K φ y ∂(μ K) ≤
    ENNReal.ofReal ((∑ z ∈ Zs, w z) * c₅ * archHeight K (glArch (𝓞 K) K x) ^ A) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)
  calc ∫⁻ y in region K x C, sq K φ y ∂(μ K)
      ≤ ∫⁻ y in ⋃ z : Zs, piece z, sq K φ y ∂(μ K) := lintegral_mono_set hcover
    _ ≤ ∑' z : Zs, ∫⁻ y in piece z, sq K φ y ∂(μ K) := lintegral_iUnion_le _ _
    _ = ∑ z : Zs, ∫⁻ y in piece z, sq K φ y ∂(μ K) := tsum_fintype _
    _ ≤ ∑ z : Zs, ENNReal.ofReal (w z) * ((n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)) :=
        Finset.sum_le_sum fun z _ => hpiece_bound z
    _ = (∑ z : Zs, ENNReal.ofReal (w z)) * (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
        rw [← Finset.sum_mul, mul_assoc]
    _ ≤ (∑ z : Zs, ENNReal.ofReal (w z)) * ENNReal.ofReal (c₅ * archHeight K (glArch (𝓞 K) K x) ^ A) *
          ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
        gcongr
    _ = ENNReal.ofReal ((∑ z ∈ Zs, w z) * c₅ * archHeight K (glArch (𝓞 K) K x) ^ A) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
        rw [← Finset.sum_coe_sort Zs w, mul_assoc (∑ z : Zs, w z),
          ENNReal.ofReal_mul (Finset.sum_nonneg fun (z : Zs) _ => hw_nonneg z),
          ENNReal.ofReal_sum_of_nonneg fun (z : Zs) _ => hw_nonneg z]

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain.MovingRegionSquareMass"

end S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain (solution)
