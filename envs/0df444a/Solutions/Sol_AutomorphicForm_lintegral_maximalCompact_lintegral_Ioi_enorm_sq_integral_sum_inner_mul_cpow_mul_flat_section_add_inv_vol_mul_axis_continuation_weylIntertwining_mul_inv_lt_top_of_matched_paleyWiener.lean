-- Prove2me | solution 1 for AutomorphicForm.lintegral_maximalCompact_lintegral_Ioi_enorm_sq_integral_sum_inner_mul_cpow_mul_flat_section_add_inv_vol_mul_axis_continuation_weylIntertwining_mul_inv_lt_top_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/eeb5d87e-948d-56a7-bcdb-3999a8412110

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

import Theorems.Thm_AutomorphicForm_continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_weylIntertwiningIntegral_le_mul_pow_of_flat
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Theorems.Thm_MellinParseval_integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_maximalCompact_lintegral_Ioi_enorm_sq_integral_sum_inner_mul_cpow_mul_flat_section_add_inv_vol_mul_axis_continuation_weylIntertwining_mul_inv_lt_top_of_matched_paleyWiener
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

namespace CuspPacket

theorem enorm_sq_eq_ofReal_norm_sq {E : Type*} [NormedAddCommGroup E] (z : E) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem lintegral_Ioi_enorm_sq_lineIntegral_zero (a : ℝ → ℂ) (ha : Integrable a) (ha2 : MemLp a 2) :
    ∫⁻ y in Set.Ioi (0 : ℝ), ‖∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t‖ₑ ^ 2 * ENNReal.ofReal y⁻¹
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ t, ‖a t‖ₑ ^ 2 := by
  obtain ⟨hint, heq⟩ :=
    MellinParseval.integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two
      0 a ha ha2
  have hexp : ∀ (y t : ℝ), (y : ℂ) ^ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = (y : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro y t; rw [Complex.ofReal_zero, zero_add]
  simp_rw [hexp] at hint heq
  have hw : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (-(2 * (0 : ℝ))) / y = y⁻¹ := by
    intro y _; rw [mul_zero, neg_zero, Real.rpow_zero, one_div]

  have hint' : IntegrableOn (fun y : ℝ => y⁻¹ * ‖∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t‖ ^ 2)
      (Set.Ioi 0) := hint.congr_fun (fun y hy => by beta_reduce; rw [hw y hy]) measurableSet_Ioi
  have heq' : ∫ y in Set.Ioi (0 : ℝ), y⁻¹ * ‖∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t‖ ^ 2
      = 2 * Real.pi * ∫ t : ℝ, ‖a t‖ ^ 2 := by
    rw [← heq]; exact (setIntegral_congr_fun measurableSet_Ioi (fun y hy => by beta_reduce; rw [hw y hy])).symm

  have h1 : ∫⁻ y in Set.Ioi (0 : ℝ), ‖∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t‖ₑ ^ 2 * ENNReal.ofReal y⁻¹
      = ∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal (y⁻¹ * ‖∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t‖ ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [enorm_sq_eq_ofReal_norm_sq, mul_comm, ← ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hy))]
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun y : ℝ => y⁻¹ * ‖∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t‖ ^ 2) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall
      (fun y hy => mul_nonneg (inv_nonneg.mpr (le_of_lt hy)) (sq_nonneg _)))
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint' hnn, heq', ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h2 : Integrable (fun t : ℝ => ‖a t‖ ^ 2) := (memLp_two_iff_integrable_sq_norm ha2.1).mp ha2
  rw [ofReal_integral_eq_lintegral_ofReal h2 (Filter.Eventually.of_forall (fun t => by positivity))]
  exact lintegral_congr (fun t => (enorm_sq_eq_ofReal_norm_sq (a t)).symm)

theorem norm_sum_sq_le {n : ℕ} (v : Fin n → ℂ) : ‖∑ j, v j‖ ^ 2 ≤ n * ∑ j, ‖v j‖ ^ 2 := by
  calc ‖∑ j, v j‖ ^ 2 ≤ (∑ j, ‖v j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Finset.univ.card : ℝ) * ∑ j, ‖v j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = n * ∑ j, ‖v j‖ ^ 2 := by rw [Finset.card_univ, Fintype.card_fin]

theorem enorm_sum_sq_le {n : ℕ} (v : Fin n → ℂ) :
    ‖∑ j, v j‖ₑ ^ 2 ≤ ∑ j, (n : ℝ≥0∞) * ‖v j‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal_norm_sq]
  calc ENNReal.ofReal (‖∑ j, v j‖ ^ 2) ≤ ENNReal.ofReal (n * ∑ j, ‖v j‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (norm_sum_sq_le v)
    _ = ∑ j, (n : ℝ≥0∞) * ‖v j‖ₑ ^ 2 := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, enorm_sq_eq_ofReal_norm_sq]

theorem lintegral_lintegral_Ioi_enorm_sq_integral_sum_mul_cpow_mul_lt_top
    {X : Type*} [MeasurableSpace X] (κ : Measure X)
    {n : ℕ} (u : Fin n → X → ℂ) (hu : ∀ j, Measurable (u j)) (hu2 : ∀ j, ∫⁻ x, ‖u j x‖ₑ ^ 2 ∂κ < ∞)
    (c : Fin n → ℝ → ℂ) (hc : ∀ j, Integrable (c j)) (hc2 : ∀ j, MemLp (c j) 2) (θ : ℝ) :
    ∫⁻ x, ∫⁻ y in Set.Ioi (0 : ℝ),
        ‖∫ t : ℝ, ∑ j, c j t * ((y : ℂ) ^ (((t + θ : ℝ) : ℂ) * Complex.I) * u j x)‖ₑ ^ 2
          * ENNReal.ofReal y⁻¹ ∂volume ∂κ < ∞ := by

  set a : X → ℝ → ℂ := fun x s => ∑ j, u j x * c j (s - θ) with ha_def
  have ha1 : ∀ x, Integrable (a x) := fun x =>
    integrable_finset_sum _ (fun j _ => ((hc j).comp_sub_right θ).const_mul (u j x))
  have ha2 : ∀ x, MemLp (a x) 2 := fun x =>
    memLp_finset_sum _ (fun j _ =>
      ((hc2 j).comp_measurePreserving (measurePreserving_sub_right volume θ)).const_mul (u j x))
  have hinner : ∀ (x : X) (y : ℝ),
      (∫ t : ℝ, ∑ j, c j t * ((y : ℂ) ^ (((t + θ : ℝ) : ℂ) * Complex.I) * u j x))
        = ∫ s : ℝ, (y : ℂ) ^ ((s : ℂ) * Complex.I) * a x s := by
    intro x y
    have hf : (fun t : ℝ => ∑ j, c j t * ((y : ℂ) ^ (((t + θ : ℝ) : ℂ) * Complex.I) * u j x))
        = fun t => (fun s : ℝ => (y : ℂ) ^ ((s : ℂ) * Complex.I) * a x s) (t + θ) := by
      funext t
      simp only [ha_def, add_sub_cancel_right, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast
      ring
    rw [hf, integral_add_right_eq_self (fun s : ℝ => (y : ℂ) ^ ((s : ℂ) * Complex.I) * a x s) θ]
  simp_rw [hinner]

  have hx : ∀ x, ∫⁻ y in Set.Ioi (0 : ℝ), ‖∫ s : ℝ, (y : ℂ) ^ ((s : ℂ) * Complex.I) * a x s‖ₑ ^ 2
      * ENNReal.ofReal y⁻¹ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ s, ‖a x s‖ₑ ^ 2 :=
    fun x => lintegral_Ioi_enorm_sq_lineIntegral_zero (a x) (ha1 x) (ha2 x)
  simp_rw [hx]

  set C : Fin n → ℝ≥0∞ := fun j => ∫⁻ s, ‖c j s‖ₑ ^ 2 with hC_def
  have hCfin : ∀ j, C j < ∞ := fun j => by
    have h2 : Integrable (fun t : ℝ => ‖c j t‖ ^ 2) := (memLp_two_iff_integrable_sq_norm (hc2 j).1).mp (hc2 j)
    have := h2.lintegral_lt_top
    simp only [hC_def]
    calc ∫⁻ s, ‖c j s‖ₑ ^ 2 = ∫⁻ s, ENNReal.ofReal (‖c j s‖ ^ 2) :=
          lintegral_congr (fun s => enorm_sq_eq_ofReal_norm_sq _)
      _ < ∞ := this
  have hbound : ∀ x, ∫⁻ s, ‖a x s‖ₑ ^ 2 ≤ ∑ j, (n : ℝ≥0∞) * ‖u j x‖ₑ ^ 2 * C j := by
    intro x
    calc ∫⁻ s, ‖a x s‖ₑ ^ 2 ≤ ∫⁻ s, ∑ j, (n : ℝ≥0∞) * (‖u j x‖ₑ ^ 2 * ‖c j (s - θ)‖ₑ ^ 2) := by
          refine lintegral_mono (fun s => ?_)
          have := enorm_sum_sq_le (fun j => u j x * c j (s - θ))
          simp only [ha_def]
          refine this.trans (le_of_eq ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [enorm_mul, mul_pow]
      _ = ∑ j, (n : ℝ≥0∞) * ‖u j x‖ₑ ^ 2 * ∫⁻ s, ‖c j (s - θ)‖ₑ ^ 2 := by
          rw [lintegral_finset_sum' _ (fun j _ =>
            ((((hc j).comp_sub_right θ).aestronglyMeasurable.aemeasurable.enorm.pow_const 2).const_mul
              (‖u j x‖ₑ ^ 2)).const_mul (n : ℝ≥0∞))]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hne : (n : ℝ≥0∞) * ‖u j x‖ₑ ^ 2 ≠ ∞ :=
            ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (ENNReal.pow_ne_top enorm_ne_top)
          rw [← lintegral_const_mul' _ _ hne]
          exact lintegral_congr (fun s => by rw [mul_assoc])
      _ = ∑ j, (n : ℝ≥0∞) * ‖u j x‖ₑ ^ 2 * C j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [lintegral_sub_right_eq_self (fun s => ‖c j s‖ₑ ^ 2) θ]

  calc ∫⁻ x, ENNReal.ofReal (2 * Real.pi) * (∫⁻ s, ‖a x s‖ₑ ^ 2) ∂κ
      ≤ ∫⁻ x, ENNReal.ofReal (2 * Real.pi) * (∑ j, (n : ℝ≥0∞) * ‖u j x‖ₑ ^ 2 * C j) ∂κ :=
        lintegral_mono (fun x => mul_le_mul_right (hbound x) _)
    _ = ENNReal.ofReal (2 * Real.pi) * ∑ j, ((n : ℝ≥0∞) * C j * ∫⁻ x, ‖u j x‖ₑ ^ 2 ∂κ) := by
        have hmeas : ∀ j, Measurable (fun x => (n : ℝ≥0∞) * ‖u j x‖ₑ ^ 2 * C j) := fun j =>
          (((hu j).enorm.pow_const 2).const_mul _).mul_const _
        rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun j _ => hmeas j)),
          lintegral_finsetSum _ (fun j _ => hmeas j)]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hne : (n : ℝ≥0∞) * C j ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (hCfin j).ne
        rw [← lintegral_const_mul' _ _ hne]
        exact lintegral_congr (fun x => by rw [mul_right_comm])
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) (hCfin j)) (hu2 j)

theorem lintegral_lintegral_Ioi_enorm_sq_integral_sum_mul_cpow_neg_mul_lt_top
    {X : Type*} [MeasurableSpace X] (κ : Measure X) [SFinite κ]
    {n : ℕ} (v : Fin n → ℝ → X → ℂ) (hv : ∀ j, Measurable (Function.uncurry (v j)))
    (hv2 : ∀ j t, ∫⁻ x, ‖v j t x‖ₑ ^ 2 ∂κ ≤ 1)
    (A : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv) (hvb : ∀ j t x, ‖v j t x‖ ≤ Cv * (1 + |t|) ^ A)
    (c : Fin n → ℝ → ℂ) (hcm : ∀ j, AEStronglyMeasurable (c j))
    (hc1 : ∀ j, Integrable (fun t : ℝ => (1 + |t|) ^ A * ‖c j t‖))
    (hc2 : ∀ j, Integrable (fun t : ℝ => ((1 + |t|) ^ A * ‖c j t‖) ^ 2)) (θ : ℝ) :
    ∫⁻ x, ∫⁻ y in Set.Ioi (0 : ℝ),
        ‖∫ t : ℝ, ∑ j, c j t * ((y : ℂ) ^ (-(((t + θ : ℝ) : ℂ) * Complex.I)) * v j (t + θ) x)‖ₑ ^ 2
          * ENNReal.ofReal y⁻¹ ∂volume ∂κ < ∞ := by
  have hθw : ∀ s : ℝ, (1 + |s|) ≤ (1 + |θ|) * (1 + |s - θ|) := by
    intro s
    have : |s| ≤ |θ| + |s - θ| := by
      calc |s| = |θ + (s - θ)| := by ring_nf
        _ ≤ |θ| + |s - θ| := abs_add_le _ _
    nlinarith [abs_nonneg θ, abs_nonneg (s - θ)]

  set b : X → ℝ → ℂ := fun x u => ∑ j, c j (-u - θ) * v j (-u) x with hb_def
  set w : ℝ → ℝ := fun t => (1 + |t|) ^ A with hw_def
  have hw1 : ∀ t, 1 ≤ w t := fun t => one_le_pow₀ (by simp [abs_nonneg])
  have hw0 : ∀ t, 0 ≤ w t := fun t => (zero_le_one.trans (hw1 t))
  have hwθ : ∀ u : ℝ, w (-u) ≤ (1 + |θ|) ^ A * w (-u - θ) := by
    intro u
    simp only [hw_def, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by simpa using hθw (-u)) A

  have hmp : MeasurePreserving (fun u : ℝ => -u - θ) volume volume :=
    (measurePreserving_sub_right volume θ).comp (Measure.measurePreserving_neg volume)

  have hvmeas : ∀ j x, Measurable (fun u : ℝ => v j (-u) x) := fun j x =>
    (hv j).comp ((measurable_neg).prodMk measurable_const)
  have hcmeas : ∀ j, AEStronglyMeasurable (fun u : ℝ => c j (-u - θ)) := fun j =>
    (hcm j).comp_measurePreserving hmp
  have hbmeas : ∀ x, AEStronglyMeasurable (b x) := fun x => by
    have : b x = fun u => ∑ j, c j (-u - θ) * v j (-u) x := rfl
    rw [this]
    exact Finset.aestronglyMeasurable_fun_sum _ (fun j _ =>
      (hcmeas j).mul (hvmeas j x).aestronglyMeasurable)

  have hG1 : ∀ j, Integrable (fun u : ℝ => w (-u - θ) * ‖c j (-u - θ)‖) := fun j =>
    (hmp.integrable_comp (hc1 j).aestronglyMeasurable).mpr (hc1 j)
  have hG2 : ∀ j, Integrable (fun u : ℝ => (w (-u - θ) * ‖c j (-u - θ)‖) ^ 2) := fun j =>
    (hmp.integrable_comp (hc2 j).aestronglyMeasurable).mpr (hc2 j)

  have hb_le : ∀ x u, ‖b x u‖ ≤ ∑ j, Cv * (1 + |θ|) ^ A * (w (-u - θ) * ‖c j (-u - θ)‖) := by
    intro x u
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [norm_mul]
    calc ‖c j (-u - θ)‖ * ‖v j (-u) x‖ ≤ ‖c j (-u - θ)‖ * (Cv * w (-u)) :=
          mul_le_mul_of_nonneg_left (hvb j (-u) x) (norm_nonneg _)
      _ ≤ ‖c j (-u - θ)‖ * (Cv * ((1 + |θ|) ^ A * w (-u - θ))) := by
          gcongr
          exact hwθ u
      _ = Cv * (1 + |θ|) ^ A * (w (-u - θ) * ‖c j (-u - θ)‖) := by ring
  have hb1 : ∀ x, Integrable (b x) := fun x =>
    Integrable.mono' (integrable_finset_sum _ (fun j _ => (hG1 j).const_mul (Cv * (1 + |θ|) ^ A)))
      (hbmeas x) (Filter.Eventually.of_forall (hb_le x))
  have hb_sq_le : ∀ x u, ‖b x u‖ ^ 2 ≤
      ∑ j, (n * (Cv * (1 + |θ|) ^ A) ^ 2) * (w (-u - θ) * ‖c j (-u - θ)‖) ^ 2 := by
    intro x u
    calc ‖b x u‖ ^ 2 ≤ (∑ j, Cv * (1 + |θ|) ^ A * (w (-u - θ) * ‖c j (-u - θ)‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb_le x u) 2
      _ ≤ (Finset.univ.card : ℝ) * ∑ j, (Cv * (1 + |θ|) ^ A * (w (-u - θ) * ‖c j (-u - θ)‖)) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = ∑ j, (n * (Cv * (1 + |θ|) ^ A) ^ 2) * (w (-u - θ) * ‖c j (-u - θ)‖) ^ 2 := by
          rw [Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => by ring)
  have hb2 : ∀ x, MemLp (b x) 2 := fun x =>
    (memLp_two_iff_integrable_sq_norm (hbmeas x)).mpr
      (Integrable.mono'
        (integrable_finsetSum _ (fun j _ => (hG2 j).const_mul (n * (Cv * (1 + |θ|) ^ A) ^ 2)))
        ((continuous_pow 2).comp_aestronglyMeasurable (hbmeas x).norm)
        (Filter.Eventually.of_forall (fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb_sq_le x u)))

  have hinner : ∀ (x : X) (y : ℝ),
      (∫ t : ℝ, ∑ j, c j t * ((y : ℂ) ^ (-(((t + θ : ℝ) : ℂ) * Complex.I)) * v j (t + θ) x))
        = ∫ u : ℝ, (y : ℂ) ^ ((u : ℂ) * Complex.I) * b x u := by
    intro x y
    have hf : (fun t : ℝ => ∑ j, c j t * ((y : ℂ) ^ (-(((t + θ : ℝ) : ℂ) * Complex.I)) * v j (t + θ) x))
        = fun t => (fun s : ℝ => (fun u : ℝ => (y : ℂ) ^ ((u : ℂ) * Complex.I) * b x u) (-s)) (t + θ) := by
      funext t
      simp only [hb_def, neg_neg, add_sub_cancel_right, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast
      ring
    rw [hf, integral_add_right_eq_self (fun s : ℝ => (fun u : ℝ => (y : ℂ) ^ ((u : ℂ) * Complex.I) * b x u) (-s)) θ]
    exact integral_neg_eq_self (fun u : ℝ => (y : ℂ) ^ ((u : ℂ) * Complex.I) * b x u) volume
  simp_rw [hinner]
  have hx : ∀ x, ∫⁻ y in Set.Ioi (0 : ℝ), ‖∫ u : ℝ, (y : ℂ) ^ ((u : ℂ) * Complex.I) * b x u‖ₑ ^ 2
      * ENNReal.ofReal y⁻¹ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, ‖b x u‖ₑ ^ 2 :=
    fun x => lintegral_Ioi_enorm_sq_lineIntegral_zero (b x) (hb1 x) (hb2 x)
  simp_rw [hx]

  have hF : ∀ j, AEMeasurable (fun p : X × ℝ => ‖c j (-p.2 - θ)‖ₑ ^ 2 * ‖v j (-p.2) p.1‖ₑ ^ 2)
      (κ.prod volume) := fun j => by
    refine AEMeasurable.fun_mul ?_ ?_
    · exact ((hcmeas j).aemeasurable.enorm.pow_const 2).comp_snd
    · exact (((hv j).comp (measurable_snd.neg.prodMk measurable_fst)).enorm.pow_const 2).aemeasurable
  have hvx : ∀ j u, Measurable (fun x : X => ‖v j (-u) x‖ₑ ^ 2) := fun j u =>
    ((hv j).comp (measurable_const.prodMk measurable_id)).enorm.pow_const 2
  have h2π : ENNReal.ofReal (2 * Real.pi) ≠ ∞ := ENNReal.ofReal_ne_top
  have hfin : ∀ j, ∫⁻ u : ℝ, ‖c j u‖ₑ ^ 2 < ∞ := fun j => by
    refine lt_of_le_of_lt (lintegral_mono (fun u => ?_)) (hc2 j).lintegral_lt_top
    rw [enorm_sq_eq_ofReal_norm_sq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (hw1 u))
  calc ∫⁻ x, ENNReal.ofReal (2 * Real.pi) * (∫⁻ u, ‖b x u‖ₑ ^ 2) ∂κ
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x, (∫⁻ u, ‖b x u‖ₑ ^ 2) ∂κ :=
        lintegral_const_mul' _ _ h2π
    _ ≤ ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ x, (∫⁻ u, ∑ j, (n : ℝ≥0∞) * (‖c j (-u - θ)‖ₑ ^ 2 * ‖v j (-u) x‖ₑ ^ 2)) ∂κ := by
        refine mul_le_mul_right (lintegral_mono (fun x => lintegral_mono (fun u => ?_))) _
        have := enorm_sum_sq_le (fun j => c j (-u - θ) * v j (-u) x)
        refine (le_of_eq (by simp only [hb_def])).trans (this.trans (le_of_eq ?_))
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [enorm_mul, mul_pow]
    _ = ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ u, (∫⁻ x, ∑ j, (n : ℝ≥0∞) * (‖c j (-u - θ)‖ₑ ^ 2 * ‖v j (-u) x‖ₑ ^ 2) ∂κ) := by
        rw [lintegral_lintegral_swap]
        change AEMeasurable (fun p : X × ℝ => ∑ j, (n : ℝ≥0∞) * (‖c j (-p.2 - θ)‖ₑ ^ 2 * ‖v j (-p.2) p.1‖ₑ ^ 2))
          (κ.prod volume)
        exact Finset.aemeasurable_fun_sum _ (fun j _ => (hF j).const_mul _)
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, ∑ j, (n : ℝ≥0∞) * ‖c j (-u - θ)‖ₑ ^ 2 := by
        refine mul_le_mul_right (lintegral_mono (fun u => ?_)) _
        rw [lintegral_finsetSum _ (fun j _ => ((hvx j u).const_mul _).const_mul _)]
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hne : (n : ℝ≥0∞) * ‖c j (-u - θ)‖ₑ ^ 2 ≠ ∞ :=
          ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (ENNReal.pow_ne_top enorm_ne_top)
        calc ∫⁻ x, (n : ℝ≥0∞) * (‖c j (-u - θ)‖ₑ ^ 2 * ‖v j (-u) x‖ₑ ^ 2) ∂κ
            = (n : ℝ≥0∞) * ‖c j (-u - θ)‖ₑ ^ 2 * ∫⁻ x, ‖v j (-u) x‖ₑ ^ 2 ∂κ := by
              rw [← lintegral_const_mul' _ _ hne]
              exact lintegral_congr (fun x => by rw [mul_assoc])
          _ ≤ (n : ℝ≥0∞) * ‖c j (-u - θ)‖ₑ ^ 2 * 1 := mul_le_mul_right (hv2 j (-u)) _
          _ = (n : ℝ≥0∞) * ‖c j (-u - θ)‖ₑ ^ 2 := mul_one _
    _ = ENNReal.ofReal (2 * Real.pi) * ∑ j, (n : ℝ≥0∞) * ∫⁻ u : ℝ, ‖c j u‖ₑ ^ 2 := by
        rw [lintegral_finsetSum' _ (fun j _ => ((hcmeas j).aemeasurable.enorm.pow_const 2).const_mul _)]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
        congr 1
        have h1 : (fun u : ℝ => ‖c j (-u - θ)‖ₑ ^ 2) = fun u => (fun s : ℝ => ‖c j (-s)‖ₑ ^ 2) (u + θ) := by
          funext u; simp only [neg_add]; ring_nf
        rw [h1, lintegral_add_right_eq_self (fun s : ℝ => ‖c j (-s)‖ₑ ^ 2) θ]
        exact lintegral_neg_eq_self (fun s : ℝ => ‖c j s‖ₑ ^ 2)
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) (hfin j)

end CuspPacket

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    ∀ (i : ιP),
      (∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ),
          ‖∫ t : ℝ, ∑ j : Fin (nE (em i)),
              (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
                (((y : ℝ) : ℂ) ^ ((((t + τ i : ℝ) : ℂ)) * Complex.I) * φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))‖ₑ ^ 2 *
            ENNReal.ofReal y⁻¹ ∂volume ∂(maximalCompactHaar K) < ⊤) ∧
      (∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ),
          ‖∫ t : ℝ, ∑ j : Fin (nE (em i)),
              (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
                (((y : ℝ) : ℂ) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I)) * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)))‖ₑ ^ 2 *
            ENNReal.ofReal y⁻¹ ∂volume ∂(maximalCompactHaar K) < ⊤) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _i1 μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _i2 μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty i

  set c : Fin (nE (em i)) → ℝ → ℂ := fun j t =>
    (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) with hc_def
  have hCIJ : ∀ j, Continuous (c j) ∧ Integrable (c j) ∧ MemLp (c j) 2 := fun j =>
    AutomorphicForm.continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty i j

  have hφcont : ∀ j, Continuous (fun k : adelicMaximalCompact K => φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) := fun j =>
    (_hφEjc (em i) j).comp (continuous_const.prodMk continuous_subtype_val)
  have hu : ∀ j, Measurable (fun k : adelicMaximalCompact K => φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) := fun j =>
    (hφcont j).measurable
  have hφbdd : ∀ j, ∃ B : ℝ, ∀ k : adelicMaximalCompact K, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ≤ B := fun j => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn ((hφcont j).continuousOn)
    exact ⟨B, fun k => hB k (Set.mem_univ k)⟩
  have hu2 : ∀ j, ∫⁻ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ₑ ^ 2 ∂(maximalCompactHaar K) < ∞ := fun j => by
    obtain ⟨B, hB⟩ := hφbdd j
    calc ∫⁻ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ₑ ^ 2 ∂(maximalCompactHaar K)
        ≤ ∫⁻ k, ENNReal.ofReal (B ^ 2) ∂(maximalCompactHaar K) := lintegral_mono (fun k => by
          rw [CuspPacket.enorm_sq_eq_ofReal_norm_sq]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hB k) 2))
      _ < ∞ := by rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  refine ⟨?_, ?_⟩
  · have hA := CuspPacket.lintegral_lintegral_Ioi_enorm_sq_integral_sum_mul_cpow_mul_lt_top
      (maximalCompactHaar K) (fun j (k : adelicMaximalCompact K) => φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) hu hu2 c
      (fun j => (hCIJ j).2.1) (fun j => (hCIJ j).2.2) (τ i)
    simpa only [hc_def] using hA
  ·
    set v : Fin (nE (em i)) → ℝ → adelicMaximalCompact K → ℂ :=
      fun j s k => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) with hv_def

    have hNEcont : ∀ j, Continuous (fun p : ℝ × adelicMaximalCompact K =>
        NE (em i) j ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K)) := by
      intro j
      obtain ⟨-, -, haxis, -, -, -, -, hNcont, -, -⟩ := _hEE (em i) j
      have hmap : Continuous (fun p : ℝ × adelicMaximalCompact K =>
          ((((p.1 : ℂ) * Complex.I), (p.2 : AdelicGL2 (𝓞 K) K)) : ℂ × AdelicGL2 (𝓞 K) K)) :=
        ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk
          (continuous_subtype_val.comp continuous_snd)
      refine hNcont.comp_continuous hmap (fun p => ⟨haxis ?_, Set.mem_univ _⟩)
      simp [Complex.mul_re]
    have hv : ∀ j, Measurable (Function.uncurry (v j)) := fun j => by
      have : Function.uncurry (v j) = fun p : ℝ × adelicMaximalCompact K =>
          ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K) := by
        funext p; rfl
      rw [this]
      exact (continuous_const.mul (hNEcont j)).measurable

    have hBφ : ∀ j, ∃ B : ℝ, ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖φE (em i) j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ B := fun j => by
      obtain ⟨B, hB⟩ := hφbdd j
      exact ⟨B, fun t k => by rw [_hφEflat (em i) j _ k]; exact hB k⟩

    have hgrow : ∀ j, ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖NE (em i) j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n := fun j => by
      obtain ⟨B, hB⟩ := hBφ j
      exact AutomorphicForm.exists_forall_norm_axis_continuation_weylIntertwiningIntegral_le_mul_pow_of_flat
        K hαm (μ (em i)) (ν (em i)) (_hμ (em i)) (_hν (em i)) (_hμic (em i)) (_hνic (em i)) (_hμc (em i)) (_hνc (em i)) (φE (em i) j) (_hφE (em i) j) (_hφEK (em i) j) (_hφEf (em i) j) (_hφEjc (em i) j) (_hφEhol (em i) j) (_hφEKu (em i) j) (OE (em i) j) (EE (em i) j) (NE (em i) j) (_hEE (em i) j) B hB
    choose Aj nj hAn using hgrow
    set Aexp : ℕ := ∑ j, nj j with hAexp
    set Cv : ℝ := ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹‖ * ∑ j, |Aj j| with hCv
    have hCv0 : 0 ≤ Cv := mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    have hvb : ∀ j t k, ‖v j t k‖ ≤ Cv * (1 + |t|) ^ Aexp := by
      intro j t k
      have h1 : (1 : ℝ) ≤ 1 + |t| := by simp [abs_nonneg]
      have hnj : nj j ≤ Aexp := by
        simp only [hAexp]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
      have hAj : |Aj j| ≤ ∑ j, |Aj j| :=
        Finset.single_le_sum (f := fun j => |Aj j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      simp only [hv_def, norm_mul]
      calc ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹‖ * ‖NE (em i) j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖
          ≤ ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹‖ * (|Aj j| * (1 + |t|) ^ Aexp) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (hAn j t k).trans ?_
            exact (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hnj) (abs_nonneg _))
        _ ≤ Cv * (1 + |t|) ^ Aexp := by
            simp only [hCv]; rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAj (by positivity)) (norm_nonneg _)

    have hv2 : ∀ j t, ∫⁻ k, ‖v j t k‖ₑ ^ 2 ∂(maximalCompactHaar K) ≤ 1 := by
      intro j t
      have h := AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
        K hαm (μ (em i)) (ν (em i)) (_hμ (em i)) (_hν (em i)) (_hμic (em i)) (_hνic (em i)) (_hμc (em i)) (_hνc (em i)) (φE (em i) j) (_hφE (em i) j) (_hφEK (em i) j) (_hφEf (em i) j) (_hφEjc (em i) j) (_hφEhol (em i) j) (_hφEKu (em i) j)
        (φE (em i) j) (_hφE (em i) j) (_hφEK (em i) j) (_hφEf (em i) j) (_hφEjc (em i) j) (_hφEhol (em i) j) (_hφEKu (em i) j)
        (OE (em i) j) (EE (em i) j) (NE (em i) j) (_hEE (em i) j) (OE (em i) j) (EE (em i) j) (NE (em i) j) (_hEE (em i) j) t
      simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
      rw [integral_complex_ofReal, integral_complex_ofReal] at h
      have h2 : ∫ k, ‖v j t k‖ ^ 2 ∂(maximalCompactHaar K) = ∫ k, ‖φE (em i) j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) := by
        simp only [hv_def]; exact_mod_cast h
      have h3 : ∫ k, ‖φE (em i) j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
        have hon := _hφEon (em i) j j
        simp only [if_true] at hon
        simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hon
        rw [integral_complex_ofReal] at hon
        have h4 : ∫ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by exact_mod_cast hon
        rw [← h4]
        exact integral_congr_ae (Filter.Eventually.of_forall (fun k => by
          show ‖φE (em i) j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 = ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2
          rw [_hφEflat (em i) j _ k]))

      have hvc : Continuous (fun k : adelicMaximalCompact K => v j t k) := by
        have : (fun k : adelicMaximalCompact K => v j t k) = (Function.uncurry (v j)) ∘ (fun k => (t, k)) := rfl
        rw [this]; exact (continuous_const.mul (hNEcont j)).comp (continuous_const.prodMk continuous_id)
      obtain ⟨Bv, hBv⟩ := isCompact_univ.exists_bound_of_continuousOn hvc.continuousOn
      have hint : Integrable (fun k => ‖v j t k‖ ^ 2) (maximalCompactHaar K) :=
        Integrable.mono' (integrable_const (Bv ^ 2)) ((continuous_pow 2).comp_aestronglyMeasurable hvc.norm.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun k => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact pow_le_pow_left₀ (norm_nonneg _) (hBv k (Set.mem_univ k)) 2))
      calc ∫⁻ k, ‖v j t k‖ₑ ^ 2 ∂(maximalCompactHaar K) = ∫⁻ k, ENNReal.ofReal (‖v j t k‖ ^ 2) ∂(maximalCompactHaar K) :=
            lintegral_congr (fun k => CuspPacket.enorm_sq_eq_ofReal_norm_sq _)
        _ = ENNReal.ofReal (∫ k, ‖v j t k‖ ^ 2 ∂(maximalCompactHaar K)) :=
            (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun k => sq_nonneg _))).symm
        _ = 1 := by rw [h2, h3, ENNReal.ofReal_one]
        _ ≤ 1 := le_rfl

    have hdec := (AutomorphicForm.differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty i).2.1
    have hcc : ∀ (j : Fin (nE (em i))) (t : ℝ),
        (∫ k, ψf i (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) = c j t := by
      intro j t
      simp only [hc_def]
      have e1 : ((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I := by push_cast; ring
      have e2 : (t : ℂ) * Complex.I + ((τ i : ℝ) : ℂ) * Complex.I = ((t + τ i : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      simp_rw [e1, e2]
    have hcm : ∀ j, AEStronglyMeasurable (c j) := fun j => (hCIJ j).1.aestronglyMeasurable
    have hc12 : ∀ j, Integrable (fun t : ℝ => (1 + |t|) ^ Aexp * ‖c j t‖) ∧
        Integrable (fun t : ℝ => ((1 + |t|) ^ Aexp * ‖c j t‖) ^ 2) := by
      intro j
      obtain ⟨m, hm, ⟨Bm, hBm⟩, hdecay⟩ := hdec j Aexp 0
      have key : ∀ t : ℝ, (1 + |t|) ^ Aexp * ‖c j t‖ ≤ m t := fun t => by
        have := hdecay 0 (by simp) t
        rwa [hcc j t] at this
      have hnn : ∀ t : ℝ, 0 ≤ (1 + |t|) ^ Aexp * ‖c j t‖ := fun t => by positivity
      have hwc : Continuous (fun t : ℝ => (1 + |t|) ^ Aexp * ‖c j t‖) := by
        exact ((continuous_const.add continuous_abs).pow _).mul (hCIJ j).1.norm
      refine ⟨Integrable.mono' hm hwc.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_)), ?_⟩
      · rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]; exact key t
      · refine Integrable.mono' (hm.const_mul Bm) ((continuous_pow 2).comp_aestronglyMeasurable hwc.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun t => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
        calc (1 + |t|) ^ Aexp * ‖c j t‖ * ((1 + |t|) ^ Aexp * ‖c j t‖) ≤ m t * m t :=
              mul_le_mul (key t) (key t) (hnn t) ((hnn t).trans (key t))
          _ ≤ Bm * m t := mul_le_mul_of_nonneg_right (hBm t) ((hnn t).trans (key t))
    have hB := CuspPacket.lintegral_lintegral_Ioi_enorm_sq_integral_sum_mul_cpow_neg_mul_lt_top
      (maximalCompactHaar K) v hv hv2 Aexp Cv hCv0 hvb c hcm (fun j => (hc12 j).1) (fun j => (hc12 j).2) (τ i)
    simpa only [hc_def, hv_def] using hB

end S_AutomorphicForm_lintegral_maximalCompact_lintegral_Ioi_enorm_sq_integral_sum_inner_mul_cpow_mul_flat_section_add_inv_vol_mul_axis_continuation_weylIntertwining_mul_inv_lt_top_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_lintegral_maximalCompact_lintegral_Ioi_enorm_sq_integral_sum_inner_mul_cpow_mul_flat_section_add_inv_vol_mul_axis_continuation_weylIntertwining_mul_inv_lt_top_of_matched_paleyWiener (solution)
