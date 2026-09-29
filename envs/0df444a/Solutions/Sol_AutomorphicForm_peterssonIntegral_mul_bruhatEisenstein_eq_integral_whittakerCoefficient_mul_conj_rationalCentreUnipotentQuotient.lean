-- Prove2me | solution 1 for AutomorphicForm.peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3abf21e6-7185-556d-b635-46f109f38f3e

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
import Theorems.Thm_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein
import Theorems.Thm_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
import Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
import Theorems.Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out
import Theorems.Thm_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_isClosed_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace RS11C9

open scoped Pointwise ENNReal

variable (F : Type) [Field F] [NumberField F]

scoped instance countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

scoped instance countable_matrix : Countable (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → F))

scoped instance countable_gl2 : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
  Units.val_injective.countable

def slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

theorem measurableSet_slab (d₁ d₂ : ℝ) : MeasurableSet (slab F d₁ d₂) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂

theorem globalPoints_mul_mem_slab_iff {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    globalPoints (𝓞 F) F γ * g ∈ slab F d₁ d₂ ↔ g ∈ slab F d₁ d₂ := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem preimage_slab {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    (fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' slab F d₁ d₂ = slab F d₁ d₂ := by
  ext g; exact globalPoints_mul_mem_slab_iff F γ g

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem enorm_coe_real_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr]

theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul_left h b
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul_right h a
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem ofReal_sq_norm (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem indicator_comp_globalPoints_mul {β : Type*} [Zero β] {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    (slab F d₁ d₂).indicator f (globalPoints (𝓞 F) F γ * g) =
      (slab F d₁ d₂).indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g := by
  by_cases hg : g ∈ slab F d₁ d₂
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((globalPoints_mul_mem_slab_iff F γ g).mpr hg)]
  · rw [Set.indicator_of_notMem hg,
      Set.indicator_of_notMem (fun h => hg ((globalPoints_mul_mem_slab_iff F γ g).mp h))]

theorem tsum_indicator_const_set {ι β : Type*} [AddCommMonoid β] [TopologicalSpace β] (s : Set (AdelicGL2 (𝓞 F) F))
    (f : ι → AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    ∑' i, s.indicator (f i) g = s.indicator (fun g => ∑' i, f i g) g := by
  by_cases hg : g ∈ s
  · simp only [Set.indicator_of_mem hg]
  · simp only [Set.indicator_of_notMem hg, tsum_zero]

theorem det_unipotentGL2 {A : Type*} [CommRing A] (u : A) : Matrix.GeneralLinearGroup.det (unipotentGL2 u) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem unipotentGL2_mul_mem_slab_iff {d₁ d₂ : ℝ} (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    unipotentGL2 u * g ∈ slab F d₁ d₂ ↔ g ∈ slab F d₁ d₂ := by
  simp only [slab, Set.mem_setOf_eq, map_mul, det_unipotentGL2, one_mul]

theorem globalPoints_scalar_mul_comm (a : Fˣ) (g : AdelicGL2 (𝓞 F) F) :
    globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) * g =
      g * globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) := by
  apply Units.ext
  push_cast
  have hval : ((globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) :
      AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (algebraMap F (AdeleRing (𝓞 F) F) (a : F)) := by
    ext i j
    rw [globalPoints_apply]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite (algebraMap F (AdeleRing (𝓞 F) F))]
  rw [hval]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem continuous_unipotentGL2 (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  have hmat : ∀ s : A → A, Continuous s → Continuous (fun x : A => (!![1, s x; 0, 1] : Matrix (Fin 2) (Fin 2) A)) := by
    intro s hs
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [hs, continuous_const]
  rw [Units.continuous_iff]
  constructor
  · have h__af := hmat id continuous_id
    simp [unipotentGL2_coe] at h__af
    exact h__af
  · have hinv : ∀ x : A, ((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) = unipotentGL2 (-x) := by
      intro x
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    simp only [hinv]
    simpa [unipotentGL2_coe] using hmat Neg.neg continuous_neg

theorem diagOne_mem_borelSubgroup (a : Fˣ) : (diagOne a : Matrix.GeneralLinearGroup (Fin 2) F) ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff]
  simp [diagOne]

theorem scalar_mem_borelSubgroup (a : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff]
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hfi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hfi, ENNReal.ofReal_zero]; exact bot_le

theorem sqrt_mul_sqrt_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

theorem unipotentGL2_mul_globalPoints_borel (b : Matrix.GeneralLinearGroup (Fin 2) F) (hb : b ∈ borelSubgroup F)
    (u : AdeleRing (𝓞 F) F) :
    unipotentGL2 u * globalPoints (𝓞 F) F b = globalPoints (𝓞 F) F b *
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F)
        (((borelDiagSnd ⟨b, hb⟩ * (borelDiagFst ⟨b, hb⟩)⁻¹ : Fˣ) : F)) * u) := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
  have hp0 : (b : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := (borelDiagFst ⟨b, hb⟩).ne_zero
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe,
    globalPoints_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, borelDiagFst, borelDiagSnd, hb10]
  have hv : (b : Matrix (Fin 2) (Fin 2) F) 0 0 * ((b⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    (borelDiagFst ⟨b, hb⟩).val_inv
  rw [Matrix.coe_units_inv] at hv
  have h1 : algebraMap F (AdeleRing (𝓞 F) F) ((b : Matrix (Fin 2) (Fin 2) F) 0 0) *
      algebraMap F (AdeleRing (𝓞 F) F) ((b : Matrix (Fin 2) (Fin 2) F)⁻¹ 0 0) = 1 := by
    rw [← map_mul, hv, map_one]
  linear_combination (-(u * algebraMap F (AdeleRing (𝓞 F) F) ((b : Matrix (Fin 2) (Fin 2) F) 1 1))) * h1

end RS11C9
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient.RS11C9"

end
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient.RS11C9"

open scoped Pointwise ENNReal

open RS11C9 in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
      (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (_hφsum : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
        ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (x y : AdelicGL2 (𝓞 F) F → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        x (globalPoints (𝓞 F) F γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        y (globalPoints (𝓞 F) F γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (_hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
      (_hxW : ∀ g, Summable fun a : F =>
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
      (w d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (𝓕 : Set (AdelicGL2 (𝓞 F) F))
      (_h𝓕s : 𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (_hintx : IntegrableOn (fun g => ‖x g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F))
      (_hinty : IntegrableOn (fun g => ‖y g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)),
    Integrable (fun q : RationalCentreUnipotentQuotient F =>
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) q.out) *
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 q.out *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1 q.out) *
          φ q.out *
          ((ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ^ (-w) : ℝ) : ℂ))
        (rationalCentreUnipotentQuotientMeasure F) ∧
    peterssonIntegral F w 𝓕
        (fun g => x g * (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) y =
      ∫ q : RationalCentreUnipotentQuotient F,
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) q.out) *
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 q.out *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1 q.out) *
          φ q.out *
          ((ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ^ (-w) : ℝ) : ℂ)
        ∂(rationalCentreUnipotentQuotientMeasure F) := by
  intro α hα D U gen ψ hψ μc νc hμu hνu hμF hνF s φ hφ hφc hφsum x y hxG hyG hxc hyc hx0 hxW w d₁ d₂ hd₁ hd 𝓕 h𝓕s h𝓕
    hintx hinty
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  set μG := adelicGLHaar (Fin 2) (𝓞 F) F with hμG
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μG := Measure.IsHaarMeasure.sigmaFinite μG
  haveI : SFinite μG := instSFiniteOfSigmaFinite
  have hSd : {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} =
      RS11C9.slab F d₁ d₂ := rfl

  obtain ⟨𝓕B, h𝓕Bm, hFD, hint₁, hid₁, hmx, hmy⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein F hα μc νc
      hμF hνF s φ hφ hφc hφsum x y hxG hyG hxc hyc w d₁ d₂ hd₁ hd 𝓕 h𝓕s h𝓕 hintx hinty
  rw [← hid₁]
  simp only [hSd] at h𝓕s h𝓕 hintx hinty hint₁ hmx hmy ⊢
  set Sd := RS11C9.slab F d₁ d₂ with hSd'
  have hSdm : MeasurableSet Sd := RS11C9.measurableSet_slab F d₁ d₂

  have hH₂c := AutomorphicForm.isClosed_rationalTorusUnipotent F
  obtain ⟨hH₂haar, hH₂right⟩ := AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F
  have hHc := AutomorphicForm.isClosed_rationalCentreUnipotent F
  obtain ⟨hHhaar, hHright⟩ := AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant F
  have h42 := AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  dsimp only at h42
  obtain ⟨hBle, hBcount, hT₂m, hT₂FD, hT₂int⟩ := h42
  haveI : Countable ((borelSubgroup F).map (globalPoints (𝓞 F) F)) := hBcount

  set ω : AdelicGL2 (𝓞 F) F → ℝ := fun g => ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) with hω
  have hωpos : ∀ g, 0 < ω g := fun g => Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _
  have hωc : Continuous ω :=
    (NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun _ =>
      Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hωG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      ω (globalPoints (𝓞 F) F γ * g) = ω g := fun γ g => by
    simp only [hω, map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  have hωN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), ω (unipotentGL2 u * g) = ω g := fun u g => by
    simp only [hω, map_mul, RS11C9.det_unipotentGL2, one_mul]
  obtain ⟨hφB, hφN⟩ :=
    AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul F hα μc νc
      hμF hνF s φ hφ
  have hindG : ∀ {β : Type} [Zero β] (γ : Matrix.GeneralLinearGroup (Fin 2) F) (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (globalPoints (𝓞 F) F γ * g) = Sd.indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g :=
    fun γ f g => RS11C9.indicator_comp_globalPoints_mul F γ f g
  have hindN : ∀ {β : Type} [Zero β] (u : AdeleRing (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (unipotentGL2 u * g) = Sd.indicator (fun g => f (unipotentGL2 u * g)) g := by
    intro β _ u f g
    by_cases hg : g ∈ Sd
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((RS11C9.unipotentGL2_mul_mem_slab_iff F u g).mpr hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (fun h => hg ((RS11C9.unipotentGL2_mul_mem_slab_iff F u g).mp h))]

  set Wx : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 g with hWx
  set Wy : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1 g with hWy

  set k₃ : AdelicGL2 (𝓞 F) F → ℂ := fun g => Sd.indicator (fun _ => (1 : ℂ)) g * Wx g * (starRingEnd ℂ) (Wy g) *
    φ g * ((ω g : ℝ) : ℂ) with hk₃

  have hψc : Continuous ψ := hψ.continuous
  have hWdef : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g =
        ∫ u, z (unipotentGL2 u * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))
          ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
    intro z g; rfl
  have hWmeas : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), Continuous z →
      Measurable fun g => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g := by
    intro z hz
    simp only [hWdef]
    have hsm : StronglyMeasurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (u : AdeleRing (𝓞 F) F) =>
        z (unipotentGL2 u * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))) := by
      refine Continuous.stronglyMeasurable ?_
      exact (hz.comp (((RS11C9.continuous_unipotentGL2 _).comp continuous_snd).mul continuous_fst)).mul
        (hψc.comp ((continuous_const.mul continuous_snd).neg))
    exact (hsm.integral_prod_right' (ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))).measurable

  have hWZ : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) g, z (globalPoints (𝓞 F) F γ * g) = z g) →
      ∀ (a : Fˣ) (g : AdelicGL2 (𝓞 F) F),
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1
        (globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) * g) =
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g := by
    intro z hzG a g
    simp only [hWdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show z (unipotentGL2 u * (_ * g)) * _ = z (unipotentGL2 u * g) * _
    rw [← mul_assoc, ← RS11C9.globalPoints_scalar_mul_comm F a (unipotentGL2 u), mul_assoc, hzG]

  have hWN : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) g, z (globalPoints (𝓞 F) F γ * g) = z g) →
      ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 (unipotentGL2 u * g) =
        ψ u * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g := by
    intro z hzG u g
    have hper : ∀ (β : F) (v : AdeleRing (𝓞 F) F),
        z (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + v) * g) = z (unipotentGL2 v * g) := by
      intro β v
      rw [unipotentGL2_add, ← RS11C9.globalPoints_unipotentGL2, mul_assoc, hzG]
    have h := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant z g hper 1 u
    rw [h, map_one, one_mul]
  have hψnorm : ∀ u : AdeleRing (𝓞 F) F, ‖ψ u‖ = 1 :=
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ
  have hψconj : ∀ u : AdeleRing (𝓞 F) F, ψ u * (starRingEnd ℂ) (ψ u) = 1 := fun u => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψnorm, one_pow]; simp

  have hk₃Z : ∀ (a : Fˣ) (g : AdelicGL2 (𝓞 F) F),
      k₃ (globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) * g) = k₃ g := by
    intro a g
    simp only [hk₃, hWx, hWy, hWZ x hxG, hWZ y hyG, hωG, hφB _ (RS11C9.scalar_mem_borelSubgroup F a)]
    rw [hindG]
  have hk₃N : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), k₃ (unipotentGL2 u * g) = k₃ g := by
    intro u g
    simp only [hk₃, hWx, hWy, hWN x hxG, hWN y hyG, hωN, hφN]
    rw [hindN, map_mul]
    calc Sd.indicator (fun _ => (1 : ℂ)) g * (ψ u * whittakerCoefficient F _ ψ x 1 g) *
          ((starRingEnd ℂ) (ψ u) * (starRingEnd ℂ) (whittakerCoefficient F _ ψ y 1 g)) * φ g * ((ω g : ℝ) : ℂ)
        = (ψ u * (starRingEnd ℂ) (ψ u)) * (Sd.indicator (fun _ => (1 : ℂ)) g * whittakerCoefficient F _ ψ x 1 g *
            (starRingEnd ℂ) (whittakerCoefficient F _ ψ y 1 g) * φ g * ((ω g : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hψconj, one_mul]
  have hk₃H : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k₃ (h * g) = k₃ g := by
    intro h hh0
    have hh : h ∈ rationalCentre F ⊔ adelicUnipotent F := hh0
    rw [Subgroup.sup_eq_closure] at hh
    refine Subgroup.closure_induction (p := fun h _ => ∀ g : AdelicGL2 (𝓞 F) F, k₃ (h * g) = k₃ g) ?_ ?_ ?_ ?_ hh
    · rintro z (⟨a, rfl⟩ | ⟨u, rfl⟩) g
      · exact hk₃Z a g
      · exact hk₃N u.toAdd g
    · intro g; rw [one_mul]
    · intro a b _ _ ha hb g; rw [mul_assoc, ha, hb]
    · intro a _ ha g
      have := ha (a⁻¹ * g)
      rw [← mul_assoc, mul_inv_cancel, one_mul] at this
      exact this.symm

  have hk₃m : Measurable k₃ := by
    simp only [hk₃]
    refine ((((measurable_const.indicator hSdm).mul (hWmeas x hxc)).mul
      (Complex.continuous_conj.measurable.comp (hWmeas y hyc))).mul hφc.measurable).mul
      (Complex.continuous_ofReal.measurable.comp hωc.measurable)

  set ν₀ : Measure (AdeleRing (𝓞 F) F) := ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F with hν₀
  have hleNU : adelicUnipotent F ≤ rationalTorus F ⊔ adelicUnipotent F := le_sup_right
  set ι₂ : AdeleRing (𝓞 F) F → rationalTorusUnipotent F := fun u =>
    Subgroup.inclusion hleNU (toAdelicUnipotent F u) with hι₂
  have hι₂c : Continuous ι₂ := by
    refine continuous_induced_rng.2 ?_
    show Continuous fun u : AdeleRing (𝓞 F) F => ((Subgroup.inclusion hleNU (toAdelicUnipotent F u) : rationalTorusUnipotent F) :
      AdelicGL2 (𝓞 F) F)
    exact RS11C9.continuous_unipotentGL2 _
  have hι₂m : Measurable ι₂ := hι₂c.measurable
  have hcoeι : ∀ u : AdeleRing (𝓞 F) F, ((ι₂ u : rationalTorusUnipotent F) : AdelicGL2 (𝓞 F) F) = unipotentGL2 u :=
    fun u => rfl
  have M2 : (rationalTorusUnipotentHaar F).restrict (ι₂ '' adelicBox F) = Measure.map ι₂ (ν₀.restrict (adelicBox F)) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hι₂m hA, Measure.restrict_apply (hι₂m hA), ← lintegral_indicator_one hA,
      hT₂int (A.indicator 1) (measurable_one.indicator hA), ← lintegral_indicator_one ((hι₂m hA).inter (measurableSet_adelicBox F)),
      ← lintegral_indicator (measurableSet_adelicBox F)]
    refine lintegral_congr fun u => ?_
    change (adelicBox F).indicator (fun u => A.indicator (1 : rationalTorusUnipotent F → ℝ≥0∞) (ι₂ u)) u =
      (ι₂ ⁻¹' A ∩ adelicBox F).indicator 1 u
    by_cases h1 : u ∈ adelicBox F <;> by_cases h2 : ι₂ u ∈ A <;>
      simp [Set.indicator_apply, Set.mem_preimage, h1, h2]
  have hν : ν₀.restrict (adelicBox F) = (productionPinsOf F D U gen (adelicBox F)).ν := by
    show (((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F).restrict (adelicBox F) =
      ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)
    rw [ProbabilityTheory.cond, Measure.restrict_smul]

  have hν₀box : ν₀ (adelicBox F) = 1 := by
    rw [hν₀, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne
  haveI : IsProbabilityMeasure (ν₀.restrict (adelicBox F)) := by
    rw [hν]; exact NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox F

  set IL : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun z g =>
    ∫⁻ u in adelicBox F, ‖z (unipotentGL2 u * g)‖ₑ ^ 2 ∂ν₀ with hIL
  have hILm : ∀ z : AdelicGL2 (𝓞 F) F → ℂ, Continuous z → Measurable (IL z) := by
    intro z hz
    have hm : Measurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (u : AdeleRing (𝓞 F) F) =>
        ‖z (unipotentGL2 u * g)‖ₑ ^ 2) :=
      ((hz.comp (((RS11C9.continuous_unipotentGL2 _).comp continuous_snd).mul continuous_fst)).measurable.enorm).pow_const 2
    exact hm.lintegral_prod_right' (ν := ν₀.restrict (adelicBox F))

  have hILinv : ∀ z : AdelicGL2 (𝓞 F) F → ℂ, Continuous z →
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) g, z (globalPoints (𝓞 F) F γ * g) = z g) →
      (∀ b ∈ borelSubgroup F, ∀ g, IL z (globalPoints (𝓞 F) F b * g) = IL z g) ∧
      (∀ (u₀ : AdeleRing (𝓞 F) F) g, IL z (unipotentGL2 u₀ * g) = IL z g) := by
    intro z hz hzG
    have hsm : ∀ (h : AdeleRing (𝓞 F) F → ℝ≥0∞), ∫⁻ u in adelicBox F, h u ∂ν₀ =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∫⁻ u in adelicBox F, h u ∂(adelicAddHaar (𝓞 F) F) := by
      intro h; rw [hν₀, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    have hper : ∀ (g : AdelicGL2 (𝓞 F) F) (β : F) (u : AdeleRing (𝓞 F) F),
        (fun u => ‖z (unipotentGL2 u * g)‖ₑ ^ 2) (algebraMap F (AdeleRing (𝓞 F) F) β + u) =
          (fun u => ‖z (unipotentGL2 u * g)‖ₑ ^ 2) u := by
      intro g β u
      simp only
      rw [unipotentGL2_add, ← RS11C9.globalPoints_unipotentGL2, mul_assoc, hzG]
    have hmeas : ∀ g : AdelicGL2 (𝓞 F) F, Measurable fun u : AdeleRing (𝓞 F) F => ‖z (unipotentGL2 u * g)‖ₑ ^ 2 :=
      fun g => ((hz.comp ((RS11C9.continuous_unipotentGL2 _).mul continuous_const)).measurable.enorm).pow_const 2
    constructor
    · intro b hb g
      simp only [hIL]
      rw [hsm, hsm]
      congr 1
      set c : Fˣ := borelDiagSnd ⟨b, hb⟩ * (borelDiagFst ⟨b, hb⟩)⁻¹ with hc
      have hrw : ∀ u : AdeleRing (𝓞 F) F, z (unipotentGL2 u * (globalPoints (𝓞 F) F b * g)) =
          z (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (c : F) * u + 0) * g) := by
        intro u
        rw [add_zero, ← mul_assoc, RS11C9.unipotentGL2_mul_globalPoints_borel F b hb u, mul_assoc, hzG]
      simp only [hrw]
      exact NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic F _ (hmeas g) (hper g) c 0
    · intro u₀ g
      simp only [hIL]
      rw [hsm, hsm]
      congr 1
      have hrw : ∀ u : AdeleRing (𝓞 F) F, z (unipotentGL2 u * (unipotentGL2 u₀ * g)) =
          z (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ((1 : Fˣ) : F) * u + u₀) * g) := by
        intro u
        rw [Units.val_one, map_one, one_mul, ← mul_assoc, ← unipotentGL2_add]
      simp only [hrw]
      exact NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic F _ (hmeas g) (hper g) 1 u₀
  obtain ⟨hILxB, hILxN⟩ := hILinv x hxc hxG
  obtain ⟨hILyB, hILyN⟩ := hILinv y hyc hyG

  set f₁ : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun z g =>
    Sd.indicator (fun g => ‖φ g‖ₑ * ENNReal.ofReal (ω g) * IL z g) g with hf₁
  set f₂ : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun z g =>
    Sd.indicator (fun g => ENNReal.ofReal (‖z g‖ ^ 2 * ‖φ g‖ * ω g)) g with hf₂
  have hrefold : ∀ z : AdelicGL2 (𝓞 F) F → ℂ, Continuous z →
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) g, z (globalPoints (𝓞 F) F γ * g) = z g) →
      (∀ b ∈ borelSubgroup F, ∀ g, IL z (globalPoints (𝓞 F) F b * g) = IL z g) →
      (∀ (u₀ : AdeleRing (𝓞 F) F) g, IL z (unipotentGL2 u₀ * g) = IL z g) →
      ∫⁻ g in 𝓕B, f₁ z g ∂μG = ∫⁻ g in 𝓕B, f₂ z g ∂μG := by
    intro z hz hzG hB hN
    have hf₁m : Measurable (f₁ z) :=
      (((hφc.measurable.enorm).mul (ENNReal.measurable_ofReal.comp hωc.measurable)).mul (hILm z hz)).indicator hSdm
    have hf₂m : Measurable (f₂ z) :=
      (ENNReal.measurable_ofReal.comp (((hz.norm.pow 2).mul hφc.norm).mul hωc).measurable).indicator hSdm
    have hf₁B : ∀ γ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, f₁ z (γ * g) = f₁ z g := by
      rintro _ ⟨b, hb, rfl⟩ g
      simp only [hf₁]
      rw [hindG]
      simp only [hωG, hφB b hb, hB b hb]
    have hf₂B : ∀ γ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, f₂ z (γ * g) = f₂ z g := by
      rintro _ ⟨b, hb, rfl⟩ g
      simp only [hf₂]
      rw [hindG]
      simp only [hωG, hφB b hb, hzG]
    have L1 := HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out μG (rationalTorusUnipotent F) hH₂c
      (rationalTorusUnipotentHaar F) ((borelSubgroup F).map (globalPoints (𝓞 F) F)) hBle (f₁ z) hf₁m hf₁B 𝓕B hFD _ hT₂FD
    have L2 := HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out μG (rationalTorusUnipotent F) hH₂c
      (rationalTorusUnipotentHaar F) ((borelSubgroup F).map (globalPoints (𝓞 F) F)) hBle (f₂ z) hf₂m hf₂B 𝓕B hFD _ hT₂FD
    rw [L1, L2]
    refine lintegral_congr fun q => ?_
    have hmt : Measurable fun t : rationalTorusUnipotent F => (t : AdelicGL2 (𝓞 F) F) * q.out :=
      (continuous_subtype_val.mul continuous_const).measurable
    rw [hT₂int (fun t => f₁ z ((t : AdelicGL2 (𝓞 F) F) * q.out)) (hf₁m.comp hmt),
      hT₂int (fun t => f₂ z ((t : AdelicGL2 (𝓞 F) F) * q.out)) (hf₂m.comp hmt)]
    show ∫⁻ u in adelicBox F, f₁ z (unipotentGL2 u * q.out) ∂ν₀ = ∫⁻ u in adelicBox F, f₂ z (unipotentGL2 u * q.out) ∂ν₀
    have h1 : ∀ u, f₁ z (unipotentGL2 u * q.out) = f₁ z q.out := by
      intro u
      simp only [hf₁]
      rw [hindN]
      simp only [hωN, hφN, hN]
    simp only [h1]
    rw [setLIntegral_const, hν₀box, mul_one]
    by_cases hq : q.out ∈ Sd
    · have h2 : ∀ u, f₂ z (unipotentGL2 u * q.out) =
          ‖φ q.out‖ₑ * ENNReal.ofReal (ω q.out) * ‖z (unipotentGL2 u * q.out)‖ₑ ^ 2 := by
        intro u
        simp only [hf₂]
        rw [hindN, Set.indicator_of_mem hq, hωN, hφN, ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (norm_nonneg _)),
          ENNReal.ofReal_mul (sq_nonneg _), RS11C9.ofReal_sq_norm, ofReal_norm_eq_enorm]
        ring
      simp only [h2]
      have hmz : Measurable fun u : AdeleRing (𝓞 F) F => ‖z (unipotentGL2 u * q.out)‖ₑ ^ 2 :=
        ((hz.comp ((RS11C9.continuous_unipotentGL2 _).mul continuous_const)).measurable.enorm).pow_const 2
      rw [lintegral_const_mul _ hmz, hf₁]
      simp only
      rw [Set.indicator_of_mem hq]
    · have h2 : ∀ u, f₂ z (unipotentGL2 u * q.out) = 0 := by
        intro u
        simp only [hf₂]
        rw [hindN, Set.indicator_of_notMem hq]
      simp only [h2, lintegral_zero, hf₁]
      rw [Set.indicator_of_notMem hq]

  have hpt : ∀ g : AdelicGL2 (𝓞 F) F,
      ∑' a : Fˣ, ‖k₃ (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ ≤ f₁ x g + f₁ y g := by
    intro g
    obtain ⟨hsum, hle, -⟩ :=
      AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
        F D U gen ψ hψ x y hxG hyG hxc hyc hx0 hxW g
    have hterm : ∀ a : Fˣ, ‖k₃ (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ =
        Sd.indicator (fun g => ‖φ g‖ₑ * ENNReal.ofReal (ω g) *
          ENNReal.ofReal (‖Wx (globalPoints (𝓞 F) F (diagOne a) * g)‖ * ‖Wy (globalPoints (𝓞 F) F (diagOne a) * g)‖)) g := by
      intro a
      simp only [hk₃, hωG, hφB _ (RS11C9.diagOne_mem_borelSubgroup F a)]
      rw [hindG]
      by_cases hg : g ∈ Sd
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
        simp only [one_mul, enorm_mul, RCLike.enorm_conj, RS11C9.enorm_coe_real_of_nonneg (hωpos g).le]
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]
        ring
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
        simp
    simp only [hterm]
    rw [RS11C9.tsum_indicator_const_set]
    by_cases hg : g ∈ Sd
    swap
    · simp only [Set.indicator_of_notMem hg, hf₁, add_zero]; exact le_rfl
    simp only [Set.indicator_of_mem hg, hf₁]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsum,
      ← mul_add]
    gcongr

    have hIx0 : 0 ≤ ∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν :=
      integral_nonneg fun _ => sq_nonneg _
    have hIy0 : 0 ≤ ∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν :=
      integral_nonneg fun _ => sq_nonneg _
    calc ENNReal.ofReal (∑' a : Fˣ, ‖Wx (globalPoints (𝓞 F) F (diagOne a) * g)‖ * ‖Wy (globalPoints (𝓞 F) F (diagOne a) * g)‖)
        ≤ ENNReal.ofReal ((∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) +
            ∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) :=
          ENNReal.ofReal_le_ofReal (hle.trans (RS11C9.sqrt_mul_sqrt_le_add hIx0 hIy0))
      _ = ENNReal.ofReal (∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) +
            ENNReal.ofReal (∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) :=
          ENNReal.ofReal_add hIx0 hIy0
      _ ≤ IL x g + IL y g := by
          gcongr
          · refine (RS11C9.ofReal_integral_le_lintegral _ fun _ => sq_nonneg _).trans (le_of_eq ?_)
            show ∫⁻ u, ENNReal.ofReal (‖x (unipotentGL2 u * g)‖ ^ 2) ∂(productionPinsOf F D U gen (adelicBox F)).ν =
              ∫⁻ u, ‖x (unipotentGL2 u * g)‖ₑ ^ 2 ∂(ν₀.restrict (adelicBox F))
            rw [hν]; simp only [RS11C9.ofReal_sq_norm]; rfl
          · refine (RS11C9.ofReal_integral_le_lintegral _ fun _ => sq_nonneg _).trans (le_of_eq ?_)
            show ∫⁻ u, ENNReal.ofReal (‖y (unipotentGL2 u * g)‖ ^ 2) ∂(productionPinsOf F D U gen (adelicBox F)).ν =
              ∫⁻ u, ‖y (unipotentGL2 u * g)‖ₑ ^ 2 ∂(ν₀.restrict (adelicBox F))
            rw [hν]; simp only [RS11C9.ofReal_sq_norm]; rfl
  have hfin₃ : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k₃ (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ ∂μG < ∞ := by
    have hf₁xm : Measurable (f₁ x) :=
      (((hφc.measurable.enorm).mul (ENNReal.measurable_ofReal.comp hωc.measurable)).mul (hILm x hxc)).indicator hSdm
    calc ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k₃ (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ ∂μG
        ≤ ∫⁻ g in 𝓕B, (f₁ x g + f₁ y g) ∂μG := lintegral_mono hpt
      _ = (∫⁻ g in 𝓕B, f₁ x g ∂μG) + ∫⁻ g in 𝓕B, f₁ y g ∂μG := lintegral_add_left hf₁xm _
      _ = (∫⁻ g in 𝓕B, f₂ x g ∂μG) + ∫⁻ g in 𝓕B, f₂ y g ∂μG := by
          rw [hrefold x hxc hxG hILxB hILxN, hrefold y hyc hyG hILyB hILyN]
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hmx, hmy⟩

  obtain ⟨hInt, -, hC, hD'⟩ :=
    AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient F 𝓕B hFD
      k₃ hk₃m hk₃H hfin₃
  refine ⟨by simpa only [hk₃] using hInt, ?_⟩

  set k₁ : AdelicGL2 (𝓞 F) F → ℂ := fun g => Sd.indicator (fun _ => (1 : ℂ)) g *
    (x g * φ g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ)) with hk₁
  have hk₁m : Measurable k₁ :=
    (measurable_const.indicator hSdm).mul ((((hxc.mul hφc).mul (Complex.continuous_conj.comp hyc)).mul
      (Complex.continuous_ofReal.comp hωc)).measurable)
  have hk₁B : ∀ γ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, k₁ (γ * g) = k₁ g := by
    rintro _ ⟨b, hb, rfl⟩ g
    simp only [hk₁, hxG, hyG, hωG, hφB b hb]
    rw [hindG]
  have hfin₁ : ∫⁻ g in 𝓕B, ‖k₁ g‖ₑ ∂μG < ∞ := hint₁.2
  obtain ⟨-, -, hC2⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μG
      (rationalTorusUnipotent F) hH₂c (rationalTorusUnipotentHaar F) ((borelSubgroup F).map (globalPoints (𝓞 F) F))
      hBle k₁ hk₁m hk₁B 𝓕B hFD _ hT₂FD hfin₁
  show ∫ g in 𝓕B, k₁ g ∂μG = _
  rw [hC2, ← hD', ← hC]

  have hPars := fun g => (AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
    F D U gen ψ hψ x y hxG hyG hxc hyc hx0 hxW g).2.2
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)

  show ∫ t in ι₂ '' adelicBox F, k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F) =
    ∑' a : Fˣ, k₃ (globalPoints (𝓞 F) F (diagOne a) * q.out)
  have hkm : AEStronglyMeasurable (fun t : rationalTorusUnipotent F => k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out))
      (Measure.map ι₂ (ν₀.restrict (adelicBox F))) :=
    (hk₁m.comp (continuous_subtype_val.mul continuous_const).measurable).aestronglyMeasurable
  rw [show (∫ t in ι₂ '' adelicBox F, k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F)) =
      ∫ t, k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out) ∂((rationalTorusUnipotentHaar F).restrict (ι₂ '' adelicBox F)) from rfl,
    M2, integral_map hι₂m.aemeasurable hkm]
  simp only [hcoeι]
  have hk₁N : ∀ (u : AdeleRing (𝓞 F) F) (g₀ : AdelicGL2 (𝓞 F) F), k₁ (unipotentGL2 u * g₀) =
      (Sd.indicator (fun _ => (1 : ℂ)) g₀ * φ g₀ * ((ω g₀ : ℝ) : ℂ)) *
        (x (unipotentGL2 u * g₀) * (starRingEnd ℂ) (y (unipotentGL2 u * g₀))) := by
    intro u g₀
    simp only [hk₁, hφN, hωN]
    rw [hindN]
    ring
  simp only [hk₁N]
  have hP' : ∫ u, x (unipotentGL2 u * q.out) * (starRingEnd ℂ) (y (unipotentGL2 u * q.out)) ∂(ν₀.restrict (adelicBox F)) =
      ∑' a : Fˣ, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 (globalPoints (𝓞 F) F (diagOne a) * q.out) *
        (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * q.out)) := by
    rw [hν]; exact hPars q.out
  rw [integral_const_mul, hP', ← tsum_mul_left]
  refine tsum_congr fun a => ?_
  simp only [hk₃, hWx, hWy, hωG, hφB _ (RS11C9.diagOne_mem_borelSubgroup F a)]
  rw [hindG]
  ring

end S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient
end P2MW
export P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient (solution)
