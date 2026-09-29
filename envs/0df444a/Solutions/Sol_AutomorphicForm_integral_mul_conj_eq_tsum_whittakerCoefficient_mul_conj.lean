-- Prove2me | solution 1 for AutomorphicForm.integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b76cc96d-301d-5f32-a0bb-847860973e04

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

namespace RS9P

variable (F : Type) [Field F] [NumberField F]

theorem countable_numberField : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

scoped instance countable_principalSubgroup : Countable ↥(AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI : Countable F := countable_numberField F
  refine Function.Surjective.countable (f := fun k : F =>
    (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : ↥(AdeleRing.principalSubgroup (𝓞 F) F))) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

theorem addChar_neg_eq_conj (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (y : AdeleRing (𝓞 F) F) : ψ (-y) = (starRingEnd ℂ) (ψ y) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ1 y)]

theorem productionPinsOf_ν (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) :
    (productionPinsOf F D U gen (adelicBox F)).ν =
      ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) := rfl

theorem setIntegral_adelicBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u in adelicBox F, G (u + x) ∂(adelicAddHaar (𝓞 F) F) =
      ∫ u in adelicBox F, G u ∂(adelicAddHaar (𝓞 F) F) := by
  set μ := adelicAddHaar (𝓞 F) F with hμ

  have h1 : ∫ u in adelicBox F, G (u + x) ∂μ = ∫ w in (fun u => u + x) '' adelicBox F, G w ∂μ := by
    have hme : MeasurableEmbedding (fun u : AdeleRing (𝓞 F) F => u + x) :=
      (Homeomorph.addRight x).measurableEmbedding
    conv_lhs => rw [← Set.preimage_image_eq (adelicBox F) (add_left_injective x)]
    rw [← hme.setIntegral_map, map_add_right_eq_self]

  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F) μ :=
    isAddFundamentalDomain_adelicBox F μ
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun u => u + x) '' adelicBox F) μ := by
    refine hFD.image_of_equiv (ν := μ) (Equiv.addRight x) ?_ (Equiv.refl _) ?_
    · simpa using (measurePreserving_add_right μ (-x)).quasiMeasurePreserving
    · intro γ u
      show (γ +ᵥ u) + x = γ +ᵥ (u + x)
      simp only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]

  have hinv : ∀ (γ : AdeleRing.principalSubgroup (𝓞 F) F) (u : AdeleRing (𝓞 F) F), G (γ +ᵥ u) = G u := by
    rintro ⟨_, β, rfl⟩ u
    exact hG β u
  rw [h1]
  exact hFD'.setIntegral_eq hFD hinv

theorem integral_cond_adelicBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u, G (u + x) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) =
      ∫ u, G u ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  simp only [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_add_right F G hG x]

theorem whittakerCoefficient_unipotentGL2_mul (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (α : F) (x : AdeleRing (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α (unipotentGL2 x * g) =
      ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g := by
  set a := algebraMap F (AdeleRing (𝓞 F) F) α with ha
  set G : AdeleRing (𝓞 F) F → ℂ := fun w => φ (unipotentGL2 w * g) * ψ (-(a * w)) with hGdef
  have hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u := by
    intro β u
    have h1 : ψ (-(a * algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
      rw [ha, ← map_mul, ← map_neg]; exact hψ _
    simp only [hGdef]
    rw [hper β u, mul_add, neg_add, AddChar.map_add_eq_mul, h1, one_mul]
  have hint : ∀ u : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 u * (unipotentGL2 x * g)) * ψ (-(a * u)) = ψ (a * x) * G (u + x) := by
    intro u
    simp only [hGdef]
    rw [← mul_assoc, ← unipotentGL2_add, show -(a * u) = a * x + -(a * (u + x)) by ring,
      AddChar.map_add_eq_mul]
    ring
  show (∫ u, φ (unipotentGL2 u * (unipotentGL2 x * g)) * ψ (-(a * u))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) =
    ψ (a * x) * ∫ u, φ (unipotentGL2 u * g) * ψ (-(a * u))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
  simp_rw [hint]
  rw [integral_const_mul, integral_cond_adelicBox_comp_add_right F G hG x]

theorem integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper₁ : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ₁ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ₁ (unipotentGL2 u * g))
    (hcont₁ : Continuous fun x : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 x * g))
    (hcont₂ : Continuous fun x : AdeleRing (𝓞 F) F => φ₂ (unipotentGL2 x * g))
    (hbdd₂ : ∃ C : ℝ, ∀ x : AdeleRing (𝓞 F) F, ‖φ₂ (unipotentGL2 x * g)‖ ≤ C)
    (hsum₁ : Summable fun α : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g‖) :
    ∫ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (φ₂ (unipotentGL2 x * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g *
        (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₂ α g) := by
  haveI : Countable F := countable_numberField F
  have hψ1 : ∀ y, ‖ψ y‖ = 1 := NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hν
  have hνeq : (productionPinsOf F D U gen (adelicBox F)).ν = ν := rfl
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_cond_adelicBox F
  set W₁ : F → ℂ := fun α => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g with hW₁
  set W₂ : F → ℂ := fun α => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₂ α g with hW₂
  set h₂ : AdeleRing (𝓞 F) F → ℂ := fun x => φ₂ (unipotentGL2 x * g) with hh₂
  obtain ⟨C, hC⟩ := hbdd₂
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)

  have hA : ∀ x : AdeleRing (𝓞 F) F,
      HasSum (fun α : F => ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * W₁ α) (φ₁ (unipotentGL2 x * g)) := by
    intro x
    have hcov : ∀ α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α (unipotentGL2 x * g) =
        ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * W₁ α :=
      fun α => whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant φ₁ g hper₁ α x
    have hcontx : Continuous fun y : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 y * (unipotentGL2 x * g)) := by
      have : (fun y : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 y * (unipotentGL2 x * g))) =
          (fun y => φ₁ (unipotentGL2 y * g)) ∘ fun y => y + x := by
        funext y; simp only [Function.comp, ← mul_assoc, ← unipotentGL2_add]
      rw [this]; exact hcont₁.comp (continuous_add_const x)
    have hsumx : Summable fun α : F => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α (unipotentGL2 x * g) := by
      refine Summable.of_norm ?_
      refine hsum₁.congr fun α => ?_
      rw [hcov α, norm_mul, hψ1, one_mul]
    have := AutomorphicForm.hasSum_whittakerCoefficient F D U gen ψ hψ φ₁ (unipotentGL2 x * g) hcontx hsumx
    simpa only [hcov] using this

  have hB : ∀ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (h₂ x) =
      ∑' α : F, W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x)) := by
    intro x
    rw [← (hA x).tsum_eq, ← tsum_mul_right]
    exact tsum_congr fun α => by ring

  have hmeas : ∀ α : F, AEStronglyMeasurable
      (fun x => W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))) ν := by
    intro α
    refine (continuous_const.mul ((hψ.continuous.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_conj.comp hcont₂))).aestronglyMeasurable
  have hbound : ∀ (α : F) (x : AdeleRing (𝓞 F) F),
      ‖W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))‖ ≤ ‖W₁ α‖ * C := by
    intro α x
    rw [norm_mul, norm_mul, hψ1, one_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
  have hint : ∀ α : F, Integrable
      (fun x => W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))) ν :=
    fun α => (integrable_const (‖W₁ α‖ * C)).mono' (hmeas α) (Filter.Eventually.of_forall (hbound α))
  have hsumint : Summable fun α : F =>
      ∫ x, ‖W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun α => integral_nonneg fun x => norm_nonneg _) (fun α => ?_)
      (hsum₁.mul_right C)
    calc ∫ x, ‖W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x))‖ ∂ν
        ≤ ∫ x, ‖W₁ α‖ * C ∂ν := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall (hbound α))
      _ = ‖W₁ α‖ * C := by simp

  have hC' : ∀ α : F, ∫ x, ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x) ∂ν =
      (starRingEnd ℂ) (W₂ α) := by
    intro α
    have : W₂ α = ∫ x, h₂ x * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂ν := rfl
    rw [this, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, addChar_neg_eq_conj F ψ hψ1, Complex.conj_conj]
    ring

  rw [hνeq]
  calc ∫ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (φ₂ (unipotentGL2 x * g)) ∂ν
      = ∫ x, ∑' α : F, W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x)) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hB)
    _ = ∑' α : F, ∫ x, W₁ α * (ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) * (starRingEnd ℂ) (h₂ x)) ∂ν :=
        (integral_tsum_of_summable_integral_norm hint hsumint).symm
    _ = ∑' α : F, W₁ α * (starRingEnd ℂ) (W₂ α) := by
        refine tsum_congr fun α => ?_
        rw [integral_const_mul, hC' α]

end RS9P
p2m_reactivate "P2MW.S_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj.RS9P"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper₁ : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ₁ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ₁ (unipotentGL2 u * g))
    (hcont₁ : Continuous fun x : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 x * g))
    (hcont₂ : Continuous fun x : AdeleRing (𝓞 F) F => φ₂ (unipotentGL2 x * g))
    (hbdd₂ : ∃ C : ℝ, ∀ x : AdeleRing (𝓞 F) F, ‖φ₂ (unipotentGL2 x * g)‖ ≤ C)
    (hsum₁ : Summable fun α : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g‖) :
    ∫ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (φ₂ (unipotentGL2 x * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g *
        (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₂ α g) :=
  RS9P.integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj F D U gen ψ hψ φ₁ φ₂ g hper₁ hcont₁ hcont₂ hbdd₂ hsum₁

end S_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj (solution)
