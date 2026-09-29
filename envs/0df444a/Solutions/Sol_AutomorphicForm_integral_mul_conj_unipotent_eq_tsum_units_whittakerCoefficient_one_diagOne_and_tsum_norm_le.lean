-- Prove2me | solution 1 for AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8f807e80-e550-51d1-8959-14e5c5a2f644

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Theorems.Thm_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le.AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGlobalAddChar whittakerCoefficient productionPinsOf AdelicGL2 globalPoints unipotentGL2 unipotentGL2_coe unipotentGL2_add globalPoints_apply integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul sum_norm_whittakerCoefficient_sq_le_integral_norm_sq"
p2m_open "AutomorphicForm"

namespace FibreParsevalC9B

variable (F : Type) [Field F] [NumberField F]

theorem continuous_unipotentGL2 :
    Continuous (fun y : AdeleRing (𝓞 F) F => (unipotentGL2 y : AdelicGL2 (𝓞 F) F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ y : AdeleRing (𝓞 F) F, (↑((unipotentGL2 y : AdelicGL2 (𝓞 F) F)⁻¹) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem slice_periodic (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g : AdelicGL2 (𝓞 F) F) (β : F) (u : AdeleRing (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ]

theorem slice_bounded (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : AdeleRing (𝓞 F) F => φ (unipotentGL2 u * g))
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g)) :
    ∃ C : ℝ, ∀ u : AdeleRing (𝓞 F) F, ‖φ (unipotentGL2 u * g)‖ ≤ C := by
  obtain ⟨K, hK, hbox⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨β, hβ, -⟩ := existsUnique_algebraMap_add_mem_adelicBox F u
  rw [← hper β u]
  exact hC _ (hbox hβ)

theorem main
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      x (globalPoints (𝓞 F) F γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      y (globalPoints (𝓞 F) F γ * g) = y g)
    (hxc : Continuous x) (hyc : Continuous y)
    (hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
    (hxW : ∀ g, Summable fun a : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
    (g : AdelicGL2 (𝓞 F) F) :
    (Summable fun a : Fˣ =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ∧
    (∑' a : Fˣ,
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ≤
      Real.sqrt (∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) *
        Real.sqrt (∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) ∧
    ∫ u, x (unipotentGL2 u * g) * (starRingEnd ℂ) (y (unipotentGL2 u * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' a : Fˣ,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
            (globalPoints (𝓞 F) F (diagOne a) * g) *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
            (globalPoints (𝓞 F) F (diagOne a) * g)) := by
  classical
  set pins := productionPinsOf F D U gen (adelicBox F) with hpins

  have hperx := slice_periodic F x hxG g
  have hpery := slice_periodic F y hyG g
  have hcx : Continuous fun u : AdeleRing (𝓞 F) F => x (unipotentGL2 u * g) :=
    hxc.comp ((continuous_unipotentGL2 F).mul continuous_const)
  have hcy : Continuous fun u : AdeleRing (𝓞 F) F => y (unipotentGL2 u * g) :=
    hyc.comp ((continuous_unipotentGL2 F).mul continuous_const)
  have hbddy := slice_bounded F y g hcy hpery

  have hWx : ∀ a : Fˣ, whittakerCoefficient F pins ψ x (a : F) g =
      whittakerCoefficient F pins ψ x 1 (globalPoints (𝓞 F) F (diagOne a) * g) := by
    intro a
    have h := whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul F D U gen ψ hψ x hxG (a : F)
      a.ne_zero g
    have ha : Units.mk0 (a : F) a.ne_zero = a := Units.ext rfl
    rw [ha] at h
    exact h
  have hWy : ∀ a : Fˣ, whittakerCoefficient F pins ψ y (a : F) g =
      whittakerCoefficient F pins ψ y 1 (globalPoints (𝓞 F) F (diagOne a) * g) := by
    intro a
    have h := whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul F D U gen ψ hψ y hyG (a : F)
      a.ne_zero g
    have ha : Units.mk0 (a : F) a.ne_zero = a := Units.ext rfl
    rw [ha] at h
    exact h

  set X : ℝ := ∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂pins.ν with hX
  set Y : ℝ := ∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂pins.ν with hY
  have hX0 : 0 ≤ X := integral_nonneg fun u => sq_nonneg _
  have hY0 : 0 ≤ Y := integral_nonneg fun u => sq_nonneg _
  set p : Fˣ → ℝ := fun a => ‖whittakerCoefficient F pins ψ x 1 (globalPoints (𝓞 F) F (diagOne a) * g)‖ with hp
  set q : Fˣ → ℝ := fun a => ‖whittakerCoefficient F pins ψ y 1 (globalPoints (𝓞 F) F (diagOne a) * g)‖ with hq
  have hBx : ∀ A : Finset Fˣ, ∑ a ∈ A, p a ^ 2 ≤ X := by
    intro A
    have h := sum_norm_whittakerCoefficient_sq_le_integral_norm_sq F D U gen ψ hψ x g hcx (A.image (Units.val : Fˣ → F))
    rw [Finset.sum_image (fun a _ b _ hab => Units.ext hab)] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) h
    rw [hp, hWx]
  have hBy : ∀ A : Finset Fˣ, ∑ a ∈ A, q a ^ 2 ≤ Y := by
    intro A
    have h := sum_norm_whittakerCoefficient_sq_le_integral_norm_sq F D U gen ψ hψ y g hcy (A.image (Units.val : Fˣ → F))
    rw [Finset.sum_image (fun a _ b _ hab => Units.ext hab)] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) h
    rw [hq, hWy]
  have hnn : ∀ a, 0 ≤ p a * q a := fun a => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound : ∀ A : Finset Fˣ, ∑ a ∈ A, p a * q a ≤ Real.sqrt X * Real.sqrt Y := by
    intro A
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq A p q
    have h2 : (∑ a ∈ A, p a ^ 2) * (∑ a ∈ A, q a ^ 2) ≤ X * Y :=
      mul_le_mul (hBx A) (hBy A) (Finset.sum_nonneg fun a _ => sq_nonneg _) hX0
    calc ∑ a ∈ A, p a * q a = Real.sqrt ((∑ a ∈ A, p a * q a) ^ 2) :=
          (Real.sqrt_sq (Finset.sum_nonneg fun a _ => hnn a)).symm
      _ ≤ Real.sqrt (X * Y) := Real.sqrt_le_sqrt (hcs.trans h2)
      _ = Real.sqrt X * Real.sqrt Y := Real.sqrt_mul hX0 Y
  refine ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound, ?_⟩

  have hP := integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj F D U gen ψ hψ x y g hperx hcx hcy hbddy (hxW g)
  rw [hP]
  set f : F → ℂ := fun α => whittakerCoefficient F pins ψ x α g *
    (starRingEnd ℂ) (whittakerCoefficient F pins ψ y α g) with hf
  have hsupp : Function.support f ⊆ Set.range (Units.val : Fˣ → F) := by
    intro α hα
    by_cases h0 : α = 0
    · exfalso
      apply hα
      rw [hf, h0]
      simp only
      rw [hx0 g, zero_mul]
    · exact ⟨Units.mk0 α h0, rfl⟩
  have key := (Units.val_injective (α := F)).tsum_eq hsupp
  show ∑' α : F, f α = _
  rw [← key]
  exact tsum_congr fun a => by simp only [hf]; rw [hWx, hWy]

end FibreParsevalC9B

end AutomorphicForm

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      x (globalPoints (𝓞 F) F γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      y (globalPoints (𝓞 F) F γ * g) = y g)
    (hxc : Continuous x) (hyc : Continuous y)
    (hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
    (hxW : ∀ g, Summable fun a : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
    (g : AdelicGL2 (𝓞 F) F) :
    (Summable fun a : Fˣ =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ∧
    (∑' a : Fˣ,
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ≤
      Real.sqrt (∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) *
        Real.sqrt (∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) ∧
    ∫ u, x (unipotentGL2 u * g) * (starRingEnd ℂ) (y (unipotentGL2 u * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' a : Fˣ,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
            (globalPoints (𝓞 F) F (diagOne a) * g) *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
            (globalPoints (𝓞 F) F (diagOne a) * g)) :=
  AutomorphicForm.FibreParsevalC9B.main F D U gen ψ hψ x y hxG hyG hxc hyc hx0 hxW g

end S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le (solution)
