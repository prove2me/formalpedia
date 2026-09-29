-- Prove2me | solution 1 for AutomorphicForm.exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6146fb86-cdff-5cee-9c44-97c7b66415ea

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentAverage_diagOne
import Theorems.Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul
import Theorems.Thm_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

noncomputable section

namespace C5K5b1

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [globalPoints, Matrix.GeneralLinearGroup.map_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

def yv (e : mixedEmbedding.mixedSpace F) (t : ℝ) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e), 0)

theorem yv_eq (e : mixedEmbedding.mixedSpace F) (t : ℝ) :
    yv F e t = @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e), 0) := rfl

theorem yv_zero (e : mixedEmbedding.mixedSpace F) : yv F e 0 = 0 := by
  rw [yv, zero_smul, map_zero]; rfl

def lam (a : F) (e : mixedEmbedding.mixedSpace F) (b : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) a⁻¹ * (b : AdeleRing (𝓞 F) F).1) * e)

theorem psi_mul_yv {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {a : F} (ha : a ≠ 0)
    (hψa : ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (e : mixedEmbedding.mixedSpace F) (b : (AdeleRing (𝓞 F) F)ˣ) (t : ℝ) :
    ψ ((b : AdeleRing (𝓞 F) F) * yv F e t) = Complex.exp ((2 * Real.pi * (t * lam F a e b) : ℝ) * Complex.I) := by
  set X : InfiniteAdeleRing F := algebraMap F (InfiniteAdeleRing F) a⁻¹ *
    ((b : AdeleRing (𝓞 F) F).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e)) with hXdef
  have hprod : (b : AdeleRing (𝓞 F) F) * yv F e t = (algebraMap F (InfiniteAdeleRing F) a * X, 0) := by
    refine Prod.ext ?_ ?_
    · show (b : AdeleRing (𝓞 F) F).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e) = _
      rw [hXdef, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
    · show (b : AdeleRing (𝓞 F) F).2 * 0 = 0
      rw [mul_zero]
  have hX : InfiniteAdeleRing.ringEquiv_mixedSpace F X
      = t • (InfiniteAdeleRing.ringEquiv_mixedSpace F
          (algebraMap F (InfiniteAdeleRing F) a⁻¹ * (b : AdeleRing (𝓞 F) F).1) * e) := by
    rw [hXdef, ← mul_assoc, map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F), RingEquiv.apply_symm_apply,
      Algebra.mul_smul_comm]
  have hTr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F X)
      = t * lam F a e b := by
    rw [hX, map_smul, smul_eq_mul, lam]
  rw [hprod, hψa X, Real.fourierChar_apply, hTr]

def mult (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (B : AdeleRing (𝓞 F) F → ℂ) (b : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ∫ x, B x * ψ ((b : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)

theorem mult_eq_coef_mul_mult {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {a : F} (ha : a ≠ 0)
    (hψa : ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (e : mixedEmbedding.mixedSpace F)
    {B B' : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (hB' : B' ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (hd : ∀ (x : AdeleRing (𝓞 F) F) (t : ℝ), HasDerivAt (fun s : ℝ => B (x - yv F e s)) (B' (x - yv F e t)) t)
    (b : (AdeleRing (𝓞 F) F)ˣ) :
    mult F ψ B' b = ((2 * Real.pi * lam F a e b : ℝ) : ℂ) * Complex.I * mult F ψ B b := by

  have hψc : Continuous fun x : AdeleRing (𝓞 F) F => ψ ((b : AdeleRing (𝓞 F) F) * x) :=
    hψ.continuous.comp (continuous_const.mul continuous_id)
  have hψ1 : ∀ x : AdeleRing (𝓞 F) F, ‖ψ ((b : AdeleRing (𝓞 F) F) * x)‖ ≤ 1 := fun x =>
    (NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _).le
  have hint : ∀ (B₀ : AdeleRing (𝓞 F) F → ℂ), B₀ ∈ NumberField.AdelicFourier.schwartzBruhat F → ∀ t : ℝ,
      Integrable (fun x => B₀ (x - yv F e t) * ψ ((b : AdeleRing (𝓞 F) F) * x)) (adelicAddHaar (𝓞 F) F) := by
    intro B₀ hB₀ t
    have h1 : Integrable (fun x => B₀ (x - yv F e t)) (adelicAddHaar (𝓞 F) F) :=
      (NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat F (adelicAddHaar (𝓞 F) F) hB₀).comp_sub_right _
    exact h1.mul_bdd hψc.aestronglyMeasurable (ae_of_all _ hψ1)

  obtain ⟨bound, hbound_int, hbound⟩ :=
    NumberField.AdelicFourier.exists_integrable_forall_norm_comp_sub_smul_le F (adelicAddHaar (𝓞 F) F) hB' e
  have hderiv : HasDerivAt (fun t : ℝ => ∫ x, B (x - yv F e t) * ψ ((b : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F))
      (∫ x, B' (x - yv F e 0) * ψ ((b : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := adelicAddHaar (𝓞 F) F) (x₀ := (0 : ℝ))
      (F := fun t x => B (x - yv F e t) * ψ ((b : AdeleRing (𝓞 F) F) * x))
      (F' := fun t x => B' (x - yv F e t) * ψ ((b : AdeleRing (𝓞 F) F) * x))
      (bound := bound) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
      (Filter.Eventually.of_forall fun t => (hint B hB t).aestronglyMeasurable) (hint B hB 0)
      (hint B' hB' 0).aestronglyMeasurable ?_ hbound_int ?_).2
    · refine ae_of_all _ fun x t ht => ?_
      rw [norm_mul]
      calc ‖B' (x - yv F e t)‖ * ‖ψ ((b : AdeleRing (𝓞 F) F) * x)‖ ≤ bound x * 1 :=
            mul_le_mul (hbound x t ht) (hψ1 x) (norm_nonneg _) ((norm_nonneg _).trans (hbound x t ht))
        _ = bound x := mul_one _
    · exact ae_of_all _ fun x t _ => (hd x t).mul_const _
  simp only [yv_zero, sub_zero] at hderiv

  have hI : (fun t : ℝ => ∫ x, B (x - yv F e t) * ψ ((b : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F))
      = fun t => Complex.exp ((2 * Real.pi * (t * lam F a e b) : ℝ) * Complex.I) * mult F ψ B b := by
    funext t
    calc ∫ x, B (x - yv F e t) * ψ ((b : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)
        = ∫ x, B x * ψ ((b : AdeleRing (𝓞 F) F) * (x + yv F e t)) ∂(adelicAddHaar (𝓞 F) F) := by
          rw [← integral_add_left_eq_self
            (fun x => B x * ψ ((b : AdeleRing (𝓞 F) F) * (x + yv F e t))) (-(yv F e t))]
          simp only [neg_add_eq_sub, sub_add_cancel]
      _ = ∫ x, (B x * ψ ((b : AdeleRing (𝓞 F) F) * x)) * ψ ((b : AdeleRing (𝓞 F) F) * yv F e t)
            ∂(adelicAddHaar (𝓞 F) F) := by
          congr 1; funext x; rw [mul_add, AddChar.map_add_eq_mul, mul_assoc]
      _ = (∫ x, B x * ψ ((b : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)) *
            ψ ((b : AdeleRing (𝓞 F) F) * yv F e t) := integral_mul_const _ _
      _ = _ := by rw [psi_mul_yv F ha hψa e b t, mul_comm]; rfl
  have hderiv2 : HasDerivAt (fun t : ℝ => ∫ x, B (x - yv F e t) * ψ ((b : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F))
      (Complex.exp ((2 * Real.pi * ((0 : ℝ) * lam F a e b) : ℝ) * Complex.I) *
        (((2 * Real.pi * lam F a e b : ℝ) : ℂ) * Complex.I) * mult F ψ B b) 0 := by
    rw [hI]
    refine HasDerivAt.mul_const ?_ _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * (t * lam F a e b)) (2 * Real.pi * lam F a e b) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (lam F a e b)).const_mul (2 * Real.pi)
    exact ((h1.ofReal_comp).mul_const Complex.I).cexp
  have heq := hderiv.unique hderiv2
  rw [zero_mul, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at heq
  exact heq

theorem main
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (hinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), G (globalPoints (𝓞 F) F γ * g) = G g)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (a : F) (ha : a ≠ 0)
    (hψa : ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (e : mixedEmbedding.mixedSpace F) :
    ∃ B' : AdeleRing (𝓞 F) F → ℂ, B' ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      ∀ (Φ' : AdelicGL2 (𝓞 F) F → ℂ),
        (∀ h : AdelicGL2 (𝓞 F) F, Φ' h = (letI := adeleBorel (𝓞 F) F
          ∫ x, B' x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) →
        ∀ b : (AdeleRing (𝓞 F) F)ˣ,
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ Φ' 1 (diagOne b) =
            ((2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
                (InfiniteAdeleRing.ringEquiv_mixedSpace F
                    (algebraMap F (InfiniteAdeleRing F) a⁻¹ * (b : AdeleRing (𝓞 F) F).1) * e) : ℝ) : ℂ) *
              Complex.I *
            whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ Φ 1 (diagOne b) := by
  obtain ⟨B', hB', hd⟩ := NumberField.AdelicFourier.exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul F hB e
  refine ⟨B', hB', fun Φ' hΦ' b => ?_⟩
  have hGleft : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      G (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = G g := fun β g => by
    rw [← globalPoints_unipotentGL2]; exact hinv _ g
  have hW := AutomorphicForm.whittakerCoefficient_unipotentAverage_diagOne F D U gen ψ hψ G hcont hMG hGleft
    B hB Φ hΦ 1 b
  have hW' := AutomorphicForm.whittakerCoefficient_unipotentAverage_diagOne F D U gen ψ hψ G hcont hMG hGleft
    B' hB' Φ' hΦ' 1 b
  have hm : ∀ B₀ : AdeleRing (𝓞 F) F → ℂ,
      (letI := adeleBorel (𝓞 F) F
        ∫ x, B₀ x * ψ (algebraMap F (AdeleRing (𝓞 F) F) 1 * ((b : AdeleRing (𝓞 F) F) * x)) ∂(adelicAddHaar (𝓞 F) F))
        = mult F ψ B₀ b := fun B₀ => by
    simp only [map_one, one_mul]; rfl
  rw [hW', hW, hm, hm, mult_eq_coef_mul_mult F hψ ha hψa e hB hB' (fun x t => hd x t) b, mul_assoc]
  rfl

end C5K5b1

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (hinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), G (globalPoints (𝓞 F) F γ * g) = G g)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (a : F) (ha : a ≠ 0)
    (hψa : ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (e : mixedEmbedding.mixedSpace F) :
    ∃ B' : AdeleRing (𝓞 F) F → ℂ, B' ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      ∀ (Φ' : AdelicGL2 (𝓞 F) F → ℂ),
        (∀ h : AdelicGL2 (𝓞 F) F, Φ' h = (letI := adeleBorel (𝓞 F) F
          ∫ x, B' x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) →
        ∀ b : (AdeleRing (𝓞 F) F)ˣ,
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ Φ' 1 (diagOne b) =
            ((2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
                (InfiniteAdeleRing.ringEquiv_mixedSpace F
                    (algebraMap F (InfiniteAdeleRing F) a⁻¹ * (b : AdeleRing (𝓞 F) F).1) * e) : ℝ) : ℂ) *
              Complex.I *
            whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ Φ 1 (diagOne b) :=
  C5K5b1.main F D U gen G hcont hMG hinv B hB Φ hΦ ψ hψ a ha hψa e

end S_AutomorphicForm_exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul (solution)
