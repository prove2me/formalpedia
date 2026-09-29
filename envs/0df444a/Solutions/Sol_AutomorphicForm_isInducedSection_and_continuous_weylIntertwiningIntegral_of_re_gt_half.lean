-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d742a4c8-7bac-567e-8d2f-76d6e13a0dd8

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight AutomorphicForm
open scoped NNReal Topology Pointwise

noncomputable section

namespace R1SlabMI

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

scoped instance regular_adelicAddHaar :
    @Measure.Regular 𝔸 (adeleBorel (𝓞 F) F) _ (adelicAddHaar (𝓞 F) F) := by
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  show Measure.Regular (Measure.addHaar)
  infer_instance

theorem integral_comp_units_mul (u : 𝔸ˣ) (f : 𝔸 → ℂ) :
    letI := adeleBorel (𝓞 F) F
    ∫ x, f ((u : 𝔸) * x) ∂(adelicAddHaar (𝓞 F) F)
      = ((distribHaarChar 𝔸 u : ℝ≥0) : ℝ)⁻¹ • ∫ x, f x ∂(adelicAddHaar (𝓞 F) F) := by
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  set μ := adelicAddHaar (𝓞 F) F with hμ
  have hmap : Measure.map (fun x : 𝔸 => (u : 𝔸) * x) μ = (distribHaarChar 𝔸 u)⁻¹ • μ := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply]
    have hpre : (fun x : 𝔸 => (u : 𝔸) * x) ⁻¹' s = u⁻¹ • s := by
      ext x
      simp only [Set.mem_preimage]
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
    rw [hpre, ← distribHaarChar_mul μ u⁻¹ s, map_inv]
    rfl
  set e : 𝔸 ≃ᵐ 𝔸 := (Homeomorph.smul u).toMeasurableEquiv with hedef
  have he : (e : 𝔸 → 𝔸) = fun x => (u : 𝔸) * x := by
    funext x; rfl
  calc ∫ x, f ((u : 𝔸) * x) ∂μ
      = ∫ x, f (e x) ∂μ := by rw [he]
    _ = ∫ y, f y ∂(Measure.map e μ) := (integral_map_equiv e f).symm
    _ = ∫ y, f y ∂((distribHaarChar 𝔸 u)⁻¹ • μ) := by rw [he, hmap]
    _ = ((distribHaarChar 𝔸 u : ℝ≥0) : ℝ)⁻¹ • ∫ x, f x ∂μ := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv]

section Diag

variable {A : Type*} [CommRing A]

def diagGL (p q : Aˣ) : GL (Fin 2) A where
  val := !![(p : A), 0; 0, (q : A)]
  inv := !![((p⁻¹ : Aˣ) : A), 0; 0, ((q⁻¹ : Aˣ) : A)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diagGL_val (p q : Aˣ) :
    ((diagGL p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(p : A), 0; 0, (q : A)] := rfl

theorem diagGL_mem_borelSubgroup (p q : Aˣ) : diagGL p q ∈ borelSubgroup A := by
  show ((diagGL p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  simp

theorem borelDiagFst_diagGL (p q : Aˣ) :
    borelDiagFst (⟨diagGL p q, diagGL_mem_borelSubgroup p q⟩ : ↥(borelSubgroup A)) = p :=
  Units.ext rfl

theorem borelDiagSnd_diagGL (p q : Aˣ) :
    borelDiagSnd (⟨diagGL p q, diagGL_mem_borelSubgroup p q⟩ : ↥(borelSubgroup A)) = q :=
  Units.ext rfl

end Diag

variable {F}

theorem adelicWeyl_inv_val :
    (((adelicWeyl (𝓞 F) F)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, 0] := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]
  ext i j
  rw [globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

theorem weylInv_mul_unipotent_mul_borel (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F)
    (x : 𝔸) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * b
      = diagGL (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))
          (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))
        * ((adelicWeyl (𝓞 F) F)⁻¹
          * unipotentGL2
              (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : 𝔸ˣ)
                  * (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 1
                + ((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : 𝔸ˣ)
                  * (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 * x)) := by
  have hb0 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := hb
  have ha : (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 0
      * (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : 𝔸ˣ) : 𝔸) = 1 :=
    (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))).mul_inv
  apply Units.ext
  simp only [Units.val_mul, adelicWeyl_inv_val, unipotentGL2_coe, diagGL_val,
    borelDiagFst_apply_val, borelDiagSnd_apply_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb0]
  linear_combination (-((b : Matrix (Fin 2) (Fin 2) 𝔸) 0 1
    + (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 * x)) * ha

theorem weylIntertwiningIntegral_borel_mul (χ₁ χ₂ : 𝔸ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    letI := adeleBorel (𝓞 F) F
    weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ (b * g)
      = ((χ₁ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((χ₂ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * (((distribHaarChar 𝔸
              ((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹
                * borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝ≥0) : ℝ) : ℂ)⁻¹
        * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  set a : 𝔸ˣ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with ha
  set d : 𝔸ˣ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with hd
  set c : 𝔸 := (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 with hc
  have hd' : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 = (d : 𝔸) := rfl
  have hpt : ∀ x : 𝔸,
      φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (b * g))
        = ((χ₁ d : ℂˣ) : ℂ) * ((χ₂ a : ℂˣ) : ℂ)
          * φ ((adelicWeyl (𝓞 F) F)⁻¹
              * unipotentGL2 ((a⁻¹ : 𝔸ˣ) * c + ((a⁻¹ * d : 𝔸ˣ) : 𝔸) * x) * g) := by
    intro x
    rw [← mul_assoc, weylInv_mul_unipotent_mul_borel b hb x, mul_assoc,
      hφ _ (diagGL_mem_borelSubgroup d a), borelDiagFst_diagGL, borelDiagSnd_diagGL, hd',
      Units.val_mul, mul_assoc ((a⁻¹ : 𝔸ˣ) : 𝔸) (d : 𝔸) x]
  unfold weylIntertwiningIntegral
  simp_rw [hpt]
  rw [integral_const_mul]
  have hdil := integral_comp_units_mul F (a⁻¹ * d)
    (fun y => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 ((a⁻¹ : 𝔸ˣ) * c + y) * g))
  have htr : ∫ y, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 ((a⁻¹ : 𝔸ˣ) * c + y) * g)
      ∂(adelicAddHaar (𝓞 F) F)
      = ∫ y, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 y * g) ∂(adelicAddHaar (𝓞 F) F) :=
    integral_add_left_eq_self (μ := adelicAddHaar (𝓞 F) F)
      (fun y => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 y * g)) ((a⁻¹ : 𝔸ˣ) * c)
  rw [hdil, htr, Complex.real_smul, Complex.ofReal_inv]
  ring

theorem factor_eq (α : 𝔸ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαΔ : ∀ t : 𝔸ˣ, ((α t : ℝˣ) : ℝ) = ((distribHaarChar 𝔸 t : ℝ≥0) : ℝ))
    (μ ν : 𝔸ˣ →* ℂˣ) (s : ℂ) (a d : 𝔸ˣ) :
    ((etaFst μ α hα s d : ℂˣ) : ℂ) * ((etaSnd ν α hα s a : ℂˣ) : ℂ)
        * (((distribHaarChar 𝔸 (a⁻¹ * d) : ℝ≥0) : ℝ) : ℂ)⁻¹
      = ((etaFst ν α hα (-s) a : ℂˣ) : ℂ) * ((etaSnd μ α hα (-s) d : ℂˣ) : ℂ) := by
  have haC : (((α a : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα a).ne'
  have hdC : (((α d : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα d).ne'
  have hmod : (((distribHaarChar 𝔸 (a⁻¹ * d) : ℝ≥0) : ℝ) : ℂ)⁻¹
      = (((α a : ℝˣ) : ℝ) : ℂ) ^ (1 : ℂ) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (-1 : ℂ) := by
    rw [← hαΔ, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, Complex.ofReal_mul,
      Complex.ofReal_inv, mul_inv, inv_inv, Complex.cpow_one, Complex.cpow_neg_one]
  rw [hmod, etaFst_apply, etaSnd_apply, etaFst_apply, etaSnd_apply]
  simp only [Units.val_mul, cpowChar_apply_val]
  have e1 : (((α d : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (-1 : ℂ)
      = (((α d : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2)) := by
    rw [← Complex.cpow_add _ _ hdC]; congr 1; ring
  have e2 : (((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α a : ℝˣ) : ℝ) : ℂ) ^ (1 : ℂ)
      = (((α a : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2) := by
    rw [← Complex.cpow_add _ _ haC]; congr 1; ring
  calc ((μ d : ℂˣ) : ℂ) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)
        * (((ν a : ℂˣ) : ℂ) * (((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)))
        * ((((α a : ℝˣ) : ℝ) : ℂ) ^ (1 : ℂ) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (-1 : ℂ))
      = ((ν a : ℂˣ) : ℂ) * ((((α a : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α a : ℝˣ) : ℝ) : ℂ) ^ (1 : ℂ))
        * (((μ d : ℂˣ) : ℂ) * ((((α d : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (-1 : ℂ))) := by
        ring
    _ = ((ν a : ℂˣ) : ℂ) * (((α a : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2)
        * (((μ d : ℂˣ) : ℂ) * (((α d : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2))) := by rw [e1, e2]

variable (F)

theorem main :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    letI := adeleBorel (𝓞 F) F
    IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s))
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) ∧
      Continuous (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) := by
  intro α hα μ ν hμ hν s hs φ hφ hφc
  letI : MeasurableSpace 𝔸 := adeleBorel (𝓞 F) F
  haveI : BorelSpace 𝔸 := borelSpace_adeleBorel (𝓞 F) F
  have hαΔ : ∀ t : 𝔸ˣ, ((α t : ℝˣ) : ℝ) = ((distribHaarChar 𝔸 t : ℝ≥0) : ℝ) := fun t => rfl
  set M : AdelicGL2 (𝓞 F) F → ℂ := weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ
    with hM
  refine ⟨?_, ?_⟩
  ·
    intro b hb g
    have h := weylIntertwiningIntegral_borel_mul (etaFst μ α hα s) (etaSnd ν α hα s) φ hφ b hb g
    rw [hM, h, ← factor_eq α hα hαΔ μ ν s]
  ·
    set σ : ℝ := s.re with hσ
    obtain ⟨Cφ, hCφ0, hCφ⟩ :=
      AutomorphicForm.exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hα μ ν hμ hν
        s φ hφ hφc
    obtain ⟨-, h1u, hsph⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
    set h : AdelicGL2 (𝓞 F) F → ℂ := fun g => ((adelicHeight F g : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)
      with hh
    have hsphσ : IsInducedSection (𝓞 F) F (etaFst 1 α hα (σ : ℂ)) (etaSnd 1 α hα (σ : ℂ)) h :=
      hsph hα (σ : ℂ)
    have hnorm_h : ∀ g, ‖h g‖ = adelicHeight F g ^ (σ + 1 / 2) := by
      intro g
      simp only [hh]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos g)]
      congr 1
      simp [Complex.add_re]
    have hHc := NumberField.AdelicHeight.continuous_adelicHeight F
    have hh_cont : Continuous h := by
      simp only [hh]
      refine Continuous.cpow ?_ continuous_const ?_
      · exact Complex.continuous_ofReal.comp hHc
      · intro g
        exact Or.inl (by simpa using adelicHeight_pos g)
    have hσ' : 1 / 2 < ((σ : ℂ)).re := by simpa [hσ] using hs
    have hwn : Continuous fun x : 𝔸 => (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x :=
      continuous_const.mul AutomorphicForm.continuous_unipotentGL2

    haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
      NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
    refine continuous_iff_continuousAt.2 fun g₀ => ?_

    obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
    obtain ⟨κ, K, hκ, hdist⟩ :=
      NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F C hCc
    have hK0 : 0 ≤ K := by
      have := (hdist 1 1 (mem_of_mem_nhds hC1)).2
      rw [one_mul] at this
      have hpos := adelicHeight_pos (F := F) 1
      nlinarith

    have hnhds : {g : AdelicGL2 (𝓞 F) F | g₀⁻¹ * g ∈ C} ∈ 𝓝 g₀ := by
      have hc : Continuous fun g : AdelicGL2 (𝓞 F) F => g₀⁻¹ * g := continuous_const.mul continuous_id
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hC1)

    set bound : 𝔸 → ℝ := fun x =>
      Cφ * K ^ (σ + 1 / 2) * ‖h ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g₀)‖ with hbound
    have hint : Integrable (fun x : 𝔸 => h ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g₀))
        (adelicAddHaar (𝓞 F) F) :=
      AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 h1u h1u (σ : ℂ) hσ'
        h hsphσ hh_cont g₀
    have hbound_int : Integrable bound (adelicAddHaar (𝓞 F) F) := by
      simp only [hbound]
      exact (hint.norm.const_mul (Cφ * K ^ (σ + 1 / 2)))
    show ContinuousAt (fun g => ∫ x, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
      ∂(adelicAddHaar (𝓞 F) F)) g₀
    refine continuousAt_of_dominated (bound := bound) ?_ ?_ hbound_int ?_
    · refine Filter.Eventually.of_forall fun g => ?_
      exact (hφc.comp (hwn.mul continuous_const)).aestronglyMeasurable
    · filter_upwards [hnhds] with g hg
      refine Filter.Eventually.of_forall fun x => ?_
      have hy : g = g₀ * (g₀⁻¹ * g) := by group
      set y := g₀⁻¹ * g with hy'
      have hle1 := hCφ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
      have hH : adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)
          ≤ K * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g₀) := by
        have := (hdist ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g₀) y hg).2
        rw [hy]
        simpa [mul_assoc] using this
      have hσpos : 0 ≤ σ + 1 / 2 := by linarith
      calc ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)‖
          ≤ Cφ * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ^ (σ + 1 / 2) := hle1
        _ ≤ Cφ * (K * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g₀)) ^ (σ + 1 / 2) := by
            gcongr
            exact (adelicHeight_pos _).le
        _ = bound x := by
            simp only [hbound]
            rw [Real.mul_rpow hK0 (adelicHeight_pos _).le, hnorm_h]
            ring
    · refine Filter.Eventually.of_forall fun x => ?_
      exact (hφc.comp (continuous_const.mul continuous_id)).continuousAt

end R1SlabMI
p2m_reactivate "P2MW.S_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half.R1SlabMI"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half.R1SlabMI"

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    letI := adeleBorel (𝓞 F) F
    IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s))
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) ∧
      Continuous (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) :=
  R1SlabMI.main F

end S_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half (solution)
