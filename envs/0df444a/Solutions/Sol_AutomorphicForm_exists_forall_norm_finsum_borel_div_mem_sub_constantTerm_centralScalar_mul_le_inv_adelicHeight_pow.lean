-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/550d43f4-d809-5d6c-88e5-2e942dae0159

import Theorems.Thm_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
import Theorems.Thm_MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap
import Theorems.Thm_NumberField_AdelicFourier_integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Set NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

open scoped ProbabilityTheory Pointwise

noncomputable section

namespace R4CuspPoissonA

section Ring

variable {R : Type*} [CommRing R]

def diagGL2 (t₁ t₂ : Rˣ) : GL (Fin 2) R where
  val := !![(t₁ : R), 0; 0, (t₂ : R)]
  inv := !![((t₁⁻¹ : Rˣ) : R), 0; 0, ((t₂⁻¹ : Rˣ) : R)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diagGL2_coe (t₁ t₂ : Rˣ) :
    (diagGL2 t₁ t₂ : Matrix (Fin 2) (Fin 2) R) = !![(t₁ : R), 0; 0, (t₂ : R)] := rfl

theorem diagGL2_inv (t₁ t₂ : Rˣ) : (diagGL2 t₁ t₂)⁻¹ = diagGL2 t₁⁻¹ t₂⁻¹ :=
  Units.ext rfl

theorem diagGL2_mul (a b c d : Rˣ) : diagGL2 a b * diagGL2 c d = diagGL2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def sliceScale (t₁ t₂ : Rˣ) : Rˣ := t₁⁻¹ * t₂

theorem unipotentGL2_inv (w : R) : (unipotentGL2 w)⁻¹ = unipotentGL2 (-w) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem unipotentGL2_apply_zero_one (w : R) :
    ((unipotentGL2 w : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = w := by
  simp [unipotentGL2_coe]

theorem diag_mul_unipotent_eq (ν τ : R) (t₁ t₂ d₁ d₂ : Rˣ) :
    diagGL2 d₁ d₂ * unipotentGL2 τ
      = (unipotentGL2 ν * diagGL2 t₁ t₂) *
          (unipotentGL2 (((sliceScale t₁ t₂ : Rˣ) : R) * (((d₁ * d₂⁻¹ : Rˣ) : R) * τ - ν)) *
            (diagGL2 d₁ d₂ * (diagGL2 t₁ t₂)⁻¹)) := by
  apply Units.ext
  have hT1 : (t₁ : R) * ((t₁⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t₁
  have hT2 : (t₂ : R) * ((t₂⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t₂
  have hD2 : (d₂ : R) * ((d₂⁻¹ : Rˣ) : R) = 1 := Units.mul_inv d₂
  rw [diagGL2_inv]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sliceScale, Units.val_mul]
    linear_combination (-(d₁ : R)) * hT1
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sliceScale, Units.val_mul]
    linear_combination
      (-(d₁ : R) * τ + ν * (d₂ : R) * ((t₂ : R) * ((t₂⁻¹ : Rˣ) : R))) * hT1
      + (-(d₁ : R) * τ * ((t₁ : R) * ((t₁⁻¹ : Rˣ) : R))) * hT2
      + (-(d₁ : R) * τ * ((t₁ : R) * ((t₁⁻¹ : Rˣ) : R)) * ((t₂ : R) * ((t₂⁻¹ : Rˣ) : R))) * hD2
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sliceScale, Units.val_mul]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, sliceScale, Units.val_mul]
    linear_combination (-(d₂ : R)) * hT2

theorem borel_inv_mul_diag_mul_unipotent (ν τ : R) (t₁ t₂ d₁ d₂ : Rˣ) :
    (unipotentGL2 ν * diagGL2 t₁ t₂)⁻¹ * (diagGL2 d₁ d₂ * unipotentGL2 τ)
      = unipotentGL2 (((sliceScale t₁ t₂ : Rˣ) : R) * (((d₁ * d₂⁻¹ : Rˣ) : R) * τ - ν)) *
          (diagGL2 d₁ d₂ * (diagGL2 t₁ t₂)⁻¹) := by
  rw [diag_mul_unipotent_eq ν τ t₁ t₂ d₁ d₂, inv_mul_cancel_left]

theorem diag_mul_unipotent (d₁ d₂ : Rˣ) (s : R) :
    diagGL2 d₁ d₂ * unipotentGL2 s = unipotentGL2 (((d₁ * d₂⁻¹ : Rˣ) : R) * s) * diagGL2 d₁ d₂ := by
  apply Units.ext
  have hD2 : (d₂ : R) * ((d₂⁻¹ : Rˣ) : R) = 1 := Units.mul_inv d₂
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]
    linear_combination (-(d₁ : R) * s) * hD2
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]

theorem inv_apply_one_zero {L : Type*} [Field L] (γ : GL (Fin 2) L)
    (h : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, h]

theorem isUnit_apply_of_apply_one_zero (b : GL (Fin 2) R)
    (h : (b : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    IsUnit ((b : Matrix (Fin 2) (Fin 2) R) 0 0) ∧ IsUnit ((b : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have hdet : IsUnit (b : Matrix (Fin 2) (Fin 2) R).det := (Matrix.isUnits_det_units b)
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  exact ⟨isUnit_of_mul_isUnit_left hdet, isUnit_of_mul_isUnit_right hdet⟩

theorem eq_unipotent_mul_diag_of_apply_one_zero (b : GL (Fin 2) R)
    (h : (b : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (w : R) (t₁ t₂ : Rˣ), b = unipotentGL2 w * diagGL2 t₁ t₂ ∧
      (t₁ : R) = (b : Matrix (Fin 2) (Fin 2) R) 0 0 ∧ (t₂ : R) = (b : Matrix (Fin 2) (Fin 2) R) 1 1 := by
  obtain ⟨h0, h1⟩ := isUnit_apply_of_apply_one_zero b h
  refine ⟨(b : Matrix (Fin 2) (Fin 2) R) 0 1 * ((h1.unit⁻¹ : Rˣ) : R), h0.unit, h1.unit, ?_,
    rfl, rfl⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagGL2, h]
  rw [mul_assoc, h1.val_inv_mul, mul_one]

theorem eq_diag_mul_unipotent_of_apply_one_zero (b : GL (Fin 2) R)
    (h : (b : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (w : R) (t₁ t₂ : Rˣ), b = diagGL2 t₁ t₂ * unipotentGL2 w ∧
      (t₁ : R) = (b : Matrix (Fin 2) (Fin 2) R) 0 0 ∧ (t₂ : R) = (b : Matrix (Fin 2) (Fin 2) R) 1 1 := by
  obtain ⟨w, t₁, t₂, hb, h1, h2⟩ := eq_unipotent_mul_diag_of_apply_one_zero b h
  refine ⟨((t₁⁻¹ * t₂ : Rˣ) : R) * w, t₁, t₂, ?_, h1, h2⟩
  rw [hb, diag_mul_unipotent, ← mul_assoc ((t₁ * t₂⁻¹ : Rˣ) : R), ← Units.val_mul]
  rw [show t₁ * t₂⁻¹ * (t₁⁻¹ * t₂) = 1 by rw [mul_mul_mul_comm, mul_inv_cancel, inv_mul_cancel, one_mul],
    Units.val_one, one_mul]

theorem diag_mul_mul_diag_apply (a d a' d' : Rˣ) (M : GL (Fin 2) R) (i j : Fin 2) :
    ((diagGL2 a d * M * diagGL2 a' d' : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j
      = ![(a : R), d] i * (M : Matrix (Fin 2) (Fin 2) R) i j * ![(a' : R), d'] j := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_mul_apply_diag (v : R) (b : GL (Fin 2) R)
    (h : (b : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ((unipotentGL2 v * b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0
        = (b : Matrix (Fin 2) (Fin 2) R) 0 0 ∧
      ((unipotentGL2 v * b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1
        = (b : Matrix (Fin 2) (Fin 2) R) 1 1 ∧
      ((unipotentGL2 v * b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, h]

end Ring

section Borel

variable (F : Type) [Field F]

def borelOf (p : Fˣ × Fˣ × F) : GL (Fin 2) F := diagGL2 p.1 p.2.1 * unipotentGL2 p.2.2

theorem borelOf_val (p : Fˣ × Fˣ × F) :
    (borelOf F p : Matrix (Fin 2) (Fin 2) F) = !![(p.1 : F), (p.1 : F) * p.2.2; 0, (p.2.1 : F)] := by
  ext i j
  simp only [borelOf, Units.val_mul, diagGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem borelOf_mem (p : Fˣ × Fˣ × F) : borelOf F p ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff, borelOf_val]
  rfl

theorem diag_ne_zero_of_mem {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) :
    (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det γ).ne_zero
  rw [Matrix.det_fin_two, (mem_borelSubgroup_iff F).1 hγ, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

def coordsOf (γ : borelSubgroup F) : Fˣ × Fˣ × F :=
  (Units.mk0 _ (diag_ne_zero_of_mem F γ.2).1, Units.mk0 _ (diag_ne_zero_of_mem F γ.2).2,
    ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 / ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0)

def borelEquiv : (Fˣ × Fˣ × F) ≃ borelSubgroup F where
  toFun p := ⟨borelOf F p, borelOf_mem F p⟩
  invFun := coordsOf F
  left_inv p := by
    obtain ⟨a, d, ξ⟩ := p
    simp only [coordsOf, borelOf_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine Prod.ext (Units.ext rfl) (Prod.ext (Units.ext rfl) ?_)
    show (a : F) * ξ / a = ξ
    field_simp
  right_inv γ := by
    obtain ⟨γ, hγ⟩ := γ
    have h00 := (diag_ne_zero_of_mem F hγ).1
    apply Subtype.ext
    apply Units.ext
    show (borelOf F (coordsOf F ⟨γ, hγ⟩) : Matrix (Fin 2) (Fin 2) F) = γ
    rw [borelOf_val]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · show (γ : Matrix (Fin 2) (Fin 2) F) 0 0 *
          ((γ : Matrix (Fin 2) (Fin 2) F) 0 1 / (γ : Matrix (Fin 2) (Fin 2) F) 0 0)
        = (γ : Matrix (Fin 2) (Fin 2) F) 0 1
      field_simp
    · exact ((mem_borelSubgroup_iff F).1 hγ).symm
    · rfl

theorem finsum_mem_borelSubgroup_eq {M : Type*} [AddCommMonoid M] (h : GL (Fin 2) F → M) :
    ∑ᶠ γ ∈ (borelSubgroup F : Set (GL (Fin 2) F)), h γ = ∑ᶠ p : Fˣ × Fˣ × F, h (borelOf F p) := by
  rw [← finsum_set_coe_eq_finsum_mem]
  exact (finsum_comp_equiv (borelEquiv F)
    (f := fun γ : ((borelSubgroup F : Set (GL (Fin 2) F)) : Type) => h γ)).symm

theorem finsum_mem_borelSubgroup_mul_right {M : Type*} [AddCommMonoid M] (h : GL (Fin 2) F → M)
    {b : GL (Fin 2) F} (hb : b ∈ borelSubgroup F) :
    ∑ᶠ γ ∈ (borelSubgroup F : Set (GL (Fin 2) F)), h (γ * b)
      = ∑ᶠ γ ∈ (borelSubgroup F : Set (GL (Fin 2) F)), h γ := by
  refine finsum_mem_eq_of_bijOn (fun γ => γ * b) ⟨?_, ?_, ?_⟩ fun _ _ => rfl
  · intro γ hγ
    exact (borelSubgroup F).mul_mem hγ hb
  · exact fun _ _ _ _ hxy => mul_right_cancel hxy
  · intro γ hγ
    exact ⟨γ * b⁻¹, (borelSubgroup F).mul_mem hγ ((borelSubgroup F).inv_mem hb), by group⟩

end Borel

section Descent

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

local notation "𝔸" => AdeleRing (𝓞 L) L
local notation "ι" => algebraMap L (AdeleRing (𝓞 L) L)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem sigmaAdelicAct_val_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j
      = (D.act σ : RingAut 𝔸) ((g : Matrix (Fin 2) (Fin 2) 𝔸) i j) := rfl

theorem sigmaAdelicAct_unipotentGL2 (t : 𝔸) :
    sigmaAdelicAct K L D σ (unipotentGL2 t) = unipotentGL2 ((D.act σ : RingAut 𝔸) t) := by
  apply Units.ext
  ext i j
  rw [sigmaAdelicAct_val_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem countable_numberField : Countable L :=
  (Module.finBasis ℚ L).equivFun.injective.countable

scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 L) L) := by
  haveI := countable_numberField L
  exact (Set.countable_range (algebraMap L (AdeleRing (𝓞 L) L))).to_subtype

def actEquiv : 𝔸 ≃ₜ+ 𝔸 :=
  { ((D.act σ : RingAut 𝔸) : 𝔸 ≃+* 𝔸).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      show Continuous (fun x => ((D.act σ : RingAut 𝔸) : 𝔸 ≃+* 𝔸).symm x)
      have h : ∀ x, ((D.act σ : RingAut 𝔸) : 𝔸 ≃+* 𝔸).symm x = (D.act σ⁻¹ : RingAut 𝔸) x := by
        intro x
        rw [map_inv]
        rfl
      simp_rw [h]
      exact D.continuous_act σ⁻¹ }

theorem actEquiv_apply (x : 𝔸) : actEquiv K L D σ x = (D.act σ : RingAut 𝔸) x := rfl

scoped instance regular_adelicAddHaar : (adelicAddHaar (𝓞 L) L).Regular := by
  show (Measure.addHaar : Measure 𝔸).Regular
  infer_instance

theorem measurePreserving_act :
    MeasurePreserving (fun x : 𝔸 => (D.act σ : RingAut 𝔸) x) (adelicAddHaar (𝓞 L) L)
      (adelicAddHaar (𝓞 L) L) := by
  have hφ : ∀ x : 𝔸, actEquiv K L D σ x ∈ AdeleRing.principalSubgroup (𝓞 L) L ↔
      x ∈ AdeleRing.principalSubgroup (𝓞 L) L := by
    intro x
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨σ⁻¹ k, ?_⟩
      have h1 : (D.act σ⁻¹ : RingAut 𝔸) ((D.act σ : RingAut 𝔸) x) = x := by
        rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      show ι (σ⁻¹ k) = x
      rw [← D.compat σ⁻¹ k, hk, actEquiv_apply, h1]
    · rintro ⟨k, hk⟩
      exact ⟨σ k, by rw [← D.compat σ k, hk]; rfl⟩
  exact (MeasureTheory.addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff
    (adelicAddHaar (𝓞 L) L) (AdeleRing.principalSubgroup (𝓞 L) L) (adelicBox L)
    (isAddFundamentalDomain_adelicBox_adelicAddHaar L) (adelicAddHaar_adelicBox_lt_top L).ne
    (actEquiv K L D σ) hφ).2

theorem setIntegral_adelicBox_comp_act {G : 𝔸 → ℂ}
    (hG : ∀ (k : L) (t : 𝔸), G (ι k + t) = G t) :
    ∫ t in adelicBox L, G ((D.act σ : RingAut 𝔸) t) ∂(adelicAddHaar (𝓞 L) L)
      = ∫ t in adelicBox L, G t ∂(adelicAddHaar (𝓞 L) L) := by
  set μ : Measure 𝔸 := adelicAddHaar (𝓞 L) L with hμ
  set φ := actEquiv K L D σ with hφdef
  have hmp : MeasurePreserving φ μ μ := measurePreserving_act K L D σ
  set e : 𝔸 ≃ᵐ 𝔸 := φ.toHomeomorph.toMeasurableEquiv with he
  have hecoe : (e : 𝔸 → 𝔸) = φ := rfl
  have hemb : MeasurableEmbedding φ := hecoe ▸ e.measurableEmbedding

  have h1 : ∫ t in adelicBox L, G (φ t) ∂μ = ∫ t in φ '' adelicBox L, G t ∂μ :=
    (hmp.setIntegral_image_emb hemb G (adelicBox L)).symm
  have hφapp : ∀ t, G ((D.act σ : RingAut 𝔸) t) = G (φ t) := fun t => rfl
  simp_rw [hφapp]
  rw [h1]

  have hB := isAddFundamentalDomain_adelicBox_adelicAddHaar L
  have hφΓ : ∀ x : 𝔸, φ x ∈ AdeleRing.principalSubgroup (𝓞 L) L ↔
      x ∈ AdeleRing.principalSubgroup (𝓞 L) L := by
    intro x
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨σ⁻¹ k, ?_⟩
      have h1 : (D.act σ⁻¹ : RingAut 𝔸) ((D.act σ : RingAut 𝔸) x) = x := by
        rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      show ι (σ⁻¹ k) = x
      rw [← D.compat σ⁻¹ k, hk]
      exact h1
    · rintro ⟨k, hk⟩
      exact ⟨σ k, by rw [← D.compat σ k, hk]; rfl⟩
  have hφs : ∀ x : 𝔸, φ.symm x ∈ AdeleRing.principalSubgroup (𝓞 L) L ↔
      x ∈ AdeleRing.principalSubgroup (𝓞 L) L := fun x => by
    rw [← hφΓ (φ.symm x), ContinuousAddEquiv.apply_symm_apply]
  set ε : AdeleRing.principalSubgroup (𝓞 L) L ≃ AdeleRing.principalSubgroup (𝓞 L) L :=
    { toFun := fun γ => ⟨φ.symm γ, (hφs γ).mpr γ.2⟩
      invFun := fun γ => ⟨φ γ, (hφΓ γ).mpr γ.2⟩
      left_inv := fun γ => Subtype.ext (by simp)
      right_inv := fun γ => Subtype.ext (by simp) } with hε
  have hsymm : MeasurePreserving e.symm μ μ := (hecoe ▸ hmp : MeasurePreserving e μ μ).symm
  have hB' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L)
      ((φ.toEquiv : 𝔸 ≃ 𝔸) '' adelicBox L) μ := by
    refine hB.image_of_equiv (φ.toEquiv : 𝔸 ≃ 𝔸) ?_ ε ?_
    · have : ((φ.toEquiv : 𝔸 ≃ 𝔸).symm : 𝔸 → 𝔸) = (e.symm : 𝔸 → 𝔸) := rfl
      rw [this]
      exact hsymm.quasiMeasurePreserving
    · intro γ x
      show φ ((φ.symm (γ : 𝔸)) + x) = (γ : 𝔸) + φ x
      rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have himg : ((φ.toEquiv : 𝔸 ≃ 𝔸) '' adelicBox L) = φ '' adelicBox L := rfl
  rw [himg] at hB'

  have hG' : ∀ (g : AdeleRing.principalSubgroup (𝓞 L) L) (x : 𝔸), G (g +ᵥ x) = G x := by
    rintro ⟨_, k, rfl⟩ x
    exact hG k x
  exact hB'.setIntegral_eq hB hG'

theorem constantTerm_cond_adelicBox_eq {G : Type*} [Group G] (u : 𝔸 → G) (f : G → ℂ) (g : G) :
    constantTerm ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) u f g
      = ((adelicAddHaar (𝓞 L) L) (adelicBox L))⁻¹.toReal
          • ∫ x in adelicBox L, f (u x * g) ∂(adelicAddHaar (𝓞 L) L) := by
  unfold constantTerm constantTermIntegrand
  rw [ProbabilityTheory.cond, integral_smul_measure]

end Descent

section TwoPoint

variable (L : Type) [Field L] [NumberField L]

local notation "𝔸" => AdeleRing (𝓞 L) L
local notation "ι" => algebraMap L (AdeleRing (𝓞 L) L)
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 L) L

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

def BA (A : Set L) : Set (GL (Fin 2) L) :=
  {γ | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A}

def PA (A : Set L) : Set (Lˣ × Lˣ × L) := {p | ((p.1 : Lˣ) : L) / ((p.2.1 : Lˣ) : L) ∈ A}

def TA (A : Set L) : Set (Lˣ × Lˣ) := {q | ((q.1 : Lˣ) : L) / ((q.2 : Lˣ) : L) ∈ A}

omit [NumberField L] in
theorem borelOf_mem_BA_iff (A : Set L) (p : Lˣ × Lˣ × L) : borelOf L p ∈ BA L A ↔ p ∈ PA L A := by
  simp only [BA, PA, Set.mem_setOf_eq, borelOf_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]

omit [NumberField L] in

theorem finsum_mem_BA_eq {M : Type*} [AddCommMonoid M] (A : Set L) (h : GL (Fin 2) L → M) :
    ∑ᶠ γ ∈ BA L A, h γ = ∑ᶠ p ∈ PA L A, h (borelOf L p) := by
  symm
  refine finsum_mem_eq_of_bijOn (borelOf L) ⟨fun p hp => (borelOf_mem_BA_iff L A p).mpr hp, ?_, ?_⟩ fun _ _ => rfl
  · intro p _ q _ hpq
    have h := (borelEquiv L).injective (Subtype.ext hpq : borelEquiv L p = borelEquiv L q)
    exact h
  · intro γ hγ
    have hγB : γ ∈ borelSubgroup L := (mem_borelSubgroup_iff L).2 hγ.1
    refine ⟨coordsOf L ⟨γ, hγB⟩, ?_, ?_⟩
    · have hval : borelOf L (coordsOf L ⟨γ, hγB⟩) = γ :=
        congrArg Subtype.val ((borelEquiv L).right_inv ⟨γ, hγB⟩)
      rw [← borelOf_mem_BA_iff, hval]
      exact hγ
    · exact congrArg Subtype.val ((borelEquiv L).right_inv ⟨γ, hγB⟩)

omit [NumberField L] in

theorem finsum_mem_BA_mul_unipotent {M : Type*} [AddCommMonoid M] (A : Set L) (h : GL (Fin 2) L → M) (k : L) :
    ∑ᶠ γ ∈ BA L A, h (γ * unipotentGL2 k) = ∑ᶠ γ ∈ BA L A, h γ := by
  have hmem : ∀ (γ : GL (Fin 2) L) (k : L), γ ∈ BA L A → γ * unipotentGL2 k ∈ BA L A := by
    intro γ k hγ
    obtain ⟨h10, hr⟩ := hγ
    have h10' : ((γ * unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]; simp [h10]
    have h00' : ((γ * unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = (γ : Matrix (Fin 2) (Fin 2) L) 0 0 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]; simp
    have h11' : ((γ * unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = (γ : Matrix (Fin 2) (Fin 2) L) 1 1 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]; simp [h10]
    refine ⟨h10', ?_⟩
    show ((γ * unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 /
        ((γ * unipotentGL2 k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A
    rw [h00', h11']; exact hr
  refine finsum_mem_eq_of_bijOn (fun γ => γ * unipotentGL2 k) ⟨fun γ hγ => hmem γ k hγ, ?_, ?_⟩ fun _ _ => rfl
  · exact fun _ _ _ _ hxy => mul_right_cancel hxy
  · intro γ hγ
    refine ⟨γ * unipotentGL2 (-k), hmem γ (-k) hγ, ?_⟩
    show γ * unipotentGL2 (-k) * unipotentGL2 k = γ
    rw [mul_assoc, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, mul_one]

def borelPartA (A : Set L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (x W : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ γ ∈ BA L A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * W)

def torusPt (p : Lˣ × Lˣ) : AdelicGL2 (𝓞 L) L :=
  diagGL2 (Units.map (algebraMap L 𝔸 : L →* 𝔸) p.1) (Units.map (algebraMap L 𝔸 : L →* 𝔸) p.2)

theorem globalPoints_diagGL2 (a d : Lˣ) :
    globalPoints (𝓞 L) L (diagGL2 a d) = torusPt L (a, d) := by
  apply Units.ext
  ext i j
  rw [AutomorphicForm.globalPoints_apply]
  fin_cases i <;> fin_cases j <;> simp [torusPt, diagGL2]

theorem globalPoints_unipotentGL2 (k : L) :
    globalPoints (𝓞 L) L (unipotentGL2 k) = unipotentGL2 (ι k) := by
  apply Units.ext
  ext i j
  rw [AutomorphicForm.globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

def slice₂ (φ : AdelicGL2 (𝓞 L) L → ℂ) (x W : AdelicGL2 (𝓞 L) L) (p : Lˣ × Lˣ) : 𝔸 → ℂ :=
  fun s => φ (x⁻¹ * torusPt L p * (unipotentGL2 s * W))

theorem borelTerm_eq_slice₂ (φ : AdelicGL2 (𝓞 L) L → ℂ) (x W : AdelicGL2 (𝓞 L) L)
    (t : 𝔸) (p : Lˣ × Lˣ × L) :
    φ (x⁻¹ * globalPoints (𝓞 L) L (borelOf L p) * (unipotentGL2 t * W))
      = slice₂ L φ x W (p.1, p.2.1) (t + ι p.2.2) := by
  obtain ⟨a, d, ξ⟩ := p
  simp only [slice₂, borelOf, map_mul, globalPoints_diagGL2, globalPoints_unipotentGL2]
  rw [add_comm t, unipotentGL2_add]
  simp only [mul_assoc]

theorem borelPartA_unipotent_eq_sum_tsum (A : Set L) [DecidablePred (· ∈ TA L A)]
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x W : AdelicGL2 (𝓞 L) L)
    (t : 𝔸) (S : Finset (Lˣ × Lˣ))
    (hfin : (Function.support fun q : (Lˣ × Lˣ) × L => slice₂ L φ x W q.1 (t + ι q.2)).Finite)
    (hS : ∀ p ∉ S, ∀ s : 𝔸, slice₂ L φ x W p s = 0) :
    borelPartA L A φ x (unipotentGL2 t * W) =
      ∑ p ∈ S.filter (· ∈ TA L A), ∑' ξ : L, slice₂ L φ x W p (t + ι ξ) := by
  classical
  rw [borelPartA, finsum_mem_BA_eq]
  simp_rw [borelTerm_eq_slice₂]

  have hre : ∑ᶠ p ∈ PA L A, slice₂ L φ x W (p.1, p.2.1) (t + ι p.2.2) =
      ∑ᶠ q ∈ TA L A ×ˢ (Set.univ : Set L), slice₂ L φ x W q.1 (t + ι q.2) := by
    refine finsum_mem_eq_of_bijOn (Equiv.prodAssoc Lˣ Lˣ L).symm ⟨?_, ?_, ?_⟩ ?_
    · intro p hp; exact ⟨hp, Set.mem_univ _⟩
    · exact (Equiv.prodAssoc Lˣ Lˣ L).symm.injective.injOn
    · intro q hq
      exact ⟨Equiv.prodAssoc Lˣ Lˣ L q, hq.1, (Equiv.prodAssoc Lˣ Lˣ L).symm_apply_apply q⟩
    · intro p _; rfl
  rw [hre, finsum_mem_def]

  set F : (Lˣ × Lˣ) × L → ℂ := fun q => slice₂ L φ x W q.1 (t + ι q.2) with hF
  set G : (Lˣ × Lˣ) × L → ℂ := (TA L A ×ˢ (Set.univ : Set L)).indicator F with hG
  have hGfin : (Function.support G).Finite :=
    hfin.subset (by rw [hG, Set.support_indicator]; exact Set.inter_subset_right)
  rw [finsum_curry G hGfin]
  have hinner : ∀ p : Lˣ × Lˣ, ∑ᶠ ξ : L, G (p, ξ) = (TA L A).indicator (fun p => ∑ᶠ ξ : L, F (p, ξ)) p := by
    intro p
    by_cases hp : p ∈ TA L A
    · rw [Set.indicator_of_mem hp]
      refine finsum_congr fun ξ => ?_
      rw [hG, Set.indicator_of_mem (show (p, ξ) ∈ TA L A ×ˢ (Set.univ : Set L) from ⟨hp, Set.mem_univ _⟩)]
    · rw [Set.indicator_of_notMem hp]
      refine finsum_eq_zero_of_forall_eq_zero fun ξ => ?_
      rw [hG, Set.indicator_of_notMem (fun h => hp h.1)]
  simp_rw [hinner]
  rw [← finsum_mem_def]
  have hsub : TA L A ∩ (Function.support fun p : Lˣ × Lˣ => ∑ᶠ ξ : L, F (p, ξ)) ⊆
      ↑(S.filter (· ∈ TA L A)) := by
    rintro p ⟨hpA, hp⟩
    rw [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨?_, hpA⟩
    by_contra hpS
    exact hp (by simp [hF, hS p hpS])
  have hsub' : (↑(S.filter (· ∈ TA L A)) : Set (Lˣ × Lˣ)) ⊆ TA L A := by
    intro p hp
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hp
    exact hp.2
  rw [finsum_mem_eq_sum_of_subset _ hsub hsub']
  refine Finset.sum_congr rfl fun p _ => ?_
  refine (tsum_eq_finsum ?_).symm
  show ((fun ξ : L => (p, ξ)) ⁻¹'
    Function.support fun q : (Lˣ × Lˣ) × L => slice₂ L φ x W q.1 (t + ι q.2)).Finite
  exact hfin.preimage fun a _ b _ h => (Prod.ext_iff.1 h).2

theorem borelPartA_sub_boxAverage_eq (A : Set L) [DecidablePred (· ∈ TA L A)]
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x W : AdelicGL2 (𝓞 L) L)
    (S : Finset (Lˣ × Lˣ))
    (hfin : ∀ t : 𝔸,
      (Function.support fun q : (Lˣ × Lˣ) × L => slice₂ L φ x W q.1 (t + ι q.2)).Finite)
    (hS : ∀ p ∉ S, ∀ s : 𝔸, slice₂ L φ x W p s = 0)
    (hInt : ∀ p ∈ S, IntegrableOn (fun t => ∑' ξ : L, slice₂ L φ x W p (t + ι ξ))
      (adelicBox L) μ𝔸)
    (hU : ∀ p ∈ S,
      ∫ t in adelicBox L, (∑' ξ : L, slice₂ L φ x W p (t + ι ξ)) ∂μ𝔸 = ∫ t, slice₂ L φ x W p t ∂μ𝔸) :
    borelPartA L A φ x W
        - ((μ𝔸 (adelicBox L))⁻¹.toReal •
            ∫ t in adelicBox L, borelPartA L A φ x (unipotentGL2 t * W) ∂μ𝔸)
      = ∑ p ∈ S.filter (· ∈ TA L A), ((∑' ξ : L, slice₂ L φ x W p (ι ξ))
          - ((μ𝔸 (adelicBox L)).toReal : ℂ)⁻¹ * ∫ t, slice₂ L φ x W p t ∂μ𝔸) := by
  have hdiag : borelPartA L A φ x W = ∑ p ∈ S.filter (· ∈ TA L A), ∑' ξ : L, slice₂ L φ x W p (ι ξ) := by
    have h := borelPartA_unipotent_eq_sum_tsum L A φ x W 0 S (hfin 0) hS
    simpa only [unipotentGL2_zero, one_mul, zero_add] using h
  have hfun : (fun t : 𝔸 => borelPartA L A φ x (unipotentGL2 t * W))
      = fun t => ∑ p ∈ S.filter (· ∈ TA L A), ∑' ξ : L, slice₂ L φ x W p (t + ι ξ) :=
    funext fun t => borelPartA_unipotent_eq_sum_tsum L A φ x W t S (hfin t) hS
  have hInt' : ∀ p ∈ S.filter (· ∈ TA L A), IntegrableOn (fun t => ∑' ξ : L, slice₂ L φ x W p (t + ι ξ))
      (adelicBox L) μ𝔸 := fun p hp => hInt p (Finset.mem_filter.1 hp).1
  rw [hdiag, hfun, integral_finsetSum _ hInt', ENNReal.toReal_inv, Complex.real_smul, Complex.ofReal_inv,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hU p (Finset.mem_filter.1 hp).1]

def entryAt (x W : AdelicGL2 (𝓞 L) L) (i j : Fin 2) (g : AdelicGL2 (𝓞 L) L) : 𝔸 :=
  ((x * g * W⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j

theorem continuous_entryAt (x W : AdelicGL2 (𝓞 L) L) (i j : Fin 2) : Continuous (entryAt L x W i j) := by
  unfold entryAt
  exact (Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)).matrix_elem
    i j

theorem entryAt_slice (x W : AdelicGL2 (𝓞 L) L) (p : Lˣ × Lˣ) (s : 𝔸) (i j : Fin 2) :
    entryAt L x W i j (x⁻¹ * torusPt L p * (unipotentGL2 s * W))
      = ((torusPt L p * unipotentGL2 s : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j := by
  unfold entryAt
  group

theorem torus_unipotent_val (p : Lˣ × Lˣ) (s : 𝔸) :
    ((torusPt L p * unipotentGL2 s : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸)
      = !![ι (p.1 : L), ι (p.1 : L) * s; 0, ι (p.2 : L)] := by
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [torusPt, diagGL2]

theorem entries_mem_of_slice₂_ne_zero (φ : AdelicGL2 (𝓞 L) L → ℂ) (x W : AdelicGL2 (𝓞 L) L)
    (p : Lˣ × Lˣ) (s : 𝔸) (h : slice₂ L φ x W p s ≠ 0) :
    ι (p.1 : L) ∈ entryAt L x W 0 0 '' tsupport φ ∧ ι (p.2 : L) ∈ entryAt L x W 1 1 '' tsupport φ ∧
      ι (p.1 : L) * s ∈ entryAt L x W 0 1 '' tsupport φ := by
  have hg : x⁻¹ * torusPt L p * (unipotentGL2 s * W) ∈ tsupport φ :=
    subset_tsupport φ (Function.mem_support.mpr h)
  refine ⟨⟨_, hg, ?_⟩, ⟨_, hg, ?_⟩, ⟨_, hg, ?_⟩⟩ <;>
    · rw [entryAt_slice, torus_unipotent_val]; simp

theorem exists_finset_slices₂
    (hdisc : ∀ C : Set 𝔸, IsCompact C → {ξ : L | ι ξ ∈ C}.Finite)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : HasCompactSupport φ) (x W : AdelicGL2 (𝓞 L) L) :
    ∃ S : Finset (Lˣ × Lˣ), (∀ p ∉ S, ∀ s : 𝔸, slice₂ L φ x W p s = 0) ∧
      (∀ p ∈ S, ∃ s : 𝔸, slice₂ L φ x W p s ≠ 0) ∧
      ∀ t : 𝔸, (Function.support fun q : (Lˣ × Lˣ) × L =>
        slice₂ L φ x W q.1 (t + ι q.2)).Finite := by
  classical
  have hK : IsCompact (tsupport φ) := hφ
  have hC : ∀ i j : Fin 2, IsCompact (entryAt L x W i j '' tsupport φ) := fun i j =>
    hK.image (continuous_entryAt L x W i j)
  have hA : (Units.val ⁻¹' {ξ : L | ι ξ ∈ entryAt L x W 0 0 '' tsupport φ}).Finite :=
    (hdisc _ (hC 0 0)).preimage Units.val_injective.injOn
  have hD : (Units.val ⁻¹' {ξ : L | ι ξ ∈ entryAt L x W 1 1 '' tsupport φ}).Finite :=
    (hdisc _ (hC 1 1)).preimage Units.val_injective.injOn
  refine ⟨((hA.prod hD).toFinset).filter (fun p => ∃ s : 𝔸, slice₂ L φ x W p s ≠ 0),
    fun p hp s => ?_, fun p hp => (Finset.mem_filter.1 hp).2, fun t => ?_⟩
  · by_contra h
    obtain ⟨h00, h11, -⟩ := entries_mem_of_slice₂_ne_zero L φ x W p s h
    exact hp (Finset.mem_filter.2 ⟨(hA.prod hD).mem_toFinset.mpr ⟨h00, h11⟩, s, h⟩)
  · have hT : ∀ p : Lˣ × Lˣ,
        {ξ : L | ι (p.1 : L) * (t + ι ξ) ∈ entryAt L x W 0 1 '' tsupport φ}.Finite := by
      intro p
      have hc : Continuous fun u : 𝔸 => ι ((p.1 : L)⁻¹) * u + -t := by fun_prop
      refine (hdisc _ ((hC 0 1).image hc)).subset ?_
      intro ξ hξ
      refine ⟨_, hξ, ?_⟩
      show ι ((p.1 : L)⁻¹) * (ι (p.1 : L) * (t + ι ξ)) + -t = ι ξ
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (Units.ne_zero p.1), map_one, one_mul]
      abel
    refine ((hA.prod hD).prod ((hA.prod hD).biUnion fun p _ => hT p)).subset ?_
    rintro ⟨p, ξ⟩ hq
    have h : slice₂ L φ x W p (t + ι ξ) ≠ 0 := hq
    obtain ⟨h00, h11, h01⟩ := entries_mem_of_slice₂_ne_zero L φ x W p _ h
    exact ⟨⟨h00, h11⟩, Set.mem_biUnion (x := p) ⟨h00, h11⟩ h01⟩

def diagEntry (i : Fin 2) (g : AdelicGL2 (𝓞 L) L) : 𝔸 := (g : Matrix (Fin 2) (Fin 2) 𝔸) i i

theorem continuous_diagEntry (i : Fin 2) : Continuous (diagEntry L i) :=
  Units.continuous_val.matrix_elem i i

theorem ratio_mem_of_mem {Ω : Set (AdelicGL2 (𝓞 L) L)} {M : AdelicGL2 (𝓞 L) L}
    {p p' : Lˣ × Lˣ} {v v' : 𝔸}
    (h : unipotentGL2 v * torusPt L p * M ∈ Ω) (h' : unipotentGL2 v' * torusPt L p' * M ∈ Ω) :
    ι ((p'.1 * p.1⁻¹ : Lˣ) : L) ∈ diagEntry L 0 '' (Ω * Ω⁻¹) ∧
      ι ((p'.2 * p.2⁻¹ : Lˣ) : L) ∈ diagEntry L 1 '' (Ω * Ω⁻¹) := by
  set g : AdelicGL2 (𝓞 L) L := (unipotentGL2 v' * torusPt L p' * M) * (unipotentGL2 v * torusPt L p * M)⁻¹
    with hgdef
  have hg : g ∈ Ω * Ω⁻¹ := Set.mul_mem_mul h' (Set.inv_mem_inv.mpr h)
  have hg' : g = unipotentGL2 v' * (torusPt L (p'.1 * p.1⁻¹, p'.2 * p.2⁻¹) * unipotentGL2 (-v)) := by
    rw [hgdef]
    have ht : torusPt L p' * (torusPt L p)⁻¹ = torusPt L (p'.1 * p.1⁻¹, p'.2 * p.2⁻¹) := by
      simp only [torusPt, diagGL2_inv, diagGL2_mul, map_mul, map_inv]
    rw [← ht, ← unipotentGL2_inv]
    group
  have hb : ((torusPt L (p'.1 * p.1⁻¹, p'.2 * p.2⁻¹) * unipotentGL2 (-v) : AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := by
    rw [torus_unipotent_val]; simp
  obtain ⟨h00, h11, -⟩ := unipotent_mul_apply_diag v' _ hb
  refine ⟨⟨g, hg, ?_⟩, ⟨g, hg, ?_⟩⟩
  · rw [diagEntry, hg', h00, torus_unipotent_val]; simp
  · rw [diagEntry, hg', h11, torus_unipotent_val]; simp

theorem exists_card_le_of_isCompact
    (hdisc : ∀ C : Set 𝔸, IsCompact C → {ξ : L | ι ξ ∈ C}.Finite)
    {Ω : Set (AdelicGL2 (𝓞 L) L)} (hΩ : IsCompact Ω) :
    ∃ N₀ : ℕ, ∀ (M : AdelicGL2 (𝓞 L) L) (T : Finset (Lˣ × Lˣ)),
      (∀ p ∈ T, ∃ v : 𝔸, unipotentGL2 v * torusPt L p * M ∈ Ω) → T.card ≤ N₀ := by
  classical
  have hΩ₁ : IsCompact (Ω * Ω⁻¹) := hΩ.mul hΩ.inv
  have hA : (Units.val ⁻¹' {ξ : L | ι ξ ∈ diagEntry L 0 '' (Ω * Ω⁻¹)}).Finite :=
    (hdisc _ (hΩ₁.image (continuous_diagEntry L 0))).preimage Units.val_injective.injOn
  have hD : (Units.val ⁻¹' {ξ : L | ι ξ ∈ diagEntry L 1 '' (Ω * Ω⁻¹)}).Finite :=
    (hdisc _ (hΩ₁.image (continuous_diagEntry L 1))).preimage Units.val_injective.injOn
  refine ⟨(hA.prod hD).toFinset.card, fun M T hT => ?_⟩
  rcases T.eq_empty_or_nonempty with hTe | ⟨p₀, hp₀⟩
  · simp [hTe]
  obtain ⟨v₀, hv₀⟩ := hT p₀ hp₀

  refine Finset.card_le_card_of_injOn (fun p : Lˣ × Lˣ => (p.1 * p₀.1⁻¹, p.2 * p₀.2⁻¹)) ?_ ?_
  · intro p hp
    obtain ⟨v, hv⟩ := hT p hp
    obtain ⟨h1, h2⟩ := ratio_mem_of_mem L hv₀ hv
    exact (hA.prod hD).mem_toFinset.mpr ⟨h1, h2⟩
  · intro p _ p' _ hpp'
    simp only [Prod.mk.injEq] at hpp'
    exact Prod.ext (mul_right_cancel hpp'.1) (mul_right_cancel hpp'.2)

end TwoPoint

section HighStructure

section Local

variable {𝕜 : Type*} [NormedField 𝕜]

theorem localHeight_torus_mul {s : GL (Fin 2) 𝕜} {β : 𝕜}
    (h00 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 0 0 = β) (h01 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 1 1 = 1)
    (g : GL (Fin 2) 𝕜) :
    localHeight (s * g) = ‖β‖ * localHeight g := by
  have hcoe : ((s * g : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
      = (s : Matrix (Fin 2) (Fin 2) 𝕜) * (g : Matrix (Fin 2) (Fin 2) 𝕜) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) 𝕜).det = β := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdet : ‖((s * g : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜).det‖
      = ‖β‖ * ‖(g : Matrix (Fin 2) (Fin 2) 𝕜).det‖ := by
    rw [hcoe, Matrix.det_mul, hdets, norm_mul]
  have hrow : rowNormSq ((s * g : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) 𝕜) := by
    rw [rowNormSq_scalar_entries_mul h10 h11 g, norm_one, one_pow, one_mul]
  unfold localHeight
  rw [hdet, hrow, mul_div_assoc]

theorem xWindowSq_torus_mul {s : GL (Fin 2) 𝕜} {β : 𝕜}
    (h00 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 0 0 = β) (h01 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) 𝕜) 1 1 = 1)
    (g : GL (Fin 2) 𝕜) :
    xWindowSq (s * g) = ‖β‖ ^ 2 * xWindowSq g := by
  have hrow : rowNormSq ((s * g : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) 𝕜) := by
    rw [rowNormSq_scalar_entries_mul h10 h11 g, norm_one, one_pow, one_mul]
  unfold xWindowSq
  rw [topNormSq_scalar_entries_mul h00 h01 g, hrow, localHeight_torus_mul h00 h01 h10 h11 g,
    mul_pow, mul_div_assoc, mul_sub]

end Local

variable (L : Type) [Field L] [NumberField L]

local notation "𝔸" => AdeleRing (𝓞 L) L
local notation "ι" => algebraMap L (AdeleRing (𝓞 L) L)

theorem glFin_diagGL2_of_snd_eq_one {β : 𝔸ˣ} (hβ : (β : 𝔸).2 = 1) :
    glFin (𝓞 L) L (diagGL2 β 1) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [glFin_apply, diagGL2, hβ] <;> rfl

theorem archHeight_glArch_diagGL2_mul (β : 𝔸ˣ) (g : AdelicGL2 (𝓞 L) L) :
    archHeight L (glArch (𝓞 L) L (diagGL2 β 1 * g))
      = (∏ v : InfinitePlace L, ‖(β : 𝔸).1 v‖ ^ v.mult) * archHeight L (glArch (𝓞 L) L g) := by
  unfold archHeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_mul, map_mul, ← mul_pow]
  congr 1
  refine localHeight_torus_mul ?_ ?_ ?_ ?_ (archComponent L v (glArch (𝓞 L) L g))
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl

theorem xWindowSq_archComponent_glArch_diagGL2_mul (β : 𝔸ˣ) (g : AdelicGL2 (𝓞 L) L)
    (v : InfinitePlace L) :
    xWindowSq (archComponent L v (glArch (𝓞 L) L (diagGL2 β 1 * g)))
      = ‖(β : 𝔸).1 v‖ ^ 2 * xWindowSq (archComponent L v (glArch (𝓞 L) L g)) := by
  rw [map_mul, map_mul]
  refine xWindowSq_torus_mul ?_ ?_ ?_ ?_ (archComponent L v (glArch (𝓞 L) L g))
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl

theorem diagGL2_mul_mem_integralWindowedSiegelSet {c u : ℝ} {x : AdelicGL2 (𝓞 L) L}
    (hx : x ∈ integralWindowedSiegelSet L c u) {t : ℝ} (ht : 1 ≤ t)
    (htH : t ^ Module.finrank ℚ L = archHeight L (glArch (𝓞 L) L x))
    {β : 𝔸ˣ} (hβf : (β : 𝔸).2 = 1) (hβa : ∀ v : InfinitePlace L, ‖(β : 𝔸).1 v‖ = t⁻¹) :
    diagGL2 β 1 * x ∈ integralWindowedSiegelSet L 1 u ∧
      archHeight L (glArch (𝓞 L) L (diagGL2 β 1 * x)) = 1 := by
  obtain ⟨hfin, _, hwin⟩ := hx
  have ht0 : 0 < t := one_pos.trans_le ht
  have hH : archHeight L (glArch (𝓞 L) L (diagGL2 β 1 * x)) = 1 := by
    rw [archHeight_glArch_diagGL2_mul, ← htH]
    simp_rw [hβa]
    rw [Finset.prod_pow_eq_pow_sum, NumberField.InfinitePlace.sum_mult_eq, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ ht0.ne')]
  refine ⟨⟨?_, hH.symm.le, fun v => ?_⟩, hH⟩
  · rw [map_mul, glFin_diagGL2_of_snd_eq_one L hβf, one_mul]; exact hfin
  · rw [xWindowSq_archComponent_glArch_diagGL2_mul, hβa]
    have hle : t⁻¹ ^ 2 ≤ 1 := by
      rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ ht)
    rcases le_or_gt 0 (xWindowSq (archComponent L v (glArch (𝓞 L) L x))) with h0 | h0
    · exact (mul_le_of_le_one_left h0 hle).trans (hwin v)
    · exact ((mul_neg_of_pos_of_neg (by positivity) h0).le).trans (sq_nonneg u)

omit [NumberField L] in

theorem exists_norm_eq (w : InfinitePlace L) {r : ℝ} (hr : 0 ≤ r) :
    ∃ a : w.Completion, ‖a‖ = r := by
  by_cases hw : InfinitePlace.IsReal w
  · refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm r, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _), ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw,
      RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_nonneg hr]
  · have hc : InfinitePlace.IsComplex w := InfinitePlace.not_isReal_iff_isComplex.mp hw
    refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm r, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
      ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hc,
      RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

theorem exists_archIdele_norm_eq {t : ℝ} (ht : 0 < t) :
    ∃ α : 𝔸ˣ, (α : 𝔸).2 = 1 ∧ ∀ v : InfinitePlace L, ‖(α : 𝔸).1 v‖ = t := by
  choose a ha using fun v : InfinitePlace L => exists_norm_eq L v ht.le
  have ha0 : ∀ v, a v ≠ 0 := fun v h => by
    have := ha v; rw [h, norm_zero] at this; exact ht.ne' this.symm
  refine ⟨⟨(fun v => a v, 1), (fun v => (a v)⁻¹, 1), ?_, ?_⟩, rfl, fun v => ha v⟩
  · refine Prod.ext (funext fun v => ?_) (one_mul 1)
    exact mul_inv_cancel₀ (ha0 v)
  · refine Prod.ext (funext fun v => ?_) (one_mul 1)
    exact inv_mul_cancel₀ (ha0 v)

theorem centralScalar_eq_diagGL2 (z : 𝔸ˣ) : centralScalar (𝓞 L) L z = diagGL2 z z := by
  apply Units.ext
  change Matrix.scalar (Fin 2) (z : 𝔸) = ((diagGL2 z z : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL2, Matrix.scalar_apply, Matrix.diagonal]

theorem centralScalar_comm (z : 𝔸ˣ) (g : AdelicGL2 (𝓞 L) L) :
    g * centralScalar (𝓞 L) L z = centralScalar (𝓞 L) L z * g := by
  apply Units.ext
  change (g : Matrix (Fin 2) (Fin 2) 𝔸) * (Matrix.scalar (Fin 2) (z : 𝔸))
    = (Matrix.scalar (Fin 2) (z : 𝔸)) * (g : Matrix (Fin 2) (Fin 2) 𝔸)
  exact ((Matrix.scalar_commute (z : 𝔸) (Commute.all _) (g : Matrix (Fin 2) (Fin 2) 𝔸)).eq).symm

theorem exists_eq_unipotent_mul_diag_mul_mem_of_one_le_archHeight (c u : ℝ) :
    ∃ K : Set (AdelicGL2 (𝓞 L) L), IsCompact K ∧
      ∀ x ∈ integralWindowedSiegelSet L c u, 1 ≤ archHeight L (glArch (𝓞 L) L x) →
        ∃ (w : 𝔸) (t₁ t₂ : 𝔸ˣ) (k : AdelicGL2 (𝓞 L) L) (α : 𝔸ˣ) (q : Lˣ) (t : ℝ),
          k ∈ K ∧ x = unipotentGL2 w * diagGL2 t₁ t₂ * k ∧
          sliceScale t₁ t₂ = α⁻¹ * Units.map (algebraMap L 𝔸 : L →* 𝔸) q ∧
          (α : 𝔸).2 = 1 ∧ (∀ v : InfinitePlace L, ‖(α : 𝔸).1 v‖ = t) ∧ 1 ≤ t ∧
          t ^ Module.finrank ℚ L = archHeight L (glArch (𝓞 L) L x) := by
  obtain ⟨K, hK, hcov⟩ := AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le L 1 u 1 one_pos
  refine ⟨K, hK, fun x hx hH => ?_⟩
  set H : ℝ := archHeight L (glArch (𝓞 L) L x) with hHdef
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hn : Module.finrank ℚ L ≠ 0 := Module.finrank_pos.ne'
  set t : ℝ := H ^ ((Module.finrank ℚ L : ℝ)⁻¹) with htdef
  have ht1 : 1 ≤ t := Real.one_le_rpow hH (by positivity)
  have ht0 : 0 < t := one_pos.trans_le ht1
  have htH : t ^ Module.finrank ℚ L = H := Real.rpow_inv_natCast_pow hH0 hn
  obtain ⟨α, hαf, hαa⟩ := exists_archIdele_norm_eq L ht0
  have hβf : ((α⁻¹ : 𝔸ˣ) : 𝔸).2 = 1 := by
    have h : adeleFin (𝓞 L) L ((α⁻¹ : 𝔸ˣ) : 𝔸) * adeleFin (𝓞 L) L (α : 𝔸) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [adeleFin_apply, adeleFin_apply, hαf, mul_one] at h
    exact h
  have hβa : ∀ v : InfinitePlace L, ‖((α⁻¹ : 𝔸ˣ) : 𝔸).1 v‖ = t⁻¹ := by
    intro v
    have h : archEval L v (adeleArch (𝓞 L) L ((α⁻¹ : 𝔸ˣ) : 𝔸))
        * archEval L v (adeleArch (𝓞 L) L (α : 𝔸)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rw [archEval_apply, archEval_apply, adeleArch_apply, adeleArch_apply] at h
    have h' : ‖((α⁻¹ : 𝔸ˣ) : 𝔸).1 v‖ * t = 1 := by
      rw [← hαa v, ← norm_mul, h, norm_one]
    exact eq_inv_of_mul_eq_one_left h'
  obtain ⟨hx', hH'⟩ := diagGL2_mul_mem_integralWindowedSiegelSet L hx ht1 htH hβf hβa
  obtain ⟨γ, z, hγ, hk⟩ := hcov _ hx' hH'.le
  set k := globalPoints (𝓞 L) L γ * (diagGL2 α⁻¹ 1 * x) * centralScalar (𝓞 L) L z with hkdef
  set b : AdelicGL2 (𝓞 L) L :=
    diagGL2 α 1 * globalPoints (𝓞 L) L γ⁻¹ * centralScalar (𝓞 L) L z⁻¹ with hbdef
  have hDinv : (diagGL2 α⁻¹ 1 : AdelicGL2 (𝓞 L) L) = (diagGL2 α 1)⁻¹ := by
    rw [diagGL2_inv, inv_one]
  have hxb : x = b * k := by
    rw [hbdef, hkdef, map_inv, map_inv, hDinv]
    rw [centralScalar_comm L z (globalPoints (𝓞 L) L γ * ((diagGL2 α 1)⁻¹ * x))]
    group
  set γi : GL (Fin 2) L := γ⁻¹ with hγidef
  have hγi10 : (γi : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    rw [hγidef]; exact inv_apply_one_zero γ hγ
  set G : AdelicGL2 (𝓞 L) L := globalPoints (𝓞 L) L γi with hGdef
  have hG : ∀ i j, (G : Matrix (Fin 2) (Fin 2) 𝔸) i j
      = algebraMap L 𝔸 ((γi : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => by
    rw [hGdef, AutomorphicForm.globalPoints_apply]
  set Z : AdelicGL2 (𝓞 L) L := centralScalar (𝓞 L) L z⁻¹ with hZdef
  have hZ : Z = diagGL2 z⁻¹ z⁻¹ := by rw [hZdef, centralScalar_eq_diagGL2]
  have hb10 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := by
    rw [hbdef, hZ, diag_mul_mul_diag_apply]
    simp [hG, hγi10]
  have hb00 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 0
      = (α : 𝔸) * algebraMap L 𝔸 ((γi : Matrix (Fin 2) (Fin 2) L) 0 0) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [hbdef, hZ, diag_mul_mul_diag_apply]
    simp [hG]
  have hb11 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1
      = algebraMap L 𝔸 ((γi : Matrix (Fin 2) (Fin 2) L) 1 1) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [hbdef, hZ, diag_mul_mul_diag_apply]
    simp [hG]
  obtain ⟨w, t₁, t₂, hbw, ht₁, ht₂⟩ := eq_unipotent_mul_diag_of_apply_one_zero b hb10
  obtain ⟨he, hd⟩ := isUnit_apply_of_apply_one_zero γi hγi10
  obtain ⟨e, he'⟩ := he
  obtain ⟨d, hd'⟩ := hd
  refine ⟨w, t₁, t₂, k, α, e⁻¹ * d, t, hk, by rw [hxb, hbw], ?_, hαf, hαa, ht1, htH⟩
  have h1 : (t₁ : 𝔸) = (α : 𝔸) * algebraMap L 𝔸 (e : L) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [ht₁, hb00, ← he']
  have h2 : (t₂ : 𝔸) = algebraMap L 𝔸 (d : L) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [ht₂, hb11, ← hd']
  have hαα : ((α⁻¹ : 𝔸ˣ) : 𝔸) * (α : 𝔸) = 1 := α.inv_mul
  have hee : algebraMap L 𝔸 ((e⁻¹ : Lˣ) : L) * algebraMap L 𝔸 (e : L) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [sliceScale, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, h1, h2]
  linear_combination
    (-(algebraMap L 𝔸 (d : L) * ((z⁻¹ : 𝔸ˣ) : 𝔸)
      * (algebraMap L 𝔸 ((e⁻¹ : Lˣ) : L) * algebraMap L 𝔸 (e : L)))) * hαα
    + (-(algebraMap L 𝔸 (d : L) * ((z⁻¹ : 𝔸ˣ) : 𝔸))) * hee

end HighStructure

section Assembly

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

local notation "𝔸" => AdeleRing (𝓞 L) L
local notation "ι" => algebraMap L (AdeleRing (𝓞 L) L)
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 L) L

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem key_identity (ν τ : 𝔸) (t₁ t₂ : 𝔸ˣ) (κ W : AdelicGL2 (𝓞 L) L) (p : Lˣ × Lˣ) :
    (unipotentGL2 ν * diagGL2 t₁ t₂ * κ)⁻¹ * torusPt L p * (unipotentGL2 τ * W)
      = κ⁻¹ * (unipotentGL2 (((sliceScale t₁ t₂ : 𝔸ˣ) : 𝔸) *
            (((Units.map (algebraMap L 𝔸 : L →* 𝔸) (p.1 * p.2⁻¹) : 𝔸ˣ) : 𝔸) * τ - ν))
          * torusPt L p * ((diagGL2 t₁ t₂)⁻¹ * W)) := by
  have h := borel_inv_mul_diag_mul_unipotent ν τ t₁ t₂
    (Units.map (algebraMap L 𝔸 : L →* 𝔸) p.1) (Units.map (algebraMap L 𝔸 : L →* 𝔸) p.2)
  rw [← map_inv, ← map_mul] at h
  have ht : torusPt L p = diagGL2 (Units.map (algebraMap L 𝔸 : L →* 𝔸) p.1)
      (Units.map (algebraMap L 𝔸 : L →* 𝔸) p.2) := rfl
  calc (unipotentGL2 ν * diagGL2 t₁ t₂ * κ)⁻¹ * torusPt L p * (unipotentGL2 τ * W)
      = κ⁻¹ * ((unipotentGL2 ν * diagGL2 t₁ t₂)⁻¹ * (torusPt L p * unipotentGL2 τ)) * W := by group
    _ = κ⁻¹ * (unipotentGL2 (((sliceScale t₁ t₂ : 𝔸ˣ) : 𝔸) *
            (((Units.map (algebraMap L 𝔸 : L →* 𝔸) (p.1 * p.2⁻¹) : 𝔸ˣ) : 𝔸) * τ - ν))
          * (torusPt L p * (diagGL2 t₁ t₂)⁻¹)) * W := by rw [ht, h]
    _ = _ := by group

theorem measurableEmbedding_mul_algebraMap {q : L} (hq : q ≠ 0) :
    MeasurableEmbedding (fun u : 𝔸 => ι q * u) := by
  have h1 : ι q⁻¹ * ι q = 1 := by rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have h2 : ι q * ι q⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  set e : 𝔸 ≃ᵐ 𝔸 :=
    { toFun := fun u => ι q * u
      invFun := fun u => ι q⁻¹ * u
      left_inv := fun u => by
        show ι q⁻¹ * (ι q * u) = u
        rw [← mul_assoc, h1, one_mul]
      right_inv := fun u => by
        show ι q * (ι q⁻¹ * u) = u
        rw [← mul_assoc, h2, one_mul]
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable } with he
  exact e.measurableEmbedding

theorem main (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AdelicGL2 (𝓞 L) L))
    (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet L c u d₁ d₂)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφf : IsFactorizableTestFn L φ) :
    ∃ T₁ : ℝ, ∀ N : ℕ, ∃ C : ℝ, ∀ A : Set L,
      ∀ x ∈ S, T₁ < NumberField.AdelicHeight.adelicHeight L x → ∀ z : 𝔸ˣ,
        ‖borelPartA L A φ x (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))
          - constantTerm ((μ𝔸)[|adelicBox L]) (fun t => unipotentGL2 t)
              (fun y => borelPartA L A φ x (sigmaAdelicAct K L D σ y)) (centralScalar (𝓞 L) L z * x)‖ ≤
          C * (NumberField.AdelicHeight.adelicHeight L x)⁻¹ ^ N := by
  classical

  obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hφf
  have hdisc : ∀ C : Set 𝔸, IsCompact C → {ξ : L | ι ξ ∈ C}.Finite :=
    fun C hC => NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hC
  set c' : ℝ := c ^ (∑ w : InfinitePlace L, w.mult) with hc'def
  obtain ⟨K₀, hK₀, hstruct⟩ := exists_eq_unipotent_mul_diag_mul_mem_of_one_le_archHeight L c' u
  obtain ⟨κ₁, K₁, hκ₁, hcmp⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact L Tc hTc

  set K' : Set (AdelicGL2 (𝓞 L) L) :=
    (fun q : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => q.1 * q.2) '' (K₀ ×ˢ Tc) with hK'def
  have hK' : IsCompact K' := (hK₀.prod hTc).image (by fun_prop)
  set Ω₀ : Set (AdelicGL2 (𝓞 L) L) :=
    (fun q : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => q.1 * q.2) '' (K' ×ˢ tsupport φ) with hΩ₀def
  have hΩ₀ : IsCompact Ω₀ := (hK'.prod hφs.isCompact).image (by fun_prop)
  set Q : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) :=
    (fun q : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => (q.1⁻¹, q.1 * q.2)) '' (K' ×ˢ tsupport φ)
    with hQdef
  have hQ : IsCompact Q := (hK'.prod hφs.isCompact).image (by fun_prop)
  obtain ⟨N₀, hN₀⟩ := exists_card_le_of_isCompact L hdisc hΩ₀
  refine ⟨max K₁ 1, fun N => ?_⟩
  obtain ⟨CH, hCH⟩ :=
    AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
      L φ hφf Q hQ (N * Module.finrank ℚ L)
  refine ⟨N₀ * (max CH 0 * (max K₁ 1) ^ N), fun A x hx hHx z => ?_⟩

  have hx' := hS hx
  rw [Set.mem_iUnion₂] at hx'
  obtain ⟨y, hy, s, hs𝔖, hsx⟩ := hx'
  subst hsx
  have hsInt : s ∈ integralWindowedSiegelSet L c' u :=
    centreCutSiegelSet_subset_integralWindowedSiegelSet hc.le hs𝔖
  have hHs : NumberField.AdelicHeight.adelicHeight L s = archHeight L (glArch (𝓞 L) L s) :=
    NumberField.AdelicHeight.adelicHeight_eq_archHeight_of_mem hs𝔖.1
  set Ah : ℝ := archHeight L (glArch (𝓞 L) L s) with hAdef
  set Hx : ℝ := NumberField.AdelicHeight.adelicHeight L (s * y) with hHxdef
  have hA0 : 0 < Ah := archHeight_pos L _
  have hHx0 : 0 < Hx := NumberField.AdelicHeight.adelicHeight_pos _
  have hcmp' : Hx ≤ K₁ * Ah := by
    have h := (hcmp s y hy).2
    rw [hHs] at h
    exact h
  have hK₁pos : 0 < K₁ := by
    by_contra h
    have : K₁ * Ah ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hA0.le
    linarith
  have hK₁le : K₁ ≤ max K₁ 1 := le_max_left _ _
  have hA1 : 1 ≤ Ah := by
    have h1 : max K₁ 1 < K₁ * Ah := hHx.trans_le hcmp'
    have h2 : K₁ * 1 ≤ K₁ * Ah := by linarith [le_max_left K₁ 1]
    exact le_of_mul_le_mul_left h2 hK₁pos
  obtain ⟨ν, t₁, t₂, k, α, q, t, hk, hsdec, hτ, hαf, hαa, ht1, htH⟩ := hstruct s hsInt hA1
  have ht0 : 0 < t := one_pos.trans_le ht1
  set κ : AdelicGL2 (𝓞 L) L := k * y with hκdef
  have hκ : κ ∈ K' := ⟨(k, y), ⟨hk, hy⟩, rfl⟩
  set W : AdelicGL2 (𝓞 L) L := sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (s * y)) with hWdef
  have hxdec : s * y = unipotentGL2 ν * diagGL2 t₁ t₂ * κ := by rw [hsdec, hκdef, mul_assoc]

  have hGper : ∀ (k' : L) (t' : 𝔸), borelPartA L A φ (s * y) (unipotentGL2 (ι k' + t') * W)
      = borelPartA L A φ (s * y) (unipotentGL2 t' * W) := by
    intro k' t'
    simp only [borelPartA]
    rw [unipotentGL2_add, ← globalPoints_unipotentGL2]
    have h := finsum_mem_BA_mul_unipotent L A
      (fun γ => φ ((s * y)⁻¹ * globalPoints (𝓞 L) L γ * (unipotentGL2 t' * W))) k'
    refine Eq.trans ?_ h
    refine finsum_mem_congr rfl fun γ _ => ?_
    simp only [map_mul, mul_assoc]
  have hCT : constantTerm ((μ𝔸)[|adelicBox L]) (fun t' => unipotentGL2 t')
        (fun y' => borelPartA L A φ (s * y) (sigmaAdelicAct K L D σ y')) (centralScalar (𝓞 L) L z * (s * y))
      = ((μ𝔸) (adelicBox L))⁻¹.toReal •
          ∫ t' in adelicBox L, borelPartA L A φ (s * y) (unipotentGL2 t' * W) ∂μ𝔸 := by
    rw [constantTerm_cond_adelicBox_eq]
    congr 1
    have h1 : ∀ t' : 𝔸, borelPartA L A φ (s * y)
        (sigmaAdelicAct K L D σ (unipotentGL2 t' * (centralScalar (𝓞 L) L z * (s * y))))
          = borelPartA L A φ (s * y) (unipotentGL2 ((D.act σ : RingAut 𝔸) t') * W) := by
      intro t'
      rw [map_mul, sigmaAdelicAct_unipotentGL2]
    simp_rw [h1]
    exact setIntegral_adelicBox_comp_act K L D σ
      (G := fun t' => borelPartA L A φ (s * y) (unipotentGL2 t' * W)) hGper
  rw [hCT]

  obtain ⟨P, hPS, hPcontrib, hPfin⟩ := exists_finset_slices₂ L hdisc φ hφs (s * y) W
  have hslice : ∀ p : Lˣ × Lˣ, slice₂ L φ (s * y) W p ∈ pureTensorSet L := fun p => by
    have h : slice₂ L φ (s * y) W p
        = fun s' : 𝔸 => φ ((s * y)⁻¹ * torusPt L p * unipotentGL2 s' * W) := by
      funext s'; simp only [slice₂, mul_assoc]
    rw [h]
    exact AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet L hφf _ _
  have hint : ∀ p : Lˣ × Lˣ, Integrable (slice₂ L φ (s * y) W p) μ𝔸 := fun p =>
    NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat L μ𝔸
      (mem_schwartzBruhat_of_mem_pureTensorSet (hslice p))
  have hInt : ∀ p ∈ P, IntegrableOn (fun t' => ∑' ξ : L, slice₂ L φ (s * y) W p (t' + ι ξ))
      (adelicBox L) μ𝔸 := fun p _ =>
    NumberField.AdelicFourier.integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet L (hslice p)
  have hU : ∀ p ∈ P, ∫ t' in adelicBox L, (∑' ξ : L, slice₂ L φ (s * y) W p (t' + ι ξ)) ∂μ𝔸
      = ∫ t', slice₂ L φ (s * y) W p t' ∂μ𝔸 := fun p _ =>
    NumberField.AdelicBox.setIntegral_adelicBox_tsum_add_algebraMap L _ (hint p)
  rw [borelPartA_sub_boxAverage_eq L A φ (s * y) W P hPfin hPS hInt hU]
  set PA' : Finset (Lˣ × Lˣ) := P.filter (· ∈ TA L A) with hPA'
  have hPA'sub : PA' ⊆ P := Finset.filter_subset _ _

  set M : AdelicGL2 (𝓞 L) L := (diagGL2 t₁ t₂)⁻¹ * W with hMdef
  have hslice_form : ∀ (p : Lˣ × Lˣ) (τ : 𝔸), slice₂ L φ (s * y) W p τ
      = φ (κ⁻¹ * (unipotentGL2 (((sliceScale t₁ t₂ : 𝔸ˣ) : 𝔸) *
          (((Units.map (algebraMap L 𝔸 : L →* 𝔸) (p.1 * p.2⁻¹) : 𝔸ˣ) : 𝔸) * τ - ν))
            * torusPt L p * M)) := by
    intro p τ
    simp only [slice₂]
    rw [hxdec, key_identity]
  have hcontribΩ : ∀ p ∈ P, ∃ v : 𝔸, unipotentGL2 v * torusPt L p * M ∈ Ω₀ := by
    intro p hp
    obtain ⟨s₀, hs₀⟩ := hPcontrib p hp
    rw [hslice_form] at hs₀
    exact ⟨_, (κ, _), ⟨hκ, subset_tsupport φ (Function.mem_support.mpr hs₀)⟩, mul_inv_cancel_left κ _⟩
  have hcard : PA'.card ≤ N₀ := (Finset.card_le_card hPA'sub).trans (hN₀ M P hcontribΩ)
  have hbr : ∀ p ∈ P,
      ‖(∑' ξ : L, slice₂ L φ (s * y) W p (ι ξ))
          - ((μ𝔸 (adelicBox L)).toReal : ℂ)⁻¹ * ∫ t', slice₂ L φ (s * y) W p t' ∂μ𝔸‖
        ≤ CH * t⁻¹ ^ (N * Module.finrank ℚ L) := by
    intro p hp
    obtain ⟨s₀, hs₀⟩ := hPcontrib p hp
    set r : 𝔸ˣ := Units.map (algebraMap L 𝔸 : L →* 𝔸) (p.1 * p.2⁻¹) with hrdef
    set v₀ : 𝔸 := ((sliceScale t₁ t₂ : 𝔸ˣ) : 𝔸) * ((r : 𝔸) * s₀ - ν) with hv₀def
    set ω : AdelicGL2 (𝓞 L) L := unipotentGL2 v₀ * torusPt L p * M with hωdef
    have hωmem : (κ⁻¹, ω) ∈ Q := by
      have h0 := hs₀
      rw [hslice_form] at h0
      have hmem : κ⁻¹ * ω ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr h0)
      refine ⟨(κ, κ⁻¹ * ω), ⟨hκ, hmem⟩, ?_⟩
      show ((κ⁻¹, κ * (κ⁻¹ * ω)) : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) = (κ⁻¹, ω)
      rw [mul_inv_cancel_left]

    set qu : Lˣ := q * (p.1 * p.2⁻¹) with hqudef
    have hq' : (qu : L) ≠ 0 := qu.ne_zero
    set e : 𝔸 := -(ι (qu : L) * s₀) with hedef
    have hccr : ((sliceScale t₁ t₂ : 𝔸ˣ) : 𝔸) * (r : 𝔸) = ι (qu : L) * ((α⁻¹ : 𝔸ˣ) : 𝔸) := by
      rw [hτ, hrdef, hqudef]
      simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul]
      ring
    set g : 𝔸 → ℂ := fun v => φ (κ⁻¹ * unipotentGL2 v * ω) with hgdef
    have hform2 : ∀ τ : 𝔸, slice₂ L φ (s * y) W p τ = g ((ι (qu : L) * τ + e) * ((α⁻¹ : 𝔸ˣ) : 𝔸)) := by
      intro τ
      rw [hslice_form, hgdef]
      simp only []
      have hn : unipotentGL2 (((sliceScale t₁ t₂ : 𝔸ˣ) : 𝔸) * ((r : 𝔸) * τ - ν))
          = unipotentGL2 ((ι (qu : L) * τ + e) * ((α⁻¹ : 𝔸ˣ) : 𝔸)) * unipotentGL2 v₀ := by
        rw [← unipotentGL2_add]
        congr 1
        rw [hedef, hv₀def]
        linear_combination (τ - s₀) * hccr
      rw [← hrdef, hn, hωdef]
      simp only [mul_assoc]

    have hsum : (∑' ξ : L, slice₂ L φ (s * y) W p (ι ξ))
        = ∑' β : L, g ((ι β + e) * ((α⁻¹ : 𝔸ˣ) : 𝔸)) := by
      simp_rw [hform2, ← map_mul]
      exact (Equiv.mulLeft₀ (qu : L) hq').tsum_eq (fun β => g ((ι β + e) * ((α⁻¹ : 𝔸ˣ) : 𝔸)))

    have hintl : ∫ τ, slice₂ L φ (s * y) W p τ ∂μ𝔸 = ∫ u, g ((u + e) * ((α⁻¹ : 𝔸ˣ) : 𝔸)) ∂μ𝔸 := by
      simp_rw [hform2]
      exact (NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar L (qu : L) hq').integral_comp
        (measurableEmbedding_mul_algebraMap L hq') (fun u => g ((u + e) * ((α⁻¹ : 𝔸ˣ) : 𝔸)))
    rw [hsum, hintl]
    have hH := hCH (κ⁻¹, ω) hωmem α t ht1 hαf hαa e
    exact hH

  have htA : t ^ Module.finrank ℚ L = Ah := htH
  have hpow : t⁻¹ ^ (N * Module.finrank ℚ L) = Ah⁻¹ ^ N := by
    rw [← htA, inv_pow, inv_pow, ← pow_mul, mul_comm]
  have hAinv : Ah⁻¹ ≤ max K₁ 1 * Hx⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hA0]
    have h1 : Hx ≤ max K₁ 1 * Ah := hcmp'.trans (mul_le_mul_of_nonneg_right hK₁le hA0.le)
    calc (1 : ℝ) = Hx * Hx⁻¹ := (mul_inv_cancel₀ hHx0.ne').symm
      _ ≤ (max K₁ 1 * Ah) * Hx⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hHx0.le)
      _ = max K₁ 1 * Hx⁻¹ * Ah := by ring
  have hAinvN : Ah⁻¹ ^ N ≤ (max K₁ 1) ^ N * Hx⁻¹ ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hA0.le) hAinv N
  have hCH0 : CH ≤ max CH 0 := le_max_left _ _
  calc ‖∑ p ∈ PA', ((∑' ξ : L, slice₂ L φ (s * y) W p (ι ξ))
          - ((μ𝔸 (adelicBox L)).toReal : ℂ)⁻¹ * ∫ t', slice₂ L φ (s * y) W p t' ∂μ𝔸)‖
      ≤ ∑ p ∈ PA', ‖(∑' ξ : L, slice₂ L φ (s * y) W p (ι ξ))
          - ((μ𝔸 (adelicBox L)).toReal : ℂ)⁻¹ * ∫ t', slice₂ L φ (s * y) W p t' ∂μ𝔸‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ PA', max CH 0 * Ah⁻¹ ^ N :=
        Finset.sum_le_sum fun p hp => (hbr p (hPA'sub hp)).trans (by
          rw [hpow]
          exact mul_le_mul_of_nonneg_right hCH0 (pow_nonneg (inv_nonneg.mpr hA0.le) N))
    _ = PA'.card * (max CH 0 * Ah⁻¹ ^ N) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N₀ * (max CH 0 * Ah⁻¹ ^ N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (mul_nonneg (le_max_right _ _) (pow_nonneg (inv_nonneg.mpr hA0.le) N))
    _ ≤ N₀ * (max CH 0 * ((max K₁ 1) ^ N * Hx⁻¹ ^ N)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAinvN (le_max_right _ _)) ?_
        exact_mod_cast Nat.zero_le N₀
    _ = N₀ * (max CH 0 * (max K₁ 1) ^ N) * Hx⁻¹ ^ N := by ring

end Assembly

end R4CuspPoissonA
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow.R4CuspPoissonA"

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφf : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ T₁ : ℝ, ∀ N : ℕ, ∃ C : ℝ, ∀ A : Set L,
      ∀ x ∈ S, T₁ < NumberField.AdelicHeight.adelicHeight L x → ∀ z : (AdeleRing (𝓞 L) L)ˣ,
        ‖(∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
          - @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                  (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
              (AutomorphicForm.centralScalar (𝓞 L) L z * x)‖ ≤
          C * (NumberField.AdelicHeight.adelicHeight L x)⁻¹ ^ N :=
  R4CuspPoissonA.main K L D σ c u d₁ d₂ hc Tc hTc S hS φ hφf

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow.R4CuspPoissonA"

end S_AutomorphicForm_exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow (solution)
