-- Prove2me | solution 1 for AutomorphicForm.continuous_of_isInducedSection_of_continuous_of_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d4d4fea4-bdd4-5496-96dd-1a68f8672636

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_of_isInducedSection_of_continuous_of_apply_ne_zero

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

namespace T1Helpers

section B1

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem diagOne_val {A : Type*} [CommRing A] (a : Aˣ) :
    ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(a : A), 0; 0, 1] := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_inv_val {A : Type*} [CommRing A] (a : Aˣ) :
    (((diagOne a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((a⁻¹ : Aˣ) : A), 0; 0, 1] := by
  rw [← map_inv, diagOne_val]

private theorem centralScalar_val (z : (AdeleRing R K)ˣ) :
    ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = !![(z : AdeleRing R K), 0; 0, (z : AdeleRing R K)] := by
  change Matrix.scalar (Fin 2) (z : AdeleRing R K) = _
  ext i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_mem_adelicBorel (y : (AdeleRing R K)ˣ) : (diagOne y : AdelicGL2 R K) ∈ adelicBorel R K := by
  show ((diagOne y : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  rw [diagOne_val]
  simp

end B1

end T1Helpers

section TorusChi

open NumberField NumberField.AdelicLevel AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

private theorem T1U_continuous_diagOne : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (diagOne y : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![(y : AdeleRing (𝓞 F) F), 0; 0, 1] := fun y => T1Helpers.diagOne_val y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := fun y => T1Helpers.diagOne_inv_val y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_coe_inv
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const

private theorem T1U_continuous_centralScalar :
    Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![(y : AdeleRing (𝓞 F) F), 0; 0, (y : AdeleRing (𝓞 F) F)] := fun y => T1Helpers.centralScalar_val (𝓞 F) F y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_val
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((centralScalar (𝓞 F) F y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] :=
      fun y => by rw [← map_inv]; exact T1Helpers.centralScalar_val (𝓞 F) F y⁻¹
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((centralScalar (𝓞 F) F y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_coe_inv
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_coe_inv

private theorem T1U_borelDiagFst_diagOne (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagOne y, T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = y
  rw [T1Helpers.diagOne_val]
  simp

private theorem T1U_borelDiagSnd_diagOne (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagOne y, T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 1
  rw [T1Helpers.diagOne_val]
  simp

private theorem T1U_borelDiagFst_centralScalar (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨centralScalar (𝓞 F) F y, centralScalar_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = y
  rw [T1Helpers.centralScalar_val]
  simp

private theorem T1U_borelDiagSnd_centralScalar (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨centralScalar (𝓞 F) F y, centralScalar_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = y
  rw [T1Helpers.centralScalar_val]
  simp

private theorem T1U_continuous_monoidHom_units_of_continuous_val (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : Continuous fun y => ((χ y : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((χ y)⁻¹ : ℂˣ) : ℂ)
  simp_rw [← map_inv]
  exact h.comp continuous_inv

end TorusChi

theorem solution
    (F : Type) [Field F] [NumberField F]
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (_hφc : Continuous φ)
    (_hne : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0) :
    Continuous χ₁ ∧ Continuous χ₂ := by
  obtain ⟨g₀, h0⟩ := _hne

  have h1val : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((χ₁ y : ℂˣ) : ℂ) = φ (diagOne y * g₀) / φ g₀ := by
    intro y
    have h := _hφ _ (T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y) g₀
    rw [T1U_borelDiagFst_diagOne, T1U_borelDiagSnd_diagOne, map_one, Units.val_one, mul_one] at h
    rw [h, mul_div_cancel_right₀ _ h0]
  have h1c : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((χ₁ y : ℂˣ) : ℂ) := by
    simp_rw [h1val]
    exact (_hφc.comp ((T1U_continuous_diagOne F).mul continuous_const)).div_const _

  have h2val : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((χ₂ y : ℂˣ) : ℂ)
      = φ (centralScalar (𝓞 F) F y * g₀) / (((χ₁ y : ℂˣ) : ℂ) * φ g₀) := by
    intro y
    have h := _hφ _ (centralScalar_mem_adelicBorel (𝓞 F) F y) g₀
    rw [T1U_borelDiagFst_centralScalar, T1U_borelDiagSnd_centralScalar] at h
    rw [h, eq_div_iff (mul_ne_zero (χ₁ y).ne_zero h0)]
    ring
  have h2c : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((χ₂ y : ℂˣ) : ℂ) := by
    simp_rw [h2val]
    refine (_hφc.comp ((T1U_continuous_centralScalar F).mul continuous_const)).div
      (h1c.mul continuous_const) fun y => mul_ne_zero (χ₁ y).ne_zero h0
  exact ⟨T1U_continuous_monoidHom_units_of_continuous_val F χ₁ h1c,
    T1U_continuous_monoidHom_units_of_continuous_val F χ₂ h2c⟩

end S_AutomorphicForm_continuous_of_isInducedSection_of_continuous_of_apply_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_continuous_of_isInducedSection_of_continuous_of_apply_ne_zero (solution)
