-- Prove2me | solution 1 for AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8947ebea-ec30-5929-87cf-dd07e8b11ea4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L A : Type) [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (α β a₁ a₂ : (L ⊗[K] A)ˣ) (ξ : L ⊗[K] A) (k : GL (Fin 2) (L ⊗[K] A)) :
    (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k)⁻¹ * diagUnits2 α β *
        AutomorphicForm.sigmaGL K L A σ (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k) =
      k⁻¹ *
        (diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₁ * a₁⁻¹)
            (β * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₂ * a₂⁻¹) *
          AutomorphicForm.unipotentGL2
            (AutomorphicForm.sigmaTensor K L A σ ξ -
              (((β * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₂ * a₂⁻¹) *
                  (α * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₁ * a₁⁻¹)⁻¹ : (L ⊗[K] A)ˣ) :
                L ⊗[K] A) * ξ)) *
        AutomorphicForm.sigmaGL K L A σ k := by
  classical

  set σT : L ⊗[K] A →+* L ⊗[K] A := AutomorphicForm.sigmaTensor K L A σ with hσT
  set s₁ : (L ⊗[K] A)ˣ := Units.map σT.toMonoidHom a₁ with hs₁
  set s₂ : (L ⊗[K] A)ˣ := Units.map σT.toMonoidHom a₂ with hs₂
  set d₁ : (L ⊗[K] A)ˣ := α * s₁ * a₁⁻¹ with hd₁
  set d₂ : (L ⊗[K] A)ˣ := β * s₂ * a₂⁻¹ with hd₂

  have hcoe : ∀ g : GL (Fin 2) (L ⊗[K] A),
      ((AutomorphicForm.sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
        (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map σT := fun g => rfl
  have hσA : AutomorphicForm.sigmaGL K L A σ (diagUnits2 a₁ a₂) = diagUnits2 s₁ s₂ := by
    apply Units.ext
    rw [hcoe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, hs₁, hs₂, Matrix.map_apply]
  have hσN : AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.unipotentGL2 ξ) = AutomorphicForm.unipotentGL2 (σT ξ) := by
    apply Units.ext
    rw [hcoe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2_coe, Matrix.map_apply]

  have ha₁ : (a₁ : L ⊗[K] A) * ((a₁⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = 1 := Units.mul_inv a₁
  have ha₂ : (a₂ : L ⊗[K] A) * ((a₂⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = 1 := Units.mul_inv a₂
  have hd1 : (a₁ : L ⊗[K] A) * (d₁ : L ⊗[K] A) = (α : L ⊗[K] A) * (s₁ : L ⊗[K] A) := by
    rw [hd₁]; push_cast; linear_combination ((α : L ⊗[K] A) * (s₁ : L ⊗[K] A)) * ha₁
  have hd2 : (a₂ : L ⊗[K] A) * (d₂ : L ⊗[K] A) = (β : L ⊗[K] A) * (s₂ : L ⊗[K] A) := by
    rw [hd₂]; push_cast; linear_combination ((β : L ⊗[K] A) * (s₂ : L ⊗[K] A)) * ha₂
  have hdd : (d₁ : L ⊗[K] A) * ((d₁⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = 1 := Units.mul_inv d₁

  have key : diagUnits2 α β * diagUnits2 s₁ s₂ * AutomorphicForm.unipotentGL2 (σT ξ) =
      diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ *
        (diagUnits2 d₁ d₂ * AutomorphicForm.unipotentGL2 (σT ξ - ((d₂ * d₁⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * ξ)) := by
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, AutomorphicForm.unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-1 : L ⊗[K] A) * hd1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-(σT ξ)) * hd1 + ((a₁ : L ⊗[K] A) * (d₂ : L ⊗[K] A) * ξ) * hdd
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-1 : L ⊗[K] A) * hd2

  calc (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k)⁻¹ * diagUnits2 α β *
          AutomorphicForm.sigmaGL K L A σ (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k)
      = (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k)⁻¹ *
          (diagUnits2 α β * diagUnits2 s₁ s₂ * AutomorphicForm.unipotentGL2 (σT ξ)) *
          AutomorphicForm.sigmaGL K L A σ k := by
        rw [map_mul, map_mul, hσA, hσN]; simp only [mul_assoc]
    _ = (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k)⁻¹ *
          (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ *
            (diagUnits2 d₁ d₂ * AutomorphicForm.unipotentGL2 (σT ξ - ((d₂ * d₁⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * ξ))) *
          AutomorphicForm.sigmaGL K L A σ k := by rw [key]
    _ = k⁻¹ * (diagUnits2 d₁ d₂ *
          AutomorphicForm.unipotentGL2 (σT ξ - ((d₂ * d₁⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * ξ)) *
          AutomorphicForm.sigmaGL K L A σ k := by group

end S_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
end P2MW
export P2MW.S_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul (solution)
