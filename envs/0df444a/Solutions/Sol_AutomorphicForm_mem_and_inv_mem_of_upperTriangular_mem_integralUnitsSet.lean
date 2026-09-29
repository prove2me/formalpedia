-- Prove2me | solution 1 for AutomorphicForm.mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a16050f8-68a3-522a-9d3c-708be0de050d

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet

set_option autoImplicit false

theorem solution
    {A : Type*} [CommRing A] (R : Set A) (hR : ∀ a ∈ R, ∀ b ∈ R, a * b ∈ R)
    (M : GL (Fin 2) A) (ζ a : Aˣ)
    (h10 : (M : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h11 : (M : Matrix (Fin 2) (Fin 2) A) 1 1 = ζ)
    (h00 : (M : Matrix (Fin 2) (Fin 2) A) 0 0 = a * ζ)
    (hM : M ∈ AutomorphicForm.integralUnitsSet R) :
    ((ζ : A) ∈ R ∧ ((ζ⁻¹ : Aˣ) : A) ∈ R) ∧ ((a : A) ∈ R ∧ ((a⁻¹ : Aˣ) : A) ∈ R) := by
  obtain ⟨hMR, hNR⟩ := AutomorphicForm.mem_integralUnitsSet.mp hM
  set N : Matrix (Fin 2) (Fin 2) A := ((M⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) with hN
  have hMN : (M : Matrix (Fin 2) (Fin 2) A) * N = 1 := by
    rw [hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * (M : Matrix (Fin 2) (Fin 2) A) = 1 := by
    rw [hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e11 : (ζ : A) * N 1 1 = 1 := by
    have h := congrFun (congrFun hMN 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add, Matrix.one_apply_eq] at h
    exact h
  have e00 : N 0 0 * ((a : A) * ζ) = 1 := by
    have h := congrFun (congrFun hNM 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, h00, h10, mul_zero, add_zero, Matrix.one_apply_eq] at h
    exact h
  have hζinv : ((ζ⁻¹ : Aˣ) : A) = N 1 1 := by
    calc ((ζ⁻¹ : Aˣ) : A) = ((ζ⁻¹ : Aˣ) : A) * ((ζ : A) * N 1 1) := by rw [e11, mul_one]
      _ = N 1 1 := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have haζinv : (((a * ζ)⁻¹ : Aˣ) : A) = N 0 0 := by
    calc (((a * ζ)⁻¹ : Aˣ) : A) = N 0 0 * ((a : A) * ζ) * (((a * ζ)⁻¹ : Aˣ) : A) := by rw [e00, one_mul]
      _ = N 0 0 := by rw [← Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
  have hζR : (ζ : A) ∈ R := h11 ▸ hMR 1 1
  have hζiR : ((ζ⁻¹ : Aˣ) : A) ∈ R := hζinv ▸ hNR 1 1
  have haζR : (a : A) * ζ ∈ R := h00 ▸ hMR 0 0
  have haζiR : (((a * ζ)⁻¹ : Aˣ) : A) ∈ R := haζinv ▸ hNR 0 0
  refine ⟨⟨hζR, hζiR⟩, ?_, ?_⟩
  · have h : (a : A) = (a : A) * ζ * ((ζ⁻¹ : Aˣ) : A) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [h]
    exact hR _ haζR _ hζiR
  · have h : ((a⁻¹ : Aˣ) : A) = (ζ : A) * (((a * ζ)⁻¹ : Aˣ) : A) := by
      rw [← Units.val_mul]
      congr 1
      group
    rw [h]
    exact hR _ hζR _ haζiR

end S_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
end P2MW
export P2MW.S_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet (solution)
