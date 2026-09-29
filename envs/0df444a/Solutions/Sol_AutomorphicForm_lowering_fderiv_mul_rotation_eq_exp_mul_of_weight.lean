-- Prove2me | solution 1 for AutomorphicForm.lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/30c30101-357c-58c9-9ea2-ab1e45a6f566

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight

set_option autoImplicit false

open Complex
open scoped Topology

noncomputable section

namespace AutomorphicForm

namespace LoweringShift

def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
def matH : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def matS : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def adH (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.cos (2 * θ) • matH - Real.sin (2 * θ) • matS

def adS (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.sin (2 * θ) • matH + Real.cos (2 * θ) • matS

theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    rw [← sq, ← sq]; exact Real.cos_sq_add_sin_sq θ
  simp [rot, Matrix.det_fin_two]
  linarith

theorem adH_mul_rot (θ : ℝ) : adH θ * rot θ = rot θ * matH := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have hcθ : (Real.sin θ ^ 2 + Real.cos θ ^ 2) * Real.cos θ = Real.cos θ := by rw [h1, one_mul]
  have hsθ : (Real.sin θ ^ 2 + Real.cos θ ^ 2) * Real.sin θ = Real.sin θ := by rw [h1, one_mul]
  have hc : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hs : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adH, rot, matH, matS, Matrix.mul_apply, Fin.sum_univ_two, hc, hs] <;> nlinarith [hcθ, hsθ, h1]

theorem adS_mul_rot (θ : ℝ) : adS θ * rot θ = rot θ * matS := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have hcθ : (Real.sin θ ^ 2 + Real.cos θ ^ 2) * Real.cos θ = Real.cos θ := by rw [h1, one_mul]
  have hsθ : (Real.sin θ ^ 2 + Real.cos θ ^ 2) * Real.sin θ = Real.sin θ := by rw [h1, one_mul]
  have hc : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hs : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adS, rot, matH, matS, Matrix.mul_apply, Fin.sum_univ_two, hc, hs] <;> nlinarith [hcθ, hsθ, h1]

def rmul (θ : ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun n => ((Matrix.of n * rot θ : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)
      map_add' := fun a b => by
        show ((Matrix.of a + Matrix.of b) * rot θ : Matrix (Fin 2) (Fin 2) ℝ) = _
        rw [Matrix.add_mul]; rfl
      map_smul' := fun r a => by
        show ((r • Matrix.of a) * rot θ : Matrix (Fin 2) (Fin 2) ℝ) = _
        rw [Matrix.smul_mul]; rfl }

theorem rmul_apply (θ : ℝ) (n : Matrix (Fin 2) (Fin 2) ℝ) :
    rmul θ n = ((n * rot θ : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := rfl

theorem exp_mul_cos_sub (k : ℤ) (θ : ℝ) :
    Complex.exp (Complex.I * k * θ) * ((Real.cos (2 * θ) : ℂ) - Complex.I * (Real.sin (2 * θ) : ℂ)) =
      Complex.exp (Complex.I * (k - 2) * θ) := by
  have h : ((Real.cos (2 * θ) : ℂ) - Complex.I * (Real.sin (2 * θ) : ℂ)) =
      Complex.exp (Complex.I * (-2 * θ)) := by
    rw [show Complex.I * (-2 * (θ : ℂ)) = ((-(2 * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h, ← Complex.exp_add]
  congr 1
  ring

theorem main (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ)
    (hF : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → DifferentiableAt ℝ F m)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F m)
    (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : 0 < m.det) (θ : ℝ) :
    (fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
          ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![1, 0; 0, -1]) -
        Complex.I *
          fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
            ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![0, 1; 1, 0])) / 2 =
      Complex.exp (Complex.I * (k - 2) * θ) *
        ((fderiv ℝ F m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ F m (m * !![0, 1; 1, 0])) / 2) := by

  change (fderiv ℝ F (m * rot θ) ((m * rot θ) * matH) -
      Complex.I * fderiv ℝ F (m * rot θ) ((m * rot θ) * matS)) / 2 =
    Complex.exp (Complex.I * (k - 2) * θ) *
      ((fderiv ℝ F m (m * matH) - Complex.I * fderiv ℝ F m (m * matS)) / 2)
  have hmr : 0 < (m * rot θ).det := by rw [Matrix.det_mul, det_rot, mul_one]; exact hm

  let mP : Fin 2 → Fin 2 → ℝ := m

  set L₁ : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ := fderiv ℝ F (m * rot θ) with hL₁
  set L₀ : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ := fderiv ℝ F m with hL₀
  have hcomp : HasFDerivAt (fun n : Fin 2 → Fin 2 → ℝ => F (rmul θ n)) (L₁.comp (rmul θ)) mP := by
    have h1 : HasFDerivAt F L₁ (rmul θ mP) := (hF _ hmr).hasFDerivAt
    have h2 : HasFDerivAt (rmul θ) (rmul θ) mP := (rmul θ).hasFDerivAt
    exact h1.comp mP h2
  have hopen : IsOpen {n : Fin 2 → Fin 2 → ℝ | 0 < (Matrix.of n).det} := by
    have hcont : Continuous fun n : Fin 2 → Fin 2 → ℝ => (Matrix.of n).det := by
      have : (fun n : Fin 2 → Fin 2 → ℝ => (Matrix.of n).det) =
          fun n => n 0 0 * n 1 1 - n 0 1 * n 1 0 := by
        funext n; rw [Matrix.det_fin_two]; rfl
      rw [this]
      fun_prop
    exact hcont.isOpen_preimage _ isOpen_Ioi
  have hev : (fun n : Fin 2 → Fin 2 → ℝ => F (rmul θ n)) =ᶠ[𝓝 mP]
      fun n => Complex.exp (Complex.I * k * θ) * F n := by
    filter_upwards [hopen.mem_nhds (show 0 < (Matrix.of mP).det from hm)]
      with n hn
    exact hk (Matrix.of n) hn θ
  have hscal : HasFDerivAt (fun n : Fin 2 → Fin 2 → ℝ => Complex.exp (Complex.I * k * θ) * F n)
      (Complex.exp (Complex.I * k * θ) • L₀) mP :=
    ((hF m hm).hasFDerivAt).const_mul _
  have hLeq : L₁.comp (rmul θ) = Complex.exp (Complex.I * k * θ) • L₀ :=
    (hcomp.congr_of_eventuallyEq hev.symm).unique hscal

  have hevalH : L₁ ((m * rot θ) * matH) = Complex.exp (Complex.I * k * θ) * L₀ (m * adH θ) := by
    have h := congrArg (fun T : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ => T (m * adH θ)) hLeq
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul] at h
    rw [rmul_apply] at h
    have hmat : (m * adH θ) * rot θ = (m * rot θ) * matH := by
      rw [Matrix.mul_assoc, adH_mul_rot, ← Matrix.mul_assoc]
    rw [hmat] at h
    exact h
  have hevalS : L₁ ((m * rot θ) * matS) = Complex.exp (Complex.I * k * θ) * L₀ (m * adS θ) := by
    have h := congrArg (fun T : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ => T (m * adS θ)) hLeq
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul] at h
    rw [rmul_apply] at h
    have hmat : (m * adS θ) * rot θ = (m * rot θ) * matS := by
      rw [Matrix.mul_assoc, adS_mul_rot, ← Matrix.mul_assoc]
    rw [hmat] at h
    exact h

  let L₀M : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℂ :=
    { toFun := fun M => L₀ M
      map_add' := fun M N => L₀.map_add M N
      map_smul' := fun r M => L₀.map_smul r M }
  have hL₀M : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, L₀ M = L₀M M := fun _ => rfl
  have hH : L₀ (m * adH θ) = (Real.cos (2 * θ) : ℂ) * L₀ (m * matH) - (Real.sin (2 * θ) : ℂ) * L₀ (m * matS) := by
    have : m * adH θ = Real.cos (2 * θ) • (m * matH) - Real.sin (2 * θ) • (m * matS) := by
      simp [adH, Matrix.mul_sub]
    rw [hL₀M, this, map_sub, LinearMap.map_smul, LinearMap.map_smul, ← hL₀M, ← hL₀M]
    simp [Complex.real_smul]
  have hS : L₀ (m * adS θ) = (Real.sin (2 * θ) : ℂ) * L₀ (m * matH) + (Real.cos (2 * θ) : ℂ) * L₀ (m * matS) := by
    have : m * adS θ = Real.sin (2 * θ) • (m * matH) + Real.cos (2 * θ) • (m * matS) := by
      simp [adS, Matrix.mul_add]
    rw [hL₀M, this, map_add, LinearMap.map_smul, LinearMap.map_smul, ← hL₀M, ← hL₀M]
    simp [Complex.real_smul]
  rw [hevalH, hevalS, hH, hS, ← exp_mul_cos_sub k θ]
  linear_combination
    (-(1 : ℂ) / 2 * Complex.exp (Complex.I * k * θ) * (Real.sin (2 * θ) : ℂ) * L₀ (m * matS)) * Complex.I_sq

end LoweringShift

end AutomorphicForm

end

theorem solution
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ)
    (hF : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → DifferentiableAt ℝ F m)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F m)
    (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : 0 < m.det) (θ : ℝ) :
    (fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
          ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![1, 0; 0, -1]) -
        Complex.I *
          fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
            ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![0, 1; 1, 0])) / 2 =
      Complex.exp (Complex.I * (k - 2) * θ) *
        ((fderiv ℝ F m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ F m (m * !![0, 1; 1, 0])) / 2) :=
  AutomorphicForm.LoweringShift.main F k hF hk m hm θ

end S_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
end P2MW
export P2MW.S_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight (solution)
