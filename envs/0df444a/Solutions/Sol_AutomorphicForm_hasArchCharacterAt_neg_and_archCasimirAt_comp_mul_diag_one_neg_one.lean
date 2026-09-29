-- Prove2me | solution 1 for AutomorphicForm.hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3098a607-a715-52c3-9727-9af07cff8300

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one

set_option autoImplicit false

noncomputable section

namespace Ws23
namespace K3

open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel Matrix
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

def eps : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by simp)

theorem eps_val : (eps : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, -1] := rfl

theorem eps_mul_eps : eps * eps = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_one, eps_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem archFlowMatrix_H_mul_eps (t : ℝ) :
    archFlowMatrix .H t * eps = eps * archFlowMatrix .H t := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, eps_val]
  fin_cases i <;> fin_cases j <;>
    simp [archFlowMatrix, splitTorusGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem archFlowMatrix_E_mul_eps (t : ℝ) :
    archFlowMatrix .E t * eps = eps * archFlowMatrix .E (-t) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, eps_val]
  fin_cases i <;> fin_cases j <;>
    simp [archFlowMatrix, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem archFlowMatrix_Fm_mul_eps (t : ℝ) :
    archFlowMatrix .Fm t * eps = eps * archFlowMatrix .Fm (-t) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, eps_val]
  fin_cases i <;> fin_cases j <;>
    simp [archFlowMatrix, lowerUnipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem archFlowAt_H_mul_eps (t : ℝ) :
    archFlowAt hw .H t * archRealGLAt hw eps = archRealGLAt hw eps * archFlowAt hw .H t := by
  show archRealGLAt hw _ * archRealGLAt hw eps = archRealGLAt hw eps * archRealGLAt hw _
  rw [← map_mul, ← map_mul, archFlowMatrix_H_mul_eps]

theorem archFlowAt_E_mul_eps (t : ℝ) :
    archFlowAt hw .E t * archRealGLAt hw eps = archRealGLAt hw eps * archFlowAt hw .E (-t) := by
  show archRealGLAt hw _ * archRealGLAt hw eps = archRealGLAt hw eps * archRealGLAt hw _
  rw [← map_mul, ← map_mul, archFlowMatrix_E_mul_eps]

theorem archFlowAt_Fm_mul_eps (t : ℝ) :
    archFlowAt hw .Fm t * archRealGLAt hw eps = archRealGLAt hw eps * archFlowAt hw .Fm (-t) := by
  show archRealGLAt hw _ * archRealGLAt hw eps = archRealGLAt hw eps * archRealGLAt hw _
  rw [← map_mul, ← map_mul, archFlowMatrix_Fm_mul_eps]

theorem archDerivAt_H_comp_mul_eps (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw .H (fun g => φ (g * archRealGLAt hw eps))
      = fun g => archDerivAt hw .H φ (g * archRealGLAt hw eps) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw .H t * archRealGLAt hw eps)) 0
    = deriv (fun t : ℝ => φ (g * archRealGLAt hw eps * archFlowAt hw .H t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAt_H_mul_eps, ← mul_assoc]

theorem archDerivAt_E_comp_mul_eps (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw .E (fun g => φ (g * archRealGLAt hw eps))
      = fun g => -archDerivAt hw .E φ (g * archRealGLAt hw eps) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw .E t * archRealGLAt hw eps)) 0
    = -deriv (fun t : ℝ => φ (g * archRealGLAt hw eps * archFlowAt hw .E t)) 0
  have hfun : (fun t : ℝ => φ (g * archFlowAt hw .E t * archRealGLAt hw eps))
      = fun t : ℝ => (fun s : ℝ => φ (g * archRealGLAt hw eps * archFlowAt hw .E s)) (-t) := by
    funext t
    rw [mul_assoc, archFlowAt_E_mul_eps, ← mul_assoc]
  rw [hfun, deriv_comp_neg (fun s : ℝ => φ (g * archRealGLAt hw eps * archFlowAt hw .E s)) (0 : ℝ), neg_zero]

theorem archDerivAt_Fm_comp_mul_eps (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw .Fm (fun g => φ (g * archRealGLAt hw eps))
      = fun g => -archDerivAt hw .Fm φ (g * archRealGLAt hw eps) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw .Fm t * archRealGLAt hw eps)) 0
    = -deriv (fun t : ℝ => φ (g * archRealGLAt hw eps * archFlowAt hw .Fm t)) 0
  have hfun : (fun t : ℝ => φ (g * archFlowAt hw .Fm t * archRealGLAt hw eps))
      = fun t : ℝ => (fun s : ℝ => φ (g * archRealGLAt hw eps * archFlowAt hw .Fm s)) (-t) := by
    funext t
    rw [mul_assoc, archFlowAt_Fm_mul_eps, ← mul_assoc]
  rw [hfun, deriv_comp_neg (fun s : ℝ => φ (g * archRealGLAt hw eps * archFlowAt hw .Fm s)) (0 : ℝ), neg_zero]

theorem archDerivAt_neg (d : ArchDir) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (-ψ) = -archDerivAt hw d ψ := by
  funext g
  show deriv (fun t : ℝ => -ψ (g * archFlowAt hw d t)) 0 = -deriv (fun t : ℝ => ψ (g * archFlowAt hw d t)) 0
  exact deriv.fun_neg

theorem archCasimirAt_comp_mul_eps (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (fun g => φ (g * archRealGLAt hw eps))
      = fun g => archCasimirAt hw φ (g * archRealGLAt hw eps) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_H_comp_mul_eps hw φ,
    archDerivAt_H_comp_mul_eps hw (archDerivAt hw .H φ), archDerivAt_Fm_comp_mul_eps hw φ]
  have hneg : (fun g => -archDerivAt hw .Fm φ (g * archRealGLAt hw eps))
      = fun g => (-archDerivAt hw .Fm φ) (g * archRealGLAt hw eps) := rfl
  rw [hneg, archDerivAt_E_comp_mul_eps hw (-archDerivAt hw .Fm φ), archDerivAt_neg]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, neg_neg]

theorem isArchSmoothAt_comp_mul_eps {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    IsArchSmoothAt hw (fun g => φ (g * archRealGLAt hw eps)) := by
  intro g
  have hε : (eps : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [eps_val, Matrix.det_fin_two_of]; norm_num
  have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℝ =>
      (Matrix.of.symm (Matrix.of e * (eps : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ))
      {e | (Matrix.of e).det ≠ 0} {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    show (Matrix.of (Matrix.of.symm (Matrix.of e * (eps : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero he hε
  refine ((hφ g).comp (contDiff_of_symm_mul_const (eps : Matrix (Fin 2) (Fin 2) ℝ)).contDiffOn hmaps).congr ?_
  intro e he
  show φ (g * archRealLiftAt hw e * archRealGLAt hw eps) = φ (g * archRealLiftAt hw _)
  rw [mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]

def epsW : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm eps

theorem archRealGLAt_eps : archRealGLAt hw eps = adelicArchGLInclAt F w (epsW hw) := rfl

omit [NumberField F] in
theorem epsW_val : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) = !![1, 0; 0, -1] := by
  ext i j
  rw [epsW, glEquivOfRingEquiv_apply_entry, eps_val]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField F] in
theorem epsW_mul_epsW : epsW hw * epsW hw = 1 := by
  rw [epsW, ← map_mul, eps_mul_eps, map_one]

omit [NumberField F] in
theorem epsW_apply_00 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = 1 := by
  rw [epsW_val]; rfl
omit [NumberField F] in
theorem epsW_apply_01 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0 := by
  rw [epsW_val]; rfl
omit [NumberField F] in
theorem epsW_apply_10 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
  rw [epsW_val]; rfl
omit [NumberField F] in
theorem epsW_apply_11 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = -1 := by
  rw [epsW_val]; rfl

omit [NumberField F] in

theorem val_epsW_mul_mul_epsW (k : GL (Fin 2) w.Completion) :
    ((epsW hw * k * epsW hw : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = !![(k : Matrix (Fin 2) (Fin 2) w.Completion) 0 0, -(k : Matrix (Fin 2) (Fin 2) w.Completion) 0 1;
           -(k : Matrix (Fin 2) (Fin 2) w.Completion) 1 0, (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, epsW_apply_00, epsW_apply_01,
      epsW_apply_10, epsW_apply_11]

omit [NumberField F] in
theorem epsW_mul_mul_epsW_mem (k : rowIsometrySubgroup₀ w.Completion) :
    epsW hw * (k : GL (Fin 2) w.Completion) * epsW hw ∈ rowIsometrySubgroup₀ w.Completion := by
  obtain ⟨hd, hnd, hiso⟩ := (mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2
  have hdet : ((epsW hw * (k : GL (Fin 2) w.Completion) * epsW hw : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
    rw [val_epsW_mul_mul_epsW, Matrix.det_fin_two_of, ← hd, Matrix.det_fin_two]
    ring
  refine (mem_rowIsometrySubgroup₀_iff w.Completion).mpr ⟨hdet, ?_, fun x y => ?_⟩
  · rw [hdet, norm_one]
  · have h := hiso x (-y)
    rw [norm_neg] at h
    rw [val_epsW_mul_mul_epsW]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have e1 : x * (k : GL (Fin 2) w.Completion) 0 0 + y * -(k : GL (Fin 2) w.Completion) 1 0
        = x * (k : GL (Fin 2) w.Completion) 0 0 + -y * (k : GL (Fin 2) w.Completion) 1 0 := by ring
    have e2 : x * -(k : GL (Fin 2) w.Completion) 0 1 + y * (k : GL (Fin 2) w.Completion) 1 1
        = -(x * (k : GL (Fin 2) w.Completion) 0 1 + -y * (k : GL (Fin 2) w.Completion) 1 1) := by ring
    rw [e1, e2, norm_neg]
    exact h

def conjK (k : rowIsometrySubgroup₀ w.Completion) : rowIsometrySubgroup₀ w.Completion :=
  ⟨epsW hw * (k : GL (Fin 2) w.Completion) * epsW hw, epsW_mul_mul_epsW_mem hw k⟩

theorem incl_mul_eps (k : rowIsometrySubgroup₀ w.Completion) :
    adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) * archRealGLAt hw eps
      = archRealGLAt hw eps * adelicArchGLInclAt F w (conjK hw k : GL (Fin 2) w.Completion) := by
  rw [archRealGLAt_eps, ← map_mul, ← map_mul]
  congr 1
  show (k : GL (Fin 2) w.Completion) * epsW hw = epsW hw * (epsW hw * (k : GL (Fin 2) w.Completion) * epsW hw)
  rw [← mul_assoc, ← mul_assoc, epsW_mul_epsW, one_mul]

omit [NumberField F] in
theorem val_archWeightOneAt (k : rowIsometrySubgroup₀ w.Completion) :
    ((archWeightOneAt hw k : ℂˣ) : ℂ)
      = ⟨ringEquivRealOfIsReal hw ((k : GL (Fin 2) w.Completion) 0 0),
         ringEquivRealOfIsReal hw ((k : GL (Fin 2) w.Completion) 0 1)⟩ := rfl

omit [NumberField F] in
theorem archWeightOneAt_conjK (k : rowIsometrySubgroup₀ w.Completion) :
    archWeightOneAt hw (conjK hw k) = (archWeightOneAt hw k)⁻¹ := by
  have hmem : glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion)
      ∈ rowIsometrySubgroup₀ ℝ :=
    map_mem_rowIsometrySubgroup₀_of_normPreserving _ (norm_ringEquivRealOfIsReal hw) _ k.2
  have hn : Complex.normSq ((archWeightOneAt hw k : ℂˣ) : ℂ) = 1 := normSq_firstRowℂ_of_mem hmem
  apply Units.ext
  rw [Units.val_inv_eq_inv_val]
  have h00 : ((conjK hw k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) 0 0
      = (k : GL (Fin 2) w.Completion) 0 0 := by
    show ((epsW hw * (k : GL (Fin 2) w.Completion) * epsW hw : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = _
    rw [val_epsW_mul_mul_epsW]; rfl
  have h01 : ((conjK hw k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) 0 1
      = -(k : GL (Fin 2) w.Completion) 0 1 := by
    show ((epsW hw * (k : GL (Fin 2) w.Completion) * epsW hw : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = _
    rw [val_epsW_mul_mul_epsW]; rfl
  rw [val_archWeightOneAt hw (conjK hw k), h00, h01, map_neg]
  rw [val_archWeightOneAt] at hn ⊢
  apply Complex.ext
  · rw [Complex.inv_re, hn, div_one]
  · rw [Complex.inv_im, hn, div_one]

omit [NumberField F] in
theorem archWeightCharAt_conjK (n : ℤ) (k : rowIsometrySubgroup₀ w.Completion) :
    archWeightCharAt hw n (conjK hw k) = archWeightCharAt hw (-n) k := by
  show (archWeightOneAt hw (conjK hw k)) ^ n = (archWeightOneAt hw k) ^ (-n)
  rw [archWeightOneAt_conjK, _root_.inv_zpow, _root_.zpow_neg]

theorem hasArchCharacterAt₀_neg_comp_mul_eps {φ : AdelicGL2 (𝓞 F) F → ℂ} {n : ℤ}
    (hφ : HasArchCharacterAt₀ F w (archWeightCharAt hw n) φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw (-n)) (fun g => φ (g * archRealGLAt hw eps)) := by
  intro k g
  show φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) * archRealGLAt hw eps)
    = (archWeightCharAt hw (-n) k : ℂ) * φ (g * archRealGLAt hw eps)
  rw [mul_assoc, incl_mul_eps, ← mul_assoc, hφ (conjK hw k) (g * archRealGLAt hw eps),
    archWeightCharAt_conjK]

end Ws23.K3

end

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion in

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ) :
    let ε : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by simp)
    HasArchCharacterAt₀ F w (archWeightCharAt hw (-k)) (fun g => φ (g * archRealGLAt hw ε)) ∧
    (IsArchSmoothAt hw φ → IsArchSmoothAt hw (fun g => φ (g * archRealGLAt hw ε))) ∧
    (archCasimirAt hw (fun g => φ (g * archRealGLAt hw ε)) =
      fun g => archCasimirAt hw φ (g * archRealGLAt hw ε)) := by
  intro ε
  have hε : ε = Ws23.K3.eps := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hε]; exact Ws23.K3.hasArchCharacterAt₀_neg_comp_mul_eps hw hk
  · rw [hε]; exact fun hφ => Ws23.K3.isArchSmoothAt_comp_mul_eps hw hφ
  · rw [hε]; exact Ws23.K3.archCasimirAt_comp_mul_eps hw φ

end S_AutomorphicForm_hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one
end P2MW
export P2MW.S_AutomorphicForm_hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one (solution)
