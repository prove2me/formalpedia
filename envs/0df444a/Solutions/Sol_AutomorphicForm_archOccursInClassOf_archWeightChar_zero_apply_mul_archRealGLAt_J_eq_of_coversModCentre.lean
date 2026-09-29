-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8dbfbf74-3687-52b0-8fa1-5b1309a9d724

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_SiegelCovering
import Theorems.Thm_AutomorphicForm_memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RJSym
namespace K3

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel Matrix"
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

def eps : GL (Fin 2) ℝ := UpperHalfPlane.J

theorem eps_val : (eps : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 0; 0, 1] := rfl

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
theorem epsW_val : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) = !![-1, 0; 0, 1] := by
  ext i j
  rw [epsW, glEquivOfRingEquiv_apply_entry, eps_val]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField F] in
theorem epsW_mul_epsW : epsW hw * epsW hw = 1 := by
  rw [epsW, ← map_mul, eps_mul_eps, map_one]

omit [NumberField F] in
theorem epsW_apply_00 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = -1 := by
  rw [epsW_val]; rfl
omit [NumberField F] in
theorem epsW_apply_01 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0 := by
  rw [epsW_val]; rfl
omit [NumberField F] in
theorem epsW_apply_10 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
  rw [epsW_val]; rfl
omit [NumberField F] in
theorem epsW_apply_11 : (epsW hw : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = 1 := by
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

end RJSym.K3

end

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf productionPinsOf_ν AdelicGL2 centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem glEquivOfRingEquiv glEquivOfRingEquiv_apply_entry map_mem_rowIsometrySubgroup₀_of_normPreserving rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightOneAt archWeightCharAt rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff normSq_firstRowℂ_of_mem archWeightCharℝ HasArchCharacterAt₀ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne adelicArchGLInclAt archRealGLAt archRealLiftAt IsArchSmoothAt ArchDir lowerUnipotentGL2_coe splitTorusGL2_coe archFlowMatrix archFlowAt archDerivAt archCasimirAt archRealLiftAt_mul_archRealGLAt contDiff_of_symm_mul_const archDerivAt_add archDerivAt_smul archCasimirAt_add archCasimirAt_smul IsBoundedOnSiegelWindows memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre"
p2m_open "AutomorphicForm"

namespace RJSymP

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix IsDedekindDomain
open AutomorphicForm.SmoothCusp HeckeIntegralSeam FLT.SmoothVectors
open scoped ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

section Plumbing

variable {w : InfinitePlace F}

theorem incl_fst (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      i j).1 = archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl

theorem incl_snd (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      i j).2 = (1 : Matrix (Fin 2) (Fin 2) _) i j := rfl

theorem incl_fst_self (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      i j).1 w = (k : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [incl_fst, archMatrixUpdate_apply_self]

theorem incl_fst_of_ne (k : GL (Fin 2) w.Completion) (i j : Fin 2) {v : InfinitePlace F}
    (hv : v ≠ w) :
    (((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      i j).1 v = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  rw [incl_fst, archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]

theorem archComponent_glArch_apply (h : AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    (archComponent F w (glArch (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w := rfl

theorem adele_fst_add (x y : AdeleRing (𝓞 F) F) : (x + y).1 = x.1 + y.1 := rfl
theorem adele_fst_mul (x y : AdeleRing (𝓞 F) F) : (x * y).1 = x.1 * y.1 := rfl
theorem adele_snd_add (x y : AdeleRing (𝓞 F) F) : (x + y).2 = x.2 + y.2 := rfl
theorem adele_snd_mul (x y : AdeleRing (𝓞 F) F) : (x * y).2 = x.2 * y.2 := rfl
theorem infAdele_add_apply (x y : InfiniteAdeleRing F) (v : InfinitePlace F) :
    (x + y) v = x v + y v := rfl
theorem infAdele_mul_apply (x y : InfiniteAdeleRing F) (v : InfinitePlace F) :
    (x * y) v = x v * y v := rfl

theorem incl_comm_of_archComponent_eq_one (h : AdelicGL2 (𝓞 F) F)
    (hh : archComponent F w (glArch (𝓞 F) F h) = 1) (k : GL (Fin 2) w.Completion) :
    h * adelicArchGLInclAt F w k = adelicArchGLInclAt F w k * h := by
  have hh' : ∀ i j : Fin 2, ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
      = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
    intro i j
    rw [← archComponent_glArch_apply, hh]; rfl
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · funext v
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, adele_fst_add, adele_fst_mul,
      infAdele_add_apply, infAdele_mul_apply]
    by_cases hv : v = w
    · subst hv
      simp only [incl_fst_self, hh']
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    · simp only [incl_fst_of_ne _ _ _ hv]
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, adele_snd_add, adele_snd_mul,
      incl_snd]
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem incl_comm_of_mem_fin {h : AdelicGL2 (𝓞 F) F} (hh : h ∈ finiteAdelicGL2Subgroup F)
    (k : GL (Fin 2) w.Completion) :
    h * adelicArchGLInclAt F w k = adelicArchGLInclAt F w k * h := by
  refine incl_comm_of_archComponent_eq_one h ?_ k
  rw [(mem_finiteAdelicGL2Subgroup_iff F h).mp hh, map_one]

theorem heckeGen_mem_fin (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  apply Units.ext
  ext i j
  rw [glArch_apply]
  exact heckeGenAt_fst _ i j

theorem mem_fin_of_mem_doubleCoset {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hU : U ≤ finiteAdelicGL2Subgroup F) {gv x : AdelicGL2 (𝓞 F) F}
    (hgv : gv ∈ finiteAdelicGL2Subgroup F) (hx : x ∈ HeckePair.doubleCoset U gv) :
    x ∈ finiteAdelicGL2Subgroup F := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu) hgv) (hU hu')

end Plumbing

section Translate

theorem isLsXi_translate {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (h : AdelicGL2 (𝓞 F) F) :
    IsLsXiFunction (𝓞 F) F ⊤ ξ (fun g => φ (g * h)) :=
  ⟨fun γ g => by simp only [mul_assoc, hφ.left_invariant],
    fun z g => by simp only [mul_assoc, hφ.central_transform]⟩

theorem isCuspidalFn_translate {Q : Type*} {mQ : MeasurableSpace Q} (ν : Measure Q)
    (uu : Q → AdelicGL2 (𝓞 F) F) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsCuspidalFn ν uu φ)
    (h : AdelicGL2 (𝓞 F) F) : IsCuspidalFn ν uu (fun g => φ (g * h)) := by
  intro g
  have := hφ (g * h)
  unfold constantTerm constantTermIntegrand at this ⊢
  simpa only [mul_assoc] using this

theorem isKfSmooth_translate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ)
    (E : AdelicGL2 (𝓞 F) F) (hE : ∀ h ∈ finiteAdelicGL2Subgroup F, h * E = E * h) :
    IsKfSmooth F (fun g => φ (g * E)) := by
  unfold IsKfSmooth at hφ ⊢
  rw [FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer] at hφ ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ (FLT.SmoothVectors.RightTranslationFn.mk φ))
    (fun u hu => ?_) hφ
  rw [MulAction.mem_stabilizer_iff] at hu ⊢
  apply FLT.SmoothVectors.RightTranslationFn.ext
  intro x
  have hx := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f (x * E)) hu
  simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
    FLT.SmoothVectors.RightTranslationFn.toFun_mk] at hx ⊢
  rw [mul_assoc, hE _ u.2, ← mul_assoc, hx]

theorem isBoundedOnSiegelWindows_translate {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsBoundedOnSiegelWindows F φ) (h : AdelicGL2 (𝓞 F) F) :
    IsBoundedOnSiegelWindows F (fun g => φ (g * h)) := by
  classical
  intro c u d₁ d₂ T hc hd₁
  obtain ⟨C, hC⟩ := hφ c u d₁ d₂ (T.image (· * h)) hc hd₁
  refine ⟨C, fun g hg => hC (g * h) ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_image, exists_prop] at hg ⊢
  obtain ⟨x, hx, s, hs, rfl⟩ := hg
  exact ⟨x * h, ⟨x, hx, rfl⟩, s, hs, by rw [mul_assoc]⟩

theorem isHeckeCosetEigenfunctionAt_translate {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hU : U ≤ finiteAdelicGL2Subgroup F) {v : HeightOneSpectrum (𝓞 F)}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {a : ℂ}
    (hφ : IsHeckeCosetEigenfunctionAt F U (heckeGen (𝓞 F) F v) v φ a)
    (E : AdelicGL2 (𝓞 F) F) (hE : ∀ h ∈ finiteAdelicGL2Subgroup F, h * E = E * h) :
    IsHeckeCosetEigenfunctionAt F U (heckeGen (𝓞 F) F v) v (fun g => φ (g * E)) a := by
  obtain ⟨reps, hsys, hsum⟩ := hφ
  refine ⟨reps, hsys, fun g => ?_⟩
  have hcomm : ∀ i, reps i * E = E * reps i := fun i =>
    hE _ (mem_fin_of_mem_doubleCoset hU (heckeGen_mem_fin v) (hsys.mem_doubleCoset i))
  have := hsum (g * E)
  unfold heckeCosetSum at this ⊢
  simp only [mul_assoc, hcomm] at this ⊢
  exact this

end Translate

end RJSymP

end AutomorphicForm

end

noncomputable section

namespace RJCusp

p2m_open "NumberField NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre.AutomorphicForm AutomorphicForm.CuspidalConstituent IsDedekindDomain"
open MeasureTheory FLT.SmoothVectors NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
theorem continuous_unipotentGL2 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ fun x : A => (unipotentGL2 x : GL (Fin 2) A)) = fun x => !![(1 : A), x; 0, 1] :=
      funext fun x => unipotentGL2_coe x
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x : A => (((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) =
        fun x => !![(1 : A), -x; 0, 1] := funext fun x => rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem integrable_slice_cond_adelicBox {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
  have hcont : Continuous (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) :=
    hφ.comp (continuous_unipotentGL2.mul continuous_const)
  have h1 : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) C (adelicAddHaar (𝓞 F) F) :=
    hcont.continuousOn.integrableOn_compact hC
  have h2 : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := h1.mono_set hBC
  unfold ProbabilityTheory.cond
  exact h2.integrable.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')

section Linear

variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

local notation "PINS" => productionPinsOf F D U gen (adelicBox F)

variable (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ)

theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) :=
  IsSmoothVector.add hφ hψ

theorem isKfSmooth_smul (c : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) : IsKfSmooth F (c • φ) := by
  unfold IsKfSmooth at hφ ⊢
  rw [isSmoothVector_iff_isOpen_stabilizer] at hφ ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ (RightTranslationFn.mk φ)) (fun h hh => ?_) hφ
  rw [MulAction.mem_stabilizer_iff] at hh ⊢
  refine RightTranslationFn.ext fun x => ?_
  have hx := congrArg (fun f => RightTranslationFn.toFun f x) hh
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at hx ⊢
  show c • φ (x * h) = c • φ x
  rw [hx]

theorem isSmoothCuspAutomorphicFnAt_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsSmoothCuspAutomorphicFnAt F PINS ξ φ) (hψ : IsSmoothCuspAutomorphicFnAt F PINS ξ ψ) :
    IsSmoothCuspAutomorphicFnAt F PINS ξ (φ + ψ) := by
  obtain ⟨⟨hφa, hφcusp⟩, hφk⟩ := hφ
  obtain ⟨⟨hψa, hψcusp⟩, hψk⟩ := hψ
  refine ⟨⟨?_, ?_⟩, isKfSmooth_add F hφk hψk⟩
  ·
    unfold IsAutomorphicFnAt at hφa hψa ⊢
    rw [lsXiMemberAt_iff] at hφa hψa ⊢
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hφa.2.add hψa.2⟩
    · simp only [Pi.add_apply, hφa.1.left_invariant, hψa.1.left_invariant]
    · simp only [Pi.add_apply, hφa.1.central_transform, hψa.1.central_transform, mul_add]
  ·
    intro g
    have hi1 := integrable_slice_cond_adelicBox F hφc g
    have hi2 := integrable_slice_cond_adelicBox F hψc g
    have h1 := hφcusp g
    have h2 := hψcusp g
    unfold constantTerm constantTermIntegrand at h1 h2 ⊢
    rw [productionPinsOf_ν] at h1 h2 ⊢
    simp only [Pi.add_apply]
    have h1' : ∫ q : AdeleRing (𝓞 F) F, φ (unipotentGL2 q * g)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) = 0 := h1
    have h2' : ∫ q : AdeleRing (𝓞 F) F, ψ (unipotentGL2 q * g)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) = 0 := h2
    have hadd := integral_add hi1 hi2
    rw [h1', h2', add_zero] at hadd
    exact hadd

theorem isSmoothCuspAutomorphicFnAt_smul (c : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsSmoothCuspAutomorphicFnAt F PINS ξ φ) :
    IsSmoothCuspAutomorphicFnAt F PINS ξ (c • φ) := by
  obtain ⟨⟨hφa, hφcusp⟩, hφk⟩ := hφ
  refine ⟨⟨?_, ?_⟩, isKfSmooth_smul F c hφk⟩
  · unfold IsAutomorphicFnAt at hφa ⊢
    rw [lsXiMemberAt_iff] at hφa ⊢
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hφa.2.const_smul c⟩
    · simp only [Pi.smul_apply, hφa.1.left_invariant]
    · simp only [Pi.smul_apply, hφa.1.central_transform, smul_eq_mul]; ring
  · intro g
    have h1 := hφcusp g
    unfold constantTerm constantTermIntegrand at h1 ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, h1, mul_zero]

end Linear

end RJCusp

end

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf productionPinsOf_ν AdelicGL2 centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem glEquivOfRingEquiv glEquivOfRingEquiv_apply_entry map_mem_rowIsometrySubgroup₀_of_normPreserving rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightOneAt archWeightCharAt rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff normSq_firstRowℂ_of_mem archWeightCharℝ HasArchCharacterAt₀ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne adelicArchGLInclAt archRealGLAt archRealLiftAt IsArchSmoothAt ArchDir lowerUnipotentGL2_coe splitTorusGL2_coe archFlowMatrix archFlowAt archDerivAt archCasimirAt archRealLiftAt_mul_archRealGLAt contDiff_of_symm_mul_const archDerivAt_add archDerivAt_smul archCasimirAt_add archCasimirAt_smul IsBoundedOnSiegelWindows memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre"
p2m_open "AutomorphicForm"

namespace RJSymMain

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix IsDedekindDomain
open AutomorphicForm.SmoothCusp HeckeIntegralSeam FLT.SmoothVectors NumberField.AdelicVolume NumberField.TateGlobal
open AutomorphicForm.RJSymP RJSym.K3
open scoped ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

abbrev pinsW (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

theorem chi0_apply {w : InfinitePlace F} (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    ((((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) k
      : ℂˣ) : ℂ) = 1 := by
  simp [archWeightCharℝ]

theorem E_mul_E {w : InfinitePlace F} (hw : w.IsReal) : archRealGLAt hw eps * archRealGLAt hw eps = 1 := by
  rw [← map_mul, eps_mul_eps, map_one]

theorem ideleNorm_det_E {w : InfinitePlace F} (hw : w.IsReal) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (archRealGLAt hw eps)) = 1 := by
  have h2 : ideleNorm F (Matrix.GeneralLinearGroup.det (archRealGLAt hw eps)) ^ 2 = 1 := by
    rw [sq, ← ideleNorm_mul, ← map_mul, E_mul_E, map_one]
    simp [ideleNorm]
  have hpos := ideleNorm_pos (F := F) (Matrix.GeneralLinearGroup.det (archRealGLAt hw eps))
  nlinarith [hpos, h2]

theorem ideleNorm_det_mul_E {w : InfinitePlace F} (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (g * archRealGLAt hw eps)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, ideleNorm_det_E, mul_one]

theorem ideleNorm_det_mem_Icc_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) {s : AdelicGL2 (𝓞 F) F}
    (hs : s ∈ centreCutSiegelSet F c u d₁ d₂) :
    ideleNorm F (Matrix.GeneralLinearGroup.det s) ∈
      Set.Icc ((min d₁ (d₁ ^ 2)) ^ Fintype.card (InfinitePlace F)) ((max d₂ (d₂ ^ 2)) ^ Fintype.card (InfinitePlace F)) := by
  obtain ⟨hfin, -, -, hdet⟩ := hs
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F s hfin]
  have hlo : 0 ≤ min d₁ (d₁ ^ 2) := le_min hd₁.le (sq_nonneg _)
  have hfac : ∀ w : InfinitePlace F, min d₁ (d₁ ^ 2) ≤ archDetNorm w s ^ w.mult ∧ archDetNorm w s ^ w.mult ≤ max d₂ (d₂ ^ 2) := by
    intro w
    obtain ⟨h1, h2⟩ := hdet w
    have h0 : 0 ≤ archDetNorm w s := (archDetNorm_pos w s).le
    rcases w.isReal_or_isComplex with hr | hc
    · rw [NumberField.InfinitePlace.mult, if_pos hr, pow_one]
      exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
    · rw [NumberField.InfinitePlace.mult, if_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc)]
      exact ⟨(min_le_right _ _).trans (pow_le_pow_left₀ hd₁.le h1 2), (pow_le_pow_left₀ h0 h2 2).trans (le_max_right _ _)⟩
  constructor
  · rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hlo) (fun w _ => (hfac w).1)
  · rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w s).le _) (fun w _ => (hfac w).2)

theorem isBoundedOnSiegelWindows_of_forall_slab {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → ‖φ g‖ ≤ B) :
    IsBoundedOnSiegelWindows F φ := by
  classical
  intro c u d₁ d₂ T hc hd₁
  by_cases hT : T.Nonempty
  · set lo : ℝ := (min d₁ (d₁ ^ 2)) ^ Fintype.card (InfinitePlace F) with hlo
    set hi : ℝ := (max d₂ (d₂ ^ 2)) ^ Fintype.card (InfinitePlace F) with hhi
    set m : ℝ := T.inf' hT (fun t => ideleNorm F (Matrix.GeneralLinearGroup.det t)) with hm
    set M : ℝ := T.sup' hT (fun t => ideleNorm F (Matrix.GeneralLinearGroup.det t)) with hM
    have hlo0 : 0 < lo := pow_pos (lt_min hd₁ (pow_pos hd₁ 2)) _
    have hm0 : 0 < m := by
      rw [hm, Finset.lt_inf'_iff]; intro t _; exact ideleNorm_pos _
    set e₁ : ℝ := lo * m with he₁
    set e₂ : ℝ := max (hi * M) (lo * m) + 1 with he₂
    have he₁0 : 0 < e₁ := mul_pos hlo0 hm0
    have he₁₂ : e₁ < e₂ := (le_max_right _ _).trans_lt (lt_add_one _)
    obtain ⟨B, hB⟩ := hφ e₁ e₂ he₁0 he₁₂
    refine ⟨B, fun g hg => hB g ?_⟩
    obtain ⟨t, ht, hg'⟩ := Set.mem_iUnion₂.mp hg
    obtain ⟨s, hs, rfl⟩ := hg'
    have hsI := ideleNorm_det_mem_Icc_of_mem_centreCutSiegelSet (F := F) hd₁ hs
    have htm : m ≤ ideleNorm F (Matrix.GeneralLinearGroup.det t) := Finset.inf'_le _ ht
    have htM : ideleNorm F (Matrix.GeneralLinearGroup.det t) ≤ M := Finset.le_sup' (fun t => ideleNorm F (Matrix.GeneralLinearGroup.det t)) ht
    rw [map_mul, ideleNorm_mul]
    constructor
    · exact mul_le_mul hsI.1 htm hm0.le ((hlo0.le).trans hsI.1)
    · refine (mul_le_mul hsI.2 htM (ideleNorm_pos _).le ?_).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
      exact hlo0.le.trans (hsI.1.trans hsI.2)
  · refine ⟨0, fun g hg => ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    simp [hT] at hg

section Deriv

variable {w : InfinitePlace F} (hw : w.IsReal)

def sgnL : List ArchDir → ℂ
  | [] => 1
  | .H :: l => sgnL l
  | .E :: l => -sgnL l
  | .Fm :: l => -sgnL l

theorem norm_sgnL (l : List ArchDir) : ‖sgnL l‖ = 1 := by
  induction l with
  | nil => simp [sgnL]
  | cons d l ih => cases d <;> simp [sgnL, ih]

theorem foldr_comp_mul_eps (φ : AdelicGL2 (𝓞 F) F → ℂ) (l : List ArchDir) :
    l.foldr (archDerivAt hw) (fun g => φ (g * archRealGLAt hw eps)) =
      fun g => sgnL l * (l.foldr (archDerivAt hw) φ) (g * archRealGLAt hw eps) := by
  induction l with
  | nil => funext g; simp [sgnL]
  | cons d l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    have hsm : (fun g => sgnL l * (l.foldr (archDerivAt hw) φ) (g * archRealGLAt hw eps)) =
        sgnL l • (fun g => (l.foldr (archDerivAt hw) φ) (g * archRealGLAt hw eps)) := by
      funext g; simp [Pi.smul_apply, smul_eq_mul]
    rw [hsm, archDerivAt_smul]
    cases d
    · rw [archDerivAt_H_comp_mul_eps]; funext g; simp [sgnL, Pi.smul_apply, smul_eq_mul]
    · rw [archDerivAt_E_comp_mul_eps]; funext g; simp [sgnL, Pi.smul_apply, smul_eq_mul]
    · rw [archDerivAt_Fm_comp_mul_eps]; funext g; simp [sgnL, Pi.smul_apply, smul_eq_mul]

theorem isArchSmoothAt_foldr {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (l : List ArchDir) :
    IsArchSmoothAt hw (l.foldr (archDerivAt hw) φ) := by
  induction l with
  | nil => exact hφ
  | cons d l ih => rw [List.foldr_cons]; exact ih.archDerivAt d

theorem foldr_add_smul {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (s : ℂ)
    (l : List ArchDir) :
    l.foldr (archDerivAt hw) (φ + s • ψ) = l.foldr (archDerivAt hw) φ + s • l.foldr (archDerivAt hw) ψ := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih,
      archDerivAt_add (isArchSmoothAt_foldr hw hφ l) ((isArchSmoothAt_foldr hw hψ l).smul s), archDerivAt_smul]

end Deriv

end RJSymMain

end AutomorphicForm

end

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf productionPinsOf_ν AdelicGL2 centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem glEquivOfRingEquiv glEquivOfRingEquiv_apply_entry map_mem_rowIsometrySubgroup₀_of_normPreserving rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightOneAt archWeightCharAt rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff normSq_firstRowℂ_of_mem archWeightCharℝ HasArchCharacterAt₀ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne adelicArchGLInclAt archRealGLAt archRealLiftAt IsArchSmoothAt ArchDir lowerUnipotentGL2_coe splitTorusGL2_coe archFlowMatrix archFlowAt archDerivAt archCasimirAt archRealLiftAt_mul_archRealGLAt contDiff_of_symm_mul_const archDerivAt_add archDerivAt_smul archCasimirAt_add archCasimirAt_smul IsBoundedOnSiegelWindows memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre"
p2m_open "AutomorphicForm"

namespace RJSymMain

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix IsDedekindDomain
open AutomorphicForm.SmoothCusp HeckeIntegralSeam FLT.SmoothVectors NumberField.AdelicVolume NumberField.TateGlobal
open AutomorphicForm.RJSymP RJSym.K3
open scoped ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

section Main

variable {w : InfinitePlace F} (hw : w.IsReal)

def Pkg (lam e : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  HasArchCharacterAt₀ F w ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
    IsArchSmoothAt hw φ ∧
    (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
      ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
          ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
    archCasimirAt hw φ = lam • φ ∧
    (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g)

theorem pkg_flip {lam e : ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hP : Pkg hw lam e φ) :
    Pkg hw lam e (fun g => φ (g * archRealGLAt hw eps)) := by
  obtain ⟨hch, hsm, hreg, hcas, hcen⟩ := hP
  refine ⟨?_, isArchSmoothAt_comp_mul_eps hw hsm, fun l => ?_, ?_, ?_⟩
  · intro k g
    show φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) * archRealGLAt hw eps) = _ * φ (g * archRealGLAt hw eps)
    rw [mul_assoc, incl_mul_eps, ← mul_assoc, hch (conjK hw k) (g * archRealGLAt hw eps), chi0_apply, chi0_apply]
  · rw [foldr_comp_mul_eps]
    refine ⟨?_, fun e₁ e₂ he₁ he => ?_⟩
    · exact continuous_const.mul ((hreg l).1.comp (continuous_id.mul continuous_const))
    · obtain ⟨B, hB⟩ := (hreg l).2 e₁ e₂ he₁ he
      refine ⟨B, fun g hg => ?_⟩
      rw [norm_mul, norm_sgnL, one_mul]
      exact hB _ (by rwa [ideleNorm_det_mul_E])
  · rw [archCasimirAt_comp_mul_eps, hcas]
    funext g; simp [Pi.smul_apply, smul_eq_mul]
  · intro t ht g
    show φ (_ * g * archRealGLAt hw eps) = _
    rw [mul_assoc, hcen t ht]

theorem pkg_add_smul {lam e : ℂ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Pkg hw lam e φ) (hψ : Pkg hw lam e ψ) (s : ℂ) :
    Pkg hw lam e (φ + s • ψ) := by
  obtain ⟨hch, hsm, hreg, hcas, hcen⟩ := hφ
  obtain ⟨hch', hsm', hreg', hcas', hcen'⟩ := hψ
  refine ⟨?_, hsm.add (hsm'.smul s), fun l => ?_, ?_, ?_⟩
  · intro k g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hch k g, hch' k g, chi0_apply]
    ring
  · rw [foldr_add_smul hw hsm hsm' s]
    refine ⟨(hreg l).1.add ((hreg' l).1.const_smul s), fun e₁ e₂ he₁ he => ?_⟩
    obtain ⟨B, hB⟩ := (hreg l).2 e₁ e₂ he₁ he
    obtain ⟨B', hB'⟩ := (hreg' l).2 e₁ e₂ he₁ he
    refine ⟨B + ‖s‖ * B', fun g hg => ?_⟩
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (norm_add_le _ _).trans (add_le_add (hB g hg) (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' g hg) (norm_nonneg _)))
  · rw [archCasimirAt_add hsm (hsm'.smul s), archCasimirAt_smul, hcas, hcas', smul_comm, ← smul_add]
  · intro t ht g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcen t ht g, hcen' t ht g]
    ring

theorem main (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) Θ'.toRawCentral)
    (hR' : Continuous R'.toFun) (lam e : ℂ) (hP : Pkg hw lam e R'.toFun) :
    ∃ R₁ : SmoothCuspRealizationAt F (pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) Θ'.toRawCentral,
      Continuous R₁.toFun ∧ Pkg hw lam e R₁.toFun ∧
        ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ g : AdelicGL2 (𝓞 F) F, R₁.toFun (g * archRealGLAt hw eps) = ε * R₁.toFun g := by
  classical
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hUfin : levelOne (𝓞 F) F Θ'.toRawCentral.level ⊓ finiteAdelicGL2Subgroup F ≤ finiteAdelicGL2Subgroup F := inf_le_right

  set φ : AdelicGL2 (𝓞 F) F → ℂ := R'.toFun with hφdef
  have hsc := R'.smoothCusp
  have hmem : IsLsXiFunction (𝓞 F) F ⊤ R'.centralChar φ ∧
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
    (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ R'.centralChar _ φ).mp hsc.1.1
  have hLs := hmem.1
  have hL2 := hmem.2
  have hcusp := hsc.1.2
  have hKf : IsKfSmooth F φ := hsc.2
  have hlev : ∀ (g : AdelicGL2 (𝓞 F) F), ∀ k ∈ (pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)).U Θ'.toRawCentral.level,
      φ (g * k) = φ g := R'.level_invariant
  have hce : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R'.exceptionalSet → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det ((pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)).gen v)) * g)
        = Θ'.toRawCentral.b v * φ g := R'.central_eigen
  have hhe : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R'.exceptionalSet →
      IsHeckeCosetEigenfunctionAt F ((pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)).U Θ'.toRawCentral.level)
        ((pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)).gen v) v φ (Θ'.toRawCentral.a v) := R'.hecke_eigen

  set E : AdelicGL2 (𝓞 F) F := archRealGLAt hw eps with hE
  have hE' : E = adelicArchGLInclAt F w (epsW hw) := rfl
  have hEcomm : ∀ h ∈ finiteAdelicGL2Subgroup F, h * E = E * h :=
    fun h hh => by rw [hE']; exact incl_comm_of_mem_fin hh (epsW hw)

  set ψ : AdelicGL2 (𝓞 F) F → ℂ := fun g => φ (g * E) with hψ
  have hψcont : Continuous ψ := hR'.comp (continuous_id.mul continuous_const)
  have hψLs : IsLsXiFunction (𝓞 F) F ⊤ R'.centralChar ψ := isLsXi_translate hLs E
  have hPψ : Pkg hw lam e ψ := pkg_flip hw hP

  have hφbdd : IsBoundedOnSiegelWindows F φ :=
    isBoundedOnSiegelWindows_of_forall_slab (by
      intro e₁ e₂ he₁ he
      obtain ⟨B, hB⟩ := (hP.2.2.1 []).2 e₁ e₂ he₁ he
      exact ⟨B, fun g hg => by simpa using hB g hg⟩)
  have hψbdd : IsBoundedOnSiegelWindows F ψ := isBoundedOnSiegelWindows_translate hφbdd E
  have hψL2 : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
    AutomorphicForm.memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
      F c u d₁ d₂ T hd hcov R'.centralChar φ hLs hR' R'.exists_ne_zero hL2 ψ hψLs hψcont hψbdd
  have hψsc : IsSmoothCuspAutomorphicFnAt F (pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) R'.centralChar ψ :=
    ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ R'.centralChar _ ψ).mpr ⟨hψLs, hψL2⟩,
      isCuspidalFn_translate _ _ hcusp E⟩, isKfSmooth_translate hKf E hEcomm⟩

  have hsq : ∀ s : ℂ, s = 1 ∨ s = -1 → s * s = 1 := by
    rintro s (rfl | rfl) <;> norm_num
  obtain ⟨s, hs, hne⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ ∃ g, (φ + s • ψ) g ≠ 0 := by
    by_cases h : ∃ g, (φ + (1 : ℂ) • ψ) g ≠ 0
    · exact ⟨1, Or.inl rfl, h⟩
    · push_neg at h
      obtain ⟨g₀, hg₀⟩ := R'.exists_ne_zero
      refine ⟨-1, Or.inr rfl, g₀, ?_⟩
      have h1 : ψ g₀ = -φ g₀ := by
        have := h g₀
        simp only [Pi.add_apply, Pi.smul_apply, one_smul] at this
        linear_combination this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1]
      intro h2
      apply hg₀
      have : (2 : ℂ) * φ g₀ = 0 := by linear_combination h2
      simpa using this

  set χ : AdelicGL2 (𝓞 F) F → ℂ := φ + s • ψ with hχ
  have hχcont : Continuous χ := hR'.add (hψcont.const_smul s)
  have hχsc : IsSmoothCuspAutomorphicFnAt F (pinsW (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) R'.centralChar χ :=
    RJCusp.isSmoothCuspAutomorphicFnAt_add F _ _ _ R'.centralChar hR' (hψcont.const_smul s) hsc
      (RJCusp.isSmoothCuspAutomorphicFnAt_smul F _ _ _ R'.centralChar s hψsc)
  have hPχ : Pkg hw lam e χ := pkg_add_smul hw hP hPψ s
  refine ⟨{ toFun := χ
            exists_ne_zero := hne
            centralChar := R'.centralChar
            smoothCusp := hχsc
            level_invariant := fun g k hk => ?_
            exceptionalSet := R'.exceptionalSet
            hecke_eigen := fun v hv => ?_
            central_eigen := fun v hv g => ?_ }, hχcont, hPχ, s, hs, fun g => ?_⟩
  ·
    show φ (g * k) + s • φ (g * k * E) = φ g + s • φ (g * E)
    rw [hlev g k hk, mul_assoc, hEcomm k (hUfin hk), ← mul_assoc, hlev (g * E) k hk]
  ·
    obtain ⟨reps, hsys, hsum⟩ := hhe v hv
    refine ⟨reps, hsys, fun g => ?_⟩
    have hcomm : ∀ i, reps i * E = E * reps i := fun i =>
      hEcomm _ (mem_fin_of_mem_doubleCoset hUfin (heckeGen_mem_fin v) (hsys.mem_doubleCoset i))
    have h1 : ∑ i, φ (g * reps i) = Θ'.toRawCentral.a v * φ g := hsum g
    have h2 : ∑ i, φ (g * E * reps i) = Θ'.toRawCentral.a v * φ (g * E) := hsum (g * E)
    have h2' : ∑ i, φ (g * reps i * E) = Θ'.toRawCentral.a v * φ (g * E) := by
      rw [← h2]; refine Finset.sum_congr rfl fun i _ => ?_; rw [mul_assoc, hcomm i, ← mul_assoc]
    show ∑ i, (φ + s • ψ) (g * reps i) = Θ'.toRawCentral.a v * (φ + s • ψ) g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    show (∑ i, φ (g * reps i)) + s * ∑ i, φ (g * reps i * E) = Θ'.toRawCentral.a v * (φ g + s * φ (g * E))
    rw [h1, h2']
    ring
  ·
    show φ (_ * g) + s • φ (_ * g * E) = Θ'.toRawCentral.b v * (φ g + s • φ (g * E))
    rw [hce v hv g, mul_assoc, hce v hv (g * E), smul_eq_mul, smul_eq_mul]
    ring
  ·
    show φ (g * E) + s • φ (g * E * E) = s * (φ g + s • φ (g * E))
    rw [mul_assoc, show E * E = 1 from E_mul_E hw, mul_one, smul_eq_mul, smul_eq_mul, mul_add, ← mul_assoc, hsq s hs, one_mul,
      add_comm]

end Main

end RJSymMain

end AutomorphicForm

end

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse
open AutomorphicForm.RJSymMain RJSym.K3

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (lam e : ℂ)
    (hocc : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = lam • φ ∧
            (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g))) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => (HasArchCharacterAt₀ F w ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = lam • φ ∧
            (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g)) ∧
          ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
            ∀ g : AdelicGL2 (𝓞 F) F, φ (g * archRealGLAt hw UpperHalfPlane.J) = ε * φ g) := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := hocc
  have hε : UpperHalfPlane.J = RJSym.K3.eps := rfl
  obtain ⟨R₁, hR₁, hP₁, ε, hε1, hJ⟩ :=
    AutomorphicForm.RJSymMain.main hw c u d₁ d₂ T hd hcov Θ' R' hR' lam e hP
  exact ⟨Θ', hΘ', R₁, hR₁, hP₁, ε, hε1, fun g => by rw [hε]; exact hJ g⟩

end S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre (solution)
