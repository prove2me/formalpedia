-- Prove2me | solution 1 for AutomorphicForm.hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/70653bec-e681-5651-8e5e-5f2eb23aad51

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open NumberField.InfinitePlace.Completion

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace ShiftR

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)

abbrev mR (k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) ℝ :=
  glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion)

theorem mR_mem (k : rowIsometrySubgroup₀ w.Completion) : mR hw k ∈ rowIsometrySubgroup₀ ℝ :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _ (norm_ringEquivRealOfIsReal hw) _ k.2

theorem incl_eq (k : rowIsometrySubgroup₀ w.Completion) :
    adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) = archRealGLAt hw (mR hw k) :=
  (archRealGLAt_glEquivOfRingEquiv hw _).symm

theorem archWeightOneAt_eq (k : rowIsometrySubgroup₀ w.Completion) :
    ((archWeightOneAt hw k : ℂˣ) : ℂ) =
      (((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
        (((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * Complex.I := by
  rw [← Complex.mk_eq_add_mul_I]
  rfl

theorem archWeightCharAt_eq (n : ℤ) (k : rowIsometrySubgroup₀ w.Completion) :
    ((archWeightCharAt hw n k : ℂˣ) : ℂ) = ((archWeightOneAt hw k : ℂˣ) : ℂ) ^ n := by
  show (((zpowGroupHom n) (archWeightOneAt hw k) : ℂˣ) : ℂ) = _
  rw [zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]

theorem archDerivAt_apply_mul_incl {n : ℤ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAt hw ψ)
    (hwt : HasArchCharacterAt₀ K w (archWeightCharAt hw n) ψ) (d : ArchDir)
    (k : rowIsometrySubgroup₀ w.Completion) (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d ψ (g * adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)) =
      (archWeightCharAt hw n k : ℂ) *
        (((((((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d *
              (((mR hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 -
            ((((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d *
              (((mR hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) 1 1)) / 2 : ℝ) : ℂ) *
            archDerivAt hw ArchDir.H ψ g +
          (((((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d *
              (((mR hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 : ℝ) : ℂ) *
            archDerivAt hw ArchDir.E ψ g +
          (((((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d *
              (((mR hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 : ℝ) : ℂ) *
            archDerivAt hw ArchDir.Fm ψ g) := by
  set m : GL (Fin 2) ℝ := mR hw k with hm
  have hD := AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul K hw ψ hψ g m⁻¹ d
  simp only [inv_inv] at hD
  have hfun : (fun s : ℝ => ψ (g * adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) * archFlowAt hw d s)) =
      fun s => (archWeightCharAt hw n k : ℂ) * ψ (g * archRealGLAt hw (m * archFlowMatrix d s * m⁻¹)) := by
    funext s
    have e : g * adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) * archFlowAt hw d s =
        g * archRealGLAt hw (m * archFlowMatrix d s * m⁻¹) * adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) := by
      rw [incl_eq hw k, archFlowAt, mul_assoc, mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_right]
    rw [e, hwt k]
  show deriv (fun s : ℝ => ψ (g * adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) * archFlowAt hw d s)) 0 = _
  rw [hfun]
  exact (hD.const_mul _).deriv

end ShiftR

open ShiftR in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (hψ : IsArchSmoothAt hw ψ)
    (hwt : HasArchCharacterAt₀ K w (archWeightCharAt hw n) ψ) :
    HasArchCharacterAt₀ K w (archWeightCharAt hw (n + 2))
        (archDerivAt hw .H ψ + Complex.I • (archDerivAt hw .E ψ + archDerivAt hw .Fm ψ)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n - 2))
        (archDerivAt hw .H ψ - Complex.I • (archDerivAt hw .E ψ + archDerivAt hw .Fm ψ)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw n) (archDerivAt hw .E ψ - archDerivAt hw .Fm ψ) := by

  have prep : ∀ k : rowIsometrySubgroup₀ w.Completion,
      ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
        ((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a] ∧
        (((mR hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, -b; b, a] ∧
        ((archWeightOneAt hw k : ℂˣ) : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
    intro k
    obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ (mR_mem hw k)
    set a := ((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
    set b := ((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
    have hm : ((mR hw k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a] := by
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · rfl
      · simpa using h10
      · simpa using h11
    have hmi : (((mR hw k)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, -b; b, a] := by
      rw [Matrix.coe_units_inv, hm]
      apply Matrix.inv_eq_left_inv
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hab]
    exact ⟨a, b, hab, hm, hmi, archWeightOneAt_eq hw k⟩
  refine ⟨fun k g => ?_, fun k g => ?_, fun k g => ?_⟩
  all_goals
    obtain ⟨a, b, hab, hm, hmi, hu⟩ := prep k
    have fH := archDerivAt_apply_mul_incl hw hψ hwt .H k g
    have fE := archDerivAt_apply_mul_incl hw hψ hwt .E k g
    have fF := archDerivAt_apply_mul_incl hw hψ hwt .Fm k g
    simp only [hm, hmi, archDirMatrix, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      mul_one, mul_zero, zero_mul, one_mul, add_zero, zero_add, mul_neg, neg_mul, neg_neg, neg_zero] at fH fE fF
    have habC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
    have hu0 : ((a : ℂ) + (b : ℂ) * Complex.I) ≠ 0 := by
      rw [← hu]; exact Units.ne_zero _
    have hχn : ((archWeightCharAt hw n k : ℂˣ) : ℂ) = ((a : ℂ) + (b : ℂ) * Complex.I) ^ n := by
      rw [archWeightCharAt_eq, hu]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [fE, fF]
    try rw [fH]
    push_cast

  · have hχ : ((archWeightCharAt hw (n + 2) k : ℂˣ) : ℂ) =
        ((archWeightCharAt hw n k : ℂˣ) : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 := by
      rw [archWeightCharAt_eq, archWeightCharAt_eq, hu, zpow_add₀ hu0]
      norm_cast
    rw [hχ]
    linear_combination (-((archWeightCharAt hw n k : ℂˣ) : ℂ) *
      (2 * a * b * (archDerivAt hw .E ψ g + archDerivAt hw .Fm ψ g) + b ^ 2 * archDerivAt hw .H ψ g) -
      ((archWeightCharAt hw n k : ℂˣ) : ℂ) * b ^ 2 * (archDerivAt hw .E ψ g + archDerivAt hw .Fm ψ g) * Complex.I) *
      Complex.I_mul_I

  · have hinv : ((a : ℂ) + (b : ℂ) * Complex.I)⁻¹ = (a : ℂ) - (b : ℂ) * Complex.I := by
      apply inv_eq_of_mul_eq_one_right
      linear_combination habC - (b : ℂ) ^ 2 * Complex.I_mul_I
    have hχ : ((archWeightCharAt hw (n - 2) k : ℂˣ) : ℂ) =
        ((archWeightCharAt hw n k : ℂˣ) : ℂ) * ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2 := by
      rw [archWeightCharAt_eq, archWeightCharAt_eq, hu, zpow_sub₀ hu0, div_eq_mul_inv, ← inv_zpow, hinv]
      norm_cast
    rw [hχ]
    linear_combination (-((archWeightCharAt hw n k : ℂˣ) : ℂ) *
      (2 * a * b * (archDerivAt hw .E ψ g + archDerivAt hw .Fm ψ g) + b ^ 2 * archDerivAt hw .H ψ g) +
      ((archWeightCharAt hw n k : ℂˣ) : ℂ) * b ^ 2 * (archDerivAt hw .E ψ g + archDerivAt hw .Fm ψ g) * Complex.I) *
      Complex.I_mul_I

  · linear_combination (((archWeightCharAt hw n k : ℂˣ) : ℂ) * (archDerivAt hw .E ψ g - archDerivAt hw .Fm ψ g)) * habC

end

end S_AutomorphicForm_hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt
end P2MW
export P2MW.S_AutomorphicForm_hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt (solution)
