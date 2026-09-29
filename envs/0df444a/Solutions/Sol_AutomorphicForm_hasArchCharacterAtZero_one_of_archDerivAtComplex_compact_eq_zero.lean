-- Prove2me | solution 1 for AutomorphicForm.hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a73f7233-0c4b-5fe4-9020-5ba837da82d2

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Theorems.Thm_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
import Theorems.Thm_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ AdelicGL2 rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff HasArchCharacterAt₀ adelicArchGLInclAt archComplexLiftAt archComplexLiftAt_of_det_ne_zero IsArchSmoothAtComplex ArchDirComplex archFlowMatrixComplex archFlowAtComplex archFlowAtComplex_zero archFlowAtComplex_add archDerivAtComplex glEquivOfRingEquiv map_mem_rowIsometrySubgroup₀_of_normPreserving archComplexLiftAt_of_symm_one archComplexGLAt_glEquivOfRingEquiv su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional"
namespace TrivKCAux
p2m_open "AutomorphicForm"

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix AutomorphicForm.WindowedSiegel
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

theorem apply_mul_archFlowAtComplex_eq (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (d : ArchDirComplex) (hd : archDerivAtComplex hw d φ = 0) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    φ (g * archFlowAtComplex hw d t) = φ g := by
  set f : ℝ → ℂ := fun t => φ (g * archFlowAtComplex hw d t) with hf
  have hderiv : ∀ t : ℝ, HasDerivAt f 0 t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) 0 0 := by
      have hda := (hφ.differentiableAt_flow d (g * archFlowAtComplex hw d t)).hasDerivAt
      have hz : deriv (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) 0 = 0 :=
        congrFun hd (g * archFlowAtComplex hw d t)
      rwa [hz] at hda
    have h1 : (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) =
        fun s => f (t + s) := by
      funext s
      simp only [hf, archFlowAtComplex_add, mul_assoc]
    rw [h1, show (0 : ℝ) = t - t by simp] at h0
    have h2 := h0.comp_sub_const t t
    have h3 : (fun x : ℝ => f (t + (x - t))) = f := by
      funext x; congr 1; ring
    rw [h3] at h2
    exact h2
  have hdiff : Differentiable ℝ f := fun t => (hderiv t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t => (hderiv t).deriv) t 0
  have h0 : f 0 = φ g := by simp only [hf, archFlowAtComplex_zero, mul_one]
  rw [← h0, ← hconst]

omit [NumberField F] in

theorem norm_ringEquivComplexOfIsComplex (x : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem coe_mem_specialUnitaryGroup (k : GL (Fin 2) ℂ) (hk : k ∈ rowIsometrySubgroup₀ ℂ) :
    (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  obtain ⟨hd, -, hiso⟩ := (mem_rowIsometrySubgroup₀_iff ℂ).mp hk
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, hd⟩
  rw [Matrix.mem_unitaryGroup_iff]
  set A := (k : Matrix (Fin 2) (Fin 2) ℂ) with hA
  have e10 := hiso 1 0
  have e01 := hiso 0 1
  have e11 := hiso 1 1
  have eI1 := hiso Complex.I 1
  simp only [one_mul, zero_mul, add_zero, zero_add, Complex.sq_norm, Complex.normSq_apply, norm_one, norm_zero,
    Complex.norm_I, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    one_pow, zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at e10 e01 e11 eI1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.star_def, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
      Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im]
  · exact ⟨by linear_combination e10, by ring⟩
  · exact ⟨by linear_combination (e11 - e10 - e01) / 2, by linear_combination -(eI1 - e10 - e01) / 2⟩
  · exact ⟨by linear_combination (e11 - e10 - e01) / 2, by linear_combination (eI1 - e10 - e01) / 2⟩
  · exact ⟨by linear_combination e01, by ring⟩

theorem rot_det (b : ℝ) :
    (Matrix.of !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)]).det = 1 := by
  have h : (Real.cos b : ℂ) ^ 2 + (Real.sin b : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq b
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  linear_combination h

theorem rot_det_ne_zero (b : ℝ) :
    (Matrix.of !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)]).det ≠ 0 := by
  rw [rot_det]; exact one_ne_zero

noncomputable def rotGL (b : ℝ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.of !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)]) (rot_det_ne_zero b)

theorem main (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y, (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ Y)
    (h0 : archDerivAtComplex hw .iH x = 0)
    (h1 : archDerivAtComplex hw .Fm x - archDerivAtComplex hw .E x = 0) :
    HasArchCharacterAt₀ F w 1 x := by
  obtain ⟨-, K2, -, -⟩ :=
    AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional F hw Y hYs hYK

  have hM : ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ), x (g * archFlowAtComplex hw .iH s) = x g :=
    fun g s => apply_mul_archFlowAtComplex_eq hw x (hYs x hx) .iH h0 g s
  have hR : ∀ (g : AdelicGL2 (𝓞 F) F) (b : ℝ),
      x (g * archComplexLiftAt hw !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)]) = x g := by
    intro g b
    set f : ℝ → ℂ := fun t =>
      x (g * archComplexLiftAt hw !![(Real.cos t : ℂ), -(Real.sin t : ℂ); (Real.sin t : ℂ), (Real.cos t : ℂ)]) with hf
    have hder : ∀ s : ℝ, HasDerivAt f 0 s := by
      intro s
      have h := (K2 x hx g s).2.1
      beta_reduce at h
      rw [h1, Pi.zero_apply] at h
      exact h
    have hdiff : Differentiable ℝ f := fun t => (hder t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hder t).deriv) b 0
    have hone : (!![((1 : ℝ) : ℂ), -((0 : ℝ) : ℂ); ((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] : Fin 2 → Fin 2 → ℂ) =
        Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h0' : f 0 = x g := by
      simp only [hf, Real.cos_zero, Real.sin_zero]
      rw [hone, archComplexLiftAt_of_symm_one, mul_one]
    calc _ = f b := rfl
      _ = f 0 := hc
      _ = x g := h0'

  intro k g
  rw [MonoidHom.one_apply, Units.val_one, one_mul]
  have hk' : glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) w.Completion) ∈
      rowIsometrySubgroup₀ ℂ :=
    map_mem_rowIsometrySubgroup₀_of_normPreserving _ (norm_ringEquivComplexOfIsComplex hw) _ k.2
  obtain ⟨a, b, c, habc⟩ :=
    Matrix.specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag _ (coe_mem_specialUnitaryGroup _ hk')
  have hGL : glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) w.Completion) =
      archFlowMatrixComplex .iH a * rotGL b * archFlowMatrixComplex .iH c := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [habc]
    rfl
  have hadelic : adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) =
      archFlowAtComplex hw .iH a *
        archComplexLiftAt hw !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)] *
        archFlowAtComplex hw .iH c := by
    rw [← archComplexGLAt_glEquivOfRingEquiv hw, hGL, map_mul, map_mul,
      archComplexLiftAt_of_det_ne_zero hw (rot_det_ne_zero b)]
    rfl
  rw [hadelic, ← mul_assoc, ← mul_assoc, hM, hR, hM]

end AutomorphicForm.TrivKCAux

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y, (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ Y)
    (h0 : archDerivAtComplex hw .iH x = 0)
    (h1 : archDerivAtComplex hw .Fm x - archDerivAtComplex hw .E x = 0)
    (h2 : archDerivAtComplex hw .iE x + archDerivAtComplex hw .iFm x = 0) :
    HasArchCharacterAt₀ F w 1 x := by
  exact AutomorphicForm.TrivKCAux.main hw Y hYs hYK x hx h0 h1

end S_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero (solution)
