-- Prove2me | solution 1 for AutomorphicForm.exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a6bae896-6ed7-5a3b-a0c7-c33023862e0e

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace K5C

open Matrix Complex

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)

def chartL (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : (Fin 2 → Fin 2 → ℂ) →L[ℝ] ℂ :=
  fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e)) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))

theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero

theorem archComplexGLAt_eq_lift (u : GL (Fin 2) ℂ) :
    archComplexGLAt hw u = archComplexLiftAt hw (Matrix.of.symm (u : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h := archComplexLiftAt_mul_archComplexGLAt hw det_of_symm_one u
  rw [archComplexLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

theorem hasDerivAt_conj_flowMatrix (m : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) *
        ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ))
      (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex d * ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) 0 := by
  have h1 := hasDerivAt_of_symm_mul_archFlowMatrixComplex ((m : Matrix (Fin 2) (Fin 2) ℂ)) d
  rw [hasDerivAt_pi] at h1
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have h1i := h1 i
  rw [hasDerivAt_pi] at h1i
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply] at h1i ⊢
  exact HasDerivAt.fun_sum fun l _ => (h1i l).mul_const _

theorem hasDerivAt_conj_flow {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    HasDerivAt (fun t : ℝ => φ (g * archComplexGLAt hw m * archFlowAtComplex hw d t * archComplexGLAt hw m⁻¹))
      (chartL hw φ g (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex d *
        ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))) 0 := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have hdiff : DifferentiableAt ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e'))
      (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
    ((hφ g).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)
  have hfun : (fun t : ℝ => φ (g * archComplexGLAt hw m * archFlowAtComplex hw d t * archComplexGLAt hw m⁻¹)) =
      (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) ∘
      (fun t : ℝ => (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) *
        ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ)) := by
    funext t
    simp only [Function.comp_apply]
    rw [mul_assoc g, mul_assoc g, archFlowAtComplex, ← map_mul, ← map_mul, archComplexGLAt_eq_lift]
    rfl
  have h0 : (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ) *
      ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ) = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [archFlowMatrixComplex_zero, Units.val_one, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hfun]
  refine HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) ?_ (hasDerivAt_conj_flowMatrix m d)
  rw [h0]
  exact hdiff.hasFDerivAt

theorem archDerivAtComplex_eq_chartL {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 K) K)
    (d : ArchDirComplex) :
    archDerivAtComplex hw d φ g = chartL hw φ g (Matrix.of.symm (archDirMatrixComplex d)) := by
  have h := hasDerivAt_conj_flow hw hφ g 1 d
  simp only [map_one, inv_one, mul_one, Units.val_one, one_mul] at h
  exact h.deriv

def K1m : Matrix (Fin 2) (Fin 2) ℂ := !![(1 + I) / 2, -((1 + I) / 2); (1 - I) / 2, (1 - I) / 2]
def K1i : Matrix (Fin 2) (Fin 2) ℂ := !![(1 - I) / 2, (1 + I) / 2; -((1 - I) / 2), (1 + I) / 2]
def K2m : Matrix (Fin 2) (Fin 2) ℂ := !![(1 + I) / 2, -((1 - I) / 2); (1 + I) / 2, (1 - I) / 2]
def K2i : Matrix (Fin 2) (Fin 2) ℂ := !![(1 - I) / 2, (1 - I) / 2; -((1 + I) / 2), (1 + I) / 2]

theorem K1m_mul_K1i : K1m * K1i = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, K1m, K1i, Matrix.mul_apply, Fin.sum_univ_two]
theorem K1i_mul_K1m : K1i * K1m = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, K1m, K1i, Matrix.mul_apply, Fin.sum_univ_two]
theorem K2m_mul_K2i : K2m * K2i = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, K2m, K2i, Matrix.mul_apply, Fin.sum_univ_two]
theorem K2i_mul_K2m : K2i * K2m = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, K2m, K2i, Matrix.mul_apply, Fin.sum_univ_two]

def K1 : GL (Fin 2) ℂ := ⟨K1m, K1i, K1m_mul_K1i, K1i_mul_K1m⟩
def K2 : GL (Fin 2) ℂ := ⟨K2m, K2i, K2m_mul_K2i, K2i_mul_K2m⟩

theorem K1_conj : (K1 : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex .iH * ((K1⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    archDirMatrixComplex .Fm - archDirMatrixComplex .E := by
  show K1m * archDirMatrixComplex .iH * K1i = archDirMatrixComplex .Fm - archDirMatrixComplex .E
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Complex.ext_iff, K1m, K1i, archDirMatrixComplex, Matrix.mul_apply, Fin.sum_univ_two]

theorem K2_conj : (K2 : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex .iH * ((K2⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    archDirMatrixComplex .iE + archDirMatrixComplex .iFm := by
  show K2m * archDirMatrixComplex .iH * K2i = archDirMatrixComplex .iE + archDirMatrixComplex .iFm
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Complex.ext_iff, K2m, K2i, archDirMatrixComplex, Matrix.mul_apply, Fin.sum_univ_two]

theorem K1m_det : K1m.det = 1 := by
  norm_num [Complex.ext_iff, K1m, Matrix.det_fin_two]
theorem K2m_det : K2m.det = 1 := by
  norm_num [Complex.ext_iff, K2m, Matrix.det_fin_two]

theorem K1m_rows (a b : ℂ) : ‖a * K1m 0 0 + b * K1m 1 0‖ ^ 2 + ‖a * K1m 0 1 + b * K1m 1 1‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp only [K1m, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im, Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat]
  ring
theorem K2m_rows (a b : ℂ) : ‖a * K2m 0 0 + b * K2m 1 0‖ ^ 2 + ‖a * K2m 0 1 + b * K2m 1 1‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp only [K2m, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im, Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem mem_rowIsometrySubgroup₀_glEquiv (M : GL (Fin 2) ℂ) (hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (hrows : ∀ a b : ℂ, ‖a * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + b * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖a * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + b * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) :
    glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm M ∈ rowIsometrySubgroup₀ w.Completion := by
  set e := ringEquivComplexOfIsComplex hw with he
  have hn : ∀ z : w.Completion, ‖z‖ = ‖e z‖ := fun z =>
    ((isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z).symm
  have hent : ∀ i j, ((glEquivOfRingEquiv e.symm M : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j =
      e.symm ((M : Matrix (Fin 2) (Fin 2) ℂ) i j) := fun i j => glEquivOfRingEquiv_apply_entry _ _ _ _
  have hmat : ((glEquivOfRingEquiv e.symm M : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) =
      (M : Matrix (Fin 2) (Fin 2) ℂ).map e.symm := by
    ext i j; rw [hent, Matrix.map_apply]
  have hdet' : ((glEquivOfRingEquiv e.symm M : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
    have h := RingHom.map_det (e.symm.toRingHom) (M : Matrix (Fin 2) (Fin 2) ℂ)
    rw [RingHom.mapMatrix_apply, hdet, map_one] at h
    have hmat' : ((glEquivOfRingEquiv e.symm M : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) =
        (M : Matrix (Fin 2) (Fin 2) ℂ).map ⇑e.symm.toRingHom := by
      rw [hmat]; rfl
    rw [hmat']
    exact h.symm
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet', ⟨by rw [hdet', norm_one], fun x y => ?_⟩⟩
  rw [hn, hn, hn x, hn y, map_add, map_add, map_mul, map_mul, map_mul, map_mul, hent, hent, hent, hent,
    e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
  exact hrows _ _

def k1 : rowIsometrySubgroup₀ w.Completion :=
  ⟨glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm K1, mem_rowIsometrySubgroup₀_glEquiv hw K1 K1m_det K1m_rows⟩
def k2 : rowIsometrySubgroup₀ w.Completion :=
  ⟨glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm K2, mem_rowIsometrySubgroup₀_glEquiv hw K2 K2m_det K2m_rows⟩

theorem incl_k1 : rowIsometryInclAt₀ K w (k1 hw) = archComplexGLAt hw K1 := rfl
theorem incl_k2 : rowIsometryInclAt₀ K w (k2 hw) = archComplexGLAt hw K2 := rfl
theorem incl_k1_inv : rowIsometryInclAt₀ K w (k1 hw)⁻¹ = archComplexGLAt hw K1⁻¹ := by rw [map_inv, map_inv, incl_k1]
theorem incl_k2_inv : rowIsometryInclAt₀ K w (k2 hw)⁻¹ = archComplexGLAt hw K2⁻¹ := by rw [map_inv, map_inv, incl_k2]

theorem conj_identity {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (m : GL (Fin 2) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hconj : (m : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex .iH * ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A)
    (g : AdelicGL2 (𝓞 K) K) :
    rightTranslate K (archComplexGLAt hw m)
        (archDerivAtComplex hw .iH (rightTranslate K (archComplexGLAt hw m⁻¹) φ)) g =
      chartL hw φ g (Matrix.of.symm A) := by
  show deriv (fun t : ℝ => φ (g * archComplexGLAt hw m * archFlowAtComplex hw .iH t * archComplexGLAt hw m⁻¹)) 0 = _
  rw [(hasDerivAt_conj_flow hw hφ g m .iH).deriv, hconj]

end K5C

open K5C in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ k₁ k₂ : rowIsometrySubgroup₀ w.Completion,
      ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ, IsArchSmoothAtComplex hw ψ →
        (archDerivAtComplex hw .Fm ψ - archDerivAtComplex hw .E ψ =
          rightTranslate K (rowIsometryInclAt₀ K w k₁)
            (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k₁⁻¹) ψ))) ∧
        (archDerivAtComplex hw .iE ψ + archDerivAtComplex hw .iFm ψ =
          rightTranslate K (rowIsometryInclAt₀ K w k₂)
            (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k₂⁻¹) ψ))) := by
  refine ⟨K5C.k1 hw, K5C.k2 hw, fun ψ hψ => ⟨?_, ?_⟩⟩
  · funext g
    rw [K5C.incl_k1, K5C.incl_k1_inv, K5C.conj_identity hw hψ K5C.K1 _ K5C.K1_conj g, Pi.sub_apply,
      K5C.archDerivAtComplex_eq_chartL hw hψ g .Fm, K5C.archDerivAtComplex_eq_chartL hw hψ g .E, ← map_sub]
    rfl
  · funext g
    rw [K5C.incl_k2, K5C.incl_k2_inv, K5C.conj_identity hw hψ K5C.K2 _ K5C.K2_conj g, Pi.add_apply,
      K5C.archDerivAtComplex_eq_chartL hw hψ g .iE, K5C.archDerivAtComplex_eq_chartL hw hψ g .iFm, ← map_add]
    rfl

end
end S_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate
end P2MW
export P2MW.S_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate (solution)
