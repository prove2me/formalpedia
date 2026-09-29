-- Prove2me | solution 1 for AutomorphicForm.apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e72a1db2-3b30-52a7-9333-ba41769ab777

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace InvZeroC

p2m_open "NumberField NumberField.InfinitePlace.NumberField AutomorphicForm IsDedekindDomain"

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

theorem apply_mul_archFlowAtComplex_eq (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex)
    (hd : archDerivAtComplex hw d φ = 0) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    φ (g * archFlowAtComplex hw d t) = φ g := by
  set f : ℝ → ℂ := fun t => φ (g * archFlowAtComplex hw d t) with hf
  have hderiv : ∀ t : ℝ, HasDerivAt f 0 t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) 0 0 := by
      have hda := (hφ.differentiableAt_flow d (g * archFlowAtComplex hw d t)).hasDerivAt
      have hz : deriv (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) 0 = 0 :=
        congrFun hd (g * archFlowAtComplex hw d t)
      rwa [hz] at hda
    have h1 : (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) = fun s => f (t + s) := by
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

theorem apply_mul_upper (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hE : archDerivAtComplex hw .E φ = 0) (hiE : archDerivAtComplex hw .iE φ = 0) (g : AdelicGL2 (𝓞 F) F) (z : ℂ) :
    φ (g * archComplexGLAt hw (unipotentGL2 z)) = φ g := by
  have hz : unipotentGL2 z = unipotentGL2 ((z.re : ℝ) : ℂ) * unipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I) := by
    rw [← unipotentGL2_add]; congr 1; exact (Complex.re_add_im z).symm
  rw [hz, map_mul, ← mul_assoc]
  have h1 : archComplexGLAt hw (unipotentGL2 ((z.re : ℝ) : ℂ)) = archFlowAtComplex hw .E z.re := rfl
  have h2 : archComplexGLAt hw (unipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I)) = archFlowAtComplex hw .iE z.im := rfl
  rw [h1, h2, apply_mul_archFlowAtComplex_eq hw φ hφ .iE hiE, apply_mul_archFlowAtComplex_eq hw φ hφ .E hE]

theorem apply_mul_lower (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hFm : archDerivAtComplex hw .Fm φ = 0) (hiFm : archDerivAtComplex hw .iFm φ = 0) (g : AdelicGL2 (𝓞 F) F) (z : ℂ) :
    φ (g * archComplexGLAt hw (lowerUnipotentGL2 z)) = φ g := by
  have hz : lowerUnipotentGL2 z = lowerUnipotentGL2 ((z.re : ℝ) : ℂ) * lowerUnipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I) := by
    rw [← lowerUnipotentGL2_add]; congr 1; exact (Complex.re_add_im z).symm
  rw [hz, map_mul, ← mul_assoc]
  have h1 : archComplexGLAt hw (lowerUnipotentGL2 ((z.re : ℝ) : ℂ)) = archFlowAtComplex hw .Fm z.re := rfl
  have h2 : archComplexGLAt hw (lowerUnipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I)) = archFlowAtComplex hw .iFm z.im := rfl
  rw [h1, h2, apply_mul_archFlowAtComplex_eq hw φ hφ .iFm hiFm, apply_mul_archFlowAtComplex_eq hw φ hφ .Fm hFm]

theorem exists_eq_lower_upper_lower_upper (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    ∃ s x c y : ℂ, h = lowerUnipotentGL2 s * unipotentGL2 x * lowerUnipotentGL2 c * unipotentGL2 y := by
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      - (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hh
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_two] at this
    exact this
  set a := (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 with ha
  set b := (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 with hb
  set c := (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 with hc
  set d := (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 with hd
  have heta : (h : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _
  by_cases hc0 : c = 0
  · have ha0 : a ≠ 0 := by
      intro h0; rw [h0, hc0] at hdet; simp at hdet
    refine ⟨-1, (a - 1) / a, a, (b + d - 1) / a, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, heta, lowerUnipotentGL2_coe, lowerUnipotentGL2_coe,
      unipotentGL2_coe, unipotentGL2_coe]
    rw [hc0] at hdet ⊢
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
      first | (linear_combination hdet) | (linear_combination -hdet) | (linear_combination a * hdet) | (linear_combination (-a) * hdet) | (linear_combination c * hdet) | (linear_combination (-c) * hdet) | ring1
  · refine ⟨0, (a - 1) / c, c, (d - 1) / c, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, heta, lowerUnipotentGL2_coe, lowerUnipotentGL2_coe,
      unipotentGL2_coe, unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
      first | (linear_combination hdet) | (linear_combination -hdet) | (linear_combination a * hdet) | (linear_combination (-a) * hdet) | (linear_combination c * hdet) | (linear_combination (-c) * hdet) | ring1

theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hD : ∀ d : ArchDirComplex, archDerivAtComplex hw d φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archComplexGLAt hw h) = φ g := by
  obtain ⟨s, x, c, y, rfl⟩ := exists_eq_lower_upper_lower_upper h hh
  rw [map_mul, map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    apply_mul_upper hw φ hφ (hD .E) (hD .iE), apply_mul_lower hw φ hφ (hD .Fm) (hD .iFm),
    apply_mul_upper hw φ hφ (hD .E) (hD .iE), apply_mul_lower hw φ hφ (hD .Fm) (hD .iFm)]

end InvZeroC

end

p2m_open "NumberField NumberField.InfinitePlace.NumberField AutomorphicForm IsDedekindDomain"

theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hD : ∀ d : ArchDirComplex, archDerivAtComplex hw d φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archComplexGLAt hw h) = φ g := by
  exact InvZeroC.main hw φ hφ hD g h hh

end S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero (solution)
