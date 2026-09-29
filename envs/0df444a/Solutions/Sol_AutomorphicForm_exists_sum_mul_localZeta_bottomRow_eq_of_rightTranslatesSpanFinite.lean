-- Prove2me | solution 1 for AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/81b05203-1ef2-5976-b870-4bbd66ecc8ed

import Mathlib
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
import Theorems.Thm_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex
import Theorems.Thm_AutomorphicForm_exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.TateLocal
open scoped ComplexConjugate

namespace R4LOC

variable {K : Type*} [NormedField K]

def diagU (u : Kˣ) : GL (Fin 2) K where
  val := !![1, 0; 0, (u : K)]
  inv := !![1, 0; 0, ((u⁻¹ : Kˣ) : K)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diagU_coe (u : Kˣ) : ((diagU u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, (u : K)] :=
  rfl

theorem diagU_mem_borel (u : Kˣ) : diagU u ∈ borelSubgroup K := by
  show ((diagU u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  simp

theorem isRowIsometry_diagU (u : Kˣ) (hu : ‖(u : K)‖ = 1) : IsRowIsometry (diagU u) := by
  constructor
  · simp [Matrix.det_fin_two, hu]
  · intro x y
    simp [hu]

theorem borelDiagFst_diagU (u : Kˣ) :
    borelDiagFst (⟨diagU u, diagU_mem_borel u⟩ : ↥(borelSubgroup K)) = 1 := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  simp

theorem borelDiagSnd_diagU (u : Kˣ) :
    borelDiagSnd (⟨diagU u, diagU_mem_borel u⟩ : ↥(borelSubgroup K)) = u := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  simp

theorem det_diagU (u : Kˣ) : Matrix.GeneralLinearGroup.det (diagU u) = u := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem diagU_mul_bottomRow (u : Kˣ) (k : GL (Fin 2) K) (i : Fin 2) :
    ((diagU u * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 i
      = (u : K) * (k : Matrix (Fin 2) (Fin 2) K) 1 i := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem sum_norm_sq_bottomRow (k : GL (Fin 2) K) (hk : IsRowIsometry k) :
    ∑ i : Fin 2, ‖(k : Matrix (Fin 2) (Fin 2) K) 1 i‖ ^ 2 = 1 := by
  have h := hk.2 0 1
  simp only [zero_mul, one_mul, zero_add, norm_zero, norm_one] at h
  rw [Fin.sum_univ_two, h]
  norm_num

end R4LOC
p2m_reactivate "P2MW.S_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite.R4LOC"

open R4LOC in
theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (μa : Measure w.Completion) [μa.IsAddHaarMeasure]
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (_h₁ : ∀ x, ‖((η₁ x : ℂˣ) : ℂ)‖ = 1) (_h₂ : ∀ x, ‖((η₂ x : ℂˣ) : ℂ)‖ = 1)
    (_h₁c : Continuous fun x : (w.Completion)ˣ => ((η₁ x : ℂˣ) : ℂ))
    (_h₂c : Continuous fun x : (w.Completion)ˣ => ((η₂ x : ℂˣ) : ℂ))
    (f : GL (Fin 2) w.Completion → ℂ) (_hfc : Continuous f)
    (_hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (_hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ (m : ℕ) (Φ : Fin m → (Fin 2 → w.Completion) → ℂ) (e : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (e j)) ∧
      (∀ j, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ j y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) ∧
      ∀ z : ℂ, 0 < z.re →
        ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
          (∑ j, e j z * (((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * localZeta μa (fun t => Φ j (fun i => t * (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                  (η₁ * η₂⁻¹) z))
            = f k := by

  set χ : (w.Completion)ˣ →* ℂˣ := η₁ * η₂⁻¹ with hχdef
  have hχval : ∀ u, ((χ u : ℂˣ) : ℂ) = ((η₁ u : ℂˣ) : ℂ) * (((η₂ u : ℂˣ) : ℂ))⁻¹ := fun u => by
    rw [hχdef, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  have hχ : ∀ u, ‖((χ u : ℂˣ) : ℂ)‖ = 1 := fun u => by
    rw [hχval, norm_mul, norm_inv, _h₁, _h₂, inv_one, mul_one]
  have hχc : Continuous fun u : (w.Completion)ˣ => ((χ u : ℂˣ) : ℂ) := by
    simp_rw [hχval]
    exact _h₁c.mul (_h₂c.inv₀ (fun u => Units.ne_zero _))

  have hpoly : ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ,
      ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
        f k = ((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
          * MvPolynomial.eval
              (Sum.elim (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (fun i => starRingEnd ℂ
                  (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P := by
    rcases isReal_or_isComplex w with hw | hw
    · exact AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
        F w hw η₁ η₂ f _hfc _hfK _hfB
    · exact AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex
        F w hw η₁ η₂ f _hfc _hfK _hfB
  obtain ⟨P, hP⟩ := hpoly

  obtain ⟨m, Φ, e, hdiff, hfmt, hmain⟩ :=
    AutomorphicForm.exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval F w μa χ hχ hχc P
  refine ⟨m, Φ, e, hdiff, hfmt, fun z hz k hk => ?_⟩
  have hx1 : ∑ i, ‖(k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i‖ ^ 2 = 1 := sum_norm_sq_bottomRow k hk

  have hequiv : ∀ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = 1 →
      MvPolynomial.eval
          (Sum.elim (fun i => extensionEmbedding w
              ((u : w.Completion) * (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
            (fun i => starRingEnd ℂ (extensionEmbedding w
              ((u : w.Completion) * (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P
        = ((χ u : ℂˣ) : ℂ)⁻¹ *
          MvPolynomial.eval
            (Sum.elim (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
              (fun i => starRingEnd ℂ
                (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P := by
    intro u hu
    have hb := diagU_mem_borel u
    have hbiso := isRowIsometry_diagU u hu
    have hbk : IsRowIsometry (diagU u * k) := hbiso.mul hk

    have h1 := _hfB (diagU u) hb hbiso k hk
    rw [borelDiagFst_diagU, borelDiagSnd_diagU, map_one, Units.val_one, one_mul] at h1
    have h2 := hP (diagU u * k) hbk
    have hdet : Matrix.GeneralLinearGroup.det (diagU u * k) = u * Matrix.GeneralLinearGroup.det k := by
      rw [map_mul, det_diagU]
    rw [hdet, map_mul η₁ u (Matrix.GeneralLinearGroup.det k), Units.val_mul] at h2
    simp only [diagU_mul_bottomRow] at h2
    have h3 := hP k hk
    rw [h2, h3] at h1

    have hne1 : ((η₁ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hne2 : ((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hne3 : ((η₂ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [hχval, mul_inv, inv_inv]
    have hgoal := h1
    field_simp
    field_simp at hgoal
    linear_combination hgoal
  have hkey := hmain z hz (fun i => (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i) hx1 hequiv
  rw [hP k hk, ← hkey, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end
end S_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite
end P2MW
export P2MW.S_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite (solution)
