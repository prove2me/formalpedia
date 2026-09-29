-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/04053ea1-e06a-5299-9109-2a84370cfe76

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact

set_option autoImplicit false

open NumberField IsDedekindDomain Matrix AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicHeight

noncomputable section

namespace R1HeightFloor

section Local

variable {K : Type*} [NormedField K]

def entrySq (M : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2

theorem entrySq_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ entrySq M := by
  unfold entrySq; positivity

theorem entrySq_pos (g : GL (Fin 2) K) : 0 < entrySq (g : Matrix (Fin 2) (Fin 2) K) := by
  have h := rowNormSq_pos g
  unfold rowNormSq at h
  unfold entrySq
  nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖, sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 1‖]

private theorem cs_two (a b c d : ℝ) :
    (a * b + c * d) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - c * b)]

private theorem norm_add_mul_sq_le (p q r s : K) :
    ‖p * q + r * s‖ ^ 2 ≤ (‖p‖ ^ 2 + ‖r‖ ^ 2) * (‖q‖ ^ 2 + ‖s‖ ^ 2) := by
  have h1 : ‖p * q + r * s‖ ≤ ‖p‖ * ‖q‖ + ‖r‖ * ‖s‖ := by
    calc ‖p * q + r * s‖ ≤ ‖p * q‖ + ‖r * s‖ := norm_add_le _ _
      _ = ‖p‖ * ‖q‖ + ‖r‖ * ‖s‖ := by rw [norm_mul, norm_mul]
  have h2 : ‖p * q + r * s‖ ^ 2 ≤ (‖p‖ * ‖q‖ + ‖r‖ * ‖s‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact h2.trans (cs_two _ _ _ _)

theorem rowNormSq_mul_le (g y : Matrix (Fin 2) (Fin 2) K) :
    rowNormSq (g * y) ≤ rowNormSq g * entrySq y := by
  have e0 : (g * y) 1 0 = g 1 0 * y 0 0 + g 1 1 * y 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : (g * y) 1 1 = g 1 0 * y 0 1 + g 1 1 * y 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold rowNormSq entrySq
  rw [e0, e1]
  have h0 := norm_add_mul_sq_le (g 1 0) (y 0 0) (g 1 1) (y 1 0)
  have h1 := norm_add_mul_sq_le (g 1 0) (y 0 1) (g 1 1) (y 1 1)
  nlinarith [h0, h1, sq_nonneg ‖g 1 0‖, sq_nonneg ‖g 1 1‖, sq_nonneg ‖y 0 0‖, sq_nonneg ‖y 0 1‖,
    sq_nonneg ‖y 1 0‖, sq_nonneg ‖y 1 1‖]

def archFactor (y : GL (Fin 2) K) : ℝ :=
  ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ / entrySq (y : Matrix (Fin 2) (Fin 2) K)

theorem archFactor_pos (y : GL (Fin 2) K) : 0 < archFactor y :=
  div_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero y)) (entrySq_pos y)

theorem localHeight_mul_archFactor_le (g y : GL (Fin 2) K) :
    localHeight g * archFactor y ≤ localHeight (g * y) := by
  have hrow : 0 < rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := rowNormSq_pos g
  have hrow' : 0 < rowNormSq ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rowNormSq_pos _
  have hE : 0 < entrySq (y : Matrix (Fin 2) (Fin 2) K) := entrySq_pos y
  have hle : rowNormSq ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) * entrySq (y : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.val_mul]; exact rowNormSq_mul_le _ _
  unfold localHeight archFactor
  rw [Units.val_mul, Matrix.det_mul, norm_mul, div_mul_div_comm]
  rw [Units.val_mul] at hrow'
  rw [div_le_div_iff₀ (mul_pos hrow hE) hrow']
  have hnn : 0 ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ := by
    positivity
  calc ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖
        * rowNormSq ((g : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K))
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖
        * (rowNormSq (g : Matrix (Fin 2) (Fin 2) K) * entrySq (y : Matrix (Fin 2) (Fin 2) K)) :=
        mul_le_mul_of_nonneg_left hle hnn
    _ = _ := by ring

end Local

section Ultra

variable {K : Type*} [NormedField K]

def entryMax (M : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  max (max ‖M 0 0‖ ‖M 0 1‖) (max ‖M 1 0‖ ‖M 1 1‖)

theorem norm_entry_le_entryMax (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) : ‖M i j‖ ≤ entryMax M := by
  unfold entryMax
  fin_cases i <;> fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem entryMax_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ entryMax M :=
  (norm_nonneg _).trans (norm_entry_le_entryMax M 0 0)

theorem entryMax_pos (g : GL (Fin 2) K) : 0 < entryMax (g : Matrix (Fin 2) (Fin 2) K) :=
  lt_of_lt_of_le (rowMaxNorm_pos g)
    (max_le (norm_entry_le_entryMax _ 1 0) (norm_entry_le_entryMax _ 1 1))

def finFactor (y : GL (Fin 2) K) : ℝ :=
  ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ / entryMax (y : Matrix (Fin 2) (Fin 2) K) ^ 2

theorem finFactor_pos (y : GL (Fin 2) K) : 0 < finFactor y :=
  div_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero y)) (pow_pos (entryMax_pos y) 2)

variable [IsUltrametricDist K]

theorem rowMaxNorm_mul_le (g y : Matrix (Fin 2) (Fin 2) K) :
    rowMaxNorm (g * y) ≤ rowMaxNorm g * entryMax y := by
  have key : ∀ j : Fin 2, ‖(g * y) 1 j‖ ≤ rowMaxNorm g * entryMax y := by
    intro j
    have e : (g * y) 1 j = g 1 0 * y 0 j + g 1 1 * y 1 j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (le_max_left _ _) (norm_entry_le_entryMax y 0 j) (norm_nonneg _)
        (rowMaxNorm_nonneg _)
    · rw [norm_mul]
      exact mul_le_mul (le_max_right _ _) (norm_entry_le_entryMax y 1 j) (norm_nonneg _)
        (rowMaxNorm_nonneg _)
  exact max_le (key 0) (key 1)

theorem finLocalHeight_mul_finFactor_le (g y : GL (Fin 2) K) :
    finLocalHeight g * finFactor y ≤ finLocalHeight (g * y) := by
  have hrow : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := rowMaxNorm_pos g
  have hrow' : 0 < rowMaxNorm ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rowMaxNorm_pos _
  have hE : 0 < entryMax (y : Matrix (Fin 2) (Fin 2) K) := entryMax_pos y
  have hle : rowMaxNorm ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) * entryMax (y : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.val_mul]; exact rowMaxNorm_mul_le _ _
  have hle2 : rowMaxNorm ((g * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
      ≤ (rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) * entryMax (y : Matrix (Fin 2) (Fin 2) K)) ^ 2 :=
    pow_le_pow_left₀ (rowMaxNorm_nonneg _) hle 2
  unfold finLocalHeight finFactor
  rw [Units.val_mul, Matrix.det_mul, norm_mul, div_mul_div_comm]
  rw [Units.val_mul] at hrow' hle2
  rw [div_le_div_iff₀ (mul_pos (pow_pos hrow 2) (pow_pos hE 2)) (pow_pos hrow' 2)]
  have hnn : 0 ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ := by
    positivity
  calc ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖
        * rowMaxNorm ((g : Matrix (Fin 2) (Fin 2) K) * (y : Matrix (Fin 2) (Fin 2) K)) ^ 2
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(y : Matrix (Fin 2) (Fin 2) K).det‖
        * (rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) * entryMax (y : Matrix (Fin 2) (Fin 2) K)) ^ 2 :=
        mul_le_mul_of_nonneg_left hle2 hnn
    _ = _ := by ring

theorem finFactor_eq_one (y : GL (Fin 2) K)
    (h : ∀ i j, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finFactor y = 1 := by

  have hdet1 : ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    refine le_antisymm (norm_det_le_one h) ?_
    have hinv : ‖((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
    have hprod : (y : Matrix (Fin 2) (Fin 2) K).det * ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
        = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have hn : ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ * ‖((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
        = 1 := by rw [← norm_mul, hprod, norm_one]
    by_contra hlt
    push Not at hlt
    have : ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ * ‖((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
        < 1 := by
      calc _ ≤ ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ * 1 :=
            mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hlt
    exact absurd hn this.ne

  have hmax_le : entryMax (y : Matrix (Fin 2) (Fin 2) K) ≤ 1 := by
    unfold entryMax
    exact max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))
  have hmax_ge : 1 ≤ entryMax (y : Matrix (Fin 2) (Fin 2) K) := by
    by_contra hlt
    push Not at hlt
    have hij : ∀ i j, ‖(y : Matrix (Fin 2) (Fin 2) K) i j‖ < 1 := fun i j =>
      (norm_entry_le_entryMax _ i j).trans_lt hlt
    have hlt' : ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ < 1 := by
      rw [Matrix.det_fin_two, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hij 0 0).le (norm_nonneg _) (hij 1 1)
      · rw [norm_neg, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hij 0 1).le (norm_nonneg _) (hij 1 0)
    rw [hdet1] at hlt'
    exact lt_irrefl _ hlt'
  unfold finFactor
  rw [hdet1, le_antisymm hmax_le hmax_ge, one_pow, div_one]

end Ultra

section UltraInv

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem entryMax_mul_le (a b : Matrix (Fin 2) (Fin 2) K) : entryMax (a * b) ≤ entryMax a * entryMax b := by
  have key : ∀ i j : Fin 2, ‖(a * b) i j‖ ≤ entryMax a * entryMax b := by
    intro i j
    have e : (a * b) i j = a i 0 * b 0 j + a i 1 * b 1 j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (norm_entry_le_entryMax a i 0) (norm_entry_le_entryMax b 0 j) (norm_nonneg _)
        (entryMax_nonneg _)
    · rw [norm_mul]
      exact mul_le_mul (norm_entry_le_entryMax a i 1) (norm_entry_le_entryMax b 1 j) (norm_nonneg _)
        (entryMax_nonneg _)
  unfold entryMax
  exact max_le (max_le (key 0 0) (key 0 1)) (max_le (key 1 0) (key 1 1))

theorem norm_det_eq_one_of_entries (k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  refine le_antisymm (norm_det_le_one h) ?_
  have hinv : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : (k : Matrix (Fin 2) (Fin 2) K).det * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hn : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = 1 := by rw [← norm_mul, hprod, norm_one]
  by_contra hlt
  push Not at hlt
  have : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      < 1 := by
    calc _ ≤ ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ * 1 :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt
  exact absurd hn this.ne

omit [IsUltrametricDist K] in
theorem entryMax_le_one_of_entries (k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) : entryMax (k : Matrix (Fin 2) (Fin 2) K) ≤ 1 := by
  unfold entryMax
  exact max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))

theorem finFactor_mul_eq_of_entries (y k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finFactor (y * k) = finFactor y := by
  have hdet : ‖((y * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = ‖(y : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, norm_det_eq_one_of_entries k h h', mul_one]
  have hmax : entryMax ((y * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = entryMax (y : Matrix (Fin 2) (Fin 2) K) := by
    refine le_antisymm ?_ ?_
    · rw [Units.val_mul]
      calc entryMax ((y : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K))
          ≤ entryMax (y : Matrix (Fin 2) (Fin 2) K) * entryMax (k : Matrix (Fin 2) (Fin 2) K) := entryMax_mul_le _ _
        _ ≤ entryMax (y : Matrix (Fin 2) (Fin 2) K) * 1 :=
            mul_le_mul_of_nonneg_left (entryMax_le_one_of_entries k h) (entryMax_nonneg _)
        _ = _ := mul_one _
    · have hy : (y : Matrix (Fin 2) (Fin 2) K) = ((y * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
      calc entryMax (y : Matrix (Fin 2) (Fin 2) K)
          = entryMax (((y * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
              * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by rw [← hy]
        _ ≤ entryMax ((y * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
              * entryMax ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := entryMax_mul_le _ _
        _ ≤ entryMax ((y * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * 1 :=
            mul_le_mul_of_nonneg_left (entryMax_le_one_of_entries k⁻¹ h') (entryMax_nonneg _)
        _ = _ := mul_one _
  unfold finFactor
  rw [hdet, hmax]

end UltraInv

section Adelic

variable (F : Type) [Field F] [NumberField F]

def archPart (y : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ w : InfinitePlace F, archFactor (archComponent F w y) ^ w.mult

def finPart (y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), finFactor (finComponent (𝓞 F) F v y)

def transFactor (y : AdelicGL2 (𝓞 F) F) : ℝ :=
  archPart F (glArch (𝓞 F) F y) * finPart F (glFin (𝓞 F) F y)

variable {F}

theorem archPart_pos (y : GL (Fin 2) (InfiniteAdeleRing F)) : 0 < archPart F y :=
  Finset.prod_pos fun _ _ => pow_pos (archFactor_pos _) _

theorem finFactor_finComponent_eventually_eq_one (y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      finFactor (finComponent (𝓞 F) F v y) = 1 := by
  have hg : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => ((y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hg' : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((y⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => (((y⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, (y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
        ∈ v.adicCompletionIntegers F)
      ∧ ∀ i j, ((y⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg i)).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg' i))
  filter_upwards [hall] with v hv
  refine finFactor_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.1 i j)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.2 i j)

theorem hasFiniteMulSupport_finFactor (y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (fun v : HeightOneSpectrum (𝓞 F) => finFactor (finComponent (𝓞 F) F v y)).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (finFactor_finComponent_eventually_eq_one y)

theorem finPart_pos (y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : 0 < finPart F y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun _ => finFactor_pos _

theorem transFactor_pos (y : AdelicGL2 (𝓞 F) F) : 0 < transFactor F y :=
  mul_pos (archPart_pos _) (finPart_pos _)

theorem archHeight_mul_archPart_le (g y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F g * archPart F y ≤ archHeight F (g * y) := by
  unfold archHeight archPart
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => ?_) (fun w _ => ?_)
  · exact mul_nonneg (pow_nonneg (localHeight_pos _).le _) (pow_nonneg (archFactor_pos _).le _)
  · rw [← mul_pow, map_mul]
    exact pow_le_pow_left₀ (mul_nonneg (localHeight_pos _).le (archFactor_pos _).le)
      (localHeight_mul_archFactor_le _ _) _

theorem finHeight_mul_finPart_le (g y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finHeight F g * finPart F y ≤ finHeight F (g * y) := by
  unfold finHeight finPart
  rw [← finprod_mul_distrib (hasFiniteMulSupport_finLocalHeight g) (hasFiniteMulSupport_finFactor y)]
  refine finprod_le_finprod ((hasFiniteMulSupport_finLocalHeight g).mul (hasFiniteMulSupport_finFactor y))
    (fun v => mul_nonneg (finLocalHeight_pos _).le (finFactor_pos _).le)
    (hasFiniteMulSupport_finLocalHeight (g * y)) (fun v => ?_)
  show finLocalHeight (finComponent (𝓞 F) F v g) * finFactor (finComponent (𝓞 F) F v y)
    ≤ finLocalHeight (finComponent (𝓞 F) F v (g * y))
  rw [map_mul]
  exact finLocalHeight_mul_finFactor_le _ _

theorem adelicHeight_mul_transFactor_le (g y : AdelicGL2 (𝓞 F) F) :
    adelicHeight F g * transFactor F y ≤ adelicHeight F (g * y) := by
  unfold adelicHeight transFactor
  rw [map_mul, map_mul, mul_mul_mul_comm]
  exact mul_le_mul (archHeight_mul_archPart_le _ _) (finHeight_mul_finPart_le _ _)
    (mul_nonneg (finHeight_pos _).le (finPart_pos _).le) (archHeight_pos F _).le

theorem continuous_archFactor {K : Type*} [NormedField K] :
    Continuous (archFactor (K := K)) := by
  unfold archFactor entrySq
  refine continuous_det_gl.norm.div ?_ fun y => (entrySq_pos y).ne'
  exact ((((continuous_entry 0 0).norm.pow 2).add ((continuous_entry 0 1).norm.pow 2)).add
    ((continuous_entry 1 0).norm.pow 2)).add ((continuous_entry 1 1).norm.pow 2)

theorem continuous_archPart : Continuous (fun y : AdelicGL2 (𝓞 F) F => archPart F (glArch (𝓞 F) F y)) := by
  unfold archPart
  exact continuous_finsetProd _ fun w _ =>
    ((continuous_archFactor.comp ((continuous_archComponent F w).comp (continuous_glArch (𝓞 F) F))).pow _)

theorem finPart_mul_eq_of_mem (y k : AdelicGL2 (𝓞 F) F) (hk : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finPart F (glFin (𝓞 F) F (y * k)) = finPart F (glFin (𝓞 F) F y) := by
  rw [mem_finiteIntegralGL2_iff] at hk
  unfold finPart
  refine finprod_congr fun v => ?_
  rw [map_mul, map_mul]
  refine finFactor_mul_eq_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

theorem isLocallyConstant_finPart :
    IsLocallyConstant (fun y : AdelicGL2 (𝓞 F) F => finPart F (glFin (𝓞 F) F y)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  have htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by simp
  refine ⟨(fun k => y * k) '' (levelZero (𝓞 F) F ⊤ : Set (AdelicGL2 (𝓞 F) F)), ?_, ?_, ?_⟩
  · exact (Homeomorph.mulLeft y).isOpenMap _ (isOpen_levelZero (𝓞 F) F htop)
  · exact ⟨1, (levelZero (𝓞 F) F ⊤).one_mem, mul_one y⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact finPart_mul_eq_of_mem y k hk

theorem continuous_transFactor : Continuous (transFactor F) :=
  (continuous_archPart (F := F)).mul (isLocallyConstant_finPart (F := F)).continuous

theorem exists_pos_forall_le_adelicHeight_mul (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (T : Set (AdelicGL2 (𝓞 F) F)) (hT : IsCompact T) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ g ∈ centreCutSiegelSet F c u d₁ d₂, ∀ y ∈ T,
      h₀ ≤ adelicHeight F (g * y) := by
  by_cases hTe : T = ∅
  · exact ⟨1, one_pos, fun g _ y hy => by simp [hTe] at hy⟩
  obtain ⟨y₀, hy₀T, hy₀⟩ := hT.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hTe)
    (continuous_transFactor (F := F)).continuousOn
  set cF : ℝ := ∏ w : InfinitePlace F, c ^ w.mult with hcF
  have hcFpos : 0 < cF := Finset.prod_pos fun w _ => pow_pos hc _
  refine ⟨cF * transFactor F y₀, mul_pos hcFpos (transFactor_pos y₀), fun g hg y hy => ?_⟩
  rw [mem_centreCutSiegelSet_iff] at hg
  have hH : adelicHeight F g = archHeight F (glArch (𝓞 F) F g) := adelicHeight_eq_archHeight_of_mem hg.1
  have hcle : cF ≤ archHeight F (glArch (𝓞 F) F g) := by
    unfold archHeight
    exact Finset.prod_le_prod (fun w _ => pow_nonneg hc.le _) fun w _ => pow_le_pow_left₀ hc.le (hg.2.1 w) _
  calc cF * transFactor F y₀ ≤ adelicHeight F g * transFactor F y := by
        rw [hH]
        exact mul_le_mul hcle (hy₀ hy) (transFactor_pos y₀).le (archHeight_pos F _).le
    _ ≤ adelicHeight F (g * y) := adelicHeight_mul_transFactor_le g y

end Adelic

end R1HeightFloor

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (T : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hT : IsCompact T) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ g ∈ AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂, ∀ y ∈ T,
      h₀ ≤ NumberField.AdelicHeight.adelicHeight F (g * y) :=
  R1HeightFloor.exists_pos_forall_le_adelicHeight_mul c u d₁ d₂ hc T hT

end S_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact (solution)
