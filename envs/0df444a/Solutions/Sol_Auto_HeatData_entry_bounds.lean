-- Prove2me | solution 1 for Auto.HeatData.entry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:25:51.672307+00:00
-- url     : https://prove2.me/submissions/4c65d401-e833-4b9d-816f-b2d0c45713b1

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_T_eq_wGram
public import Theorems.Thm_Auto_HeatData_S_eq_wGram
public import Theorems.Thm_Auto_HeatData_Dc_eq
public import Theorems.Thm_Auto_edec_pos
public import Theorems.Thm_Auto_norm_wGram_le
public import Theorems.Thm_Auto_HeatData_norm_A_le
public import Theorems.Thm_Auto_HeatData_MA_nonneg
public import Theorems.Thm_Auto_HeatData_norm_rowMat_le
public import Theorems.Thm_Auto_HeatData_weight_bounds
public import Theorems.Thm_Auto_HeatData_sqw_nonneg

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) {σa σb : ℝ} (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ v, (∀ a b, ‖Hd.T p σ v a
      b‖ ≤ C * phi σb v p ^ 2 ∧ ‖Hd.Ui p σ v a b‖ ≤ C * phi σb v p ^ 2 ∧ ‖wGram (Hd.Brow p σ v)
      (Hd.ddw p σ v) a b‖ ≤ C * phi σb v p ^ 2) ∧ (∀ i j, ‖Hd.S p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧
      ‖Hd.Pnext p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧ ‖Hd.Pprev p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧
      ‖wGram (Hd.Bnext p σ v) (Hd.ddw p σ (v + 1)) i j‖ ≤ C * phi σb v p ^ 2 ∧ ‖wGram (Hd.Bprev p
      σ v) (Hd.ddw p σ (v - 1)) i j‖ ≤ C * phi σb v p ^ 2) := by
  obtain ⟨Cw, hCw, hw⟩ := Hd.weight_bounds hh ha hab
  set sC := √Cw
  have hsC : 0 ≤ sC := Real.sqrt_nonneg _
  set K := (Fintype.card ι : ℝ) * (Hd.MA * sC) ^ 2 * Cw
  have hK : 0 ≤ K := by have := Hd.MA_nonneg; positivity
  refine ⟨2 * K, by positivity, fun p σ hσ v => ?_⟩
  have hσpos : ∀ k, 0 < σ k := fun k => ha.trans_le (hσ k).1
  set E0 := edec σb (p v)
  set E1 := edec σb (p (v + 1))
  set E2 := edec σb (p (v - 1))
  have hE0 : 0 ≤ E0 := (edec_pos _ _).le
  have hE1 : 0 ≤ E1 := (edec_pos _ _).le
  have hE2 : 0 ≤ E2 := (edec_pos _ _).le
  have hphi : phi σb v p = E0 * (E1 + E2) := rfl
  have hMA := Hd.MA_nonneg
  have hBrow : ∀ i a, ‖Hd.Brow p σ v i a‖ ≤ Hd.MA * sC * (E1 + E2) := by
    intro i a
    rw [Brow, Dc_eq, rdiag, Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd : |Hd.dv p σ v a| ≤ sC * (E1 + E2) := by
      rcases a with j | j
      · simp only [dv, Sum.elim_inl]
        rw [abs_of_nonneg (Hd.sqw_nonneg _ _ _ _)]
        have := (hw p σ hσ (v + 1) j).2.2.2
        nlinarith
      · simp only [dv, Sum.elim_inr]
        rw [abs_of_nonneg (Hd.sqw_nonneg _ _ _ _)]
        have := (hw p σ hσ (v - 1) j).2.2.2
        nlinarith
    rw [mul_assoc]
    exact mul_le_mul (Hd.norm_rowMat_le v i a) hd (abs_nonneg _) hMA
  have hrow : ∀ f : ι → ℝ, (∀ i, |f i| ≤ Cw * E0 ^ 2) → ∀ a b,
      ‖wGram (Hd.Brow p σ v) f a b‖ ≤ 2 * K * phi σb v p ^ 2 := by
    intro f hf a b
    refine (norm_wGram_le _ f hBrow hf a b).trans ?_
    rw [hphi]
    have : (Fintype.card ι : ℝ) * (Hd.MA * sC * (E1 + E2) * (Cw * E0 ^ 2) * (Hd.MA * sC * (E1 +
        E2))) = K * (E0 * (E1 + E2)) ^ 2 := by
      simp only [K]; ring
    rw [this]
    have : 0 ≤ K * (E0 * (E1 + E2)) ^ 2 := by positivity
    linarith
  have hBn : ∀ j i, ‖Hd.Bnext p σ v j i‖ ≤ Hd.MA * sC * E0 := by
    intro j i
    rw [Bnext, rdiag, Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Hd.sqw_nonneg _ _ _ _), mul_assoc]
    simp only [Matrix.conjTranspose_apply, norm_star]
    exact mul_le_mul (Hd.norm_A_le v i j) (hw p σ hσ v i).2.2.2 (Hd.sqw_nonneg _ _ _ _) hMA
  have hBp : ∀ j i, ‖Hd.Bprev p σ v j i‖ ≤ Hd.MA * sC * E0 := by
    intro j i
    rw [Bprev, rdiag, Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Hd.sqw_nonneg _ _ _ _), mul_assoc]
    exact mul_le_mul (Hd.norm_A_le (v - 1) j i) (hw p σ hσ v i).2.2.2 (Hd.sqw_nonneg _ _ _ _)
      hMA
  have hcol : ∀ (B : Matrix ι ι ℂ) (E : ℝ), 0 ≤ E → E ≤ E1 + E2 → (∀ j i, ‖B j i‖ ≤ Hd.MA * sC * E0)
      → ∀ f : ι → ℝ, (∀ i, |f i| ≤ Cw * E ^ 2) →
      ∀ a b, ‖wGram B f a b‖ ≤ K * phi σb v p ^ 2 := by
    intro B E hE hEle hB f hf a b
    refine (norm_wGram_le _ f hB hf a b).trans ?_
    rw [hphi]
    have : (Fintype.card ι : ℝ) * (Hd.MA * sC * E0 * (Cw * E ^ 2) * (Hd.MA * sC * E0)) =
        K * (E0 * E) ^ 2 := by simp only [K]; ring
    rw [this]
    gcongr
  have h1 : E1 ≤ E1 + E2 := by linarith
  have h2 : E2 ≤ E1 + E2 := by linarith
  refine ⟨fun a b => ⟨?_, ?_, ?_⟩, fun i j => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [T_eq_wGram Hd p σ hh (hσpos v)]
    exact hrow _ (fun i => (hw p σ hσ v i).1) a b
  · exact hrow _ (fun i => (hw p σ hσ v i).2.1) a b
  · exact hrow _ (fun i => (hw p σ hσ v i).2.2.1) a b
  · rw [S_eq_wGram Hd p σ hh (hσpos _) (hσpos _), Matrix.add_apply]
    refine (norm_add_le _ _).trans ?_
    have := hcol _ E1 hE1 h1 hBn _ (fun i => (hw p σ hσ (v + 1) i).1) i j
    have := hcol _ E2 hE2 h2 hBp _ (fun i => (hw p σ hσ (v - 1) i).1) i j
    linarith
  · have := hcol _ E1 hE1 h1 hBn _ (fun i => (hw p σ hσ (v + 1) i).2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    rw [Pnext]; linarith
  · have := hcol _ E2 hE2 h2 hBp _ (fun i => (hw p σ hσ (v - 1) i).2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    rw [Pprev]; linarith
  · have := hcol _ E1 hE1 h1 hBn _ (fun i => (hw p σ hσ (v + 1) i).2.2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    linarith
  · have := hcol _ E2 hE2 h2 hBp _ (fun i => (hw p σ hσ (v - 1) i).2.2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    linarith
end Auto.HeatData
