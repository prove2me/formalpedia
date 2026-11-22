-- Prove2me | solution 1 for Auto.HeatData.neighbor_cost_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:22:08.499023+00:00
-- url     : https://prove2.me/submissions/c5e91ba6-480e-4598-9f34-ec7025ce3982

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_ne_top
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_matCost_comparison
public import Theorems.Thm_Auto_matCost_anti
public import Theorems.Thm_Auto_rowMat_insert
public import Theorems.Thm_Auto_fromBlocks_diag_posSemidef
public import Theorems.Thm_Auto_matCost_fromBlocks_ge
public import Theorems.Thm_Auto_HeatData_Ui_eq
public import Theorems.Thm_Auto_HeatData_Pprev_succ_eq
public import Theorems.Thm_Auto_HeatData_Pnext_pred_eq
public import Theorems.Thm_Auto_HeatData_S_eq_sum
public import Theorems.Thm_Auto_two_blocks_sub_gram_posSemidef

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) {w : Fin 3} (hσ : 0 < σ w) {η : ℝ} (hη : 0 < η) :
    Hd.Yprev p σ η (w + 1) + Hd.Ynext p σ η (w - 1) ≤ √2 * Hd.V p σ η w := by
  set A := Hd.W p σ w
  set B := Hd.W p σ (w - 1)
  set Nm := Hd.N p σ w
  have hpd : ∀ X : Matrix ι ι ℂ, X.PosSemidef → (X + (η : ℂ) • 1).PosDef := fun X hX =>
    posDef_add_smul_one hX hη
  set Q := Matrix.fromBlocks (Aᴴ * A + (η : ℂ) • 1) 0 0 (B * Bᴴ + (η : ℂ) • 1)
  have hQ1 := hpd _ (Matrix.posSemidef_conjTranspose_mul_self A)
  have hQ2 := hpd _ (Matrix.posSemidef_self_mul_conjTranspose B)
  have hQ : Q.PosSemidef := fromBlocks_diag_posSemidef hQ1.posSemidef hQ2.posSemidef
  have hTQ : Hd.T p σ w + (η : ℂ) • 1 ≤ ((2 : ℝ) : ℂ) • Q := by
    rw [Matrix.le_iff]
    exact two_blocks_sub_gram_posSemidef A B hη.le
  have hcmp := matCost_comparison hQ two_pos hTQ (Hd.Ui p σ w)
  have hUi : Hd.Ui p σ w = Matrix.fromBlocks (Aᴴ * Nm * A) (Aᴴ * Nm * Bᴴ) (B * Nm * A) (B * Nm * Bᴴ)
      := by
    rw [Hd.Ui_eq p σ hh hσ]; exact rowMat_insert _ _ _
  have hdis := matCost_fromBlocks_ge hQ1.posSemidef hQ2.posSemidef (Aᴴ * Nm * A) (Aᴴ * Nm * Bᴴ) (B *
      Nm * A) (B * Nm * Bᴴ)
  rw [← hUi] at hdis
  have hS1 : Aᴴ * A + (η : ℂ) • 1 ≤ Hd.S p σ (w + 1) + (η : ℂ) • 1 := by
    rw [Matrix.le_iff, Hd.S_eq_sum p σ (w + 1), show w + 1 - 1 = w by abel,
        add_sub_add_right_eq_sub]
    convert Matrix.posSemidef_self_mul_conjTranspose (Hd.W p σ (w + 1)) using 1 <;>
      first | rfl | exact add_sub_cancel_right _ _
  have hS2 : B * Bᴴ + (η : ℂ) • 1 ≤ Hd.S p σ (w - 1) + (η : ℂ) • 1 := by
    rw [Matrix.le_iff, Hd.S_eq_sum p σ (w - 1), add_sub_add_right_eq_sub]
    convert Matrix.posSemidef_conjTranspose_mul_self (Hd.W p σ (w - 1 - 1)) using 1 <;>
      first | rfl | exact add_sub_cancel_left _ _
  have hSpsd : ∀ v, (Hd.S p σ v).PosSemidef := fun v =>
    Matrix.posSemidef_self_mul_conjTranspose _
  have hY1 := matCost_anti (hpd _ (hSpsd _)).posSemidef hS1 (Hd.Pprev p σ (w + 1))
  have hY2 := matCost_anti (hpd _ (hSpsd _)).posSemidef hS2 (Hd.Pnext p σ (w - 1))
  rw [← Hd.Pprev_succ_eq p σ hh hσ, ← Hd.Pnext_pred_eq p σ hh hσ] at hdis
  have hmain : matCost (Hd.S p σ (w + 1) + (η : ℂ) • 1) (Hd.Pprev p σ (w + 1)) +
      matCost (Hd.S p σ (w - 1) + (η : ℂ) • 1) (Hd.Pnext p σ (w - 1)) ≤
      ENNReal.ofReal √2 * matCost (Hd.T p σ w + (η : ℂ) • 1) (Hd.Ui p σ w) := by
    have h1 : ENNReal.ofReal √2 * ENNReal.ofReal (√2)⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity),
        mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 two_pos), ENNReal.ofReal_one]
    calc _ ≤ matCost Q (Hd.Ui p σ w) := by
          refine le_trans (add_le_add hY1 hY2) ?_
          exact hdis
      _ = ENNReal.ofReal √2 * (ENNReal.ofReal (√2)⁻¹ * matCost Q (Hd.Ui p σ w)) := by
        rw [← mul_assoc, h1, one_mul]
      _ ≤ _ := by gcongr
  have hfin := matCost_ne_top (posDef_add_smul_one (Matrix.posSemidef_conjTranspose_mul_self (Hd.R p
      σ w)) hη) (Hd.Ui p σ w)
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hmain
  rw [ENNReal.toReal_add (matCost_ne_top (hpd _ (hSpsd _)) _) (matCost_ne_top (hpd _ (hSpsd _)) _),
      ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
  exact this
end Auto.HeatData
