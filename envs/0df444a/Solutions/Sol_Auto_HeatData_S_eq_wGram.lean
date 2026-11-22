-- Prove2me | solution 1 for Auto.HeatData.S_eq_wGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:35:28.906549+00:00
-- url     : https://prove2.me/submissions/a93ff45d-0e8b-4094-b0b2-0d69d2c24e15

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_rdiag_mul_rdiag
public import Theorems.Thm_Auto_HeatData_rdiag_conjTranspose
public import Theorems.Thm_Auto_HeatData_sq_mul_sq
public import Theorems.Thm_Auto_HeatData_R_eq

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
theorem _root_.solution (hh : 0 ≤ Hd.h) {v : Fin 3} (hσ1 : 0 < σ (v + 1)) (hσ2 : 0 < σ (v - 1)) :
    Hd.S p σ v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) + wGram (Hd.Bprev p σ v) (Hd.w p σ (v
      - 1)) := by
  set D := rdiag (Hd.sqw p σ v)
  set A' := rowMat (Hd.A v) (Hd.A (v - 1))
  have hDc : Hd.Dc p σ v * (Hd.Dc p σ v)ᴴ =
      Matrix.fromBlocks (rdiag (Hd.w p σ (v + 1))) 0 0 (rdiag (Hd.w p σ (v - 1))) := by
    rw [Dc, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [rdiag_conjTranspose, rdiag_mul_rdiag, sq_mul_sq Hd p σ hh hσ1,
      sq_mul_sq Hd p σ hh hσ2]
  have hA : ∀ X Y : Matrix ι ι ℂ, A' * Matrix.fromBlocks X 0 0 Y * A'ᴴ =
      Hd.A v * X * (Hd.A v)ᴴ + (Hd.A (v - 1))ᴴ * Y * Hd.A (v - 1) := by
    intro X Y
    simp only [A', rowMat]
    rw [show Matrix.fromCols (Hd.A v) (Hd.A (v - 1))ᴴ * Matrix.fromBlocks X 0 0 Y =
      Matrix.fromCols (Hd.A v * X + (Hd.A (v - 1))ᴴ * 0) (Hd.A v * 0 + (Hd.A (v - 1))ᴴ * Y) from
        Matrix.fromCols_mul_fromBlocks _ _ _ _ _ _]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [show Matrix.fromCols (Hd.A v * X + (Hd.A (v - 1))ᴴ * 0) (Hd.A v * 0 + (Hd.A (v - 1))ᴴ * Y) *
        Matrix.fromRows (Hd.A v)ᴴ (Hd.A (v - 1)) = (Hd.A v * X + (Hd.A (v - 1))ᴴ * 0) * (Hd.A v)ᴴ +
        (Hd.A v * 0 + (Hd.A (v - 1))ᴴ * Y) * Hd.A (v - 1) from
        Matrix.fromCols_mul_fromRows _ _ _ _]
    simp
  have hS : Hd.S p σ v = D * (A' * (Hd.Dc p σ v * (Hd.Dc p σ v)ᴴ) * A'ᴴ) * D := by
    rw [S, R_eq]
    simp only [D, A', Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]
  rw [hS, hDc, hA]
  simp only [wGram, Bnext, Bprev, Matrix.conjTranspose_mul, rdiag_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, D]
end Auto.HeatData
