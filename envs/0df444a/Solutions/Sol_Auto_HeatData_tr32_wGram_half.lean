-- Prove2me | solution 1 for Auto.HeatData.tr32_wGram_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:40.735621+00:00
-- url     : https://prove2.me/submissions/81d48439-3499-49a8-be7d-de348ee531e9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_wGram_smul
public import Theorems.Thm_Auto_HeatData_tr32_smul

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
theorem _root_.solution (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ : Matrix κ κ ℂ)
    (B : Matrix ι κ ℂ) (f : ι → ℝ) :
    tr32 η Γ (wGram B (fun i => f i / 2)) = tr32 η Γ (wGram B f) / 2 := by
  rw [show (fun i => f i / 2) = (1 / 2 : ℝ) • f by funext i; simp; ring, wGram_smul,
    tr32_smul]; ring
end Auto.HeatData
