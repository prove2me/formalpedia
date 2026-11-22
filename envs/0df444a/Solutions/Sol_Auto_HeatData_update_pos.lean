-- Prove2me | solution 1 for Auto.HeatData.update_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:47:01.774209+00:00
-- url     : https://prove2.me/submissions/64320476-4659-48d9-9419-5bf62c94a594

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
theorem _root_.solution {σ : Fin 3 → ℝ} (hσ : ∀ k, 0 < σ k) (k : Fin 3) :
    ∀ j, 0 < (fun τ => Function.update σ k τ) (σ k) j := by
  intro j; simp [hσ]
end Auto.HeatData
