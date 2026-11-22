-- Prove2me | solution 1 for Auto.HeatData.hasDerivAt_sqw_curve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:36.789826+00:00
-- url     : https://prove2.me/submissions/b9420ac4-74a8-4195-82dd-4f9d6d7491ed

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_w_pos
public import Theorems.Thm_Auto_HeatData_hasDerivAt_w_curve

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
omit [DecidableEq ι] [Fintype ι]
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {θ₀ : ℝ}
    (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀) (hσ : ∀ k, 0 < c θ₀ k) (k : Fin 3) (i : ι) :
    HasDerivAt (fun θ => Hd.sqw p (c θ) k i) (c' k * Hd.dsq p (c θ₀) k i) θ₀ := by
  classical
  have hpos : 0 < Hd.w p (c θ₀) k i := Hd.w_pos p (c θ₀) hh (hσ k) i
  have := (Hd.hasDerivAt_w_curve p hc hσ k i).sqrt hpos.ne'
  exact this.congr_deriv (by unfold HeatData.dsq HeatData.sqw; ring)
end Auto.HeatData
