-- Prove2me | solution 1 for Auto.HeatData.hasDerivAt_w_curve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:46:54.56995+00:00
-- url     : https://prove2.me/submissions/1d23d0d5-437e-481f-bbb7-484e4915d1f7

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_hasDerivAt_gweight___b6d5e5597986
public import Theorems.Thm_Auto_HeatData_ddw_def

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
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {θ₀ : ℝ}
    (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀) (hσ : ∀ k, 0 < c θ₀ k) (k : Fin 3) (i : ι) :
    HasDerivAt (fun θ => Hd.w p (c θ) k i) (c' k * (Hd.ddw p (c θ₀) k i / 2)) θ₀ := by
  have := (hasDerivAt_gweight_σ Hd.u Hd.h (p k) (hσ k) i).comp θ₀ (hc k)
  exact this.congr_deriv (by simp only [ddw_def]; ring)
end Auto.HeatData
