-- Prove2me | solution 1 for Auto.HeatData.Dfun_mul_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:35:04.725802+00:00
-- url     : https://prove2.me/submissions/32d00a22-c1dc-4baa-8970-335b11dd0806

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_gweight_nonneg__bb3decd414c3

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) (d : ℕ) {s : ℝ} (hs : 0 < s) (p : Fin 3 → ℝ) (v : Fin 3)
    (i : ι) :
    Dfun d s (Hd.u i - p v) * Hd.sqw p (fun _ => 11 / 10 * s) v i ^ 2 = Hd.h * (√s ^ d *
      gaussianD d (21 / 20 * s) (Hd.u i - p v)) := by
  rw [show Hd.sqw p (fun _ => 11 / 10 * s) v i ^ 2 = Hd.w p (fun _ => 11 / 10 * s) v i from
    Real.sq_sqrt (gweight_nonneg' _ hh _ _ _)]
  have hg := (gaussian_pos (by positivity : (0 : ℝ) < 11 / 10 * s) (Hd.u i - p v)).ne'
  simp only [w, gweight, Dfun]
  rw [div_mul_eq_mul_div, div_eq_iff hg]; ring
end Auto.HeatData
