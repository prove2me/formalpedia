-- Prove2me | solution 1 for Auto.HeatData.Z_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:28:05.531848+00:00
-- url     : https://prove2.me/submissions/03fd896b-722b-494c-bce8-46e2dbb11540

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_matCostBil_le
public import Theorems.Thm_Auto_posDef_add_smul_one

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
theorem _root_.solution (p σ : Fin 3 → ℝ) {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    Hd.Z p σ η v ≤ (Hd.Ynext p σ η v + Hd.Yprev p σ η v) / 2 := by
  have hPD := posDef_add_smul_one (Matrix.posSemidef_self_mul_conjTranspose (Hd.R p σ v)) hη
  have h := (le_abs_self _).trans (abs_matCostBil_le hPD (Hd.Pnext p σ v) (Hd.Pprev p σ v))
  have h1 : 0 ≤ Hd.Ynext p σ η v := ENNReal.toReal_nonneg
  have h2 : 0 ≤ Hd.Yprev p σ η v := ENNReal.toReal_nonneg
  have hs1 := Real.sq_sqrt h1
  have hs2 := Real.sq_sqrt h2
  change Hd.Z p σ η v ≤ √(Hd.Ynext p σ η v) * √(Hd.Yprev p σ η v) at h
  nlinarith [sq_nonneg (√(Hd.Ynext p σ η v) - √(Hd.Yprev p σ η v))]
end Auto.HeatData
