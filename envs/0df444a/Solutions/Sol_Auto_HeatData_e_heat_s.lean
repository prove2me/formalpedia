-- Prove2me | solution 1 for Auto.HeatData.e_heat_s
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:25:02.397422+00:00
-- url     : https://prove2.me/submissions/3607379e-6a0d-410c-8f20-2f92e42949b5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_hasDerivAt_e_curve
public import Theorems.Thm_Auto_HeatData_tr32_Mnext_eq
public import Theorems.Thm_Auto_HeatData_tr32_Mprev_eq
public import Theorems.Thm_Auto_HeatData_tr32_wGram_half

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
theorem _root_.solution (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα : ∀ k, 0 < α k)
    {s : ℝ} (hs : 0 < s) (v : Fin 3) :
    HasDerivAt (fun t => Hd.e p (fun k => α k * t) η v) ((α v * tr32 η (Hd.T p (fun k => α k *
      s) v) (wGram (Hd.Brow p (fun k => α k * s) v) (Hd.ddw p (fun k => α k * s) v)) + α (v + 1) *
      tr32 η (Hd.S p (fun k => α k * s) v) (wGram (Hd.Bnext p (fun k => α k * s) v) (Hd.ddw p (fun
      k => α k * s) (v + 1))) + α (v - 1) * tr32 η (Hd.S p (fun k => α k * s) v) (wGram (Hd.Bprev
      p (fun k => α k * s) v) (Hd.ddw p (fun k => α k * s) (v - 1)))) / 2) s := by
  have hσ : ∀ k, 0 < (fun k => α k * s) k := fun k => mul_pos (hα k) hs
  have h1 := Hd.hasDerivAt_e_curve p hh hη (c := fun t k => α k * t) (c' := α) (θ₀ := s) (fun k =>
      by simpa using (hasDerivAt_id s).const_mul (α k)) hσ v
  refine h1.congr_deriv ?_
  rw [Hd.tr32_Mnext_eq p _ hh hη hσ, Hd.tr32_Mprev_eq p _ hh hη hσ, Mrow, tr32_wGram_half,
    tr32_wGram_half, tr32_wGram_half]
  ring
end Auto.HeatData
