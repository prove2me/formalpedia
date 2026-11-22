-- Prove2me | solution 1 for Auto.HeatData.continuous_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:25:18.449894+00:00
-- url     : https://prove2.me/submissions/6630fdc5-407c-4785-8a23-70ccd0566bbf

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuous_gaussianD_comp

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
open Auto.HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k) (k : Fin 3)
    (i : ι) :
    Continuous fun x => Hd.w (p x) (σ x) k i := by
  have := continuous_gaussianD_comp 0 ((continuous_apply k).comp hσ) (continuous_const.sub
      ((continuous_apply k).comp hp)) (fun x => hpos x k) (t := fun x =>
      Hd.u i - p x k)
  simp only [gaussianD_zero] at this
  exact continuous_const.mul this
end Auto.HeatData
