-- Prove2me | solution 1 for Auto.HeatData.norm_A_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:48:16.579446+00:00
-- url     : https://prove2.me/submissions/fdd3ed43-ca45-4caf-a396-5e485b3e7f71

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
variable (Hd : HeatData ι)
omit [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (k : Fin 3) (i j : ι) : ‖Hd.A k i j‖ ≤ Hd.MA := by
  unfold MA
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ i, ∑ j, ‖Hd.A k i j‖) (fun _ _ => by
      positivity) (Finset.mem_univ k))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖Hd.A k i j‖) (fun _ _ => by
      positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖Hd.A k i j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
end Auto.HeatData
