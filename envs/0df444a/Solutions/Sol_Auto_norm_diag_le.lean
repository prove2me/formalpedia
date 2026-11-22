-- Prove2me | solution 1 for Auto.norm_diag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:47.004786+00:00
-- url     : https://prove2.me/submissions/ea2c3912-9a43-44a5-a1d3-08c117d903e7

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_norm_entry_sum_sq_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace Auto
theorem _root_.solution {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (i : κ) :
    ‖D i i‖ ≤ d := by
  have h := norm_entry_sum_sq_le hD hDd i
  have : ‖D i i‖ ^ 2 ≤ d ^ 2 := (Finset.single_le_sum (f := fun j => ‖D i j‖ ^ 2) (fun j _ =>
      sq_nonneg _) (Finset.mem_univ i)).trans h
  exact abs_le_of_sq_le_sq' this hd |>.2 |> fun h => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (sq_le_sq₀ (norm_nonneg _) hd).1 this
end Auto
