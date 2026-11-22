-- Prove2me | solution 1 for Auto.hasDerivAt_gweightD1_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:52.973769+00:00
-- url     : https://prove2.me/submissions/1170dcb0-f8f5-4570-9b23-6eb8b62ac424

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (u : ι → ℝ) (h σ p : ℝ) (i : ι) :
    HasDerivAt (fun q => -(h * gaussianD 1 σ (u i - q))) (h * gaussianD 2 σ (u i - p)) p := by
  have := (((hasDerivAt_gaussianD 1 σ (u i - p)).comp p ((hasDerivAt_id p).const_sub (u
      i))).const_mul h).neg
  convert this using 1 <;> first | rfl | (simp [gweight, gaussianD_zero, Function.comp] <;> ring)
end Auto
