-- Prove2me | solution 1 for Auto.quadForm_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:06:13.393484+00:00
-- url     : https://prove2.me/submissions/3f95e9c7-07f5-44a4-8b52-361d16f9e221

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_sub_right

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]
namespace Auto
theorem _root_.solution {A B : Matrix n n ℂ} (hAB : (B - A).PosSemidef) (X : Matrix n n ℂ) :
    hsRe X (A * X) + hsRe X (X * A) ≤ hsRe X (B * X) + hsRe X (X * B) := by
  classical
  have h0 : ((B - A) - ((0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by simpa using hAB
  have := sylvester_lower h0 h0 X
  simp only [add_zero, zero_mul] at this
  rw [hsRe_add_right, Matrix.sub_mul, Matrix.mul_sub, hsRe_sub_right, hsRe_sub_right] at this
  linarith
end Auto
