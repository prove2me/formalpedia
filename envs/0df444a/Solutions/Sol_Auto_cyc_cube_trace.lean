-- Prove2me | solution 1 for Auto.cyc_cube_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:11:16.685885+00:00
-- url     : https://prove2.me/submissions/7b41e61f-1eac-4c91-b5e5-d27a8208e7d3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_blk3_mul
public import Theorems.Thm_Auto_blk3_trace

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
namespace Auto
theorem _root_.solution :
    ((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2)) ^ 3).trace = 3 * (D0 * W0 * D1 * W1 * D2 *
      W2).trace + 3 * (D0 * W2ᴴ * D2 * W1ᴴ * D1 * W0ᴴ).trace := by
  rw [← blk3_mul, pow_three, ← blk3_mul, ← blk3_mul, blk3_trace]
  simp only [cycDb, cycMb, Matrix.mul_fin_three, mul_zero, zero_mul, add_zero, zero_add,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_fin_const, Matrix.trace_add]
  have c1 : (D1 * (W1 * (D2 * (W2 * (D0 * W0))))).trace = (D0 * (W0 * (D1 * (W1 * (D2 *
      W2))))).trace := by
    have := Matrix.trace_mul_comm (D1 * W1 * D2 * W2) (D0 * W0)
    simpa only [Matrix.mul_assoc] using this
  have c2 : (D2 * (W2 * (D0 * (W0 * (D1 * W1))))).trace = (D0 * (W0 * (D1 * (W1 * (D2 *
      W2))))).trace := by
    have := Matrix.trace_mul_comm (D2 * W2) (D0 * W0 * D1 * W1)
    simpa only [Matrix.mul_assoc] using this
  have c3 : (D1 * (W0ᴴ * (D0 * (W2ᴴ * (D2 * W1ᴴ))))).trace = (D0 * (W2ᴴ * (D2 * (W1ᴴ * (D1 *
      W0ᴴ))))).trace := by
    have := Matrix.trace_mul_comm (D1 * W0ᴴ) (D0 * W2ᴴ * D2 * W1ᴴ)
    simpa only [Matrix.mul_assoc] using this
  have c4 : (D2 * (W1ᴴ * (D1 * (W0ᴴ * (D0 * W2ᴴ))))).trace = (D0 * (W2ᴴ * (D2 * (W1ᴴ * (D1 *
      W0ᴴ))))).trace := by
    have := Matrix.trace_mul_comm (D2 * W1ᴴ * D1 * W0ᴴ) (D0 * W2ᴴ)
    simpa only [Matrix.mul_assoc] using this
  simp only [Matrix.mul_assoc] at *
  rw [c1, c2, c3, c4]
  ring
end Auto
