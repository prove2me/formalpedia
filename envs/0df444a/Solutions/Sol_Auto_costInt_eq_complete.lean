-- Prove2me | solution 1 for Auto.costInt_eq_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:21:27.280799+00:00
-- url     : https://prove2.me/submissions/6e6238cd-ce13-4c66-b8f8-e777f883df6d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_sub_right
public import Theorems.Thm_Auto_hsRe_mul_left_adj
public import Theorems.Thm_Auto_hsRe_mul_right_adj

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
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]
namespace Auto
theorem _root_.solution {A K X₀ : Matrix n n ℂ} (hA : A.IsHermitian)
    (hK : A * X₀ + X₀ * A = K) (X : Matrix n n ℂ) :
    costInt A K X = hsRe K X₀ - hsRe (X - X₀) (A * (X - X₀) + (X - X₀) * A) := by
  classical
  have hsym : ∀ U W : Matrix n n ℂ, hsRe U (A * W + W * A) = hsRe (A * U + U * A) W := by
    intro U W
    rw [hsRe_add_right, hsRe_mul_left_adj hA, hsRe_mul_right_adj hA, hsRe_comm (A * U) W,
      hsRe_comm (U * A) W, hsRe_comm (A * U + U * A) W, hsRe_add_right]
  have hL : A * (X - X₀) + (X - X₀) * A = (A * X + X * A) - K := by
    rw [← hK]; noncomm_ring
  rw [hL, hsRe_sub_right, hsRe_comm (X - X₀), hsRe_comm (X - X₀), hsRe_sub_right,
    hsRe_sub_right, hsRe_comm (A * X + X * A) X, hsRe_comm (A * X + X * A) X₀, hsym X₀ X, hK,
    hsRe_comm K X₀, ← hK, hsym X₀ X₀, hK, costInt, hsRe_add_right]
  ring
end Auto
