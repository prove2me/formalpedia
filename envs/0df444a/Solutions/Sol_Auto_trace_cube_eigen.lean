-- Prove2me | solution 1 for Auto.trace_cube_eigen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:43.305805+00:00
-- url     : https://prove2.me/submissions/298b9537-7d37-4db9-908f-c05b329f1ce6

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_trace_conj_unitary

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
theorem _root_.solution {κ : Type*} [Fintype κ] [DecidableEq κ] (U : Matrix.unitaryGroup κ ℂ)
    (m : κ → ℝ) (Dt : Matrix κ κ ℂ) :
    (((U : Matrix κ κ ℂ) * Dt * star (U : Matrix κ κ ℂ) * ((U : Matrix κ κ ℂ) * diagonal (fun i
      => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) ^ 3).trace = ∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ)
      : ℂ) * Dt i j * Dt j k * Dt k i := by
  have hU'U : star (U : Matrix κ κ ℂ) * U = 1 := Unitary.coe_star_mul_self U
  set A := Dt * diagonal (fun i => (m i : ℂ))
  have hA : (U : Matrix κ κ ℂ) * Dt * star (U : Matrix κ κ ℂ) * ((U : Matrix κ κ ℂ) * diagonal (fun
      i => (m i : ℂ)) * star (U : Matrix κ κ ℂ)) = (U : Matrix κ κ ℂ) * A * star (U : Matrix κ κ ℂ)
      := by
    simp only [A, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul]
  have hcube : ((U : Matrix κ κ ℂ) * A * star (U : Matrix κ κ ℂ)) ^ 3 = (U : Matrix κ κ ℂ) * (A ^ 3)
      * star (U : Matrix κ κ ℂ) := by
    simp only [pow_three, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul,
      ← Matrix.mul_assoc (star (U : Matrix κ κ ℂ)) (U : Matrix κ κ ℂ), hU'U, Matrix.one_mul]
  have hAe : ∀ x y, A x y = Dt x y * (m y : ℂ) := fun x y => by
    simp only [A, Matrix.mul_diagonal]
  rw [hA, hcube, trace_conj_unitary, pow_three]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum, hAe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring
end Auto
