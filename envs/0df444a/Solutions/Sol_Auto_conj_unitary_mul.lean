-- Prove2me | solution 1 for Auto.conj_unitary_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:45.507418+00:00
-- url     : https://prove2.me/submissions/86643c71-8939-45e5-aae6-72ff77a833f0

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
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
namespace Auto
theorem _root_.solution {κ : Type*} [Fintype κ] [DecidableEq κ] (U : Matrix.unitaryGroup κ ℂ)
    (X Y : Matrix κ κ ℂ) :
    star (U : Matrix κ κ ℂ) * (X * Y) * (U : Matrix κ κ ℂ) = (star (U : Matrix κ κ ℂ) * X * U) *
      (star (U : Matrix κ κ ℂ) * Y * U) := by
  have hUU2 : ∀ Z : Matrix κ κ ℂ, (U : Matrix κ κ ℂ) * (star (U : Matrix κ κ ℂ) * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, show (U : Matrix κ κ ℂ) * star (U : Matrix κ κ ℂ) = 1 from
      Unitary.coe_mul_star_self U, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hUU2]
end Auto
