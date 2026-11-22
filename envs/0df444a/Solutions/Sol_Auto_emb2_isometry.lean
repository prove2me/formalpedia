-- Prove2me | solution 1 for Auto.emb2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:10:39.212808+00:00
-- url     : https://prove2.me/submissions/d5d15078-79b9-42de-af4d-1e00f370777e

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
namespace Auto
theorem _root_.solution {p r : Fin 3} (hpr : p ≠ r) : (emb2 (ι := ι) p r)ᴴ * emb2 (ι := ι) p r = 1 := by
  ext s t
  rcases s with a | a <;> rcases t with b | b <;>
    simp only [emb2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.one_apply, Prod.mk.injEq,
      apply_ite star, star_one, star_zero, ite_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, ite_false] <;>
    simp [hpr, hpr.symm, eq_comm]
end Auto
