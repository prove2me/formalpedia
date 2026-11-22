-- Prove2me | solution 1 for Auto.blk3_diag_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:11:06.414022+00:00
-- url     : https://prove2.me/submissions/ee50d729-b931-4aaf-a93d-56dbafceea23

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
theorem _root_.solution (X0 X1 X2 : Matrix ι ι ℂ) :
    blk3 !![X0, 0, 0; 0, X1, 0; 0, 0, X2] = emb1 (ι := ι) 0 * X0 * (emb1 (ι := ι) 0)ᴴ + emb1 (ι :=
        ι) 1 * X1 * (emb1 (ι := ι) 1)ᴴ +
        emb1 (ι := ι) 2 * X2 * (emb1 (ι := ι) 2)ᴴ := by
  ext ⟨w, a⟩ ⟨w', b⟩
  simp only [Matrix.add_apply, Matrix.mul_apply, emb1, Matrix.of_apply,
    Matrix.conjTranspose_apply, blk3, Matrix.comp_apply]
  fin_cases w <;> fin_cases w' <;> simp [Prod.ext_iff]
end Auto
