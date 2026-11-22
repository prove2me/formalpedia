-- Prove2me | solution 1 for Auto.phaseBlocks_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:50.419805+00:00
-- url     : https://prove2.me/submissions/6ef1117a-0278-4118-a8db-64b56bf16b6b

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
theorem _root_.solution {c : ℂ} (hc : ‖c‖ = 1) (left : Bool) :
    (if left then Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1 else Matrix.fromBlocks 1 0 0
      (c • (1 : Matrix ι ι ℂ))) * (if left then Matrix.fromBlocks (c • (1 : Matrix ι ι ℂ)) 0 0 1
      else Matrix.fromBlocks 1 0 0 (c • (1 : Matrix ι ι ℂ)))ᴴ = 1 := by
  have hcc : c * star c = 1 := by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  have hcc2 : (starRingEnd ℂ) c * c = 1 := by rw [mul_comm]; simpa using hcc
  cases left <;>
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, smul_smul, hcc2,
        Matrix.fromBlocks_one, Matrix.conjTranspose_smul]
end Auto
