-- Prove2me | solution 1 for Auto.sqrt_fromBlocks_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:54.623817+00:00
-- url     : https://prove2.me/submissions/ab918b7c-bf92-4c85-948d-43861cfb476e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_fromBlocks_diag_posSemidef

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] {P Q : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) :
    open scoped Classical in CFC.sqrt (Matrix.fromBlocks P 0 0 Q) = Matrix.fromBlocks (CFC.sqrt
      P) 0 0 (CFC.sqrt Q) := by
  classical
  have hsP : (CFC.sqrt P).PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hsQ : (CFC.sqrt Q).PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hnn : 0 ≤ Matrix.fromBlocks (CFC.sqrt P) 0 0 (CFC.sqrt Q) := (fromBlocks_diag_posSemidef hsP
      hsQ).nonneg
  refine CFC.sqrt_unique ?_ hnn
  rw [Matrix.fromBlocks_multiply]
  simp [CFC.sqrt_mul_sqrt_self P hP.nonneg, CFC.sqrt_mul_sqrt_self Q hQ.nonneg]
end Auto
