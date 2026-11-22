-- Prove2me | solution 1 for Auto.matCostBil_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:15:14.102735+00:00
-- url     : https://prove2.me/submissions/70ccd0fd-208e-459c-a94a-2a94960058ae

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_toReal_eq
public import Theorems.Thm_Auto_matCostBil_eq

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCostBil P K K = (matCost P K).toReal := by
  rw [matCostBil_eq hP, (matCost_toReal_eq hP K).2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast
end Auto
