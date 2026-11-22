-- Prove2me | solution 1 for Auto.matCost_fromBlocks_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:13.74754+00:00
-- url     : https://prove2.me/submissions/b8a79ef3-290d-45d3-a746-e02069a9028e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_fromBlocks_diag
public import Theorems.Thm_Auto_costInt_fromBlocks_diag

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
namespace Auto
theorem _root_.solution {P1 P2 : Matrix ι ι ℂ} (hP1 : P1.PosSemidef) (hP2 : P2.PosSemidef)
    (K11 K12 K21 K22 : Matrix ι ι ℂ) :
    matCost P1 K11 + matCost P2 K22 ≤ matCost (Matrix.fromBlocks P1 0 0 P2) (Matrix.fromBlocks
      K11 K12 K21 K22) := by
  rw [matCost, matCost]
  refine ENNReal.iSup_add_iSup_le fun X1 X2 => ?_
  rw [matCost, sqrt_fromBlocks_diag hP1 hP2]
  set c1 := costInt (CFC.sqrt P1) K11 X1
  set c2 := costInt (CFC.sqrt P2) K22 X2
  have h0 : ∀ A K : Matrix ι ι ℂ, costInt A K 0 = 0 := fun A K => by simp [costInt, hsRe]
  let Y1 : Matrix ι ι ℂ := if 0 ≤ c1 then X1 else 0
  let Y2 : Matrix ι ι ℂ := if 0 ≤ c2 then X2 else 0
  have e1 : costInt (CFC.sqrt P1) K11 Y1 = max c1 0 := by
    by_cases h : 0 ≤ c1
    · simp only [Y1, h, ite_true, max_eq_left h]; rfl
    · simp [Y1, h, h0, max_eq_right (le_of_not_ge h)]
  have e2 : costInt (CFC.sqrt P2) K22 Y2 = max c2 0 := by
    by_cases h : 0 ≤ c2
    · simp only [Y2, h, ite_true, max_eq_left h]; rfl
    · simp [Y2, h, h0, max_eq_right (le_of_not_ge h)]
  refine le_trans ?_ (le_iSup _ (Matrix.fromBlocks Y1 0 0 Y2))
  rw [costInt_fromBlocks_diag, e1, e2, mul_add,
    ENNReal.ofReal_add (by positivity) (by positivity)]
  gcongr
  · exact le_max_left _ _
  · exact le_max_left _ _
end Auto
