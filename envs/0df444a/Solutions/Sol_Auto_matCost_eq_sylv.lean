-- Prove2me | solution 1 for Auto.matCost_eq_sylv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:23:08.455236+00:00
-- url     : https://prove2.me/submissions/f63df02c-3fad-4064-ae82-ba4cac7c085e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_sub_posSemidef
public import Theorems.Thm_Auto_costInt_eq_complete

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
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (hP : (P - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ENNReal.ofReal ((3 / 2) * hsRe K (sylvSol (CFC.sqrt P) K)) := by
  have hs := sqrt_sub_posSemidef hη.le hP
  have hsη : 0 < √η := Real.sqrt_pos.2 hη
  set A := CFC.sqrt P
  have hAh : A.IsHermitian := (CFC.sqrt_nonneg P).posSemidef.isHermitian
  have hX := (sylvSol_spec hsη hs K).1
  set X₀ := sylvSol A K
  have hq : ∀ D : Matrix n n ℂ, 0 ≤ hsRe D (A * D + D * A) := by
    intro D
    have := sylvester_lower hs hs D
    have : 0 ≤ (√η + √η) * hsSq D := by have := hsSq_nonneg D; positivity
    linarith
  refine le_antisymm (iSup_le fun X => ?_) ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [costInt_eq_complete hAh hX X]
    have := hq (X - X₀)
    nlinarith
  · refine le_trans (le_of_eq ?_) (le_iSup _ X₀)
    rw [costInt_eq_complete hAh hX X₀, sub_self]
    simp [hsRe]
end Auto
