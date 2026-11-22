-- Prove2me | solution 1 for Auto.sqrt_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:22:45.770006+00:00
-- url     : https://prove2.me/submissions/888397f9-ed1c-48b9-9685-9ccab1afb3a2

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
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {Y : Matrix n n ℂ} {η : ℝ} (hη : 0 ≤ η)
    (hY : (Y - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    (CFC.sqrt Y - ((√η : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have halg : ∀ r : ℝ≥0, algebraMap ℝ≥0 (Matrix n n ℂ) r = ((r : ℝ) : ℂ) • 1 := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  set r : ℝ≥0 := ⟨η, hη⟩ with hr
  have h1 : algebraMap ℝ≥0 (Matrix n n ℂ) r ≤ Y := by
    rw [halg, Matrix.le_iff]; exact hY
  have h2 := CFC.sqrt_le_sqrt _ _ h1
  rw [CFC.sqrt_algebraMap, halg] at h2
  rw [Matrix.le_iff] at h2
  convert h2 using 3 <;> first | rfl | (rw [Real.coe_sqrt]; rfl)
end Auto
