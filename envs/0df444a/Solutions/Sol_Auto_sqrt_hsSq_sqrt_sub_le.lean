-- Prove2me | solution 1 for Auto.sqrt_hsSq_sqrt_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:05.845651+00:00
-- url     : https://prove2.me/submissions/0fc8980f-cb97-4b82-9611-db252085631c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_sub_posSemidef

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
theorem _root_.solution {Y₁ Y₂ : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (h₁ : (Y₁ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (h₂ : (Y₂ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    √(hsSq (CFC.sqrt Y₁ - CFC.sqrt Y₂)) ≤ √(hsSq (Y₁ - Y₂)) / (√η + √η) := by
  have hY₁ : 0 ≤ Y₁ := by
    have := h₁.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη.le : (0 : ℂ) ≤ η))
    simpa using this.nonneg
  have hY₂ : 0 ≤ Y₂ := by
    have := h₂.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη.le : (0 : ℂ) ≤ η))
    simpa using this.nonneg
  have e : CFC.sqrt Y₁ * (CFC.sqrt Y₁ - CFC.sqrt Y₂) + (CFC.sqrt Y₁ - CFC.sqrt Y₂) * CFC.sqrt Y₂ =
      Y₁ - Y₂ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, CFC.sqrt_mul_sqrt_self Y₁ hY₁,
      CFC.sqrt_mul_sqrt_self Y₂ hY₂]
    abel
  have := sqrt_hsSq_le_sylvester (by positivity : 0 < √η + √η) (sqrt_sub_posSemidef hη.le h₁)
      (sqrt_sub_posSemidef hη.le h₂) (CFC.sqrt Y₁ - CFC.sqrt Y₂)
  rwa [e] at this
end Auto
