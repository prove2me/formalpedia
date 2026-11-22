-- Prove2me | solution 1 for Auto.abs_kernIntegrand_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:41:45.362718+00:00
-- url     : https://prove2.me/submissions/c9fcdbe1-237f-4b9c-ac55-c9672c455a6a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_gaussianD_scale
public import Theorems.Thm_Auto_abs_gaussianD_le_const

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → ∀ t, |kernIntegrand m s t| ≤ C / (s * √s) := by
  obtain ⟨M, hM⟩ := abs_gaussianD_le_const m (σ := 63 / 20) (by norm_num)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun s hs t => ?_⟩
  have hss : 0 < √s := Real.sqrt_pos.2 hs
  unfold kernIntegrand
  rw [gaussianD_scale m (by norm_num) hs]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos (by positivity : (0 : ℝ) < √s ^ m),
    abs_of_pos (by positivity : (0 : ℝ) < (√s)⁻¹ ^ (m + 1))]
  have h1 := hM ((√s)⁻¹ * t)
  have e : √s ^ m * ((√s)⁻¹ ^ (m + 1) * |gaussianD m (63 / 20) ((√s)⁻¹ * t)|) / s =
      |gaussianD m (63 / 20) ((√s)⁻¹ * t)| / (s * √s) := by
    rw [inv_pow, pow_succ]
    field_simp
  rw [e]
  gcongr
end Auto
