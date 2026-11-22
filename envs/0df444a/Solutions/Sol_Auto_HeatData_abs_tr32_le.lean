-- Prove2me | solution 1 for Auto.HeatData.abs_tr32_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:26.476272+00:00
-- url     : https://prove2.me/submissions/4e6b37da-9c67-4dc1-a2d4-f2b4636072b9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsSq_sqrt_eq

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace Auto
namespace HeatData
theorem _root_.solution {Γ : Matrix κ κ ℂ} (hΓ : Γ.PosSemidef) {η : ℝ} (hη : 0 ≤ η)
    (K : Matrix κ κ ℂ) :
    |HeatData.tr32 η Γ K| ≤ (3 / 2) * √(Γ.trace.re + Fintype.card κ * η) * √(hsSq K) := by
  have hP : 0 ≤ Γ + (η : ℂ) • (1 : Matrix κ κ ℂ) := (hΓ.add (Matrix.PosSemidef.one.smul (by
      exact_mod_cast hη))).nonneg
  have e1 : ((CFC.sqrt (Γ + (η : ℂ) • 1) * K).trace).re = hsRe (CFC.sqrt (Γ + (η : ℂ) • 1)) K := by
    rw [hsRe, (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq]
  have e2 : (Γ + (η : ℂ) • (1 : Matrix κ κ ℂ)).trace.re = Γ.trace.re + Fintype.card κ * η := by
    simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]; ring
  rw [HeatData.tr32, e1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), mul_assoc]
  gcongr
  refine (abs_hsRe_le _ _).trans ?_
  rw [hsSq_sqrt_eq hP, e2]
end HeatData
end Auto
