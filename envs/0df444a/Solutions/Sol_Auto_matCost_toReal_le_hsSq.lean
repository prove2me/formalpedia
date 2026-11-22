-- Prove2me | solution 1 for Auto.matCost_toReal_le_hsSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:24:48.122299+00:00
-- url     : https://prove2.me/submissions/fb31eede-9c28-47c5-a8bc-b71ad9456a89

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_sub_posSemidef
public import Theorems.Thm_Auto_matCost_eq_sylv

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
theorem _root_.solution {P : Matrix κ κ ℂ} {η : ℝ} (hη : 0 < η)
    (hP : (P - (η : ℂ) • (1 : Matrix κ κ ℂ)).PosSemidef) (K : Matrix κ κ ℂ) :
    (matCost P K).toReal ≤ (3 / 4) * hsSq K / √η := by
  have hsη : 0 < √η := Real.sqrt_pos.2 hη
  rw [matCost_eq_sylv hη hP, ENNReal.toReal_ofReal']
  have hX := sqrt_hsSq_sylvSol_le hsη (sqrt_sub_posSemidef hη.le hP) K
  have h1 := (le_abs_self _).trans (abs_hsRe_le K (sylvSol (CFC.sqrt P) K))
  have hK := Real.sq_sqrt (hsSq_nonneg K)
  have hK0 := Real.sqrt_nonneg (hsSq K)
  refine max_le ?_ (by have := hsSq_nonneg K; positivity)
  have : √(hsSq K) * √(hsSq (sylvSol (CFC.sqrt P) K)) ≤ √(hsSq K) * (√(hsSq K) / (√η + √η)) :=
    mul_le_mul_of_nonneg_left hX hK0
  have e3 : √(hsSq K) * (√(hsSq K) / (√η + √η)) = hsSq K / (2 * √η) := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (hsSq_nonneg K)]; ring
  rw [e3] at this
  calc 3 / 2 * hsRe K (sylvSol (CFC.sqrt P) K) ≤ 3 / 2 * (hsSq K / (2 * √η)) := by linarith
    _ = _ := by field_simp; ring
end Auto
