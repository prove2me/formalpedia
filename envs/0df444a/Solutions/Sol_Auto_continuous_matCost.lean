-- Prove2me | solution 1 for Auto.continuous_matCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:39.197476+00:00
-- url     : https://prove2.me/submissions/e8dfa1c6-acdf-4fcf-b230-0633727a84e5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_sub_posSemidef
public import Theorems.Thm_Auto_add_smul_one_sub_posSemidef
public import Theorems.Thm_Auto_matCost_eq_sylv
public import Theorems.Thm_Auto_continuous_re_trace
public import Theorems.Thm_Auto_continuous_sqrt_add

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace Auto
theorem _root_.solution {Γ K : X → Matrix κ κ ℂ} (hΓ : Continuous Γ) (hK : Continuous K)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => (matCost (Γ x + (η : ℂ) • 1) (K x)).toReal := by
  have hsη : 0 < √η := Real.sqrt_pos.2 hη
  have hP : ∀ x, (Γ x + (η : ℂ) • 1 - (η : ℂ) • (1 : Matrix κ κ ℂ)).PosSemidef := fun x =>
    add_smul_one_sub_posSemidef (hpsd x) η
  have : (fun x => (matCost (Γ x + (η : ℂ) • 1) (K x)).toReal) = fun x =>
      max ((3 / 2) * hsRe (K x) (sylvSol (CFC.sqrt (Γ x + (η : ℂ) • 1)) (K x))) 0 := by
    funext x
    rw [matCost_eq_sylv hη (hP x), ENNReal.toReal_ofReal']
  rw [this]
  have hS := continuous_sqrt_add hΓ hpsd hη
  have hX : Continuous fun x => sylvSol (CFC.sqrt (Γ x + (η : ℂ) • 1)) (K x) := by
    rw [← continuousOn_univ]
    exact ContinuousOn.sylvSol hS.continuousOn hK.continuousOn hsη fun x _ =>
      sqrt_sub_posSemidef hη.le (hP x)
  refine (continuous_const.mul ?_).max continuous_const
  exact continuous_re_trace (hK.matrix_conjTranspose.matrix_mul hX)
end Auto
