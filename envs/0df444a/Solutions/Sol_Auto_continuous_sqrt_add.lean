-- Prove2me | solution 1 for Auto.continuous_sqrt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:23:06.847451+00:00
-- url     : https://prove2.me/submissions/45d99a22-5993-4ba8-a976-5baaae6a0a71

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_add_smul_one_sub_posSemidef
public import Theorems.Thm_Auto_ContinuousOn_matSqrt

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
theorem _root_.solution {Γ : X → Matrix κ κ ℂ} (hΓ : Continuous Γ)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => CFC.sqrt (Γ x + (η : ℂ) • 1) := by
  rw [← continuousOn_univ]
  exact ContinuousOn.matSqrt (hΓ.add continuous_const).continuousOn hη fun x _ =>
    add_smul_one_sub_posSemidef (hpsd x) η
end Auto
