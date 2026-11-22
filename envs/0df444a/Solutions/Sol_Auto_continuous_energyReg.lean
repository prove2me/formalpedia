-- Prove2me | solution 1 for Auto.continuous_energyReg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:29.298851+00:00
-- url     : https://prove2.me/submissions/c7713c44-0fb1-45c2-be8a-45dd28c62ed4

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_energyReg_eq_trace
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
theorem _root_.solution {Γ : X → Matrix κ κ ℂ} (hΓ : Continuous Γ)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => energyReg η (Γ x) := by
  have : (fun x => energyReg η (Γ x)) = fun x =>
      (((Γ x + (η : ℂ) • 1) * CFC.sqrt (Γ x + (η : ℂ) • 1)).trace).re -
        η ^ (3 / 2 : ℝ) * Fintype.card κ := by
    funext x; exact energyReg_eq_trace (hpsd x) hη.le
  rw [this]
  exact (continuous_re_trace ((hΓ.add continuous_const).matrix_mul (continuous_sqrt_add hΓ hpsd
      hη))).sub continuous_const
end Auto
