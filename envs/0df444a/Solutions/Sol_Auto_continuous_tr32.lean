-- Prove2me | solution 1 for Auto.continuous_tr32
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:26:08.255089+00:00
-- url     : https://prove2.me/submissions/8ccfd68a-7341-462a-a84c-162eff8017dc

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
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
    Continuous fun x => HeatData.tr32 η (Γ x) (K x) :=
  continuous_const.mul (continuous_re_trace ((continuous_sqrt_add hΓ hpsd hη).matrix_mul hK))
end Auto
