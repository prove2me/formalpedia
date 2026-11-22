-- Prove2me | solution 1 for Auto.matCost_tendsto_regularization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:36:22.809396+00:00
-- url     : https://prove2.me/submissions/d9e5d2fc-b114-4751-9bd3-c6337492ff86

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_anti
public import Theorems.Thm_Auto_matCost_le_liminf

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
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ)
    {η : ℕ → ℝ} (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => matCost (P + (η m : ℂ) • 1) K) atTop (𝓝 (matCost P K)) := by
  apply tendsto_of_le_liminf_of_limsup_le (matCost_le_liminf hP K hη0 hη)
  apply limsup_le_of_le isCobounded_le_of_bot
  filter_upwards [] with m
  have hi : ((η m : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hη0 m)
  exact matCost_anti (hP.add hi) (le_add_of_nonneg_right hi.nonneg) K
end Auto
