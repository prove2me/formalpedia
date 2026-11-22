-- Prove2me | solution 1 for Auto.matCost_le_liminf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:34:41.124034+00:00
-- url     : https://prove2.me/submissions/d285a9dd-e6f1-411a-aff2-753ed775dc72

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_tendsto_sqrt_add_smul

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ) {η : ℕ → ℝ}
    (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    matCost P K ≤ liminf (fun m => matCost (P + (η m : ℂ) • 1) K) atTop := by
  refine iSup_le fun X => ?_
  have hc : Continuous fun A : Matrix n n ℂ => costInt A K X := by
    unfold costInt hsRe
    fun_prop
  have hlim : Tendsto (fun m => ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (P + (η m : ℂ) • 1))
      K X)) atTop (𝓝 (ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt P) K X))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((hc.tendsto _).comp (tendsto_sqrt_add_smul hP hη0 hη) |>.const_mul (3 / 2))
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun m => le_iSup (fun X =>
    ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (P + (η m : ℂ) • 1)) K X)) X)
end Auto
