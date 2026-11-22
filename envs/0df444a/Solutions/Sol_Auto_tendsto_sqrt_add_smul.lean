-- Prove2me | solution 1 for Auto.tendsto_sqrt_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:32:58.005563+00:00
-- url     : https://prove2.me/submissions/74cd1d07-066c-4ca6-849b-5738f690c5ce

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_eq_conj_diagonal
public import Theorems.Thm_Auto_sqrt_add_smul_eq

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
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℕ → ℝ}
    (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => CFC.sqrt (P + (η m : ℂ) • 1)) atTop (𝓝 (CFC.sqrt P)) := by
  rw [sqrt_eq_conj_diagonal hP]
  simp_rw [sqrt_add_smul_eq hP (hη0 _)]
  refine ((tendsto_const_nhds.mul ?_).mul tendsto_const_nhds)
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simp only [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
    have := ((tendsto_const_nhds (x := hP.1.eigenvalues i)).add hη).sqrt
    simpa using this
  · exact tendsto_const_nhds
end Auto
