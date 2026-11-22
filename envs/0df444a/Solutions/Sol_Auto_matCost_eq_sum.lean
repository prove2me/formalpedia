-- Prove2me | solution 1 for Auto.matCost_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:52.841946+00:00
-- url     : https://prove2.me/submissions/f3c47a6f-012b-4bf2-b536-5468e948a349

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_eq_sum_of_conj

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]
namespace Auto
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ∑ i, ∑ j, ENNReal.ofReal ((3 / 2) * ‖(star (hP.1.eigenvectorUnitary : Matrix n
      n ℂ) * K * (hP.1.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2) / ENNReal.ofReal
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by
  refine matCost_eq_sum_of_conj _ _ hP.eigenvalues_nonneg ?_ K
  have := hP.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  exact this
end Auto
