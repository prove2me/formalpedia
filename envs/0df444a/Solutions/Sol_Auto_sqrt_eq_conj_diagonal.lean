-- Prove2me | solution 1 for Auto.sqrt_eq_conj_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:40:35.019984+00:00
-- url     : https://prove2.me/submissions/99c5e6cb-8bd8-4049-b489-ea2c5b670f71

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    CFC.sqrt P = (hP.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((√(hP.1.eigenvalues i) : ℝ) : ℂ)) * star (hP.1.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [CFC.sqrt_eq_real_sqrt P hP.nonneg, cfcₙ_eq_cfc, hP.1.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  rfl
end Auto
