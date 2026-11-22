-- Prove2me | solution 1 for Auto.eigCoord_sylvSol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:07:52.545997+00:00
-- url     : https://prove2.me/submissions/17506c4d-0e37-4c73-beea-fcc21226f3ba

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_eq_conj_diagonal
public import Theorems.Thm_Auto_sqrt_eigenvalues_pos
public import Theorems.Thm_Auto_sqrt_sub_posSemidef
public import Theorems.Thm_Auto_exists_lower_bound_of_posDef

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {Y : Matrix n n ℂ} (hY : Y.PosDef) (K : Matrix n n ℂ) (i j : n) :
    eigCoord hY.1 (sylvSol (CFC.sqrt Y) K) i j = eigCoord hY.1 K i j / ((√(hY.1.eigenvalues i) +
      √(hY.1.eigenvalues j) : ℝ) : ℂ) := by
  obtain ⟨U, hUdef⟩ : ∃ U, U = hY.1.eigenvectorUnitary := ⟨_, rfl⟩
  set a : n → ℝ := fun i => √(hY.1.eigenvalues i)
  have hE : ∀ Z, eigCoord hY.1 Z = star (U : Matrix n n ℂ) * Z * (U : Matrix n n ℂ) := by
    intro Z; rw [hUdef]; rfl
  have hU'U : star (U : Matrix n n ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hl : ∀ Z : Matrix n n ℂ, star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hU'U, Matrix.one_mul]
  obtain ⟨μ, hμ, hμY⟩ := exists_lower_bound_of_posDef hY
  have hX := (sylvSol_spec (Real.sqrt_pos.2 hμ) (sqrt_sub_posSemidef hμ.le hμY) K).1
  set X := sylvSol (CFC.sqrt Y) K
  have hsq : CFC.sqrt Y = (U : Matrix n n ℂ) * diagonal (fun i => (a i : ℂ)) *
      star (U : Matrix n n ℂ) := by rw [hUdef]; exact sqrt_eq_conj_diagonal hY.posSemidef
  have key : diagonal (fun i => (a i : ℂ)) * eigCoord hY.1 X + eigCoord hY.1 X *
      diagonal (fun i => (a i : ℂ)) = eigCoord hY.1 K := by
    rw [← hX]
    simp only [hE, hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hl, hU'U,
      Matrix.mul_one]
  have := congrFun (congrFun key i) j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have hc : ((a i + a j : ℝ) : ℂ) ≠ 0 := by
    have := add_pos (sqrt_eigenvalues_pos hY i) (sqrt_eigenvalues_pos hY j)
    exact_mod_cast this.ne'
  rw [← this, eq_div_iff hc]
  push_cast
  ring
end Auto
