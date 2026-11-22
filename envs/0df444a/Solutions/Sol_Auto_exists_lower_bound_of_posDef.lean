-- Prove2me | solution 1 for Auto.exists_lower_bound_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:06:33.921804+00:00
-- url     : https://prove2.me/submissions/69866cf5-ef23-4c1f-88e9-cb12d24186a4

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_add_smul_one_eq_conj

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Fintype n]
namespace Auto
theorem _root_.solution [Finite n] {Y : Matrix n n ℂ} (hY : Y.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ (Y - (μ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  let := Fintype.ofFinite n
  by_cases hn : IsEmpty n
  · exact ⟨1, one_pos, by
      rw [show Y - ((1 : ℝ) : ℂ) • (1 : Matrix n n ℂ) = 0 from Subsingleton.elim _ _]
      exact Matrix.PosSemidef.zero⟩
  rw [not_isEmpty_iff] at hn
  set μ := Finset.univ.inf' Finset.univ_nonempty (fun i => hY.1.eigenvalues i)
  have hμ : 0 < μ := (Finset.lt_inf'_iff _).2 fun i _ => hY.eigenvalues_pos i
  refine ⟨μ, hμ, ?_⟩
  have e := add_smul_one_eq_conj hY.1 (-μ)
  rw [show Y - (μ : ℂ) • 1 = Y + ((-μ : ℝ) : ℂ) • 1 by push_cast; rw [neg_smul, sub_eq_add_neg]]
  rw [e]
  have hD : (diagonal (fun i => ((hY.1.eigenvalues i + -μ : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have : μ ≤ hY.1.eigenvalues i := Finset.inf'_le _ (Finset.mem_univ i)
    exact_mod_cast (by linarith : (0 : ℝ) ≤ hY.1.eigenvalues i + -μ)
  have := hD.mul_mul_conjTranspose_same (hY.1.eigenvectorUnitary : Matrix n n ℂ)
  rwa [← Matrix.star_eq_conjTranspose] at this
end Auto
