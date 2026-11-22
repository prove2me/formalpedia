-- Prove2me | solution 1 for Auto.matCost_toReal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:11:11.815097+00:00
-- url     : https://prove2.me/submissions/6cd62202-9527-448f-8af8-662394add3ef

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_eq_sum
public import Theorems.Thm_Auto_sqrt_eigenvalues_pos

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
theorem _root_.solution {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCost P K ≠ ⊤ ∧ (matCost P K).toReal = ∑ i, ∑ j, (3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2 /
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by
  have hc : ∀ i j, 0 < √(hP.1.eigenvalues i) + √(hP.1.eigenvalues j) := fun i j =>
    add_pos (sqrt_eigenvalues_pos hP i) (sqrt_eigenvalues_pos hP j)
  have h := matCost_eq_sum hP.posSemidef K
  have e : ∀ i j, ENNReal.ofReal ((3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2) /
      ENNReal.ofReal (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) =
      ENNReal.ofReal ((3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2 / (√(hP.1.eigenvalues i) +
          √(hP.1.eigenvalues j))) := fun i j =>
    (ENNReal.ofReal_div_of_pos (hc i j)).symm
  simp only [eigCoord] at e
  simp only [e] at h
  have h' : matCost P K = ENNReal.ofReal (∑ i, ∑ j, (3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2 /
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j))) := by
    rw [h, ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by
      have := hc i j; positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := hc i j; positivity)]
    rfl
  refine ⟨by rw [h']; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [h', ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    have := hc i j; positivity)]
end Auto
