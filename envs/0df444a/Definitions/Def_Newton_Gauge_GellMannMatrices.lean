-- Prove2me | Definitions.Def_Newton_Gauge_GellMannMatrices
-- name    : Newton_Gauge_GellMannMatrices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:22.440784+00:00
-- url     : https://prove2.me/theorems/271d60f8-e080-49e7-94e8-e5aea0fc6d30
-- title:
--   Gell Mann Matrices
-- statement:
--   Definitions and structural lemmas for Gell Mann Matrices, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean

import Definitions.Def_Newton_Gauge_LieAlgebra
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


set_option autoImplicit false
open Matrix
namespace Newton
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![1, 0]]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, -Complex.I], ![Complex.I, 0]]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 0], ![0, -1]]
@[simp]
theorem pauliX_trace : trace pauliX = 0 := by
  simp only [pauliX, trace, Fin.sum_univ_two, diag, cons_val_zero, cons_val_one]
  ring
@[simp]
theorem pauliY_trace : trace pauliY = 0 := by
  simp only [pauliY, trace, Fin.sum_univ_two, diag, cons_val_zero, cons_val_one]
  ring
@[simp]
theorem pauliZ_trace : trace pauliZ = 0 := by
  simp only [pauliZ, trace, Fin.sum_univ_two, diag, cons_val_zero, cons_val_one]
  ring
theorem pauliX_hermitian : conjTranspose pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.conjTranspose_apply]; simp [pauliX])
theorem pauliZ_hermitian : conjTranspose pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.conjTranspose_apply]; simp [pauliZ])
theorem pauliY_hermitian : conjTranspose pauliY = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.conjTranspose_apply]; simp [pauliY])
noncomputable def su2Gen1Matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2 : ℂ) • pauliX
noncomputable def su2Gen2Matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2 : ℂ) • pauliY
noncomputable def su2Gen3Matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2 : ℂ) • pauliZ
@[simp]
theorem su2Gen1Matrix_trace : trace su2Gen1Matrix = 0 := by
  simp only [su2Gen1Matrix, trace_smul, pauliX_trace, smul_zero]
@[simp]
theorem su2Gen2Matrix_trace : trace su2Gen2Matrix = 0 := by
  simp only [su2Gen2Matrix, trace_smul, pauliY_trace, smul_zero]
@[simp]
theorem su2Gen3Matrix_trace : trace su2Gen3Matrix = 0 := by
  simp only [su2Gen3Matrix, trace_smul, pauliZ_trace, smul_zero]
theorem star_neg_I_div_2 : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
  simp only [star_div₀, star_neg, Complex.star_def, Complex.conj_I, h2]
  ring
theorem su2Gen1Matrix_antiHermitian : conjTranspose su2Gen1Matrix = -su2Gen1Matrix := by
  unfold su2Gen1Matrix
  simp only [conjTranspose_smul, pauliX_hermitian, neg_smul, star_neg_I_div_2]
theorem su2Gen2Matrix_antiHermitian : conjTranspose su2Gen2Matrix = -su2Gen2Matrix := by
  unfold su2Gen2Matrix
  simp only [conjTranspose_smul, pauliY_hermitian, neg_smul, star_neg_I_div_2]
theorem su2Gen3Matrix_antiHermitian : conjTranspose su2Gen3Matrix = -su2Gen3Matrix := by
  unfold su2Gen3Matrix
  simp only [conjTranspose_smul, pauliZ_hermitian, neg_smul, star_neg_I_div_2]
noncomputable def su2Gen1 : SuNAlgebra 2 where
  matrix := su2Gen1Matrix
  trace_zero := su2Gen1Matrix_trace
  anti_hermitian := su2Gen1Matrix_antiHermitian
noncomputable def su2Gen2 : SuNAlgebra 2 where
  matrix := su2Gen2Matrix
  trace_zero := su2Gen2Matrix_trace
  anti_hermitian := su2Gen2Matrix_antiHermitian
noncomputable def su2Gen3 : SuNAlgebra 2 where
  matrix := su2Gen3Matrix
  trace_zero := su2Gen3Matrix_trace
  anti_hermitian := su2Gen3Matrix_antiHermitian
def gellMann1 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]]
def gellMann2 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, -Complex.I, 0], ![Complex.I, 0, 0], ![0, 0, 0]]
def gellMann3 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0], ![0, -1, 0], ![0, 0, 0]]
def gellMann4 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]]
def gellMann5 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, -Complex.I], ![0, 0, 0], ![Complex.I, 0, 0]]
def gellMann6 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]]
def gellMann7 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 0], ![0, 0, -Complex.I], ![0, Complex.I, 0]]
def gellMann8_unnorm : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, -2]]
def su2StructureConstant (a b c : Fin 3) : ℝ :=
  if (a, b, c) = (0, 1, 2) ∨ (a, b, c) = (1, 2, 0) ∨ (a, b, c) = (2, 0, 1) then 1
  else if (a, b, c) = (2, 1, 0) ∨ (a, b, c) = (1, 0, 2) ∨ (a, b, c) = (0, 2, 1) then -1
  else 0
noncomputable def embedMatrix2 (M : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  fun i j =>
    if hi : i.val < 2 then
      if hj : j.val < 2 then
        M ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else 0
theorem embedMatrix2_trace (M : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    trace (embedMatrix2 M N) = trace M := by
  simp only [trace, diag]
  -- Auxiliary lemma: only i.val < 2 gives nonzero contribution
  have key : ∀ i : Fin (N + 2), embedMatrix2 M N i i =
      if h : i.val < 2 then M ⟨i.val, h⟩ ⟨i.val, h⟩ else 0 := by
    intro i
    simp only [embedMatrix2]
    by_cases h : i.val < 2
    · simp only [h, dite_true]
    · simp only [h, dite_false]
  simp only [key]
  -- Expand the right-hand side
  rw [Fin.sum_univ_two]
  -- Extract the i = 0, 1 terms from the left-hand side sum
  have h0_lt : (0 : Fin (N + 2)).val < 2 := Nat.zero_lt_two
  have h1_lt : (1 : Fin (N + 2)).val < 2 := Nat.one_lt_two
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (N + 2))), ← Finset.sdiff_singleton_eq_erase]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp⟩ :
      (1 : Fin (N + 2)) ∈ Finset.univ \ {0}), ← Finset.sdiff_singleton_eq_erase]
  simp only [h0_lt, h1_lt, dite_true]
  -- Show that the remaining sum is 0
  have hrest : ∑ i ∈ (Finset.univ \ {0}) \ {(1 : Fin (N + 2))},
      (if h : i.val < 2 then M ⟨i.val, h⟩ ⟨i.val, h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hi
    have hne0 : i ≠ 0 := hi.1
    have hne1 : i ≠ 1 := hi.2
    have hnotlt : ¬i.val < 2 := by
      by_contra hlt
      -- i.val < 2 and i ≠ 0 and i ≠ 1 is a contradiction
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      rcases hval with hv0 | hv1
      · exact hne0 (Fin.ext hv0)
      · exact hne1 (Fin.ext hv1)
    simp [hnotlt]
  rw [hrest, add_zero]
  -- M ⟨1, _⟩ ⟨1, _⟩ + M ⟨0, _⟩ ⟨0, _⟩ = M 0 0 + M 1 1
  have h0eq : (⟨(0 : Fin (N + 2)).val, h0_lt⟩ : Fin 2) = 0 := Fin.ext rfl
  have h1eq : (⟨(1 : Fin (N + 2)).val, h1_lt⟩ : Fin 2) = 1 := Fin.ext rfl
  simp only [h0eq, h1eq]
theorem embedMatrix2_antiHermitian (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : conjTranspose M = -M) (N : ℕ) :
    conjTranspose (embedMatrix2 M N) = -embedMatrix2 M N := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
  simp only [embedMatrix2]
  by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
  · -- i < 2, j < 2
    simp only [hi, hj, dite_true]
    have hM' := congr_fun₂ hM ⟨i.val, hi⟩ ⟨j.val, hj⟩
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply] at hM'
    exact hM'
  · -- i < 2, j ≥ 2
    simp only [hi, hj, dite_true, dite_false, star_zero, neg_zero]
  · -- i ≥ 2, j < 2
    simp only [hi, hj, dite_false, dite_true, star_zero, neg_zero]
  · -- i ≥ 2, j ≥ 2
    simp only [hi, hj, dite_false, star_zero, neg_zero]
noncomputable def embedSu2 (A : SuNAlgebra 2) (N : ℕ) : SuNAlgebra (N + 2) where
  matrix := embedMatrix2 A.matrix N
  trace_zero := by rw [embedMatrix2_trace]; exact A.trace_zero
  anti_hermitian := embedMatrix2_antiHermitian A.matrix A.anti_hermitian N
end Newton


