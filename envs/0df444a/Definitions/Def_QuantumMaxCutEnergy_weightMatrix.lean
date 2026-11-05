-- Prove2me | Definitions.Def_QuantumMaxCutEnergy_weightMatrix
-- name    : QuantumMaxCutEnergy_weightMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:13:40.933234+00:00
-- url     : https://prove2.me/theorems/0fabade8-7172-4bd7-a544-3b3e39e76109
-- title:
--   The symmetric weight matrix of a Quantum Max Cut input
-- statement:
--   For a weighted graph $G$ — an `Input` of the Quantum Max Cut estimation model, carrying a nonnegative rational weight $w_{\{i,j\}}$ on each unordered pair $i<j$ of $\{1,\dots,n\}$ — the **weight matrix** $A(G)$ is the symmetric $n\times n$ real matrix with
--   $$A(G)_{ij}=\begin{cases} w_{\{i,j\}} & i<j,\\ w_{\{i,j\}} & j<i,\\ 0 & i=j,\end{cases}$$
--   that is, the weight of the edge when $i\neq j$ and zero on the diagonal.
--
--   This is the matrix $a$ of the Max-Cut semidefinite relaxation (4.3.15) of Ben-Tal–Nemirovski, p. 170, for the graph $G$; the relaxation's objective is $\tfrac14\sum_{i,j}A(G)_{ij}(1-X_{ij})$ over $X\succeq0$ with $X_{ii}=1$. It is the matrix written inline in `QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`; naming it once keeps later statements readable and lets structural facts (symmetry, zero diagonal) be recorded as simp lemmas.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.14)-(4.3.15), pp. 170-174; the graph matrix of the MAXCUT semidefinite relaxation, in the Quantum Max Cut estimation model's encoding.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

/-!
# The symmetric weight matrix of a Quantum Max Cut input

`QuantumMaxCutEnergy.Input` carries a nonnegative rational weight on each unordered pair
`{i,j}`, `i < j`. The Max-Cut semidefinite relaxation is stated in terms of the symmetric
matrix with those weights off the diagonal and zero diagonal; this file fixes that matrix
once, so that theorems about the relaxation do not have to repeat the `if i < j` case split.

It is the matrix appearing in `QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The symmetric zero-diagonal weight matrix of an input: `weightMatrix G i j` is the weight of
the edge `{i,j}` when `i ≠ j`, and `0` on the diagonal. -/
noncomputable def weightMatrix (G : Input) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  Matrix.of fun i j =>
    if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0

@[simp] lemma weightMatrix_apply_of_lt {G : Input} {i j : Fin G.n} (h : i < j) :
    weightMatrix G i j = (G.weights ⟨(i, j), h⟩ : ℝ) := by
  simp [weightMatrix, h]

@[simp] lemma weightMatrix_apply_of_gt {G : Input} {i j : Fin G.n} (h : j < i) :
    weightMatrix G i j = (G.weights ⟨(j, i), h⟩ : ℝ) := by
  simp [weightMatrix, h, not_lt.mpr (le_of_lt h)]

@[simp] lemma weightMatrix_apply_self {G : Input} (i : Fin G.n) : weightMatrix G i i = 0 := by
  simp [weightMatrix]

/-- The weight matrix is symmetric. -/
lemma weightMatrix_transpose (G : Input) : Matrix.transpose (weightMatrix G) = weightMatrix G := by
  ext i j
  by_cases h : i < j
  · rw [Matrix.transpose_apply, weightMatrix_apply_of_lt h, weightMatrix_apply_of_gt h]
  · by_cases h' : j < i
    · rw [Matrix.transpose_apply, weightMatrix_apply_of_gt h', weightMatrix_apply_of_lt h']
    · simp [weightMatrix, h, h']

end QuantumMaxCutEnergy


