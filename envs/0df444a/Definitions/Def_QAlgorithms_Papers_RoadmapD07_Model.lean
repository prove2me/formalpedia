-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapD07_Model
-- name    : QAlgorithms_Papers_RoadmapD07_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:44.229043+00:00
-- url     : https://prove2.me/theorems/00e206e7-028c-4a38-8dac-f39aa6ff1353
-- title:
--   Hamiltonian Decoded Quantum Interferometry for General Pauli Hamiltonians: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Hamiltonian Decoded Quantum Interferometry for General Pauli Hamiltonians, arXiv:2601.18773v1, https://arxiv.org/abs/2601.18773v1. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_HDQIPreparation
noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.RoadmapD07

/-- The coefficient input for Theorem 5's unit-cost arithmetic preprocessing.
Addresses below `m` contain the Hamiltonian coefficients, the next `l + 1`
addresses contain the polynomial coefficients, and all other addresses are zero.
No normalization factor, reference amplitudes, or gate entries are supplied. -/
def coefficientInput {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (l : ℕ) : ℕ → ℝ :=
  fun a => if h : a < m then c ⟨a, h⟩ else if a < m + (l + 1) then P.coeff (a - m) else 0

/-- Arithmetic programs may introduce only the constants `0`, `1`, and `-1`.
This prevents a chosen program from hiding precomputed reference or gate entries
in its constant instructions. Arithmetic and memory access have unit cost
(Lemma 4, arXiv:2601.18773v1, PDF pp.7-8). -/
def HasStandardConstants : ArithmeticProgram → Prop
  | .done => True
  | .step op rest =>
      (match op with
        | .constant _ v => v = 0 ∨ v = 1 ∨ v = -1
        | _ => True) ∧ HasStandardConstants rest
  | .loop _ body rest => HasStandardConstants body ∧ HasStandardConstants rest

/-- The computed MPS data of Eqs.(12)-(13), with bond dimension `l + 1`.
Address zero stores the normalization, followed by the two boundary vectors,
then the two local matrices for each term in row-major order. -/
def ComputesReferenceData {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (l : ℕ)
    (result : ℕ → ℝ) : Prop :=
  result 0 = hdqiReferenceNorm c P l ∧
    (∀ j : Fin (l + 1), (result (1 + j) : ℂ) = (hdqiReferenceMPS c P l).left j) ∧
    (∀ j : Fin (l + 1), (result (1 + (l + 1) + j) : ℂ) =
      (hdqiReferenceMPS c P l).right j) ∧
    ∀ (i : Fin m) (y : Fin 2) (j k : Fin (l + 1)),
      (result (1 + 2 * (l + 1) + ((i * 2 + y) * (l + 1) + j) * (l + 1) + k) : ℂ) =
        (hdqiReferenceMPS c P l).localMatrix i y j k


end QAlgorithms.Papers.RoadmapD07


