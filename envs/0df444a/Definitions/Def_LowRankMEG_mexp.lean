-- Prove2me | Definitions.Def_LowRankMEG_mexp
-- name    : LowRankMEG_mexp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:19.035687+00:00
-- url     : https://prove2.me/theorems/58058d6b-bf60-4263-94b4-d830f36e8f36
-- title:
--   The matrix exponential $\exp(A)$
-- statement:
--   For a symmetric matrix with eigen-decomposition $A=V\operatorname{diag}(\lambda_1,\dots,\lambda_n)V^\top$, the **matrix exponential** is
--   $$
--   \exp(A)=V\operatorname{diag}(e^{\lambda_1},\dots,e^{\lambda_n})V^\top.
--   $$
--   It is the map that Matrix Exponentiated Gradient applies at every step.
--
--   **Formalization Note** The definition is Mathlib's continuous functional calculus, `cfc Real.exp A`. Every argument in the mission is symmetric.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, §2.1, p.5

import Mathlib

namespace LowRankMEG

/-- **The matrix exponential** `exp(A) = V diag(exp λ₁, …, exp λ_n) Vᵀ` of a symmetric matrix.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, §2.1, p.5.

**Formalization Note.** Mathlib's continuous functional calculus, so this is the spectral formula
(`Matrix.IsHermitian.cfc_eq`). Every argument in this mission is symmetric. -/
noncomputable def mexp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cfc Real.exp A

end LowRankMEG


