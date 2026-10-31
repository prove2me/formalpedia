-- Prove2me | Definitions.Def_FuchsThesis_Holevo_eigval
-- name    : FuchsThesis_Holevo_eigval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:13.404465+00:00
-- url     : https://prove2.me/theorems/b178c87a-d5af-42d8-ac5a-2383d6ecf556
-- title:
--   Eigenvalues $\lambda_j$ of a Hermitian operator
-- statement:
--   For a Hermitian operator $\hat\rho$ on a $D$-dimensional space, $\lambda_1,\dots,\lambda_D$ denote its eigenvalues, listed with multiplicity, with a matching orthonormal eigenbasis $\{|j\rangle\}$, $\hat\rho|j\rangle=\lambda_j|j\rangle$.
--
--   They enter the von Neumann entropy (3.150) and the expressions (3.160), (3.181), (3.183), (3.188).
--
--   **Formalization Note** The eigenvalues are Mathlib's `Matrix.IsHermitian.eigenvalues`, indexed by the index type of the matrix, in the order matching the eigenvector columns used for matrix elements (`eigCoord`). For a non-Hermitian matrix the value is a junk $0$; the mission applies it only to density operators and their mixtures.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.150), p.66 (PDF p.75); p.67 (PDF p.76) before (3.160)

import Mathlib

namespace FuchsThesis.Holevo

open Classical in
/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.150), p.66 (PDF p.75), and p.67 (PDF p.76) before
(3.160): the eigenvalues `λ_j`, `j = 1, …, D`, of a Hermitian operator `ρ̂` (with multiplicity).

**Formalization Note.** For a Hermitian matrix this is Mathlib's `IsHermitian.eigenvalues`,
indexed by the matrix index type `d` and listed with multiplicity, in the order matching the
columns of `IsHermitian.eigenvectorUnitary` (`FuchsThesis.Holevo.eigCoord`). For a non-Hermitian
matrix the value is the junk `0`; every statement applies it to density operators or their
mixtures, which are Hermitian. -/
noncomputable def eigval {d : Type} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : d → ℝ :=
  if h : ρ.IsHermitian then h.eigenvalues else 0

end FuchsThesis.Holevo


