-- Prove2me | Definitions.Def_VRAccelCLT_specRad
-- name    : VRAccelCLT_specRad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:08.713987+00:00
-- url     : https://prove2.me/theorems/666ec3d2-568f-4c27-80cc-e74e21a19008
-- title:
--   Spectral radius $\rho(A)$ of a real square matrix
-- statement:
--   For a real square matrix $A$, the **spectral radius** $\rho(A)$ is the largest modulus of an eigenvalue of $A$, where the eigenvalues are the real **or complex** roots of $\det(vI-A)=0$:
--
--   $$
--   \rho(A)=\max\{|v| : v\in\mathbb C,\ \det(vI-A)=0\}.
--   $$
--
--   The paper's hypotheses $\rho(P)<1$ (Lemma 7, Theorem 2) and the identity (46) for $\rho(H_2)$ are stated with this quantity.
--
--   **Formalization Note** $\rho(A)$ is Mathlib's spectral radius of the complexified matrix, a value in $[0,\infty]$ (finite for matrices). The spectrum is taken over $\mathbb C$: the matrices $H_2$ and $P_2$ of Theorem 2 have non-real eigenvalues. For an empty index type the value is $0$.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Notation, p.5

import Mathlib

namespace VRAccelCLT

/-- **Spectral radius of a real square matrix.** Lei, Shanbhag, arXiv:2006.07769v3, Notation, p.5:
"ρ(P) denotes the spectral radius of P", the largest modulus of an eigenvalue of `P`.

`specRad A` is Mathlib's `spectralRadius ℂ` of the complexified matrix `A.map (algebraMap ℝ ℂ)`:
the supremum of `‖z‖` over the complex eigenvalues of `A`.

**Formalization Note.** The value lies in `ℝ≥0∞`; for a matrix it is finite (the complex spectrum is
the finite set of eigenvalues), so `specRad A < 1` is the paper's `ρ(A) < 1`. The spectrum is taken
over `ℂ`, not `ℝ`: the matrices of this paper (e.g. `P₂` of Theorem 2) have non-real eigenvalues,
and a real spectrum would miss them. For an empty index type the value is `0`. -/
noncomputable def specRad {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : ENNReal :=
  spectralRadius ℂ (A.map (algebraMap ℝ ℂ))

end VRAccelCLT


