-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Supplement_gibbs
-- name    : SparseSDP_TwoSided_Supplement_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:29:57.339663+00:00
-- url     : https://prove2.me/theorems/ab8edb61-9dca-4dc9-9890-0a3ba548e100
-- title:
--   Gibbs state $\Omega_H=e^{-H}/\operatorname{Tr}e^{-H}$ and Gibbs expectations $\operatorname{Tr}(A\Omega_H)$
-- statement:
--   For a complex $n\times n$ matrix $H$ (Hermitian in every use), the **Gibbs state** is
--   $$
--   \Omega_H=\frac{e^{-H}}{\operatorname{Tr}(e^{-H})},
--   $$
--   with $e^{-H}$ the matrix exponential, and the **Gibbs expectation** of an observable $A$ is $\operatorname{Tr}(A\Omega_H)$.
--
--   These are the quantities estimated in Theorem 5.1 and, with $H_t$ the accumulated MMWU Hamiltonian, those supplied to the θ-oracle and the primal phase in Theorem 6.2.
--
--   **Formalization Note** For Hermitian $A$ and $H$ the trace $\operatorname{Tr}(A\Omega_H)$ is real; the definition takes its real part. For Hermitian $H$ on a nonempty index, $\operatorname{Tr}(e^{-H})>0$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §5 opening, p. 27; Eqs. (99), (189)

import Mathlib

open Matrix

namespace SparseSDP.TwoSided.Supplement

variable {n : ℕ}

/-- The Gibbs state `Ω_H := e^{−H}/Tr(e^{−H})` of a complex `n × n` matrix `H`.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
§5 opening, p. 27.

**Formalization Note.** `NormedSpace.exp` is the matrix exponential. For Hermitian `H` on a nonempty
index the trace `Tr(e^{−H})` is real and positive, so the normalization is a genuine division. -/
noncomputable def gibbs (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.trace (NormedSpace.exp (-H)))⁻¹ • NormedSpace.exp (-H)

/-- The Gibbs expectation `Tr(A Ω_H)` (Eq. (99), p. 27; Eq. (189), p. 37).

**Formalization Note.** For Hermitian `A` and `H` the trace is real; its real part is taken so that
the value is a real number. -/
noncomputable def gibbsExpect (A H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (A * gibbs H)).re

end SparseSDP.TwoSided.Supplement


