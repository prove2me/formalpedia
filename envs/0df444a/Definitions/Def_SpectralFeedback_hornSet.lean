-- Prove2me | Definitions.Def_SpectralFeedback_hornSet
-- name    : SpectralFeedback_hornSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:17.173263+00:00
-- url     : https://prove2.me/theorems/e0e2c40b-8279-4f58-ba33-539aa1ccf4e2
-- title:
--   The real Horn cone of spectral triples $(\lambda(A),\lambda(B),\lambda(A+B))$
-- statement:
--   For $n\ge0$, the **real Horn cone** is the set of spectral triples
--   $$
--   \mathcal H_n=\bigl\{(\lambda^\downarrow(A),\ \lambda^\downarrow(B),\ \lambda^\downarrow(A+B)) : A,B\in\mathbb C^{n\times n}\text{ Hermitian}\bigr\}\subseteq\mathbb R^n\times\mathbb R^n\times\mathbb R^n,
--   $$
--   where $\lambda^\downarrow$ lists the eigenvalues in decreasing order with multiplicity. A triple $(a,b,\lambda)$ in it is called feasible. The Horn–Klyachko–Knutson–Tao theory describes this set; the paper uses that it is a convex cone invariant under exchanging the two summands.
--
--   **Formalization Note** Spectra are 0-based vectors `Fin n → ℝ` built from `eigDesc`.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), proof of Theorem H.2, p.109 (PDF p.111); proof of Theorem F.4, p.94 (PDF p.96); Appendix C, p.28 (PDF p.30), citing [KT99]

import Mathlib
import Definitions.Def_SpectralFeedback_eigDesc

namespace SpectralFeedback

/-- **The real Horn cone** of spectral triples (Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), proof of Theorem H.2, p.109
(PDF p.111); proof of Theorem F.4, p.94: "The feasible spectral triples `(a, b, λ)` form the real
Horn cone"; Appendix C, p.28 (PDF p.30), citing Knutson–Tao [KT99]): the set of triples
`(λ↓(A), λ↓(B), λ↓(A + B)) ∈ ℝⁿ × ℝⁿ × ℝⁿ` for Hermitian `A, B ∈ ℂ^{n×n}`, each spectrum listed in
decreasing order with multiplicity.

**Formalization Note** Spectra are `Fin n → ℝ` via `eigDesc` (0-based, decreasing). The matrices
are complex Hermitian, as in the paper. -/
noncomputable def hornSet (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) :=
  {t | ∃ A B : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian ∧ B.IsHermitian ∧
    t = (fun i : Fin n => eigDesc A (i : ℕ), fun i : Fin n => eigDesc B (i : ℕ),
      fun i : Fin n => eigDesc (A + B) (i : ℕ))}

end SpectralFeedback


