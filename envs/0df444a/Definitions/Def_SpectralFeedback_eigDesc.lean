-- Prove2me | Definitions.Def_SpectralFeedback_eigDesc
-- name    : SpectralFeedback_eigDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:25:50.534297+00:00
-- url     : https://prove2.me/theorems/456bdb14-ca98-4c1f-adb1-66127b8d982a
-- title:
--   Decreasing eigenvalues $\lambda_1(A)\ge\dots\ge\lambda_d(A)$, padded with zeros
-- statement:
--   For a Hermitian matrix $A\in\mathbb C^{d\times d}$, list its eigenvalues with multiplicity in decreasing order,
--
--   $$
--   \lambda_1(A)\ge\lambda_2(A)\ge\dots\ge\lambda_d(A),
--   $$
--
--   and pad the list with zeros: $\lambda_i(A)=0$ for $i>d$. This is the convention of §H.1.1 ("Eigenvalues are decreasing and padded with zeros"), used for every spectral reward, for the paired spectrum $c$ and for the Horn cone of the mission.
--
--   **Formalization Note** Indices are 0-based: `eigDesc A i` is $\lambda_{i+1}(A)$. The values are Mathlib's sorted eigenvalues `Matrix.IsHermitian.eigenvalues₀` (proved antitone in Mathlib). On a non-Hermitian matrix the value is the junk $0$; every statement of the mission applies it to Hermitian matrices only.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), §H.1.1, p.108 (PDF p.110); Theorem H.2, p.109 (PDF p.111)

import Mathlib

namespace SpectralFeedback

/-- **Decreasing eigenvalues, padded with zeros** (Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), §H.1.1, p.108 (PDF p.110):
"Eigenvalues are decreasing and padded with zeros"; also Theorem H.2, p.109).

`eigDesc A i` is the `(i+1)`-st largest eigenvalue `λ_{i+1}(A)` of a Hermitian matrix
`A ∈ ℂ^{d×d}`, counted with multiplicity, for `i < d`, and `0` for `i ≥ d`.

**Formalization Note** Indices are 0-based: the paper's `λ_i` is `eigDesc A (i - 1)`. The value is
read off Mathlib's sorted eigenvalues `Matrix.IsHermitian.eigenvalues₀` (which Mathlib proves
antitone), never the unsorted `IsHermitian.eigenvalues`. On a non-Hermitian matrix the value is the
junk `0`; every statement of the mission applies `eigDesc` to Hermitian (mostly positive
semidefinite) matrices only. -/
noncomputable def eigDesc {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (i : ℕ) : ℝ :=
  open Classical in
  if h : A.IsHermitian ∧ i < d then h.1.eigenvalues₀ ⟨i, by simpa using h.2⟩ else 0

end SpectralFeedback


