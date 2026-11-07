-- Prove2me | Definitions.Def_PolySphereLP_lapC
-- name    : PolySphereLP_lapC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:16.665675+00:00
-- url     : https://prove2.me/theorems/76038ac7-d3ac-4af4-a167-3ce2b8a467d3
-- title:
--   Laplacian $\Delta$ of a complex polynomial
-- statement:
--   For a polynomial $f\in\mathbb C[x_1,\dots,x_n]$ the **Laplacian** is
--   $$\Delta f=\sum_{i=1}^n\frac{\partial^2 f}{\partial x_i^2}.$$
--   A polynomial is **harmonic** when $\Delta f=0$. The paper uses harmonic polynomials with complex coefficients in Lemma 2.1, Theorem 2.2 and Lemma A.4.
--
--   **Formalization Note** The same formula as the published real Laplacian `SphereSOS.Rate.laplacian`, over $\mathbb C$. Variables and coordinates are indexed by `Fin n` (from $0$).
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §2.2, p.10; §A.2, p.25

import Mathlib

namespace PolySphereLP

/-- **The Laplacian of a complex polynomial.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §2.2, p.10 and §A.2, p.25: a polynomial `G`
is harmonic when `ΔG = ∑ᵢ ∂ᵢ² G = 0`; Lemma 2.1, Theorem 2.2 and Lemma A.4 use complex coefficients.

`lapC f = ∑ᵢ ∂ᵢ ∂ᵢ f` for `f ∈ ℂ[x₁,…,xₙ]`.

**Formalization Note.** The same formula as the published real Laplacian
`SphereSOS.Rate.laplacian`, over `ℂ`; variables are indexed by `Fin n` (0-based). -/
noncomputable def lapC {n : ℕ} (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i f)

end PolySphereLP


