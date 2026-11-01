-- Prove2me | Definitions.Def_GaussianGLOCC_sympSpec
-- name    : GaussianGLOCC_sympSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:33.617318+00:00
-- url     : https://prove2.me/theorems/a6aa6035-bf25-4554-a388-3c252f266826
-- title:
--   Ordered symplectic spectrum $s(M)$ of a real $2n\times 2n$ matrix
-- statement:
--   For a real $2n\times 2n$ matrix $M$ the **symplectic eigenvalues** are the moduli of the eigenvalues of $\sigma M$ (p.3: "The symplectic spectrum of $\gamma$ can be directly calculated as the modulus of the eigenvalues of $\sigma\gamma$"). For a real symmetric positive semidefinite $M$ the $2n$ eigenvalues of $\sigma M$ come in pairs $\pm i d_k$, $d_k\ge 0$, and
--
--   $$
--   s(M)=(d_1\le d_2\le\dots\le d_n)
--   $$
--
--   is the vector of symplectic eigenvalues in ascending order, each listed once. It is the object compared in Lemma 2 and in eq. (25).
--
--   **Formalization Note** `sympSpec M k` sorts the moduli of the $2n$ complex roots of the characteristic polynomial of $\sigma M$ (with multiplicity) ascendingly and takes the entry at position $2k$; indices are 0-based. The definition is total and agrees with the paper's on all positive semidefinite $M$, singular ones included. The sanity file checks $s(\mathbb 1)=1$ on one mode.
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, p.3 (symplectic spectrum); Lemma 2, p.4 (ascending order)

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, p.3: "The symplectic spectrum of γ
can be directly calculated as the modulus of the eigenvalues of σγ", and p.4, Lemma 2: "the
vectors consisting of the (ascendingly ordered) symplectic eigenvalues".

`sympSpec M k` is the `k`-th smallest symplectic eigenvalue of the real `2n × 2n` matrix `M`
(`k = 0, …, n − 1`), each symplectic eigenvalue listed once.

**Formalization Note.** The `2n` eigenvalues of `σM` (roots of its complex characteristic
polynomial, with algebraic multiplicity) are taken in modulus and sorted ascendingly; for a
real symmetric positive semidefinite `M` they come in pairs `±i d_k`, so the sorted list of
moduli is `d₁, d₁, d₂, d₂, …`, and `sympSpec M k` is its entry at position `2k`. The
definition is total; it is the paper's symplectic spectrum on positive semidefinite `M`,
including singular ones (Lemma 2 allows `M ≥ 0`). Indices are 0-based (`Fin n`), the paper's
are `1, …, n`. `σ` is the paper's `σ` (`GaussianGLOCC.sigma`); the moduli do not depend on
its sign. -/
noncomputable def sympSpec {n : ℕ} (M : Cov n) : Fin n → ℝ := fun k =>
  ((((sigma n * M).map (fun x : ℝ => (x : ℂ))).charpoly.roots.map (fun z => ‖z‖)).sort
    (· ≤ ·)).getD (2 * k.val) 0

end GaussianGLOCC


