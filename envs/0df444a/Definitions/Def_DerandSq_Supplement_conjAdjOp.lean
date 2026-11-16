-- Prove2me | Definitions.Def_DerandSq_Supplement_conjAdjOp
-- name    : DerandSq_Supplement_conjAdjOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:04:50.063114+00:00
-- url     : https://prove2.me/theorems/f8d081e5-f95e-4535-ba46-50b5df37f314
-- title:
--   $B = U A U^*$ as an operator on $\mathbb C^N$
-- statement:
--   The permutation-conjugated adjacency matrix $B = U A U^*$ of (5.1), viewed as a bounded linear operator on the Hilbert space $\mathbb C^N$ (the matrix algebra $M_N(\mathbb C)$ of Example 2.3, with the operator norm). This is the form in which ∗-polynomials are evaluated at $B_1, \dots, B_r$, traced, and normed.
--
--   **Formalization Note** The real matrix is mapped entrywise into $\mathbb C$ and read as an operator on `EuclideanSpace ℂ (Fin N)`.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (5.1), p.24; Example 2.3, p.8

import Mathlib
import Definitions.Def_DerandSq_Supplement_conjAdj

namespace DerandSq.Supplement

/-- The permutation-conjugated adjacency matrix `B = U A U^*` of (5.1), Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.24, as a
bounded operator on `ℂ^N` (Example 2.3, p.8: `M_N(ℂ)` with the operator norm), so that
∗-polynomials can be evaluated at it.

**Formalization Note** The real matrix `conjAdj G σ` is mapped entrywise into `ℂ` and read as
an operator on `EuclideanSpace ℂ (Fin N)` by `Matrix.toEuclideanCLM`. -/
noncomputable def conjAdjOp {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin N)) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) ((conjAdj G σ).map (fun x : ℝ => (x : ℂ)))

end DerandSq.Supplement


