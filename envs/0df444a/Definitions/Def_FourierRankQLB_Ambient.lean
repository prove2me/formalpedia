-- Prove2me | Definitions.Def_FourierRankQLB_Ambient
-- name    : FourierRankQLB_Ambient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:10.899303+00:00
-- url     : https://prove2.me/theorems/ce340a01-9bde-40f9-abea-935eeee082b1
-- title:
--   The ambient Euclidean space $\mathbb R^n$
-- statement:
--   The space $\mathbb R^n$ with the Euclidean norm $\|\cdot\|_2$ and the inner product $c^Tx$. All balls, distances and linear objectives of the paper live here.
--
--   **Formalization Note** It is `EuclideanSpace ℝ (Fin n)`. The hidden block of the hard ellipsoids is the first $d_n$ coordinates.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §2.1, p.12

import Mathlib

namespace FourierRankQLB

/-- The ambient space `ℝⁿ` with its Euclidean norm and inner product.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §2.1, p. 12.

**Formalization Note.** Every ball, distance and inner product of the paper is the Euclidean one.
For `n = d + ℓ` the hidden block is the first `d = dn n` coordinates. -/
abbrev Ambient (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

end FourierRankQLB


