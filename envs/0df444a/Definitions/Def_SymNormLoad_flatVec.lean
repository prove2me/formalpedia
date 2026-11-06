-- Prove2me | Definitions.Def_SymNormLoad_flatVec
-- name    : SymNormLoad_flatVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:46.785457+00:00
-- url     : https://prove2.me/theorems/c5b730b9-adcf-4ea8-8e68-916eeadb9a64
-- title:
--   Flat vector $\mathbf 1_k$
-- statement:
--   For $k\in\{0,\dots,M\}$, the **flat vector** $\mathbf 1_k\in\mathbb R^M$ has its first $k$ coordinates equal to $1$ and the remaining coordinates equal to $0$.
--
--   The values of $\Psi$ on flat vectors determine the bounds of Lemma 2.2 and the load transform.
--
--   **Formalization Note** Coordinates are 0-based, so the first $k$ coordinates are the indices $i<k$.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 2.1.1, p.9

import Mathlib

namespace SymNormLoad

/-- **Flat vector `1_k`.** Chen–Im–Sirri, *Online Load Balancing under Symmetric Norms*,
manuscript (STOC 2027 submission), §2.1.1, p.9: for `k ∈ {0, …, M}`, `1_k ∈ ℝ^M` is the vector
whose first `k` coordinates are `1` and whose remaining coordinates are `0`.

**Formalization Note** Coordinates are 0-based, so "the first `k` coordinates" are the indices
`i < k`. For `k > M` the vector is all ones (never used). -/
def flatVec (M k : ℕ) : Fin M → ℝ :=
  fun i => if i.val < k then 1 else 0

end SymNormLoad


