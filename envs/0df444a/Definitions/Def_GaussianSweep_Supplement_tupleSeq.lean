-- Prove2me | Definitions.Def_GaussianSweep_Supplement_tupleSeq
-- name    : GaussianSweep_Supplement_tupleSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:37:45.398496+00:00
-- url     : https://prove2.me/theorems/038a0dea-90c8-4784-bf36-3a5678e0eda0
-- title:
--   The sequence a finite tuple $(a_3,\dots,a_k)$ stands for
-- statement:
--   A finite tuple $(a_3,\dots,a_k)$ stands for the sequence $(a_d)_{d \ge 3}$ that continues it with $a_d = 1$ for all $d > k$.
--
--   **Formalization Note** The tuple is the list $[a_3,\dots,a_k]$, read at index $d - 3$; indices $d < 3$ are not part of the sequence, are set to $0$ and never used.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 9.1, p.56 (PDF p.58)

import Mathlib

namespace GaussianSweep.Supplement

/-- The sequence `(a_d)_{d≥3}` that a finite tuple `(a₃, …, a_k)` stands for
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 9.1, p.56 (PDF p.58)): it continues the tuple with
`a_d = 1` for all `d > k`.

**Formalization Note** The tuple is the list `[a₃, …, a_k]`, so `a_d` is its entry at index
`d − 3` for `3 ≤ d ≤ k` and `1` beyond. Indices `d < 3` are not part of the sequence; they are
set to `0` and never used (every sum over the sequence starts at `d = 3`). -/
def tupleSeq (l : List ℝ) (d : ℕ) : ℝ :=
  if d < 3 then 0 else l.getD (d - 3) 1

end GaussianSweep.Supplement


