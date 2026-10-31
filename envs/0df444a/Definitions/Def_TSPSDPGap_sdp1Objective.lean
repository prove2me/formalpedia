-- Prove2me | Definitions.Def_TSPSDPGap_sdp1Objective
-- name    : TSPSDPGap_sdp1Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:52.369981+00:00
-- url     : https://prove2.me/theorems/1c48e086-6508-4f0d-b767-4f7afd8e78f7
-- title:
--   Objective of SDP (1): $\tfrac12\operatorname{trace}((D\otimes C^{(n)}_1)Y)$
-- statement:
--   For an $n\times n$ cost matrix $D$ and $Y\in\mathbb R^{n^2\times n^2}$, the **objective of SDP (1)** is
--   $$
--   \tfrac12\operatorname{trace}\bigl((D\otimes C^{(n)}_1)Y\bigr),
--   $$
--   where $C^{(n)}_1$ is the adjacency matrix of the $n$-cycle. On the lift of a permutation matrix it is the cost of the corresponding tour.
--
--   **Formalization Note** The cost matrix is the outer Kronecker factor and $C^{(n)}_1$ the inner one, as printed.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, SDP (1), p.6

import Mathlib
import Definitions.Def_TSPSDPGap_circBasis

open scoped Kronecker

namespace TSPSDPGap

/-- **The objective of SDP (1)**, `½ trace((D ⊗ C^{(n)}_1) Y)`.
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, (1), p.6: "min ½ trace((D ⊗ C^{(n)}_1)Y)".

**Formalization Note.** `D` is the `n × n` cost matrix (indexed by cities `Fin n`, 0-based) and
`Y` is indexed by `Fin n × Fin n`; the cost matrix is the outer Kronecker factor and the cycle
adjacency `C^{(n)}_1 = circBasis n 1` the inner one, as printed. -/
noncomputable def sdp1Objective (n : ℕ) (D : Matrix (Fin n) (Fin n) ℝ)
    (Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace ((D ⊗ₖ circBasis n 1) * Y)

end TSPSDPGap


