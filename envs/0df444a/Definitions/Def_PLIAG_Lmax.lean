-- Prove2me | Definitions.Def_PLIAG_Lmax
-- name    : PLIAG_Lmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:41.558087+00:00
-- url     : https://prove2.me/theorems/9c2fbd05-b80e-427e-8fdd-8d356accd1c8
-- title:
--   The constant $L=\max_{k\ge0}\sum_{j\in\mathcal J_k}L_j$
-- statement:
--   With $L_j$ the constants of assumption B1,
--
--   $$
--   L:=\max_{k\ge0}\sum_{j\in\mathcal J_k}L_j .
--   $$
--
--   It is the largest total relative-smoothness constant of the linearized blocks, and it enters the step-size bound (4.5) and the delayed error term $\Delta_k$.
--
--   **Formalization Note** A real supremum over $k$. The family takes at most $2^N$ values, so it is bounded and the supremum is attained: it is the paper's maximum.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Lemma 4.1, p.11, and Theorem 4.2, p.12

import Mathlib

namespace PLIAG

/-- **The constant `L`** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, Lemma 4.1 p.11, Theorem 4.2
p.12): `L := max_{k ≥ 0} Σ_{j ∈ J_k} L_j`, with `L_j` the constants of assumption B1.

**Formalization Note.** A real supremum over `k`. The family `k ↦ Σ_{j ∈ J_k} L_j` takes at most
`2^N` values (one per subset of `Fin N`), so it is bounded and the supremum is attained: it is the
paper's maximum. -/
noncomputable def Lmax {N : ℕ} (Lc : Fin N → ℝ) (J : ℕ → Finset (Fin N)) : ℝ :=
  ⨆ k, ∑ j ∈ J k, Lc j

end PLIAG


