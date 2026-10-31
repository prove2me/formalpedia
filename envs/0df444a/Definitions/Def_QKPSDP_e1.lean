-- Prove2me | Definitions.Def_QKPSDP_e1
-- name    : QKPSDP_e1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:50.162922+00:00
-- url     : https://prove2.me/theorems/01fb040c-e949-461a-83e9-bf0c88b9908e
-- title:
--   The first unit vector $e_1 \in \mathbb R^r$
-- statement:
--   For $r \ge 1$, $e_1 \in \mathbb R^r$ is the vector whose first entry is $1$ and whose other entries are $0$.
--
--   It fixes the first row of the factorization $Y = (e_1\ R^\top)^\top (e_1\ R^\top)$, which makes $Y_{11} = 1$ automatic.
--
--   **Formalization Note** Indices start at $0$, so the first entry is index $0$; the definition needs $r \ge 1$.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, p.3 (below (SQKELR))

import Mathlib

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, p.3 (below (SQKELR)): "`e₁ ∈ ℝʳ` is such that its first entry
is 1 and all other entries are zero."

**Formalization Note** Indices of `ℝʳ` are `Fin r`, from 0, so the paper's first entry is index
`0`; `[NeZero r]` (i.e. `r ≥ 1`) is needed for that index to exist. Every theorem of the mission
assumes `r ≥ 3`, which implies it. -/
noncomputable def e1 (r : ℕ) [NeZero r] : Fin r → ℝ :=
  Pi.single 0 1

end QKPSDP


