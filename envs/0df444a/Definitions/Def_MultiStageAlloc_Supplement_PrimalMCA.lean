-- Prove2me | Definitions.Def_MultiStageAlloc_Supplement_PrimalMCA
-- name    : MultiStageAlloc_Supplement_PrimalMCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:17:00.856168+00:00
-- url     : https://prove2.me/theorems/a81fc7b9-ac2a-582a-ab5a-74533e1ae88a
-- title:
--   PRIMAL-MCA and the offline benchmark $\mathrm{OPT}(I)$ for configuration allocation (§2.2)
-- statement:
--   For an instance of configuration allocation with demands $n_j=1$, PRIMAL-MCA is the linear program
--   $$
--   \max_{x,z\ge 0}\ \sum_{i\in U}\sum_{c\in C}\sum_{j\in V} w_{i,c,j}\,x_{i,c,j}
--   $$
--   subject to
--
--   1. $\sum_{i\in U}\sum_{c\in C}x_{i,c,j}\le 1$ for every $j\in V$;
--   2. $\sum_{c\in C}z_{i,c}\le 1$ for every $i\in U$;
--   3. $x_{i,c,j}\le \xi_{i,c,j}\,z_{i,c}$ for all $i,c,j$.
--
--   Here $z_{i,c}$ is the fraction of configuration $c$ given to user $i$, and $x_{i,c,j}$ is the number of those impressions that advertiser $j$ pays for. The benchmark $\mathrm{OPT}(I)$ is the optimal value of this program.
--
--   **Formalization Note** $\mathrm{OPT}(I)$ is a real supremum over the feasible set. The set is nonempty ($x=z=0$) and its values are bounded, because $0\le x_{i,c,j}\le\xi_{i,c,j}$, so the supremum is the true optimal value.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §2.2, p.13 (PRIMAL-MCA)

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_MCAInstance

namespace MultiStageAlloc.Supplement

variable {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}

/-- **The feasible set of PRIMAL-MCA**, the offline LP of Feng & Niazadeh, arXiv:2211.16581v1,
§2.2, p.13, at `n_j = 1`: `x, z ≥ 0`, `∑_{i,c} x_{i,c,j} ≤ 1` for every advertiser `j`,
`∑_c z_{i,c} ≤ 1` for every user `i`, and `x_{i,c,j} ≤ ξ_{i,c,j} z_{i,c}`. Here `z_{i,c}` is the
fraction of configuration `c` given to user `i`, and `x_{i,c,j}` the number of those impressions
advertiser `j` pays for. -/
def PrimalFeasible (I : MCAInstance U C V K) (x : U → C → V → ℝ) (z : U → C → ℝ) : Prop :=
  (∀ i c j, 0 ≤ x i c j) ∧ (∀ i c, 0 ≤ z i c) ∧ (∀ j, ∑ i, ∑ c, x i c j ≤ 1) ∧
    (∀ i, ∑ c, z i c ≤ 1) ∧ ∀ i c j, x i c j ≤ I.ξ i c j * z i c

/-- **The objective of PRIMAL-MCA**, `∑_{i,c,j} w_{i,c,j} x_{i,c,j}`, arXiv:2211.16581v1, p.13. -/
def primalValue (I : MCAInstance U C V K) (x : U → C → V → ℝ) : ℝ :=
  ∑ i, ∑ c, ∑ j, I.price i c j * x i c j

/-- **The offline benchmark `OPT(I)` of configuration allocation**: the optimal value of
PRIMAL-MCA, arXiv:2211.16581v1, p.13 and Definition 1, p.14.

**Formalization Note.** A real `sSup`. The set is nonempty (`x = z = 0`) and bounded above, since
`0 ≤ x_{i,c,j} ≤ ξ_{i,c,j} z_{i,c} ≤ ξ_{i,c,j}`; so the `sSup` is the true optimal value, not Lean's
default `0`. -/
noncomputable def mcaOPT (I : MCAInstance U C V K) : ℝ :=
  sSup ((fun p : (U → C → V → ℝ) × (U → C → ℝ) => primalValue I p.1) ''
    {p | PrimalFeasible I p.1 p.2})

end MultiStageAlloc.Supplement


