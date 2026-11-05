-- Prove2me | Definitions.Def_MultiStageAlloc_OfflineLP
-- name    : MultiStageAlloc_OfflineLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:41.292184+00:00
-- url     : https://prove2.me/theorems/55df6261-9aca-4fdc-9521-81c66cbe0dc6
-- title:
--   The offline primal LP and the benchmark $\mathrm{OPT}$
-- statement:
--   The offline primal LP of the maximum vertex weighted matching is
--   $$
--   \max_{z\ge 0}\ \sum_{(i,j)\in E} w_j z_{ij}\quad\text{s.t.}\quad \sum_j z_{ij}\le 1\ (i\in U),\quad \sum_i z_{ij}\le n_j\ (j\in V),
--   $$
--   and $\mathrm{OPT}(I)$ is its optimal value. It is the benchmark against which the competitive ratio of Definition 1 is measured.
--
--   **Formalization Note** $\mathrm{OPT}$ is a real supremum over a set that is nonempty and bounded above, so it is the true optimal value.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Definition 1, p.14; Primal-Dual-MWM, p.20

import Mathlib
import Definitions.Def_MultiStageAlloc_Instance

namespace MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

/-- **The feasible set of the offline primal LP**, the left program of (Primal-Dual-MWM),
arXiv:2211.16581v1, p.20: `z ≥ 0` carried by `E`, `∑_j z_ij ≤ 1` for each `i`, and
`∑_i z_ij ≤ n_j` for each `j`. At `n_j = 1` this is the printed LP. -/
def OfflineFeasible (I : Instance U V K) (z : U → V → ℝ) : Prop :=
  (∀ i j, 0 ≤ z i j) ∧ (∀ i j, z i j ≠ 0 → I.edge i j) ∧ (∀ i, ∑ j, z i j ≤ 1) ∧
    ∀ j, ∑ i, z i j ≤ I.cap j

/-- **The objective of the offline primal LP**, `∑_{(i,j) ∈ E} w_j z_ij`, arXiv:2211.16581v1, p.20. -/
def offlineValue (I : Instance U V K) (z : U → V → ℝ) : ℝ :=
  ∑ i, ∑ j, I.w j * z i j

/-- **The offline benchmark `OPT(I)`** of Definition 1, arXiv:2211.16581v1, p.14, taken as the optimal
value of the fractional offline LP of p.20.

**Formalization Note.** A real `sSup`. The set is nonempty (`z = 0`) and bounded above (each `z` has
`∑_j z_ij ≤ 1`, so its value is at most `∑_i max_j w_j`), so `sSup` is the true maximum value and not
Lean's default `0`. -/
noncomputable def OPT (I : Instance U V K) : ℝ :=
  sSup (offlineValue I '' {z | OfflineFeasible I z})

end MultiStageAlloc


