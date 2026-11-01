-- Prove2me | Definitions.Def_ParetoIneff_TieRule
-- name    : ParetoIneff_TieRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:56.076739+00:00
-- url     : https://prove2.me/theorems/af6dc20c-c00b-42ad-81b4-542b25b594e6
-- title:
--   Tie-breaking rule for $\mathcal{SP}_\alpha$
-- statement:
--   Definition 6 assigns each task to a machine in $\arg\min_{i\in N}s_{i,j}$, "breaking ties arbitrarily". A **tie-breaking rule** makes this choice explicit: for every number of tasks $m$, every task $j$ and every report vector for that task, it names a machine with the smallest report.
--
--   Every theorem about $\mathcal{SP}_\alpha$ in this mission holds for all such rules.
--
--   **Formalization Note** The rule sees only the reports for the task in question, which is what keeps the mechanism task-independent. It may depend on $m$ and on $j$.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Definition 6, p.16

import Mathlib

open NNReal

namespace ParetoIneff

/-- A **tie-breaking rule** for `𝒮𝒫_α`, Definition 6, arXiv:1809.03454v7, p.16 ("assigns the task
to the fastest machine `ι(j) ∈ argmin_{i∈N} s_{i,j}` (breaking ties arbitrarily)"): for every
number of tasks `m`, every task `j` and every vector of reports for that task, a machine with the
smallest report.

**Formalization Note** The rule sees only the reports for task `j` (it may depend on `m` and `j`),
which is what makes `𝒮𝒫_α` task-independent. Every theorem about `𝒮𝒫_α` quantifies over all
tie-breaking rules. -/
structure TieRule (n : ℕ) where
  /-- The machine chosen for task `j` of `m` at the reports `v` for that task. -/
  pick : (m : ℕ) → Fin m → (Fin n → ℝ≥0) → Fin n
  /-- The chosen machine has the smallest report. -/
  pick_min : ∀ (m : ℕ) (j : Fin m) (v : Fin n → ℝ≥0) (i : Fin n), v (pick m j v) ≤ v i

end ParetoIneff


