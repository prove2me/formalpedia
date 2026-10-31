-- Prove2me | Definitions.Def_PCLAssort_tildeEdges
-- name    : PCLAssort_tildeEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:49.62804+00:00
-- url     : https://prove2.me/theorems/7d1dcf5e-e871-4812-bb14-56cd16d6edf3
-- title:
--   Edge set of the subgraph $\tilde G_z$
-- statement:
--   The subgraph $\tilde G_z$ of $G_z$ consists of all edges of nonnegative weight:
--
--   $$
--   \tilde E_z=\{e\in E: w_e(z)\ge 0\}.
--   $$
--
--   It contains all edges leaving vertices $i$ with $r_i\ge z$, and is the graph on which the rounding algorithm runs.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §3, p.791 (PDF p.7)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight

namespace PCLAssort

/-- Edge set of the subgraph `G̃_z` of `G_z` consisting of all nonnegative-weight edges (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §3,
pp.790–791). -/
noncomputable def tildeEdges {n : ℕ} (I : PCLInstance n) (z : ℝ) : Finset (Option (Fin n) × Option (Fin n)) :=
  (pclEdges n).filter (fun e => 0 ≤ pclWeight I z e)

end PCLAssort


