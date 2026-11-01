-- Prove2me | Definitions.Def_AndOrSched_worstCost
-- name    : AndOrSched_worstCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:40.781891+00:00
-- url     : https://prove2.me/theorems/0b150ea2-e3ce-4459-88d1-65b8dab69e9a
-- title:
--   Worst-case cost over tie-breakings
-- statement:
--   For given sort keys, the largest cost $\sum_j w_jC_j$ of the schedule of an order compatible with the keys. It is a maximum over a finite set when that set is nonempty. A bound on its expectation over $\beta$ bounds the expected cost for every way of breaking the remaining ties.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, "Break all other ties arbitrarily"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
open scoped Classical NNReal

namespace AndOrSched

/-- The largest cost of a schedule that Algorithm 1 or 2 may return for a fixed realization of `β`
(Happach, Schulz, arXiv:2001.07011v1, §2, p.7, "Break all other ties arbitrarily"): the maximum of `Σ wⱼ Cⱼ` over all orders
compatible with the sort keys `key`.

**Formalization Note** This is a supremum over a finite set of orders, so it is a maximum whenever
some compatible order exists (which the milestones assert). Bounding its expectation bounds the
expected cost of every tie-breaking at once. -/
noncomputable def worstCost (I : Instance) (key : I.N → ℕ) : ℝ :=
  ⨆ σ : {σ : I.N ≃ Fin (Fintype.card I.N) // Compat I key σ}, cost I (listC I σ.1)

end AndOrSched


