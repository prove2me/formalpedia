-- Prove2me | Definitions.Def_ReusableMatching_reward
-- name    : ReusableMatching_reward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:34.125865+00:00
-- url     : https://prove2.me/theorems/d29d6cda-f44d-4576-83a4-68944671f3a3
-- title:
--   The reward of Periodic Reranking
-- statement:
--   For a seed vector $Y$, the **reward** of Periodic Reranking is
--
--   $$
--   \sum_{(i,t)\in \mathrm{PR}(Y)} r_i,
--   $$
--
--   the total weight of the resources matched, counted once per match (an unmatched arrival contributes $0$). Its expectation over the seeds is the quantity compared with $\mathrm{OPT}$.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, p.3 ("obtains a reward of r_i each time the offline node i gets matched")

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking

namespace ReusableMatching

/-- **The reward of Periodic Reranking** for the seed vector `Y` (arXiv:2110.07084v2, p.3: "an
algorithm for this problem obtains a reward of `r_i` each time the offline node `i` gets matched"):
the sum, over the arrivals `t`, of the weight `r_i` of the resource `i` matched to `t` (`0` for an
unmatched arrival). -/
noncomputable def reward {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) : ℝ :=
  ∑ t : Fin n, (PeriodicReranking I β Y t).elim 0 I.r

end ReusableMatching


