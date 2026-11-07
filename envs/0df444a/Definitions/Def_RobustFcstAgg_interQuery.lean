-- Prove2me | Definitions.Def_RobustFcstAgg_interQuery
-- name    : RobustFcstAgg_interQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:16.210432+00:00
-- url     : https://prove2.me/theorems/6eacb31f-642e-4ebf-bd0d-d05a8e86bbd5
-- title:
--   Intersection query
-- statement:
--   The **intersection query** for a nonempty $S$ asks an expert of $S$ for $\mathrm{inter}(S)=\sum_{T\supseteq S}X_T$. Each such $T$ contains the expert, so the answer is a sum of the signals that expert observes.
--
--   **Formalization Note** The expert is $\min S$. The source needs only an expert in $S$, and any choice gives the same random variable and the same complexities. The answer does not depend on $\mathcal D$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 3.1, p.9; proof of Proposition 2, p.9

import Mathlib
import Definitions.Def_RobustFcstAgg_Query

namespace RobustFcstAgg

/-- **Intersection query.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 3.1, p.9: `inter(S) = Σ_{T ⊇ S} X_T`, answered by an expert of `S`.

**Formalization Note.** The agent is `S.min'`: the source only needs `agent ∈ S` (proof of Proposition 2, p.9), and every
choice gives the same random variable and the same complexities. Every `T ⊇ S` contains the agent, so the sum runs over
coordinates the agent sees. The answer does not depend on `D`. -/
def interQuery {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : Query n where
  agent := S.min' hS
  eval := fun _ s => ∑ T : AgentSig (S.min' hS) with S ⊆ T.1.1, s T

end RobustFcstAgg


