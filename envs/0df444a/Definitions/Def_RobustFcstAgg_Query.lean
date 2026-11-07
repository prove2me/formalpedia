-- Prove2me | Definitions.Def_RobustFcstAgg_Query
-- name    : RobustFcstAgg_Query
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:16.413215+00:00
-- url     : https://prove2.me/theorems/0d6cde1b-4d7f-4cad-aed1-9db3ebaa3b8d
-- title:
--   Query: a function $Q(S_i,\mathcal D)$ of one expert\'s information
-- statement:
--   A **query** is assigned to an expert $\mathrm{agent}(Q)=i\in[n]$ and is a function $Q:(S_i,\mathcal D)\to\mathbb R$ of that expert's information and of the instance, which the experts know.
--
--   **Formalization Note** The type of the function is what stops a query from reading the signal of another expert. No measurability is bundled here; on an eliciting graph it follows almost everywhere from Condition 1.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.1, p.4

import Mathlib
import Definitions.Def_RobustFcstAgg_InfoStruct
import Definitions.Def_RobustFcstAgg_AgentSig

namespace RobustFcstAgg

/-- **Query.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.1, p.4: "each `Q ∈ 𝒬` is assigned to an expert `agent(Q) ∈ [n]`. A query with
`agent(Q) = i` is a function `Q : (S_i, D) → ℝ`".

**Formalization Note.** The type of `eval` is what stops a query from reading another expert's signal.
`eval` may depend on `D`, which the experts know; the principal does not (see `Rule`). No measurability
is bundled: on a DAG it follows a.e. from Condition 1 (`SatisfiesCondition1`). -/
structure Query (n : ℕ) where
  /-- The expert answering the query. -/
  agent : Fin n
  /-- The answer, as a function of the instance and the expert's signal. -/
  eval : InfoStruct n → (AgentSig agent → ℝ) → ℝ

end RobustFcstAgg


