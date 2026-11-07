-- Prove2me | Definitions.Def_RobustFcstAgg_AgentLE
-- name    : RobustFcstAgg_AgentLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:13.441801+00:00
-- url     : https://prove2.me/theorems/ef680a07-2b1d-4eb7-8db6-2a1b42f1d298
-- title:
--   Agent complexity at most $d$ on a DAG: $\max_Q|I^*_G(Q)|\le d$
-- statement:
--   $I^*_G(Q)=\{\mathrm{agent}(Q'):Q'\in N^*_G(Q)\}$ is the set of experts whose beliefs are relevant to $Q$, where $N^*_G(Q)$ is the set of queries reachable from $Q$, including $Q$. This predicate says that $\max_Q|I^*_G(Q)|\le d$. Experts are counted, not queries.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.2, p.6

import Mathlib
import Definitions.Def_RobustFcstAgg_Query
import Definitions.Def_RobustFcstAgg_Reachable

namespace RobustFcstAgg

/-- **Agent complexity at most `d` on a DAG: `max_Q |I*_G(Q)| ≤ d`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.2, p.6:
"`I*_G(Q) := {agent(Q′) : Q′ ∈ N*_G(Q)}`".

**Formalization Note.** `Q` itself is counted, `Y` is not, and experts are counted rather than queries. `Set.ncard` is
the true cardinality here, since the set lies in the finite type `Fin n`. -/
def AgentLE {n : ℕ} {ι : Type} (Q : ι → Query n) (out : ι → Finset (Option ι)) (d : ℕ) : Prop :=
  ∀ j, {i : Fin n | ∃ j', Reachable out j j' ∧ (Q j').agent = i}.ncard ≤ d

end RobustFcstAgg


