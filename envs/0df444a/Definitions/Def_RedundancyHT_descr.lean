-- Prove2me | Definitions.Def_RedundancyHT_descr
-- name    : RedundancyHT_descr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:44.447758+00:00
-- url     : https://prove2.me/theorems/6605735a-2d54-457c-a839-db46d0be5b77
-- title:
--   The state descriptor $(c;u)$ of the c.o.s. queue
-- statement:
--   The descriptor of a state of the cancel-on-start queue is the pair $(c_1,\dots,c_{\tilde M};u_1,\dots,u_L)$: $c_m$ is the type of the $m$th oldest waiting job and $u_l$ the $l$th longest idle server. It omits the jobs in service.
--
--   **Formalization Note** The list $u$ contains the useful servers only. If every server is useful, this is the descriptor of the paper. A server compatible with no job type stays idle forever and has no effect on the jobs.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.3.2, p.8

import Definitions.Def_BipartiteMatchingHT_Delay_Queue
import Definitions.Def_RedundancyHT_useful

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay Classical
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The state descriptor `(c₁,…,c_{M̃}; u₁,…,u_L)` of p.8** (arXiv:2005.14566v5): the types of the
waiting jobs, oldest first, and the idle servers, longest idle first.

**Formalization Note.** The published `QueueState` keeps jobs in arrival order and its `idle` list
longest idle first. The list `u` keeps the useful servers only: a server compatible with no type is
idle forever, it has no effect on the jobs, and it would make `λ_𝒞` vanish in (5). If every server is
useful, `u` is the printed list. -/
def descr {n m : ℕ} (D : Model n m) (q : QueueState n m) : List (Fin n) × List (Fin m) :=
  ((q.jobs.filter (fun x => x.server.isNone)).map (fun x => x.kind),
    q.idle.filter (fun j => decide (useful D j)))

end RedundancyHT


