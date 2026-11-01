-- Prove2me | Definitions.Def_RedundancyHT_cosCount
-- name    : RedundancyHT_cosCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:52.231202+00:00
-- url     : https://prove2.me/theorems/450acc0a-de30-4568-9125-52ecd6f876cd
-- title:
--   The number $Q_S$ of type-$S$ jobs in a c.o.s. state
-- statement:
--   In a state of the cancel-on-start queue, $Q_S$ counts all type-$S$ jobs present, whether waiting or in service. The heavy-traffic theorem is about this total count.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §3, p.9

import Definitions.Def_BipartiteMatchingHT_Delay_Queue

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **`Q_S` for c.o.s.**: the number of type-`i` jobs in the state, waiting or in service
(arXiv:2005.14566v5, §3, p.9).

**Formalization Note.** The published `QueueState` keeps the jobs in service, with
`server = some j`. The descriptor of (5) omits them, so `Q_S` is defined on the full state. -/
def cosCount {n m : ℕ} (q : QueueState n m) (i : Fin n) : ℕ :=
  q.jobs.countP (fun x => x.kind == i)

end RedundancyHT


