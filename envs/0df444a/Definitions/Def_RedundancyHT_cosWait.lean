-- Prove2me | Definitions.Def_RedundancyHT_cosWait
-- name    : RedundancyHT_cosWait
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:14.42007+00:00
-- url     : https://prove2.me/theorems/9bbe38b5-6170-40bc-a4f7-3205c8e06a40
-- title:
--   The number $\tilde Q_S$ of waiting type-$S$ jobs in a c.o.s. state
-- statement:
--   In a state of the cancel-on-start queue, $\tilde Q_S$ counts the type-$S$ jobs that have not started service.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §3, p.9

import Definitions.Def_BipartiteMatchingHT_Delay_Queue

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **`Q̃_S` for c.o.s.**: the number of waiting type-`i` jobs in the state
(arXiv:2005.14566v5, §3, p.9). -/
def cosWait {n m : ℕ} (q : QueueState n m) (i : Fin n) : ℕ :=
  q.jobs.countP (fun x => x.kind == i && x.server.isNone)

end RedundancyHT


