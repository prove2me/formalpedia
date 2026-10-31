-- Prove2me | Definitions.Def_MultiServerAppt_clientCount
-- name    : MultiServerAppt_clientCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:53.696932+00:00
-- url     : https://prove2.me/theorems/748d9cf8-db44-4d2b-8fe4-d7ceb46fa8fd
-- title:
--   The number $j$ of clients in a state
-- statement:
--   For a state $(j,m)$ this is $j$: it equals $s+1+q$ on a saturated state $(q,m)$ and $\xi+1$ on an unsaturated state $(\xi,m)$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11

import Mathlib
import Definitions.Def_MultiServerAppt_State

namespace MultiServerAppt

/-- The coordinate `j` of a state: the number of clients in the system. Kuiper–Lee, Appointment
Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11. -/
def clientCount {ι : Type*} {s i : ℕ} : State ι s i → ℕ
  | .inl p => s + 1 + p.1
  | .inr p => p.1 + 1

end MultiServerAppt


