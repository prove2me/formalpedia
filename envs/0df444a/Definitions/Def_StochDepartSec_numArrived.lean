-- Prove2me | Definitions.Def_StochDepartSec_numArrived
-- name    : StochDepartSec_numArrived
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:11.478982+00:00
-- url     : https://prove2.me/theorems/589e791e-180c-48d2-b28a-801e424a7cec
-- title:
--   Number of arrivals $K_t$ up to time $t$
-- statement:
--   For a time $t$, $K_t(\omega)=\#\{i : a_i\le t\}$ is the number of candidates that have arrived up to and including time $t$.
--
--   **Formalization Note** Arrivals at time exactly $t$ are counted. Definition 3 says both "arrived up to time $t$" and "arrived prior to $t$"; the closed reading follows §3.2 (p.8), where the arrivals after $t$ are drawn from $\mathcal A$ conditioned on $(t,1]$.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Definition 3, p.6; §3.2, p.8

import Mathlib
import Definitions.Def_StochDepartSec_Outcome

namespace StochDepartSec

/-- `K_t`: the number of candidates that have arrived up to and including time `t`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Definition 3, p.6: "K_t, the number of candidates that have arrived up to time t"; §3.2, p.8:
the future after t is drawn "from A conditioned on (t, 1]".

**Formalization Note** Arrivals at time exactly `t` count (`a i ≤ t`). Definition 3 also says
"arrived prior to t"; the closed reading is fixed by p.8, where the arrivals after `t` are drawn
from `(t, 1]`. -/
noncomputable def numArrived {n : ℕ} (ω : Outcome n) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin n => arrival ω i ≤ t).card

end StochDepartSec


