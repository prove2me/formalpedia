-- Prove2me | Definitions.Def_ReservationPolicy_plainEfforts
-- name    : ReservationPolicy_plainEfforts
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:39.869186+00:00
-- url     : https://prove2.me/theorems/2ba10b05-2edc-4374-8e47-c03d181970fb
-- title:
--   Efforts of a non-investing student with uncertain admission
-- statement:
--   For a cutoff $d$, the efforts available to a student who does not invest are
--   $$
--   \{e\ge 0:\ 0<\rho(\phi e,d)<1\}.
--   $$
--   This is the regime in which formula (4) holds for such a student.
--
--   **Formalization Note** The same conventions as `investEfforts`.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), pp.8–11

import Mathlib
import Definitions.Def_ReservationPolicy_Params
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The efforts open to a non-investing student at cutoff `d`: `0 ≤ e`, with admission probability
strictly between `0` and `1`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), pp.8–11 (PDF 8–11).

**Formalization Note** The same two readings as `investEfforts`. -/
def plainEfforts (P : Params) (d : ℝ) : Set ℝ :=
  {e | 0 ≤ e ∧ 0 < admitProb (P.ϕ * e) d ∧ admitProb (P.ϕ * e) d < 1}

end ReservationPolicy


