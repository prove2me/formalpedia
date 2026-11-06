-- Prove2me | Definitions.Def_MaxMinFracSched_density
-- name    : MaxMinFracSched_density
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:40.310388+00:00
-- url     : https://prove2.me/theorems/f8d76038-eb81-4d01-a5c4-f12d7f855f60
-- title:
--   Work density $\rho_J([L,R])$
-- statement:
--   For an instance $J$ and an interval $[L,R]$ with $L<R$,
--   $$\rho_J([L,R])=\frac{W_J([L,R])}{R-L}.$$
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 3.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_workIn

namespace MaxMinFracSched

/-- **The work density `ρ_J([L, R])`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 3.1 (Work density), p.12 (PDF p.14):
"ρJ(I) := WJ(I)/|I|".

`density J L R = W_J([L, R]) / (R − L)`.

**Formalization Note.** Only used for `L < R`. -/
noncomputable def density (J : Finset Job) (L R : ℝ) : ℝ :=
  workIn J L R / (R - L)

end MaxMinFracSched


