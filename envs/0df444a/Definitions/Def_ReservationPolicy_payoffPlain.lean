-- Prove2me | Definitions.Def_ReservationPolicy_payoffPlain
-- name    : ReservationPolicy_payoffPlain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:15.376508+00:00
-- url     : https://prove2.me/theorems/d39f78a9-e54f-4f24-b76b-ebbb35615189
-- title:
--   Payoff of a student who does not invest
-- statement:
--   A student who does not invest (every type-$y$ student, and a type-$x$ student who chooses not to) and exerts effort $e$, facing cutoff $d$ and reward $r$, has expected payoff
--   $$
--   \rho(\phi e,d)\,r-ke^2 .
--   $$
--   The student takes $d$ and $r$ as given.
--
--   **Formalization Note** $\rho$ is the true admission probability `admitProb`, which equals the paper's $(1-d+\phi e)/2$ when $|d-\phi e|<1$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (5), (6), (8), (17), pp.11–12, 19

import Mathlib
import Definitions.Def_ReservationPolicy_Params
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The expected payoff of a student who does not invest and exerts effort `e`, given the cutoff `d`
and the reward `r`: a type-`y` student, or a type-`x` student who does not invest. Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), eqs. (5), (6), (8), (17), pp.11, 12, 19 (PDF 11, 12, 19). -/
noncomputable def payoffPlain (P : Params) (d r e : ℝ) : ℝ :=
  admitProb (P.ϕ * e) d * r - P.k * e ^ 2

end ReservationPolicy


