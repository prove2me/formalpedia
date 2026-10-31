-- Prove2me | Definitions.Def_ReservationPolicy_admitProb
-- name    : ReservationPolicy_admitProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:06.076988+00:00
-- url     : https://prove2.me/theorems/2ad145d6-e451-42e2-899e-c98e0e295c17
-- title:
--   Admission probability $\Pr(m+\varepsilon>d)$
-- statement:
--   A student with mean ability $m$ has ability $m+\varepsilon$ and is admitted at cutoff $d$ exactly when her ability is higher than $d$. Her admission probability is
--   $$
--   \rho(m,d)=\Pr\bigl(m+\varepsilon>d\bigr),\qquad \varepsilon\sim U[-1,1].
--   $$
--   The mean ability is $e$ for a student who invests and $\phi e$ for one who does not, by (1).
--
--   This is the object from which the paper's linear formula (4) is derived.
--
--   **Formalization Note** The definition is the true probability, equal to $0$ or $1$ outside the noise support. Formula (4) is the theorem `eq_4`.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), pp.9–11

import Mathlib
import Definitions.Def_ReservationPolicy_noise

open MeasureTheory

namespace ReservationPolicy

/-- The probability that a student of mean ability `m` is admitted at cutoff `d`: the noise measure
of `{ε | d < m + ε}`, since the college "admits all students with tests scores higher than `d`".
Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), pp.9–11 (PDF 9–11).

**Formalization Note** This is the true, clipped probability, not the formula (4); (4) is the
theorem `eq_4`, valid when `|d − m| < 1`. The paper's mean ability is `m = e` if the student
invests and `m = ϕ e` otherwise, (1). -/
noncomputable def admitProb (m d : ℝ) : ℝ :=
  noise.real {ε | d < m + ε}

end ReservationPolicy


