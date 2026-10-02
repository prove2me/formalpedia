-- Prove2me | Definitions.Def_NumStochOpt_ListScheduling_FirstStage
-- name    : NumStochOpt_ListScheduling_FirstStage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T20:57:24.47195+00:00
-- url     : https://prove2.me/theorems/55374f73-6e16-48d6-917b-2b6f0594f181
-- title:
--   The cost estimate $Z'_n(m) = cm + n\mu/m$ and the heuristic first-stage decision $m^{H1}$
-- statement:
--   This file fixes the heuristic first-stage decision of the machine investment problem.
--
--   Machines cost $c > 0$ each and the jobs have mean processing time $\mu > 0$. Replacing the expected optimal makespan by its asymptotic value $n\mu/m$ gives the estimate of the two-stage cost
--
--   $$
--   Z'_n(m) = cm + \frac{n\mu}{m}.
--   $$
--
--   Over the positive reals $Z'_n$ is minimized at $\sqrt{n\mu/c}$. The **heuristic first-stage decision** $m^{H1}$ is whichever of $\lfloor \sqrt{n\mu/c}\rfloor$ and $\lceil \sqrt{n\mu/c}\rceil$ gives the smaller value of $Z'_n$.
--
--   This is the number of machines bought by the two-stage heuristic whose asymptotic clairvoyance is stated on p. 211.
--
--   **Formalization Note** `approxCost c μ n m` is $Z'_n(m)$ for a natural number $m$. `firstStageMachines c μ n` returns the floor when $Z'_n(\lfloor\cdot\rfloor) \le Z'_n(\lceil\cdot\rceil)$ (so ties go to the floor) and the ceiling otherwise; when the floor is $0$ (not a meaningful machine count) it returns the ceiling. For $n = 0$ the value is $0$, which plays no role in the asymptotic statements.
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, §8.3, p. 210, Z'_n(m) and m^{H1}

import Mathlib

namespace NumStochOpt.ListScheduling

/-- The estimate `Z'_n(m) = c m + n μ / m` of the two-stage cost of buying `m` machines at
cost `c` each (Rinnooy Kan–Stougie, Ch. 8 of Ermoliev & Wets (1988), p. 210). -/
noncomputable def approxCost (c μ : ℝ) (n m : ℕ) : ℝ :=
  c * m + n * μ / m

/-- The heuristic first-stage decision `m^{H1}`: the better (for `Z'_n`) of
`⌊√(nμ/c)⌋` and `⌈√(nμ/c)⌉`, the floor on a tie; the ceiling when the floor is `0`. -/
noncomputable def firstStageMachines (c μ : ℝ) (n : ℕ) : ℕ :=
  if ⌊Real.sqrt (n * μ / c)⌋₊ = 0 then ⌈Real.sqrt (n * μ / c)⌉₊
  else if approxCost c μ n ⌊Real.sqrt (n * μ / c)⌋₊ ≤ approxCost c μ n ⌈Real.sqrt (n * μ / c)⌉₊
    then ⌊Real.sqrt (n * μ / c)⌋₊
  else ⌈Real.sqrt (n * μ / c)⌉₊

end NumStochOpt.ListScheduling


