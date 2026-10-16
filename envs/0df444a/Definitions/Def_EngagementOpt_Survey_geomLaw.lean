-- Prove2me | Definitions.Def_EngagementOpt_Survey_geomLaw
-- name    : EngagementOpt_Survey_geomLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:55.02803+00:00
-- url     : https://prove2.me/theorems/2b34e60d-e061-4d5b-b5ee-9c302cd9bdbb
-- title:
--   Geometric law on $\{1,2,\dots\}$ with continuation probability $r$
-- statement:
--   For a continuation probability $r$ and $k\in\{0,1,2,\dots\}$, define
--
--   $$
--   g_r(k)=\begin{cases} r^{k-1}(1-r), & k\ge 1,\\ 0, & k=0.\end{cases}
--   $$
--
--   For $r\in[0,1)$ this is the law of the number of steps of a run that, after each step, continues with probability $r$ and stops with probability $1-r$: the distribution $\mathrm{Geom}(1-r)$ on $\{1,2,\dots\}$. In the model of Kleinberg, Mullainathan and Raghavan, system 2's interest span $T_q$ has law $g_q$ and system 1's tail run $T_p=T-T_q+1$ has law $g_p$.
--
--   **Formalization Note** The value at $k=0$ is set to $0$ explicitly, so that the natural-number exponent $k-1$ is never evaluated outside the support.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 19 (T_q ∼ Geom(1−q), T − T_q + 1 ∼ Geom(1−p)); p. 7 (the two phases)

import Mathlib

namespace EngagementOpt.Survey

/-- The geometric law on `{1, 2, …}` with continuation probability `r`: the probability that a
run which continues after each step with probability `r` (and stops with probability `1 - r`)
lasts exactly `k` steps, `Pr[X = k] = r ^ (k - 1) * (1 - r)` for `k ≥ 1`, and `0` for `k = 0`.
This is `Geom(1 - r)` in the notation of Kleinberg–Mullainathan–Raghavan, arXiv:2202.11776v3,
p. 19. -/
noncomputable def geomLaw (r : ℝ) (k : ℕ) : ℝ :=
  if 1 ≤ k then r ^ (k - 1) * (1 - r) else 0

end EngagementOpt.Survey


