-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_servers
-- name    : DimCallCenters_Rationalized_servers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:04:07.000301+00:00
-- url     : https://prove2.me/theorems/5ecc5f17-c7bb-4bd7-abc1-c10461ba5346
-- title:
--   Square-root staffing level $N_\lambda(x)$
-- statement:
--   For service rate $\mu > 0$, arrival rate $\lambda > 0$ and $x \in \mathbb R$,
--
--   $$N_\lambda(x) = \frac{\lambda}{\mu} + x\sqrt{\lambda/\mu},$$
--
--   so that $x = (N - \lambda/\mu)/\sqrt{\lambda/\mu}$ is the normalized number of servers in excess of the offered load $\lambda/\mu$, the minimum needed for stability.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 11, Section 3, N_lambda(x)

import Mathlib

namespace DimCallCenters.Rationalized

/-- The staffing level `N_λ(x) = λ/μ + x √(λ/μ)` of p. 11, with `x` the normalized number of
servers in excess of the offered load `λ/μ`. -/
noncomputable def servers (μ lam x : ℝ) : ℝ :=
  lam / μ + x * Real.sqrt (lam / μ)

end DimCallCenters.Rationalized


