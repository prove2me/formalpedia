-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_piLam
-- name    : DimCallCenters_Rationalized_piLam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:26:25.394351+00:00
-- url     : https://prove2.me/theorems/6dc6a7a2-61fa-4c4c-8a3c-8edb478659c1
-- title:
--   Continuous delay probability $\pi_\lambda(x)$
-- statement:
--   For service rate $\mu$, arrival rate $\lambda$ and $x > 0$,
--
--   $$\pi_\lambda(x) = H(N_\lambda(x), \lambda/\mu),$$
--
--   the continuous extension of the probability of waiting at the staffing level $N_\lambda(x)$. It equals $\pi(N_\lambda(x),\lambda/\mu)$ when $N_\lambda(x)$ is an integer.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, pi_lambda(x)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_servers
import Definitions.Def_DimCallCenters_Rationalized_contErlangC

namespace DimCallCenters.Rationalized

/-- The continuous delay probability `π_λ(x) = H(N_λ(x), λ/μ)` of p. 12. -/
noncomputable def piLam (μ lam x : ℝ) : ℝ :=
  contErlangC (servers μ lam x) (lam / μ)

end DimCallCenters.Rationalized


