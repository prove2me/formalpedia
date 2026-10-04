-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_Flam
-- name    : DimCallCenters_Rationalized_Flam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:26:33.700983+00:00
-- url     : https://prove2.me/theorems/95034250-ceb0-462e-808f-c83aa9df64f6
-- title:
--   Normalized staffing cost $F_\lambda(x)$
-- statement:
--   For a staffing-cost function $F$, service rate $\mu$, arrival rate $\lambda$ and $x \in \mathbb R$,
--
--   $$F_\lambda(x) = F(N_\lambda(x)) - F(\lambda/\mu),$$
--
--   the staffing cost in excess of the cost $F(\lambda/\mu)$ of the minimum stable level.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 11, Section 3, F_lambda(x)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_servers

namespace DimCallCenters.Rationalized

/-- The normalized staffing cost `F_λ(x) = F(N_λ(x)) - F(λ/μ)` of p. 11. -/
noncomputable def Flam (F : ℝ → ℝ) (μ lam x : ℝ) : ℝ :=
  F (servers μ lam x) - F (lam / μ)

end DimCallCenters.Rationalized


