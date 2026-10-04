-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_Glam
-- name    : DimCallCenters_Rationalized_Glam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:54:20.083156+00:00
-- url     : https://prove2.me/theorems/650d8201-731d-4513-9f7b-5a22b592a9b0
-- title:
--   Normalized waiting cost $G_\lambda(x)$
-- statement:
--   For the model $(\mu, D_\lambda)$, arrival rate $\lambda$ and $x$,
--
--   $$G_\lambda(x) = \lambda\, G(N_\lambda(x),\lambda),$$
--
--   the rate at which waiting cost accrues if every customer were delayed, at the staffing level $N_\lambda(x)$. Meaningful for $x > 0$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 11, Section 3, G_lambda(x)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_servers
import Definitions.Def_DimCallCenters_Rationalized_waitCost

namespace DimCallCenters.Rationalized

/-- The normalized waiting cost `G_λ(x) = λ G(N_λ(x), λ)` of p. 11. -/
noncomputable def Glam (M : WaitModel) (lam x : ℝ) : ℝ :=
  lam * waitCost M (servers M.μ lam x) lam

end DimCallCenters.Rationalized


