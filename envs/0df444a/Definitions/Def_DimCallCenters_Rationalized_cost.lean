-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_cost
-- name    : DimCallCenters_Rationalized_cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:53:56.084947+00:00
-- url     : https://prove2.me/theorems/08c6ff36-6526-4294-9a9d-1f35892e5b57
-- title:
--   Expected total cost $C(N,\lambda)$
-- statement:
--   For an integer staffing level $N > \lambda/\mu$, a staffing-cost function $F$ and the model $(\mu, D_\lambda)$, the **expected total cost per unit of time** is
--
--   $$C(N,\lambda) = F(N) + \lambda\,\pi(N,\lambda/\mu)\,G(N,\lambda),$$
--
--   the staffing cost plus the arrival rate times the expected waiting cost per customer, $\pi(N,\lambda/\mu)$ being the probability of waiting and $G(N,\lambda)$ the conditional expected waiting cost.
--
--   **Formalization Note** $N$ is a natural number; the value for $N \le \lambda/\mu$ is never used: optimal levels $N^*_\lambda$ are always quantified over $N > \lambda/\mu$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 11, Section 2, display C(N, lambda) = F(N) + lambda pi(N, lambda/mu) G(N, lambda)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_waitCost

namespace DimCallCenters.Rationalized

/-- The expected total cost per unit time `C(N, λ) = F(N) + λ π(N, λ/μ) G(N, λ)` of p. 11, for an
integer staffing level `N`. Meaningful for `N > λ/μ`. -/
noncomputable def cost (M : WaitModel) (F : ℝ → ℝ) (N : ℕ) (lam : ℝ) : ℝ :=
  F N + lam * erlangC N (lam / M.μ) * waitCost M N lam

end DimCallCenters.Rationalized


