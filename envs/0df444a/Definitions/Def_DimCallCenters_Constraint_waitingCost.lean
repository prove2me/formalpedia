-- Prove2me | Definitions.Def_DimCallCenters_Constraint_waitingCost
-- name    : DimCallCenters_Constraint_waitingCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:57:32.902975+00:00
-- url     : https://prove2.me/theorems/cf75e29e-f7b0-46e2-951a-3eebb42df572
-- title:
--   Waiting cost K(N, λ) = λ π(N, λ/μ) G(N, λ)
-- statement:
--   For a wait model, an integer staffing level $N$ and an arrival rate $\lambda > 0$ with $N > \lambda/\mu$, the **waiting cost** per unit of time is
--
--   $$K(N,\lambda) = \lambda\,\pi(N,\lambda/\mu)\,G(N,\lambda),$$
--
--   the arrival rate times the expected waiting cost $E\,D_\lambda(\mathrm{Wait})$ of one customer. Section 8 staffs the system with the fewest servers that keep $K(N,\lambda)$ below a target $M_\lambda$.
--
--   **Formalization Note** $N \in \mathbb N$; the formula is evaluated literally for $N \le \lambda/\mu$, a range the mission never uses.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 24, Section 8, definition of K(N, λ) after (31)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_waitCost

namespace DimCallCenters.Constraint

/-- The waiting cost `K(N, λ) = λ π(N, λ/μ) G(N, λ)` of Section 8 (p. 24), at an integer
staffing level `N`. -/
noncomputable def waitingCost (M : DimCallCenters.Rationalized.WaitModel) (N : ℕ) (lam : ℝ) : ℝ :=
  lam * DimCallCenters.Rationalized.erlangC N (lam / M.μ) * DimCallCenters.Rationalized.waitCost M N lam

end DimCallCenters.Constraint


