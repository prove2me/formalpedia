-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_waitCost
-- name    : DimCallCenters_Rationalized_waitCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:25:18.333437+00:00
-- url     : https://prove2.me/theorems/ce446c6a-3e86-4426-9361-63185cfc4a23
-- title:
--   Conditional expected waiting cost $G(N,\lambda)$
-- statement:
--   Let $\mu > 0$ and $(D_\lambda)$ be as in the standing assumptions. For a real staffing level $N > \lambda/\mu$, the **conditional expected waiting cost** of a delayed customer is
--
--   $$G(N,\lambda) = (N\mu-\lambda)\int_0^\infty D_\lambda(t)\,e^{-(N\mu-\lambda)t}\,dt,$$
--
--   the expectation of $D_\lambda$ under the exponential waiting-time law of rate $N\mu - \lambda$. The paper notes that $G$ is defined for non-integer $N > \lambda/\mu$ as well.
--
--   **Formalization Note** $N$ is real. For $N \le \lambda/\mu$ the expression has no meaning in the paper; its Lean value there is never used.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 11, Section 2, definition of G(N, lambda)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_WaitModel

namespace DimCallCenters.Rationalized

/-- The conditional expected waiting cost `G(N, λ) = (Nμ - λ) ∫_0^∞ D_λ(t) e^{-(Nμ-λ)t} dt` of
p. 11, for real `N`. Meaningful for `N > λ/μ`, where the integrand is integrable by
`WaitModel.hDint`. -/
noncomputable def waitCost (M : WaitModel) (N lam : ℝ) : ℝ :=
  (N * M.μ - lam) * ∫ t in Set.Ioi 0, M.D lam t * Real.exp (-(N * M.μ - lam) * t)

end DimCallCenters.Rationalized


