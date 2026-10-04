-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_staffCost
-- name    : DimCallCenters_Rationalized_staffCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:17:40.409163+00:00
-- url     : https://prove2.me/theorems/9472c177-8fad-4f8c-9c33-1a494997df29
-- title:
--   Cost of rounding to the cheaper neighbour, $S_\lambda(x)$
-- statement:
--   For $x > 0$, the cost of staffing at the cheaper of the two integers next to $N_\lambda(x)$ is
--
--   $$S_\lambda(x) = \min\{C(\lfloor N_\lambda(x)\rfloor,\lambda),\ C(\lceil N_\lambda(x)\rceil,\lambda)\},$$
--
--   display (10). A staffing function $z_\lambda$ is asymptotically optimal when $S_\lambda(z_\lambda) - F(\lambda/\mu)$ is asymptotically equal to the optimal excess cost $C(N^*_\lambda,\lambda) - F(\lambda/\mu)$.
--
--   **Formalization Note** When $\lfloor N_\lambda(x)\rfloor \le \lambda/\mu$ the floor is not a stable staffing level and $C(\lfloor N_\lambda(x)\rfloor,\lambda)$ is undefined; the term is then omitted and $S_\lambda(x) = C(\lceil N_\lambda(x)\rceil,\lambda)$. Without this convention a junk value at an unstable level could undercut the optimum.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 13, Section 3, Eq. (10)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_servers
import Definitions.Def_DimCallCenters_Rationalized_cost

namespace DimCallCenters.Rationalized

/-- The cost of rounding `N_λ(x)` to the cheaper neighbouring integer, (10) on p. 13:
`S_λ(x) = min {C(⌊N_λ(x)⌋, λ), C(⌈N_λ(x)⌉, λ)}`. Convention: when `⌊N_λ(x)⌋ ≤ λ/μ` the floor
is not a stable staffing level and `C(⌊N_λ(x)⌋, λ)` is undefined, so it is omitted and
`S_λ(x) = C(⌈N_λ(x)⌉, λ)`. -/
noncomputable def staffCost (M : WaitModel) (F : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  if (⌊servers M.μ lam x⌋₊ : ℝ) ≤ lam / M.μ then cost M F ⌈servers M.μ lam x⌉₊ lam
  else min (cost M F ⌊servers M.μ lam x⌋₊ lam) (cost M F ⌈servers M.μ lam x⌉₊ lam)

end DimCallCenters.Rationalized


