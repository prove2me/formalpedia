-- Prove2me | Definitions.Def_DimCallCenters_Constraint_gapCost
-- name    : DimCallCenters_Constraint_gapCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:37:27.539363+00:00
-- url     : https://prove2.me/theorems/9135cb78-abd9-4487-acbe-ef5e77fa08ab
-- title:
--   Rounding gap T_λ(x) of (32)
-- statement:
--   Fix a wait model, an arrival rate $\lambda > 0$, a constraint level $M_\lambda > 0$ and the optimal staffing level $N^*_\lambda$, the least integer $N > \lambda/\mu$ with $K(N,\lambda) \le M_\lambda$. For $x > 0$ the **rounding gap** is
--
--   $$T_\lambda(x) = \min\Big\{\,\big|K(\lfloor N_\lambda(x)\rfloor,\lambda) - M_\lambda\big|,\ \big|K(\lceil N_\lambda(x)\rceil,\lambda) - M_\lambda\big|,\ \big|K(\lceil N_\lambda(x)\rceil,\lambda) - K(N^*_\lambda,\lambda)\big|\,\Big\}.$$
--
--   It measures how well a staffing rule $x$, once $N_\lambda(x)$ is rounded down or up, meets the constraint, or how close it comes to the waiting cost of the optimal level. A staffing function $z_\lambda$ is called asymptotically optimal when $T_\lambda(z_\lambda)/M_\lambda \to 0$ as $\lambda \to \infty$.
--
--   **Formalization Note** The level $N^*_\lambda$ and the target $M_\lambda$ are arguments of the function. The first term is included only when $\lfloor N_\lambda(x)\rfloor > \lambda/\mu$, i.e. when rounding down still gives a stable staffing level at which $K$ is defined; otherwise the minimum is over the two ceiling terms. Omitting the term can only make $T_\lambda$ larger, so it never makes a statement about $T_\lambda$ easier. For $x > 0$ the ceiling $\lceil N_\lambda(x)\rceil$ always exceeds $\lambda/\mu$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 24, Section 8, Eq. (32)

import Mathlib
import Definitions.Def_DimCallCenters_Constraint_waitingCost
import Definitions.Def_DimCallCenters_Rationalized_servers

namespace DimCallCenters.Constraint

/-- The rounding gap `T_λ(x)` of (32), p. 24, for a given optimal level `N*_λ = Nst` and
constraint level `M_λ = m`:
`T_λ(x) = min{|K(⌊N_λ(x)⌋, λ) - M_λ|, |K(⌈N_λ(x)⌉, λ) - M_λ|, |K(⌈N_λ(x)⌉, λ) - K(N*_λ, λ)|}`.
Convention: the floor term is included only when `⌊N_λ(x)⌋ > λ/μ`, i.e. when it is a stable
staffing level at which `K` is defined; otherwise the minimum is over the two ceiling terms. -/
noncomputable def gapCost (M : DimCallCenters.Rationalized.WaitModel) (lam : ℝ) (Nst : ℕ) (m x : ℝ) : ℝ :=
  if lam / M.μ < (⌊DimCallCenters.Rationalized.servers M.μ lam x⌋₊ : ℝ) then
    min |waitingCost M ⌊DimCallCenters.Rationalized.servers M.μ lam x⌋₊ lam - m|
      (min |waitingCost M ⌈DimCallCenters.Rationalized.servers M.μ lam x⌉₊ lam - m|
        |waitingCost M ⌈DimCallCenters.Rationalized.servers M.μ lam x⌉₊ lam - waitingCost M Nst lam|)
  else
    min |waitingCost M ⌈DimCallCenters.Rationalized.servers M.μ lam x⌉₊ lam - m|
      |waitingCost M ⌈DimCallCenters.Rationalized.servers M.μ lam x⌉₊ lam - waitingCost M Nst lam|

end DimCallCenters.Constraint


