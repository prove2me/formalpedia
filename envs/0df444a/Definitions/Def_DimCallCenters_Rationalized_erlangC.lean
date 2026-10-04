-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_erlangC
-- name    : DimCallCenters_Rationalized_erlangC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:03:52.752993+00:00
-- url     : https://prove2.me/theorems/fa195c98-4144-4e2d-a8db-df0460164182
-- title:
--   Erlang-C formula $\pi(N,\nu)$
-- statement:
--   For an integer number of servers $N \ge 1$ and offered load $\nu = \lambda/\mu$ with $0 < \nu < N$, the **probability of waiting** in the M/M/N queue is the Erlang-C formula
--
--   $$\pi(N,\nu) = \frac{\nu^N}{N!}\left\{\left(1-\frac{\nu}{N}\right)\sum_{n=0}^{N-1}\frac{\nu^n}{n!} + \frac{\nu^N}{N!}\right\}^{-1}.$$
--
--   It is the factor $\pi(N,\lambda/\mu)$ in the expected total cost $C(N,\lambda)$.
--
--   **Formalization Note** The formula is transcribed in exactly the shape of p. 10. It is only meaningful for $0<\nu<N$; every use in the mission is at such arguments.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 10, Section 2, formula for pi(N, nu)

import Mathlib

namespace DimCallCenters.Rationalized

/-- The Erlang-C delay probability `π(N, ν)` of p. 10:
`π(N, ν) = (ν^N / N!) {(1 - ν/N) ∑_{n=0}^{N-1} ν^n/n! + ν^N/N!}⁻¹`.
Meaningful for `0 < ν < N`. -/
noncomputable def erlangC (N : ℕ) (ν : ℝ) : ℝ :=
  ν ^ N / (N.factorial : ℝ) *
    ((1 - ν / (N : ℝ)) * ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)
      + ν ^ N / (N.factorial : ℝ))⁻¹

end DimCallCenters.Rationalized


