-- Prove2me | Definitions.Def_AlmostMMS_rhoQN
-- name    : AlmostMMS_rhoQN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:39.706596+00:00
-- url     : https://prove2.me/theorems/697c1060-a407-4b39-930d-b08aae9142c0
-- title:
--   Theorem 3.3, pp.25–26 — $\gamma$, $\lambda$ and $\rho_{q,n}$
-- statement:
--   The parameters of the case split between a large and a small average tail: $\gamma=\min(\varepsilon,1/(2q))$, $\lambda=2q/(2q-1)=(1-1/(2q))^{-1}$, and
--   $$
--   \rho_{q,n}=8+4\log_\lambda\big(q^3d^2(d+2)n\big)+8q\log\big((d+2)n\big),
--   $$
--   with $\log$ base $2$.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 3.3, pp.25–26; Corollary 5.1, p.39

import Mathlib

namespace AlmostMMS

open Finset

/-- `γ = min(ε, 1/(2q))` (Theorem 3.3, p.25).
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…). -/
noncomputable def gammaQ (ε : ℝ) (q : ℕ) : ℝ :=
  min ε (1 / (2 * (q : ℝ)))

/-- `λ = 2q/(2q - 1)` (Theorem 3.3, p.25), which equals `(1 - 1/(2q))⁻¹` (Corollary 5.1, p.39). -/
noncomputable def lambdaQ (q : ℕ) : ℝ :=
  2 * (q : ℝ) / (2 * (q : ℝ) - 1)

/-- `ρ_{q,n} = 8 + 4 log_λ(q³ d² (d + 2) n) + 8q log((d + 2) n)` (Theorem 3.3, p.26), with `log` base
`2`. -/
noncomputable def rhoQN (q d n : ℕ) : ℝ :=
  8 + 4 * Real.logb (lambdaQ q) ((q : ℝ) ^ 3 * (d : ℝ) ^ 2 * ((d : ℝ) + 2) * (n : ℝ))
    + 8 * (q : ℝ) * Real.logb 2 (((d : ℝ) + 2) * (n : ℝ))

end AlmostMMS


