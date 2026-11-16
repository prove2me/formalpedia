-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_epsRho
-- name    : ParetoNCSched_Supplement_epsRho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:33:16.000482+00:00
-- url     : https://prove2.me/theorems/48af3ad4-f88d-4a99-b59b-be9bf414e1ed
-- title:
--   The consistency excess $\varepsilon(\rho)$
-- statement:
--   For $\rho>0$,
--
--   $$\varepsilon(\rho)=\int_0^1\frac{v^2}{v^2+3\rho v+\rho^2}\,dv,$$
--
--   the expectation of the random fraction $B=V^2/(V^2+3\rho V+\rho^2)$ for $V$ uniform on $(0,1)$. $\mathrm{RT}_\rho$ is $(1+\varepsilon(\rho))$-consistent.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem 1.3, p.4; (25), p.40

import Mathlib

namespace ParetoNCSched.Supplement

/-- **The consistency excess `ε(ρ)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem 1.3, p.4, and (25), p.40:
"ε(ρ) = ∫₀¹ v² dv / (v² + 3ρv + ρ²)".

**Formalization Note.** An interval integral over `[0, 1]`; for `ρ > 0` the integrand is
continuous on `[0, 1]`. -/
noncomputable def epsRho (ρ : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, v ^ 2 / (v ^ 2 + 3 * ρ * v + ρ ^ 2)

end ParetoNCSched.Supplement


