-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rho0
-- name    : ParetoNCSched_Supplement_rho0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:33:00.868308+00:00
-- url     : https://prove2.me/theorems/ba16ddac-b22d-47e4-8b42-9586644b2a67
-- title:
--   The threshold $\rho_0=(\sqrt{10}-3)/2$
-- statement:
--   $$\rho_0=\frac{\sqrt{10}-3}{2}\approx0.081,$$
--
--   the smallest parameter for which the randomized algorithm $\mathrm{RT}_\rho$ is analysed (Theorem 1.3). It equals $\hat g(4/5)$ for $\hat g(w)=(\sqrt{5+4/w}-3)/2$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem 1.3, p.4; Appendix H, p.39

import Mathlib

namespace ParetoNCSched.Supplement

/-- **The threshold `ρ₀`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem 1.3, p.4, and Appendix H, p.39:
"ρ0 = (√10 − 3)/2 ≈ 0.081".

**Formalization Note.** The exact value; the decimal is not used. -/
noncomputable def rho0 : ℝ :=
  (Real.sqrt 10 - 3) / 2

end ParetoNCSched.Supplement


