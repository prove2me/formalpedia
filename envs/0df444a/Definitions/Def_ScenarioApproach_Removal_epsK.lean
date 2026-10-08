-- Prove2me | Definitions.Def_ScenarioApproach_Removal_epsK
-- name    : ScenarioApproach_Removal_epsK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T05:39:37.449191+00:00
-- url     : https://prove2.me/theorems/40aba605-7b4c-44aa-8e31-c7018b14c960
-- title:
--   Eq. (1.9) — the violation level $\varepsilon_k$ after discarding $k$ scenarios
-- statement:
--   For a number $N$ of scenarios, a number $k$ of discarded scenarios, a number $d$ of decision variables, and a confidence parameter $\beta$, define
--
--   $$
--   \varepsilon_k = \frac{k}{N} + \left[ \frac{\sqrt k}{N} + \frac{\sqrt k + 1}{N}\left( (d-1)\ln(k+d-1) + \frac{d-1}{\sqrt k} + \ln\frac1\beta \right) \right].
--   $$
--
--   The first term $k/N$ is the empirical risk (the fraction of discarded, hence violated, scenarios); the bracket is a margin that accounts for statistical fluctuation and for the optimization bias. Theorem 1.2 guarantees that the solution obtained after discarding $k$ scenarios has violation at most $\varepsilon_k$ with confidence $1-\beta$.
--
--   **Formalization Note** The formula is transcribed literally with real arithmetic. It is meaningful for $N \ge 1$, $k \ge 1$ (the formula divides by $\sqrt k$), $d \ge 1$ and $\beta \in (0,1)$; every theorem using it states these ranges as hypotheses (outside them Lean's conventions $x/0 = 0$ and $\ln x = 0$ for $x \le 0$ would apply).
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 18, Theorem 1.2, Eq. (1.9)

import Mathlib

namespace ScenarioApproach.Removal

/-- The violation level `ε_k` of formula (1.9) (Campi–Garatti 2018, p. 18):
`ε_k = k/N + [√k/N + ((√k+1)/N)((d−1) ln(k+d−1) + (d−1)/√k + ln(1/β))]`. -/
noncomputable def epsK (N k d : ℕ) (β : ℝ) : ℝ :=
  (k : ℝ) / N + (Real.sqrt k / N + (Real.sqrt k + 1) / N *
    (((d : ℝ) - 1) * Real.log ((k : ℝ) + d - 1) + ((d : ℝ) - 1) / Real.sqrt k + Real.log (1 / β)))

end ScenarioApproach.Removal


