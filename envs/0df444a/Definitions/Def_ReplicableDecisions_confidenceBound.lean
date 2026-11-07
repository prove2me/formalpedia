-- Prove2me | Definitions.Def_ReplicableDecisions_confidenceBound
-- name    : ReplicableDecisions_confidenceBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:22.312531+00:00
-- url     : https://prove2.me/theorems/f362ffab-6487-4ff5-8abc-d7a70d5c05c3
-- title:
--   The confidence term $\log(1/(4\beta))/(-2\log(1-s^2))$, read as zero at $s=1$
-- statement:
--   For $\beta>0$ and $s\in(0,1]$, the confidence term is
--
--   $$
--   \frac{\log(1/(4\beta))}{-2\log(1-s^2)},
--   $$
--
--   read as zero if $s=1$.
--
--   With $s=s_1$ it is the part of the lower bound on $n^\star(\beta,\rho)$ that depends on $\beta$.
--
--   **Formalization Note** Proposition 3.9 prints the denominator as $2\log(1/(1-s^2))$, the same number. The case $s=1$ is written out rather than left to the convention $\log 0=0$ of Lean.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Theorem 3.1, p.10 (PDF p.12); Proposition 3.9, p.14 (PDF p.16)

import Mathlib

namespace ReplicableDecisions

open Classical in
/-- **The confidence lower bound** `log(1/(4β)) / (−2 log(1 − s²))`, "read as zero if s₁ = 1". Chen,
*Replicable Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 3.1,
p.10 (PDF p.12), and Proposition 3.9, p.14 (PDF p.16).

**Formalization Note.** Proposition 3.9 prints the denominator as `2 log(1/(1 − s²))`, the same
number. The case `s = 1` is written out rather than left to `Real.log 0 = 0`. -/
noncomputable def confidenceBound (β s : ℝ) : ℝ :=
  if s = 1 then 0 else Real.log (1 / (4 * β)) / (-2 * Real.log (1 - s ^ 2))

end ReplicableDecisions


