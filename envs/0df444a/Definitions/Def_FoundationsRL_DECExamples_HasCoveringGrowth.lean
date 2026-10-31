-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_HasCoveringGrowth
-- name    : FoundationsRL_DECExamples_HasCoveringGrowth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:44.640991+00:00
-- url     : https://prove2.me/theorems/e434bc03-b7ad-4064-a002-b586c7078afc
-- title:
--   Covering-number growth $\mathcal N_\rho(\Pi,\varepsilon)\le\varepsilon^{-d}$ for $\varepsilon\in(0,1]$
-- statement:
--   A subset $\Pi'\subseteq\Pi$ is an $\varepsilon$-cover of the metric space $(\Pi,\rho)$ if every $\pi\in\Pi$ has some $\pi'\in\Pi'$ with $\rho(\pi,\pi')\le\varepsilon$; $\mathcal N_\rho(\Pi,\varepsilon)$ is the size of the smallest such cover. The space has **covering growth of dimension** $d$ if
--
--   $$
--   \mathcal N_\rho(\Pi,\varepsilon)\le\varepsilon^{-d}\qquad\text{for all }\varepsilon\in(0,1].
--   $$
--
--   For example the unit interval with $\rho(x,y)=|x-y|$ satisfies it with $d=1$. This is the hypothesis of Proposition 18.
--
--   **Formalization Note** $\mathcal N_\rho(\Pi,\varepsilon)$ is Mathlib's internal covering number `Metric.coveringNumber ε univ` (closed balls, centers in $\Pi$), valued in $\mathbb N\cup\{\infty\}$ and compared in $[0,\infty]$, so an infinite covering number fails the condition. The notes require the bound for all $\varepsilon>0$, which no nonempty space satisfies: at $\varepsilon>1$ it would demand $1\le\mathcal N_\rho(\Pi,\varepsilon)\le\varepsilon^{-d}<1$. The condition is therefore required on $(0,1]$, where it is meaningful; the notes' condition implies it.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.3.3 and Proposition 18, p. 73

import Mathlib
open scoped NNReal ENNReal

namespace FoundationsRL.DECExamples

/-- The growth condition `N_ρ(D, ε) ≤ ε^{−d}` on the covering number of Proposition 18.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §4.3.3, p. 73.

**Formalization Note.** `N_ρ(D, ε)`, the size of the smallest `ε`-cover `D' ⊆ D`, is Mathlib's
internal `Metric.coveringNumber`, valued in `ℕ∞`; it is compared in `ℝ≥0∞`, so an infinite covering
number fails the condition rather than becoming a junk real. The condition is required for
`ε ∈ (0, 1]` only. The notes print "for all `ε > 0`", which no nonempty space satisfies: at `ε > 1`
it would ask `1 ≤ N_ρ(D, ε) ≤ ε^{−d} < 1`. -/
def HasCoveringGrowth (D : Type*) [MetricSpace D] (d : ℝ) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
    ((Metric.coveringNumber ε (Set.univ : Set D) : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((ε : ℝ) ^ (-d))

end FoundationsRL.DECExamples


