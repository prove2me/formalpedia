-- Prove2me | Definitions.Def_ucbPolicy
-- name    : ucbPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-17T20:10:42.578586+00:00
-- url     : https://prove2.me/theorems/0377e41f-d8cf-4f4b-8588-1da46f159729
-- statement:
--   The UCB($\delta$) policy characterization (L&S Algorithm 3). The UCB index of arm $i$ is
--
--   $$\hat\mu_i + \sqrt{\frac{2\log(1/\delta)}{T_i}}$$
--
--   (taken to be $\infty$ when $T_i = 0$, encoded by the unpulled-arm clause). `IsUCBPolicy δ π` holds iff each round $\pi$ deterministically plays an unpulled arm if one exists, and otherwise an arm maximizing the index (any tie-breaking).
-- source:
--   L&S Ch 7, Algorithm 3, p.102-105

import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 7, Algorithm 3:
the Upper Confidence Bound policy at confidence level `δ`.

The UCB index of arm `i` after the first `t` rounds is `∞` if `T_i(t) = 0` and
`μ̂_i(t) + sqrt (2 log (1/δ) / T_i(t))` otherwise; the policy plays an arm with
maximal index. We characterize UCB as a predicate on policies: in every round
the played arm is deterministic and maximizes the index (equivalently: if some
arm is unpulled, an unpulled arm is played; otherwise a maximizer of the
real-valued index is played). This captures Algorithm 3 for every tie-breaking
rule.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The (finite part of the) UCB index of arm `i` given history `h`
(L&S Algorithm 3): `μ̂_i + sqrt (2 log (1/δ) / T_i)`. -/
noncomputable def ucbIndex {k n : ℕ} (δ : ℝ) (i : Fin k)
    (h : BanditHistory k n) : ℝ :=
  armEmpiricalMean i h + Real.sqrt (2 * Real.log (1 / δ) / armPullCount i h)

/-- `IsUCBPolicy δ π`: the policy `π` is an instance of UCB(δ)
(L&S Algorithm 3, any tie-breaking): each round it deterministically plays an
unpulled arm if one exists (index `∞`), and otherwise an arm maximizing the
UCB index. -/
def IsUCBPolicy {k : ℕ} (δ : ℝ) (π : BanditPolicy k) : Prop :=
  ∀ n (h : BanditHistory k n), ∃ a : Fin k,
    (π.select n) h = Measure.dirac a ∧
    ((∃ j, armPullCount j h = 0) → armPullCount a h = 0) ∧
    ((∀ j, armPullCount j h ≠ 0) → ∀ j, ucbIndex δ j h ≤ ucbIndex δ a h)

end BanditAlgorithm


