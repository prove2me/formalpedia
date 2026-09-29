-- Prove2me | Definitions.Def_mossPolicy
-- name    : mossPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-19T02:57:01.58009+00:00
-- url     : https://prove2.me/theorems/b9ad2127-6b3a-46d5-a6f3-4ab6fc8fc4ee
-- statement:
--   The MOSS policy characterization (L&S Ch 9, Algorithm 7). It provides the truncated logarithm $\log^+(x) = \log\max\{1,x\}$ and the horizon-aware index
--
--   $$\hat\mu_i + \sqrt{\frac{4}{T_i}\log^+\!\left(\frac{n}{k T_i}\right)}$$
--
--   ($\infty$ when $T_i = 0$, encoded by the unpulled-arm clause, which captures the "choose each arm once" initialization for any order), and the predicate `IsMOSSPolicy` $n$ $\pi$, which holds iff each round $\pi$ deterministically plays an unpulled arm if one exists and otherwise an index maximizer (any tie-breaking).
-- source:
--   L&S Ch 9, Algorithm 7, p.123

import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 9, Algorithm 7,
p.123: the MOSS (Minimax Optimal Strategy in the Stochastic case) policy.

MOSS knows the horizon `n`. It chooses each arm once and subsequently plays
`A_t = argmax_i (μ̂_i(t-1) + sqrt ((4 / T_i(t-1)) log⁺ (n / (k T_i(t-1)))))`,
where `log⁺(x) = log max {1, x}`. The algorithm box only prescribes "choose
each arm once" (no order); as for `IsUCBPolicy`, the initialization phase is
encoded by the unpulled-arm clause (index `∞` when `T_i = 0`), which captures
Algorithm 7 for every initialization order and tie-breaking rule.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The truncated logarithm `log⁺(x) = log max {1, x}` (L&S Algorithm 7). -/
noncomputable def logPlus (x : ℝ) : ℝ :=
  Real.log (max 1 x)

/-- The (finite part of the) MOSS index of arm `i` at horizon `n = horizon`
given history `h` (L&S Algorithm 7):
`μ̂_i + sqrt ((4 / T_i) * log⁺ (horizon / (k * T_i)))`. -/
noncomputable def mossIndex {k n : ℕ} (horizon : ℕ) (i : Fin k)
    (h : BanditHistory k n) : ℝ :=
  armEmpiricalMean i h +
    Real.sqrt ((4 / armPullCount i h) *
      logPlus (horizon / (k * (armPullCount i h : ℝ))))

/-- `IsMOSSPolicy horizon π`: the policy `π` is an instance of MOSS at horizon
`horizon` (L&S Algorithm 7, any initialization order and tie-breaking): each
round it deterministically plays an unpulled arm if one exists (index `∞`),
and otherwise an arm maximizing the MOSS index. -/
def IsMOSSPolicy {k : ℕ} (horizon : ℕ) (π : BanditPolicy k) : Prop :=
  ∀ n (h : BanditHistory k n), ∃ a : Fin k,
    (π.select n) h = Measure.dirac a ∧
    ((∃ j, armPullCount j h = 0) → armPullCount a h = 0) ∧
    ((∀ j, armPullCount j h ≠ 0) → ∀ j, mossIndex horizon j h ≤ mossIndex horizon a h)

end BanditAlgorithm


