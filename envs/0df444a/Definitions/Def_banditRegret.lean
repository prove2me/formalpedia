-- Prove2me | Definitions.Def_banditRegret
-- name    : banditRegret
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-17T20:10:11.625131+00:00
-- url     : https://prove2.me/theorems/42f25bb1-4bae-4d67-82c1-90870d4fc2a5
-- statement:
--   The (expected) regret of policy $\pi$ on bandit $\nu$ over horizon $n$:
--
--   $$R_n(\pi,\nu) = n\mu^* - \mathbb{E}_{\nu\pi}\left[\sum_{t=1}^n X_t\right].$$
-- source:
--   L&S Ch 4.4, Eq. (4.1), p.60

import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §4.4, Eq. (4.1):
the (expected) regret of a policy on a stochastic bandit over horizon `n`,
`R_n = n μ* − E[∑_{t=1}^n X_t]`, where the expectation is over the canonical
bandit measure of the policy/environment interconnection.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The expected regret `R_n(π, ν) = n μ* − E_{νπ}[∑_{t=1}^n X_t]`
(L&S Eq. (4.1)). -/
noncomputable def banditRegret {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (n : ℕ) : ℝ :=
  n * banditOptimalMean ν - ∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π n)

end BanditAlgorithm


