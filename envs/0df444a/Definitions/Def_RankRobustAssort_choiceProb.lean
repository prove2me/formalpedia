-- Prove2me | Definitions.Def_RankRobustAssort_choiceProb
-- name    : RankRobustAssort_choiceProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:48.304327+00:00
-- url     : https://prove2.me/theorems/66bdfa3b-3f8a-4267-bc82-fb5ba2bd412f
-- title:
--   Choice probability $\mathcal D^\lambda_i(S)$ of a ranking-based choice model
-- statement:
--   For a distribution $\lambda\in\Delta_\Sigma$ over rankings, an assortment $S\subseteq\mathcal N_0$ and a product $i$, the predicted purchase frequency of $i$ is
--
--   $$
--   \mathcal D^\lambda_i(S)=\sum_{\sigma\in\Sigma}\mathbb I\Big\{i=\arg\min_{j\in S}\sigma(j)\Big\}\,\lambda_\sigma,
--   $$
--
--   the probability that a customer whose ranking is drawn from $\lambda$ finds $i$ the most preferred product of $S$. In particular $\mathcal D^\lambda_i(S)=0$ for $i\notin S$.
--
--   These predictions are compared with the historical data on the past assortments and enter the expected revenue.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §2, p.7

import Mathlib
import Definitions.Def_RankRobustAssort_IsTop

open Classical

namespace RankRobustAssort

/-- The purchase probability of product `i` from assortment `S` under the ranking-based choice
model `λ`:
`𝒟^λ_i(S) ≜ ∑_{σ∈Σ} 𝕀{i = arg min_{j∈S} σ(j)} λ_σ`.

Sturt, arXiv:2112.05010v4, §2, p.7.

Formalization Note: the indicator is `IsTop σ S i`; the sum runs over all permutations of
`Fin (n+1)`. The definition is used both for assortments `S ∋ 0` and for past assortments `S_m`
(which need not contain `0`), as on pp.7–8. -/
noncomputable def choiceProb {n : ℕ} (lam : Equiv.Perm (Fin (n + 1)) → ℝ)
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℝ :=
  ∑ σ, if IsTop σ S i then lam σ else 0

end RankRobustAssort


