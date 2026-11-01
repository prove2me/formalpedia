-- Prove2me | Definitions.Def_WiretapFeedback_activeBeta
-- name    : WiretapFeedback_activeBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:38.496984+00:00
-- url     : https://prove2.me/theorems/9e112288-58eb-4e55-8ff3-2d7e7216ded8
-- title:
--   Optimal type-II error of active hypothesis testing $\beta_\epsilon(W,V,n)$
-- statement:
--   Let $W,V:\mathcal X\to\mathcal O$ be two discrete memoryless channels. An **$n$-length active hypothesis test** consists of (possibly randomized) encoder mappings $e_t:\mathcal F^t\to\mathcal X$, $1\le t\le n$, feedback mappings $f_t:\mathcal O^t\to\mathcal F$, $0\le t\le n-1$, and a test $T$ on $\{0,1\}$ given the inputs, outputs and feedback $(X^n,O^n,\mathbf F)$. For $0\le\epsilon<1$, $\beta_\epsilon(W,V,n)$ is the infimum of the type-II error probability over all $n$-length active hypothesis tests for the null hypothesis $W$ and the alternative $V$ whose type-I error probability is at most $\epsilon$:
--   $$
--   \beta_\epsilon(W,V,n)=\inf_{\text{strategies}}\ \beta_\epsilon\bigl(P^{W}_{X^nO^n\mathbf F},\,P^{V}_{X^nO^n\mathbf F}\bigr).
--   $$
--
--   **Formalization Note** The infimum runs over every strategy (any feedback alphabet, any local randomness at transmitter and receiver) and, for each strategy, over every test on the observation, which is the optimal type-II error of the two observation laws.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §III, p.2 (definition of β_ϵ(W, V, n))

import Mathlib
import Definitions.Def_WiretapFeedback_testBeta
import Definitions.Def_WiretapFeedback_FeedbackStrategy_obsLaw

open scoped ENNReal

namespace WiretapFeedback

/-- The optimal type-II error `β_ϵ(W, V, n)` of `n`-length **active hypothesis testing** between
two channels `W, V : X → O`, Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §III, p. 2: an `n`-length
active hypothesis test consists of (possibly randomized) encoder mappings `e_t : 𝓕ᵗ → X`, feedback
mappings `f_t : Oᵗ → 𝓕` and a test `T` on `{0, 1}` given `(Xⁿ, Oⁿ, 𝐅)`; `β_ϵ(W, V, n)` is the
infimum of the type-II error probability over all such tests whose type-I error probability is at
most `ϵ`.

**Formalization Note** The infimum runs over every transmission–feedback strategy
(`FeedbackStrategy`: arbitrary feedback alphabet and arbitrary local randomness of transmitter
and receiver) and, for each, over every test on the observation `(Xⁿ, Oⁿ, 𝐅)`; for a fixed
strategy this is `β_ϵ` of the two observation laws (`testBeta`). -/
noncomputable def activeBeta {X O : Type} [Fintype O] (ε : ℝ) (W V : WildeQIT.Channel X O)
    (n : ℕ) : ℝ≥0∞ :=
  ⨅ S : FeedbackStrategy X O n, testBeta ε (S.obsLaw W) (S.obsLaw V)

end WiretapFeedback


