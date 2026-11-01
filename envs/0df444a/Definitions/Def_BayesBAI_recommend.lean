-- Prove2me | Definitions.Def_BayesBAI_recommend
-- name    : BayesBAI_recommend
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:57:06.159524+00:00
-- url     : https://prove2.me/theorems/f5a7ecdb-e648-4477-86ba-28a70ba391dc
-- title:
--   The recommendation $J(T)$ of two-stage exploration
-- statement:
--   The **two-stage exploration** algorithm (TSE, Algorithm 1) recommends an arm $J(T)$ as follows. If $|\hat{\mathcal J}^*|=1$, it returns the unique arm of $\hat{\mathcal J}^*$. Otherwise it returns
--   $$
--   J(T)=\arg\max_{i\in\hat{\mathcal J}^*}\hat\mu_{i,\,n_1+n_2(|\hat{\mathcal J}^*|)},
--   $$
--   ties being resolved by the given rule.
--
--   **Formalization Note.** $\hat\mu_i(T)$ is the cumulative mean at the end of round $T$: it uses first-stage and second-stage samples together. The early return leaves budget unused, as in the algorithm.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Algorithm 1, p.6

import Mathlib
import Definitions.Def_BayesBAI_candidates
import Definitions.Def_BayesBAI_secondPulls
import Definitions.Def_BayesBAI_TieBreak

namespace BayesBAI

/-- The recommendation `J(T)` of Algorithm 1 (TSE), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3,
p.6. If `Ĵ*` has one element, return it. Otherwise return the `arg max` over `Ĵ*` of `μ̂_i(T)`.

**Formalization Note.** `μ̂_i(T)` is the **cumulative** mean of arm `i` at the end of round `T`: it uses
the `n₁` first-stage samples and the `n₂(|Ĵ*|)` second-stage samples together. The early return leaves
budget unused, as in the algorithm. -/
noncomputable def recommend {K T : ℕ} (sel : TieBreak K) (q : ℝ) (ω : Tape K T) : Fin K :=
  if h : (candidates q ω).card = 1 then (Finset.card_eq_one.mp h).choose
  else sel.sel (candidates q ω)
    (fun i => empMean ω i (firstPulls K q T + secondPulls K q T (candidates q ω).card))

end BayesBAI


