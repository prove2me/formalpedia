-- Prove2me | Definitions.Def_AnytimeAdaVR_xhat
-- name    : AnytimeAdaVR_xhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:37:42.505183+00:00
-- url     : https://prove2.me/theorems/043cdf21-c81d-4680-8ab7-e665d6d99197
-- title:
--   Output $\hat x^{\mathrm{lin}}_T$ of Algorithm 4 after $T$ queries
-- statement:
--   Algorithm 4 publishes $Z^{\mathrm{lin}}_n$ for checkpoint $n=2^k$ at the end of round $2n$. After $T$ global queries (optimization, initialization and validation queries all counted), the output $\hat x^{\mathrm{lin}}_T$ is the last published point: $Z^{\mathrm{lin}}_{2^k}$ for the largest $k$ whose publication round ends at a count $\le T$, and $x_{\mathrm{init}}$ before the first publication (at query $9$). This is the output at every budget, including budgets that end inside a round or between the two queries of an M pair.
--
--   The algorithm receives only $x_{\mathrm{init}}$ and oracle access: no problem constant, budget or regime.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), Algorithm 4, p.9; §5.3, pp.9–10; App. E.1, p.26

import Mathlib
import Definitions.Def_AnytimeAdaVR_checkpointPoint
import Definitions.Def_AnytimeAdaVR_roundEnd

namespace AnytimeAdaVR

/-- **The output `x̂^lin_T` of Algorithm 4 after `T` total queries.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), Algorithm 4, lines 1, 7–8
and 13, p.9; §5.3, pp.9–10 ("After each query response, complete any newly enabled query-free
updates and publication before honoring an interruption"; "Pauses … return the last published
candidate"); App. E.1, p.26 ("Until the first publication the output is xinit; at every later query
it is the last published point").

Checkpoint `n = 2^k` is published at the end of round `2n`, i.e. at global query count
`roundEnd (2^(k+1))`. So after `T` queries the output is `checkpointPoint g xinit k ω` for the
largest `k` with `roundEnd (2^(k+1)) ≤ T`, and `xinit` if there is none. This covers every budget,
including budgets that end inside a round or between the two queries of an M pair.

**Formalization Note.** The algorithm receives only `xinit` (and the oracle); no problem constant,
regime or budget enters the paths, the schedule or the selection. Every relevant `k` is `< T`
(`roundEnd (2^(k+1)) ≥ 2^(k+1) > k`), so the search over `Finset.range T` loses nothing. -/
noncomputable def xhat {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (T : ℕ) (ω : Tape Ξ) : EuclideanSpace ℝ (Fin d) :=
  let ks := (Finset.range T).filter (fun k => roundEnd (2 ^ (k + 1)) ≤ T)
  if h : ks.Nonempty then checkpointPoint g xinit (ks.max' h) ω else xinit

end AnytimeAdaVR


