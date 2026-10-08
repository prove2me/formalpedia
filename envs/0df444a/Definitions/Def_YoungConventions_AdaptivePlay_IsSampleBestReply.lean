-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsSampleBestReply
-- name    : YoungConventions_AdaptivePlay_IsSampleBestReply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:01:34.042217+00:00
-- url     : https://prove2.me/theorems/c6e0a315-bef5-4789-94e5-e60efdb2e9c1
-- title:
--   Best reply of player $i$ to a sample $K$ of plays (§3, pp. 61–62)
-- statement:
--   Each period, every player inspects a sample of plays drawn without replacement from the last $m$ periods. A **sample** of a state $h$ is a set $K \subseteq \{0, \dots, m-1\}$ of positions. A strategy $x \in S_i$ is a **best reply of player $i$ to the sample $K$** if it maximizes $i$'s total payoff against the sampled plays:
--   $$\sum_{t \in K} u_i\big(y, (h_t)_{-i}\big) \;\le\; \sum_{t \in K} u_i\big(x, (h_t)_{-i}\big) \qquad \text{for every } y \in S_i .$$
--   Dividing by $|K|$, this is a best reply to the empirical distribution of the opponents' strategies in the sampled plays.
--
--   **Formalization Note** The paper does not write the payoff against a sample. This is the reading consistent with §7, p. 71, where payoffs are weighted by sample frequencies $k'/k$. The sampled object is a whole play, so the opponents' strategies $(h_t)_{-i}$ are taken jointly, not as independent marginals (the two differ when there are three or more players). A sample is a set of positions, so a play that occurs at two sampled positions counts twice.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, pp. 61–62 (PDF pp. 6–7); payoff against a sample as in §7, p. 71

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History

namespace YoungConventions.AdaptivePlay

open Finset

/-- **Best reply to a sample of plays** (Young 1993, *The Evolution of Conventions*, Econometrica
61:57–84, §3, pp. 61–62, PDF pp. 6–7: "each player inspects `k` plays drawn without replacement
from the most recent `m` periods"; "`s` is `i`'s best reply" to a sample).

A sample is a set `K` of positions of the state `h`. The strategy `x ∈ Sᵢ` is a best reply of
player `i` to the sample `K` if it maximizes `i`'s total payoff against the sampled plays:
for every `y ∈ Sᵢ`,
`∑_{t ∈ K} uᵢ(y, (hₜ)₋ᵢ) ≤ ∑_{t ∈ K} uᵢ(x, (hₜ)₋ᵢ)`.

**Formalization Note.** The paper never writes the payoff against a sample. This is the reading
consistent with §7, p. 71 (the display before (5) compares payoffs weighted by the sample
frequencies `k′/k`): `i` maximizes the expected payoff against the empirical distribution of the
sampled plays, which is the total payoff divided by `|K|`. The sampled object is a whole play
(a strategy tuple), so the opponents' strategies `(hₜ)₋ᵢ` are taken jointly, not as independent
marginals. A sample is a set of **positions**, so two equal plays at different positions count
twice. The `i`-th coordinate of each sampled play is ignored. -/
def IsSampleBestReply {ι : Type*} [DecidableEq ι] {S : ι → Type*} {m : ℕ}
    (u : ι → (∀ i, S i) → ℝ) (h : History S m) (K : Finset (Fin m)) (i : ι) (x : S i) : Prop :=
  ∀ y : S i, ∑ t ∈ K, u i (Function.update (h t) i y) ≤ ∑ t ∈ K, u i (Function.update (h t) i x)

end YoungConventions.AdaptivePlay


