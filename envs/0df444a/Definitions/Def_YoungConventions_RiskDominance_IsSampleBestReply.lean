-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsSampleBestReply
-- name    : YoungConventions_RiskDominance_IsSampleBestReply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:19.009399+00:00
-- url     : https://prove2.me/theorems/3976fe96-df84-4fbe-bf00-d0f1ca6b3450
-- title:
--   Best reply of a player to some sample of size $k$
-- statement:
--   Fix the sample size $k$. A **sample of size $k$ from $h$** is a set $K$ of $k$ periods among the $m$ periods recorded in $h=(h_1,\dots,h_m)$. A strategy $x\in S_i$ is a **best reply of player $i$ to the sample $K$** if it maximizes $i$'s total payoff against the sampled plays,
--   $$\sum_{t\in K}u_i(y,h_{t,-i})\le\sum_{t\in K}u_i(x,h_{t,-i})\qquad\text{for all }y\in S_i,$$
--   where $(y,h_{t,-i})$ is the play $h_t$ with $i$'s strategy replaced by $y$. The predicate says that $x$ is a best reply of $i$ to **some** sample of size $k$ from $h$.
--
--   This is the set of choices a player can make without making a mistake: it is the support of a best-reply distribution, and a component of a new play outside it is a mistake.
--
--   **Formalization Note** Samples are sets of positions, so a play that occurs several times in $h$ can be sampled several times (draws without replacement from the last $m$ periods). The paper does not write the payoff against a sample; maximizing the summed (equivalently, average) payoff against the sampled plays is the reading consistent with p. 71, where Column's best reply is computed from the sample frequencies $k'/k$. Ties are allowed: $x$ is *a* maximizer.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, pp. 61–62; §6, p. 68 (Mistake)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History

namespace YoungConventions.RiskDominance

/-- **Best reply of player `i` to some sample of size `k` from `h`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, pp. 61–62
(PDF pp. 6–7): "each player inspects `k` plays drawn without replacement from the most recent `m`
periods" and `pᵢ(s|h) > 0` "if and only if there exists a sample of size `k` to which `s` is `i`'s
best reply"; §6, p. 68 (PDF p. 13): a mistake is a choice "that is not an optimal response by agent
`i` to any sample of size `k` from `h`".

`x ∈ Sᵢ` is a best reply of `i` to some sample of size `k` from `h` iff there is a set `K` of `k`
positions of `h` such that `x` maximizes `i`'s total payoff against the sampled plays:
`∑_{t ∈ K} uᵢ(y, h_t,−ᵢ) ≤ ∑_{t ∈ K} uᵢ(x, h_t,−ᵢ)` for every `y ∈ Sᵢ`.

**Formalization Note.** A sample is a set of `k` **positions** (periods), so a play repeated in `h`
can be sampled several times (draws "without replacement from the most recent `m` periods"). The
paper never writes the payoff against a sample; the reading used here — `i` maximizes the summed
(equivalently, average) payoff against the sampled plays, each play entering as the whole profile of
the others — is the one consistent with p. 71, where Column's best reply is computed from the sample
frequencies `k′/k`. "Best reply" means *a* maximizer (ties allowed, p. 71: "If equality holds in (5)
then strategy 2 is among Column's best replies"). `Function.update (h t) i y` is the play `h t` with
`i`'s strategy replaced by `y`. -/
def IsSampleBestReply {ι : Type*} [DecidableEq ι] {S : ι → Type*} {m : ℕ}
    (u : ι → ((i : ι) → S i) → ℝ) (k : ℕ) (h : YoungConventions.AdaptivePlay.History S m) (i : ι) (x : S i) : Prop :=
  ∃ K : Finset (Fin m), K.card = k ∧
    ∀ y : S i, ∑ t ∈ K, u i (Function.update (h t) i y) ≤ ∑ t ∈ K, u i (Function.update (h t) i x)

end YoungConventions.RiskDominance


