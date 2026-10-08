-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
-- name    : YoungConventions_AdaptivePlay_IsBestReplyDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:02:23.022051+00:00
-- url     : https://prove2.me/theorems/6d102b21-87cc-439b-ab2b-904ecfe132a0
-- title:
--   Best-reply distribution $p_i(\cdot \mid h)$ with sample size $k$ (§3, p. 62)
-- statement:
--   Fix a sample size $k$. For each player $i$ and state $h \in H$, let $p_i(x \mid h)$ be the probability that player $i$ chooses $x \in S_i$ in the next period. The family $p$ is a **best-reply distribution** if for every $i$ and $h$:
--   1. $p_i(\cdot \mid h)$ is a probability distribution on $S_i$: $p_i(x \mid h) \ge 0$ and $\sum_{x \in S_i} p_i(x \mid h) = 1$;
--   2. $p_i(x \mid h) > 0$ if and only if there is a sample $K$ of $k$ positions of $h$ such that $x$ is a best reply of $i$ to $K$.
--
--   The probabilities depend on the state only, not on the date. No particular sampling law is imposed: an agent may, for instance, be more likely to hear about recent precedents than older ones. Only the support of $p_i(\cdot \mid h)$ is fixed.
--
--   **Formalization Note** A sample of size $k$ drawn without replacement from the last $m$ periods is a set of $k$ positions of $h$. All theorems of the mission quantify over every best-reply distribution.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, pp. 61–62 (PDF pp. 6–7)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsSampleBestReply

namespace YoungConventions.AdaptivePlay

open Finset

/-- **Best-reply distribution** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§3, pp. 61–62, PDF pp. 6–7): "For each `s ∈ Sᵢ`, let `pᵢ(s|h)` be the probability that agent `i`
chooses `s`. We assume that `pᵢ(·)` is a *best-reply distribution* in the sense that `pᵢ(s|h) > 0`
if and only if there exists a sample of size `k` to which `s` is `i`'s best reply, and that
`pᵢ(s|h)` is independent of `t`."

`IsBestReplyDistribution u k p` holds iff, for every player `i` and state `h`, `pᵢ(·|h)` is a
probability distribution on `Sᵢ`, and `pᵢ(x|h) > 0` exactly when there is a set `K` of `k`
positions of `h` such that `x` is a best reply of `i` to the plays at `K` (`IsSampleBestReply`).

**Formalization Note.** `p i h x` is `pᵢ(x|h)`; it is a function of the state only, which encodes
time-independence. No particular sampling law is fixed: the paper explicitly allows non-uniform
sampling (p. 61, "It is not necessary to assume that every subset of `k` precedents out of the last
`m` is equally likely"), and every theorem of this mission quantifies over all best-reply
distributions. A sample of size `k` drawn without replacement from the last `m` periods is a set
`K ⊆ Fin m` of positions with `|K| = k`. -/
def IsBestReplyDistribution {ι : Type*} [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    {m : ℕ} (u : ι → (∀ i, S i) → ℝ) (k : ℕ) (p : ∀ i, History S m → S i → ℝ) : Prop :=
  (∀ i h x, 0 ≤ p i h x) ∧ (∀ i h, ∑ x, p i h x = 1) ∧
    ∀ i h x, 0 < p i h x ↔ ∃ K : Finset (Fin m), K.card = k ∧ IsSampleBestReply u h K i x

end YoungConventions.AdaptivePlay


