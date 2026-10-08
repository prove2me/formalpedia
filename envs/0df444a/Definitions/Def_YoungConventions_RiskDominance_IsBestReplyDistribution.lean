-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
-- name    : YoungConventions_RiskDominance_IsBestReplyDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:08.300158+00:00
-- url     : https://prove2.me/theorems/50ad19c7-93f1-496c-b347-60f5fcc4aab8
-- title:
--   Best-reply distribution $p_i(\cdot\mid h)$
-- statement:
--   A family $p=(p_i(\cdot\mid h))_{i,h}$ is a **best-reply distribution** (for sample size $k$) if for every player $i$ and state $h$, $p_i(\cdot\mid h)$ is a probability distribution on $S_i$ and
--   $$p_i(s\mid h)>0\iff s\text{ is a best reply of } i \text{ to some sample of size } k \text{ from } h.$$
--   Here $p_i(s\mid h)$ is the probability that player $i$ chooses $s$ in state $h$; it does not depend on the time.
--
--   The sampling law is not fixed: every theorem of the mission holds for every best-reply distribution, as the paper allows ("It is not necessary to assume that every subset of $k$ precedents out of the last $m$ is equally likely", p. 61).
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, p. 62

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_IsSampleBestReply

namespace YoungConventions.RiskDominance

/-- **Best-reply distribution.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, p. 62 (PDF p. 7): "For each `s ∈ Sᵢ`, let `pᵢ(s|h)` be
the probability that agent `i` chooses `s`. We assume that `pᵢ(·)` is a best-reply distribution in
the sense that `pᵢ(s|h) > 0` if and only if there exists a sample of size `k` to which `s` is `i`'s
best reply, and that `pᵢ(s|h)` is independent of `t`."

`p i h` is a probability distribution on `S i` for every player `i` and state `h`, whose support is
exactly the set of best replies of `i` to some sample of size `k` from `h`.

**Formalization Note.** Time-independence is built in (`p` depends only on `h`). The sampling law is
**not** fixed: every theorem of this mission quantifies over all best-reply distributions (p. 61:
"It is not necessary to assume that every subset of `k` precedents out of the last `m` is equally
likely"). -/
def IsBestReplyDistribution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ}
    (u : ι → ((i : ι) → S i) → ℝ) (k : ℕ) (p : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) : Prop :=
  ∀ (i : ι) (h : YoungConventions.AdaptivePlay.History S m),
    (∀ x, 0 ≤ p i h x) ∧ (∑ x, p i h x = 1) ∧ ∀ x, (0 < p i h x ↔ IsSampleBestReply u k h i x)

end YoungConventions.RiskDominance


