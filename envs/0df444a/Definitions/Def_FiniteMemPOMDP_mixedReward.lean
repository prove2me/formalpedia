-- Prove2me | Definitions.Def_FiniteMemPOMDP_mixedReward
-- name    : FiniteMemPOMDP_mixedReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:13.253677+00:00
-- url     : https://prove2.me/theorems/b98406fc-898a-41b9-bceb-ac99cd3ddf68
-- title:
--   Expected reward $g(p,\sigma^*(p))$ of a mixed stationary strategy
-- statement:
--   For a belief $p$ and a mixed stationary strategy $\sigma^*:\Delta(\mathcal K)\to\Delta(\mathcal A)$,
--
--   $$g(p,\sigma^*(p))=\sum_{k\in\mathcal K}\sum_{a\in\mathcal A}p(k)\,\sigma^*(p)(a)\,g(k,a),$$
--
--   the expected stage reward when the state is drawn from $p$ and the action from $\sigma^*(p)$.
--
--   **Formalization Note** The paper uses this linear extension of $g$ without writing it out.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma A.8 (3), p.24

import Mathlib
import Definitions.Def_FiniteMemPOMDP_POMDP

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A]

/-- **The expected stage reward `g(p, σ*(p))` of a mixed stationary strategy.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma A.8 (3), p.24: "∫_{∆(K)} g(p, σ∗(p))
µ∗(dp)", the reward function extended linearly to beliefs and mixed actions.

`mixedReward Γ σs p = ∑_k ∑_a p(k) σs(p)(a) g(k, a)`: the expected reward when the state is drawn
from the belief `p` and the action from `σs(p)`, independently.

**Formalization Note** The paper uses the linear extension `g(p, x) = ∑_{k,a} p(k) x(a) g(k, a)`
without writing it out. -/
noncomputable def mixedReward {S : Type} (Γ : POMDP K A S) (σs : stdSimplex ℝ K → stdSimplex ℝ A)
    (p : stdSimplex ℝ K) : ℝ :=
  ∑ k, ∑ a, p.1 k * (σs p).1 a * Γ.g k a

end FiniteMemPOMDP


