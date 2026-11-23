-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Supplement_FixedContextProtocol
-- name    : CrossLearnCB_UCB1CL_Supplement_FixedContextProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:49:40.1318+00:00
-- url     : https://prove2.me/theorems/85a9204c-bdaf-4269-9474-af16d667cdd9
-- title:
--   §2.2, pp. 9–10 — deterministic context sequences, adversarial hindsight regret and stochastic pseudo-regret
-- statement:
--   For a fixed sequence $c_t$ and a fixed reward table $r$, a policy sees exactly the masked graph feedback of the protocol. The probability of an arm sequence is the product of its history-dependent arm probabilities. Its expected reward is the corresponding finite sum. The adversarial benchmark is
--   $$\sum_c\max_i\sum_{t:c_t=c}r_{i,t}(c),$$
--   and adversarial regret subtracts the algorithm's reward. For stochastic rewards with means $\mu_i(c)$, expected pseudo-regret is
--   $$\sum_t\max_i\mu_i(c_t)-\mathbb E\sum_t r_{I_t,t}(c_t).$$
--   These definitions supply the adversarial-context regimes of Theorems 4 and 6.
--
--   **Formalization Note** Rounds are `Fin T`. Rewards in the stochastic expression have the same product over independent round vectors as `StochInstance`, with fixed coordinate marginals and possibly time-dependent within-round couplings; its context distribution field is unused. Valid measurable policies and bounded supported rewards make all integrands measurable and bounded by the finite horizon. The imported protocol retains the stochastic-context ex ante benchmark as well.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 9–10, §2.2, all three regret benchmarks

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

namespace CrossLearnCB.UCB1CL.Supplement

open MeasureTheory

/-- Algorithm reward with an oblivious deterministic context sequence (§2.2, p. 10).
Only the arm draws are averaged. The record is exactly the existing masked feedback record. -/
noncomputable def fixedAlgReward {K C T : ℕ} (G : Fin K → Fin C → Fin C → Prop)
    (ctx : Fin T → Fin C) (A : Policy K C) (r : Fin T → Fin K → Fin C → ℝ) : ℝ :=
  ∑ a : Fin T → Fin K,
    (∏ t : Fin T, A t (hist G r (fun s => (ctx s, a s)) t) (ctx t) (a t)) *
      ∑ t : Fin T, r t (a t) (ctx t)

open Classical in
/-- Regret for adversarial rewards and contexts: the best stationary policy in hindsight. -/
noncomputable def fixedAdvRegret {K C T : ℕ} [NeZero K]
    (G : Fin K → Fin C → Fin C → Prop) (ctx : Fin T → Fin C)
    (A : Policy K C) (r : Fin T → Fin K → Fin C → ℝ) : ℝ :=
  (∑ c, Finset.univ.sup' Finset.univ_nonempty
    (fun i => ∑ t ∈ Finset.univ.filter (fun t => ctx t = c), r t i c)) -
      fixedAlgReward G ctx A r

/-- Regret for stochastic rewards and an oblivious context sequence, against the highest
mean arm in each context. The unused context law in S has no role in this definition. -/
noncomputable def fixedStochRegret {K C T : ℕ} [NeZero K]
    (G : Fin K → Fin C → Fin C → Prop) (ctx : Fin T → Fin C)
    (S : StochInstance K C) (A : Policy K C) : ℝ :=
  (∑ t : Fin T, Finset.univ.sup' Finset.univ_nonempty (fun i => S.mean i (ctx t))) -
    ∫ r, fixedAlgReward G ctx A r ∂(S.tableLaw T)

end CrossLearnCB.UCB1CL.Supplement


