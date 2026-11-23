-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Supplement_RoundRegret
-- name    : CrossLearnCB_UCB1CL_Supplement_RoundRegret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:50:30.593232+00:00
-- url     : https://prove2.me/theorems/1b4bb646-1757-4c43-b720-be5977a65b06
-- title:
--   Lemma 6, p. 51 — one-round stochastic pseudo-regret for the non-contextual lower bound
-- statement:
--   The expected stochastic pseudo-regret in round $t<T$ is
--   $$\sum_c D(c)\max_i\mu_i(c)-\mathbb E[r_{I_t,t}(c_t)].$$
--   The full-horizon protocol determines the law of the history used by the arm choice. The sum of these round values is the existing expected pseudo-regret. In Lemma 6 there is one context, and a uniform finite mixture of stochastic instances supplies a lower bound simultaneously for every algorithm and every round.
--
--   **Formalization Note** The expectation over contexts and arms is a finite trajectory sum inside the reward-table integral, whose law is a product over rounds and allows within-round correlation. All uses have valid measurable policies and reward laws supported in $[0,1]$, so integrability follows from measurability and boundedness.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 51, Lemma 6; p. 53, Appendix C.7

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

namespace CrossLearnCB.UCB1CL.Supplement

open MeasureTheory
/-- One round's expected pseudo-regret with stochastic rewards and i.i.d. contexts.
Summing it over rounds gives stochRegret; it uses the same full-horizon history law. -/
noncomputable def roundStochRegret {K C T : ℕ} [NeZero K] (t : Fin T)
    (G : Fin K → Fin C → Fin C → Prop) (S : StochInstance K C) (A : Policy K C) : ℝ :=
  (∑ d, S.D d * Finset.univ.sup' Finset.univ_nonempty (fun i => S.mean i d)) -
    ∫ r, expect G S.D A r (fun τ => r t (τ t).2 (τ t).1) ∂(S.tableLaw T)

end CrossLearnCB.UCB1CL.Supplement


