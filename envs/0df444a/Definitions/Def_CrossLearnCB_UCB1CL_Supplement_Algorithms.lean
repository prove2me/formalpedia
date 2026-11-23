-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Algorithms
-- name    : CrossLearnCB_UCB1CL_Supplement_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:48:53.529219+00:00
-- url     : https://prove2.me/theorems/d2da63c6-b806-4f00-a61f-2310d6f51cbe
-- title:
--   Algorithms 2 and 3, pp. 22–23 — EXP3.CL (known D) and EXP3.CL-U (unknown D, one CL graph)
-- statement:
--   Both algorithms keep a weight $w_{i,t}(c)$ for every arm $i$ and context $c$, all initially $1$, and in round $t$ (paper's indexing) pull arm $i$ in context $c_t$ with probability
--
--   $$p_{i,t}(c) = (1 - K\alpha)\,\frac{w_{i,t-1}(c)}{\sum_{j=1}^K w_{j,t-1}(c)} + \alpha .$$
--
--   1. **EXP3.CL** (Algorithm 2) knows the context distribution $D$ and uses $\alpha = \beta = \sqrt{\log K / (\bar\lambda K T)}$ with $\bar\lambda = \frac1K\sum_i \lambda(G_i)$. After pulling $I_t$ in context $c_t$, for every $c \in O_{I_t}(c_t)$ it sets
--   $$w_{I_t,t}(c) = w_{I_t,t-1}(c)\,\exp\!\Big(\beta\, \frac{r_{I_t,t}(c)}{\sum_{c' \in I_{I_t}(c)} D(c')\, p_{I_t,t}(c')}\Big),$$
--   and leaves every other weight unchanged.
--   2. **EXP3.CL-U** (Algorithm 3) assumes one CL graph $G$ for all arms and does not know $D$. It uses $\alpha = (\log K / (K^2 T))^{1/3}$ and $\beta = \sqrt{\alpha \log K / T}$, and for every $c \in O(c_t)$ sets
--   $$w_{I_t,t}(c) = w_{I_t,t-1}(c)\,\exp\!\Big(\beta\, \frac{r_{I_t,t}(c)}{p_{I_t,t}(c_t)}\Big).$$
--
--   Here $O_i(c)$ and $I_i(c)$ are the out- and in-neighbours of $c$ in $G_i$. The probabilities form a probability vector when $K\alpha \le 1$, i.e. $K\log K \le \bar\lambda T$ for EXP3.CL and $K \log K \le T$ for EXP3.CL-U.
--
--   **Formalization Note** The weights are computed by recursion on the learner's record of past rounds (context, arm, revealed rewards), so each algorithm is a policy of the protocol definitions; the weights after $t$ recorded rounds are the paper's $w_{\cdot,t}$ and give the probabilities of the 0-based round $t$ (the paper's round $t+1$). Logarithms are natural. EXP3.CL-U's definition takes no context distribution as input. The update of Algorithm 3 is applied for $c \in O(c_t)$, as in its box and in estimator (7).
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 22, Algorithm 2 (EXP3.CL), estimator (6) p. 21; p. 23, Algorithm 3 (EXP3.CL-U), estimator (7)

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_AcyclicNumber
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

namespace CrossLearnCB.UCB1CL.Supplement

/-! ### EXP3.CL (Algorithm 2, p. 22) and EXP3.CL-U (Algorithm 3, p. 23)

Weights are computed from the learner's record `h : Fin t → Obs K C` of rounds `0, …, t-1`
(each entry: context `c_s`, pulled arm `I_s`, revealed rewards). `w` after `t` rounds is the
paper's `w_{·,t}`; the probabilities used at the 0-based round `t` (the paper's round `t + 1`)
are computed from it. -/

/-- The exploration mixture `p_i(c) = (1 − Kα) w_i(c) / Σ_j w_j(c) + α`. -/
noncomputable def mixProb {K C : ℕ} (α : ℝ) (w : Fin K → Fin C → ℝ) (i : Fin K) (c : Fin C) :
    ℝ :=
  (1 - (K : ℝ) * α) * (w i c / ∑ j, w j c) + α

/-- EXP3.CL's parameter `α = β = √(log K / (λ̄ K T))`. -/
noncomputable def exp3CLRate {K C : ℕ} (T : ℕ) (G : Fin K → Fin C → Fin C → Prop) : ℝ :=
  Real.sqrt (Real.log K / (lambdaBar G * K * T))

open Classical in
/-- EXP3.CL's weights after the recorded rounds: all `1` initially; after round `s` with
context `c_s` and arm `I_s`, for every `c ∈ O_{I_s}(c_s)` the weight `w_{I_s}(c)` is multiplied
by `exp(β r_{I_s,s}(c) / Σ_{c' ∈ I_{I_s}(c)} D(c') p_{I_s,s}(c'))`; all other weights stay. -/
noncomputable def exp3CLWeights {K C : ℕ} (T : ℕ) (G : Fin K → Fin C → Fin C → Prop)
    (D : Fin C → ℝ) : (t : ℕ) → (Fin t → Obs K C) → Fin K → Fin C → ℝ
  | 0, _ => fun _ _ => 1
  | t + 1, h =>
    let w := exp3CLWeights T G D t (fun s => h s.castSucc)
    let o := h (Fin.last t)
    fun i c =>
      if i = o.2.1 ∧ G o.2.1 o.1 c then
        w i c * Real.exp (exp3CLRate T G * o.2.2 c /
          ∑ c' ∈ Finset.univ.filter (fun c' => G o.2.1 c' c),
            D c' * mixProb (exp3CLRate T G) w o.2.1 c')
      else w i c

/-- EXP3.CL (Algorithm 2) as a policy: in context `c` it pulls arm `i` with probability
`p_{i}(c)` computed from the current weights. It knows `T`, the graphs and `D`. -/
noncomputable def exp3CL {K C : ℕ} (T : ℕ) (G : Fin K → Fin C → Fin C → Prop)
    (D : Fin C → ℝ) : Policy K C :=
  fun t h c i => mixProb (exp3CLRate T G) (exp3CLWeights T G D t h) i c

/-- EXP3.CL-U's exploration parameter `α = (log K / (K² T))^{1/3}`. -/
noncomputable def exp3CLUAlpha (K T : ℕ) : ℝ :=
  (Real.log K / ((K : ℝ) ^ 2 * T)) ^ (1 / 3 : ℝ)

/-- EXP3.CL-U's learning rate `β = √(α log K / T)`. -/
noncomputable def exp3CLUBeta (K T : ℕ) : ℝ :=
  Real.sqrt (exp3CLUAlpha K T * Real.log K / T)

open Classical in
/-- EXP3.CL-U's weights for a single CL graph `G` (`G c c'` is the edge `c → c'`): all `1`
initially; after round `s`, for every `c ∈ O(c_s)` the weight `w_{I_s}(c)` is multiplied by
`exp(β r_{I_s,s}(c) / p_{I_s,s}(c_s))`. The context distribution is never used. -/
noncomputable def exp3CLUWeights {K C : ℕ} (T : ℕ) (G : Fin C → Fin C → Prop) :
    (t : ℕ) → (Fin t → Obs K C) → Fin K → Fin C → ℝ
  | 0, _ => fun _ _ => 1
  | t + 1, h =>
    let w := exp3CLUWeights T G t (fun s => h s.castSucc)
    let o := h (Fin.last t)
    fun i c =>
      if i = o.2.1 ∧ G o.1 c then
        w i c * Real.exp (exp3CLUBeta K T * o.2.2 c / mixProb (exp3CLUAlpha K T) w o.2.1 o.1)
      else w i c

/-- EXP3.CL-U (Algorithm 3) as a policy; it knows `T` and `G`, not `D`. -/
noncomputable def exp3CLU {K C : ℕ} (T : ℕ) (G : Fin C → Fin C → Prop) : Policy K C :=
  fun t h c i => mixProb (exp3CLUAlpha K T) (exp3CLUWeights T G t h) i c

end CrossLearnCB.UCB1CL.Supplement


