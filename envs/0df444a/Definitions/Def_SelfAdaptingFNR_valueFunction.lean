-- Prove2me | Definitions.Def_SelfAdaptingFNR_valueFunction
-- name    : SelfAdaptingFNR_valueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:55.155518+00:00
-- url     : https://prove2.me/theorems/c7e14e8e-d955-4966-a97e-6055f97c0c5e
-- title:
--   WDP value function $V_t$ by the Bellman equations (1)
-- statement:
--   For a weakly coupled MDP, the **value function** $V_t:\mathcal S_t\to\mathbb R$ is given by the Bellman equations
--   $$V_t(s)=\max_{a\in\mathcal A_t(s)}\Big\{r_t(s,a)+\sum_{s'\in\mathcal S_{t+1}}\mathbb P(s'\mid s,a)\,V_{t+1}(s')\Big\},\qquad t\in\mathcal T,\ s\in\mathcal S_t,$$
--   with the terminal condition $V_T(\cdot)=0$. $V_0(s^0)$ is the value of an optimal policy.
--
--   **Formalization Note** The recursion (1) is the definition; the paper states that the optimal-policy value function "can also be represented recursively through the Bellman equations". The maximum is taken over the nonempty finite set $\mathcal A_t(s)$, so no default value is involved.
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §2.1, p.7, Bellman equations (1)

import Mathlib
import Definitions.Def_SelfAdaptingFNR_WDP

open scoped Classical

namespace SelfAdaptingFNR

variable {J K T : ℕ}

/-- **The WDP value function** `V_t(s)` by the Bellman equations (1) of Nadarajah & Cire,
*Self-Adapting Network Relaxations for Weakly Coupled MDPs*, SSRN 4081430 (Aug. 2023), §2.1,
p.7:
`V_t(s) = max_{a ∈ 𝒜_t(s)} { r_t(s,a) + ∑_{s′ ∈ 𝒮_{t+1}} ℙ(s′|s,a) V_{t+1}(s′) }` for `t < T`,
with the terminal condition `V_T(·) := 0`.

**Formalization Note.** The paper first defines `V_t` as the optimal expected reward over
policies and then states that it "can also be represented recursively through the Bellman
equations"; the recursion (1) is used here as the definition. The maximum is `Finset.sup'` over
the action set `𝒜_t(s)`, which is nonempty for `t < T` by `WDP.A_nonempty`, so no junk value
enters. For `t ≥ T` the value is `0` (the terminal condition at `t = T`; periods `t > T` are
never used). -/
noncomputable def WDP.V (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j) : ℝ :=
  if ht : t < T then
    (M.actionSet t s).sup' (M.actionSet_nonempty ht s) fun a =>
      M.reward t s a + ∑ s' : (j : Fin J) → M.S (t + 1) j, M.transProb t s a s' * M.V (t + 1) s'
  else 0
termination_by T - t

end SelfAdaptingFNR


