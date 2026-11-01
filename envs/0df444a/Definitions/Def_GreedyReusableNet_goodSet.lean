-- Prove2me | Definitions.Def_GreedyReusableNet_goodSet
-- name    : GreedyReusableNet_goodSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:38.379325+00:00
-- url     : https://prove2.me/theorems/4688c2b3-6ea7-4d8e-80d5-74d0df6fda45
-- title:
--   The good set $\mathcal A^\pi_{t,+}$
-- statement:
--   For a policy $\pi$ and the benchmark OPT,
--   $$\mathcal A^\pi_{t,+}=\{B\in\mathcal A^{\mathrm{OPT}}_t:\ n^{\mathrm{OPT}}_t(B)\ge n^\pi_t(B),\ B\text{ is available for }\pi\},$$
--   the bundles of OPT's action set in period $t$ on which OPT has used every arm at least as often as $\pi$, and all of whose arms are available to $\pi$ at the start of period $t$. On these bundles the oracle bounds OPT's reward by $\pi$'s; the remaining ones are charged to $\pi$'s activations through the queue coupling.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.2, p.19

import Mathlib
import Definitions.Def_GreedyReusableNet_History

namespace GreedyReusableNet

/-- **The "good" set** `𝒜^π_{t,+} = {B : B ∈ 𝒜^OPT_t, n^OPT_t(B) ≥ n^π_t(B), B is available for π}`
(Simchi-Levi, Zheng & Zhu, SSRN 3981123, §3.2, p.19), computed from the history `h` of `π` and
the history `h'` of OPT: the bundles of the action set OPT took in period `t` on which OPT's count
before period `t` is at least `π`'s count, element-wise, and all of whose arms are available for
`π` at the start of period `t`. -/
noncomputable def goodSet {N : ℕ} (h h' : History N) (t : ℕ) : Finset (Finset (Fin N)) := by
  classical
  exact (actionAt h' t).filter (fun B =>
    (∀ i ∈ B, counts (h.take t) i ≤ counts (h'.take t) i) ∧ B ⊆ freeArms (h.take t) t)

end GreedyReusableNet


