-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_queueU
-- name    : CrossLayerControl_ECCA_queueU
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:46:22.90818+00:00
-- url     : https://prove2.me/theorems/4c0c914e-a60f-4f68-96a5-42d81eab24a6
-- title:
--   The data queues $U_i(t)$ of the downlink
-- statement:
--   Given initial backlogs $u_0\in\mathbb R^L$, states $s(t)$, admitted data $r(t)$ and powers $p(t)$, the backlog of link $i$ is
--   $$U_i(0)=u_{0,i},\qquad U_i(t+1)=\max[U_i(t)-C_i(p(t),s(t)),0]+r_i(t),$$
--   the queue law of §3.1 with service $C_i(P(t),S(t))$ and arrivals $R_i(t)$.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, §6.3.1, p. 113; §3.1, p. 23

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_queueLaw

namespace CrossLayerControl.ECCA

/-- **The data queues Uᵢ(t) of the downlink.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), §6.3.1, p. 113: "Let Ri(t) represent the flow control decision for
queue i at time t, and let Ui(t) represent the current backlog in queue i." Each queue follows the
law of §3.1, p. 23, with service µ(t) = Ci(P(t), S(t)) and arrivals A(t) = Ri(t).

Given the initial backlog `u₀`, the states `s τ`, the admitted data `r τ` and the powers `p τ`,
`queueU M u₀ s r p t i` is `Uᵢ(t)`: `Uᵢ(0) = u₀ i` and
`Uᵢ(t + 1) = max (Uᵢ(t) − Cᵢ(p t, s t)) 0 + rᵢ(t)`. -/
noncomputable def queueU {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (u₀ : Fin L → ℝ) (s : ℕ → 𝒮)
    (r p : ℕ → Fin L → ℝ) (t : ℕ) : Fin L → ℝ :=
  fun i => queueLaw (u₀ i) (fun τ => M.C i (p τ) (s τ)) (fun τ => r τ i) t

end CrossLayerControl.ECCA


