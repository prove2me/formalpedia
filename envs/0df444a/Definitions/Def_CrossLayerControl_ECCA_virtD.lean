-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_virtD
-- name    : CrossLayerControl_ECCA_virtD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:46:54.119667+00:00
-- url     : https://prove2.me/theorems/820dce17-49df-4a1d-9569-d4c41922fdaa
-- title:
--   The virtual power queue $D(t)$, (6.13)
-- statement:
--   For power allocations $p(t)$, the virtual power queue is
--   $$D(0)=0,\qquad D(t+1)=\max[D(t)-P_{av},0]+\sum_{i=1}^L p_i(t).\tag{6.13}$$
--
--   $D(t)$ is the accumulated power expenditure in excess of the average budget; keeping it bounded enforces the average power constraint.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, (6.13), p. 114

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_queueLaw

namespace CrossLayerControl.ECCA

/-- **The virtual power queue D(t), (6.13).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), (6.13), p. 114: "D(t + 1) = max[D(t) − Pav, 0] + Σ_{i=1}^L Pi(t).
(6.13) with initial condition D(0) = 0."

`virtD M p t` is `D(t)` for the power allocations `p τ`: the queue law of §3.1 with initial value
`0`, constant service `Pav` and arrivals `Σᵢ pᵢ(τ)`. -/
noncomputable def virtD {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (p : ℕ → Fin L → ℝ) (t : ℕ) : ℝ :=
  queueLaw 0 (fun _ => M.Pav) (fun τ => ∑ i, p τ i) t

end CrossLayerControl.ECCA


