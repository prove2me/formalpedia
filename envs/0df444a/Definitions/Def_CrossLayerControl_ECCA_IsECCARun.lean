-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_IsECCARun
-- name    : CrossLayerControl_ECCA_IsECCARun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:31.325576+00:00
-- url     : https://prove2.me/theorems/97aab691-5824-4d87-b216-1369a9fa7538
-- title:
--   A run of the Energy Constrained Control Algorithm (ECCA)
-- statement:
--   For arrivals $a(t)$, states $s(t)$, initial backlogs $u_0$ and a control parameter $V$, the decisions $r(t)$ (admitted data) and $p(t)$ (power) form an ECCA run when, at every slot $t$, with $U=U(t)$ and $D=D(t)$ the backlogs the decisions generate:
--
--   1. (flow control) $0\le r_i(t)\le a_i(t)$ for all $i$, and $r(t)$ minimizes $\sum_i (U_i-V)r'_i$ over all $r'$ with $0\le r'_i\le a_i(t)$;
--   2. (power allocation) $p(t)$ is feasible and maximizes
--   $$\sum_{i=1}^L \big[U_i\,C_i(P',s(t))-D\,P'_i\big]\tag{6.14}$$
--   over all feasible power vectors $P'$.
--
--   ECCA is the algorithm whose performance Theorem 6.3 describes.
--
--   **Formalization Note** ECCA is a relation: every minimizer and maximizer is allowed, so ties are broken arbitrarily; the paper's rule "admit everything iff $U_i(t)\le V$" is one such run. If the maximum in (6.14) is not attained, no run exists.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, p. 114 (ECCA, (6.14))

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_virtD

namespace CrossLayerControl.ECCA

/-- **A run of the Energy Constrained Control Algorithm (ECCA).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), p. 114 (unnumbered): "Flow Control: Minimize Σ_{i=1}^L [Ui(t) − V]Ri(t)
such that 0 ≤ Ri(t) ≤ Ai(t) for all i. That is, every timeslot and for each queue i, we allow the
full set of new arrivals Ai(t) into the queue whenever Ui(t) ≤ V. Else, we drop all new arrivals
for queue i entering on that timeslot. Power Allocation: Every timeslot, observe the current
topology state S(t) and the current queue backlogs U(t) and D(t), and allocate power
P(t) = (P1(t),...,PL(t)) according to the following optimization: Maximize:
Σ_{i=1}^L [Ui(t)Ci(P,S(t)) − D(t)Pi(t)] (6.14) Subject to: Σ_{i=1}^L Pi(t) ≤ Pmax. The virtual power
queue D(t) is then updated via (6.13)."

`IsECCARun M V u₀ a s r p` says that, for the arrivals `a`, the states `s` and the initial backlog
`u₀`, the decisions `r` (admitted data) and `p` (power) are those of ECCA with parameter `V`: at
every slot `t`, with `U = U(t)` (`queueU`) and `D = D(t)` (`virtD`) the backlogs the decisions
generate,
1. `0 ≤ rᵢ(t) ≤ aᵢ(t)` for all `i`, and `r(t)` minimizes `Σᵢ (Uᵢ − V) r'ᵢ` over all `r'` with
   `0 ≤ r'ᵢ ≤ aᵢ(t)` for all `i`;
2. `p(t)` is a feasible power vector and maximizes `Σᵢ (Uᵢ Cᵢ(P', s(t)) − D P'ᵢ)` over all
   feasible `P'`.

**Formalization Note.** ECCA is encoded as a relation: every minimizer and every maximizer is
allowed, so ties are broken arbitrarily. The paper's flow rule "admit all of Aᵢ(t) iff Uᵢ(t) ≤ V"
is one such minimizer. Power vectors have nonnegative entries (`IsFeasiblePower`). When the maximum
in (6.14) is not attained (C discontinuous), no run exists, as the paper's algorithm is then
undefined. -/
def IsECCARun {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (V : ℝ) (u₀ : Fin L → ℝ)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ) : Prop :=
  ∀ t,
    (∀ i, 0 ≤ r t i ∧ r t i ≤ a t i) ∧
    (∀ r' : Fin L → ℝ, (∀ i, 0 ≤ r' i ∧ r' i ≤ a t i) →
      ∑ i, (queueU M u₀ s r p t i - V) * r t i ≤ ∑ i, (queueU M u₀ s r p t i - V) * r' i) ∧
    IsFeasiblePower M (p t) ∧
    (∀ P' : Fin L → ℝ, IsFeasiblePower M P' →
      ∑ i, (queueU M u₀ s r p t i * M.C i P' (s t) - virtD M p t * P' i) ≤
        ∑ i, (queueU M u₀ s r p t i * M.C i (p t) (s t) - virtD M p t * p t i))

end CrossLayerControl.ECCA


