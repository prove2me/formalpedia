-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
-- name    : CrossLayerControl_ECCA_DownlinkHyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:58.002426+00:00
-- url     : https://prove2.me/theorems/506e0069-6dbb-43ce-85ea-bac74a806a90
-- title:
--   Standing assumptions of Theorem 6.3: $\beta$-condition and cross-monotonicity
-- statement:
--   The downlink hypothesis asserts the rate hypothesis (signs and (3.4)) and, for every feasible power vector $P$, every state $s$ and all links $i,j$:
--
--   1. (the $\beta$-condition) $\beta>0$ and
--   $$C_i(P,s)\le C_i(P[i],s)+\beta P_i;$$
--   2. (cross-monotonicity) if $j\ne i$, then
--   $$C_j(P,s)\le C_j(P[i],s),$$
--   that is, switching off the power of link $i$ never lowers the rate of another link.
--
--   These are the hypotheses under which ECCA's virtual power queue stays bounded.
--
--   **Formalization Note** Cross-monotonicity is a correction: it is not on the page, and without it the page's claim "if $D(t)>U_i(t)\beta$ then $P_i(t)=0$" is false. Counterexample satisfying every printed assumption: $L=2$, $P_{max}=1$, $P_{av}=0.5$, $\beta=0.01$, $V=10$, $\hat R=1$, $\mu_{max}=1$, $C_1\equiv0$, $C_2(P)=1[P_1\ge1]$, $A\equiv(0,1)$; ECCA allocates $P=(1,0)$ while $D>\beta U_1=0$, and $D(t)$ reaches $10>\beta V+\beta\hat R+P_{max}=1.11$. Cross-monotonicity holds for the "$L$ distinct channels" of §6.3.1 and for interference-limited rates.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, p. 115 (β-condition); correction C1

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
import Definitions.Def_CrossLayerControl_ECCA_zeroAt
import Definitions.Def_CrossLayerControl_ECCA_RateHyp

namespace CrossLayerControl.ECCA

/-- **The standing assumptions of Theorem 6.3: (3.4), the β-condition, and cross-monotonicity.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), p. 115 (unnumbered): "assume there exists a constant β > 0 such
that for any link i, any topology state S(t), and any power vector P such that Σi Pi ≤ Pmax, we
have: Ci(P,S(t)) ≤ Ci(P[i],S(t)) + βPi, where P = (P1,...,PL), and P[i] is equal to P with the
exception that the ith entry is set to zero."

`DownlinkHyp M` asserts `RateHyp M` (signs and (3.4)) and, for every feasible power vector `P`,
every state `s` and all links `i`, `j`:
* (β-condition) `0 < β` and `Cᵢ(P, s) ≤ Cᵢ(P[i], s) + β Pᵢ`;
* (cross-monotonicity, correction C1) if `j ≠ i` then `Cⱼ(P, s) ≤ Cⱼ(P[i], s)`: switching off the
  power of link `i` never lowers the rate of another link.

**Formalization Note (correction C1).** Cross-monotonicity is not on the page. It is needed: the
page derives "if D(t) > Ui(t)β, then Pi(t) = 0" from the β-condition alone, which is false when the
power of link `i` raises the rate of another link. A counterexample satisfying every printed
assumption: L = 2, Pmax = 1, Pav = 0.5, β = 0.01, V = 10, R̂ = 1, µmax = 1, C₁ ≡ 0,
C₂(P) = 1[P₁ ≥ 1], A ≡ (0, 1). ECCA allocates P = (1, 0) at slot 3 with D = 0.5 > βU₁ = 0, and D(t)
reaches 10 > βV + βR̂ + Pmax = 1.11. Cross-monotonicity holds for the "L distinct channels" of
§6.3.1 (each Cᵢ depending on Pᵢ only) and for interference-limited rates, which decrease in the
other links' powers. The β-condition is required only at power vectors with nonnegative entries. -/
structure DownlinkHyp {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) : Prop extends RateHyp M where
  beta_pos : 0 < M.β
  beta_cond : ∀ P, IsFeasiblePower M P → ∀ s i, M.C i P s ≤ M.C i (zeroAt P i) s + M.β * P i
  cross_mono : ∀ P, IsFeasiblePower M P → ∀ s i j, j ≠ i → M.C j P s ≤ M.C j (zeroAt P i) s

end CrossLayerControl.ECCA


