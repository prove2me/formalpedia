-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_rStar
-- name    : CrossLayerControl_ECCA_rStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:50:03.6357+00:00
-- url     : https://prove2.me/theorems/1f79dc1c-0410-4671-b663-4463da95066e
-- title:
--   The optimal throughput $\sum_i r_i^*$
-- statement:
--   The optimal throughput is
--   $$\sum_i r_i^*=\sup\Big\{\sum_i r_i\ :\ (r,c,p)\in\overline{K(\mu)},\ r_i\le c_i\ \text{for all } i,\ p\le P_{av}\Big\},$$
--   where $\overline{K(\mu)}$ is the closure of the set of rate–service–power triples of stationary randomized decisions.
--
--   It is the largest throughput a stationary randomized decision (in the limit) can support with every admitted rate at most its service rate and average power at most $P_{av}$.
--
--   **Formalization Note** The paper calls $\sum_i r_i^*$ "the optimal throughput over all possible policies" without a formula; this closure relaxation is shown to dominate every admissible policy by a milestone of the mission. Under bounded arrivals the set is nonempty (it contains $0$) and bounded above by $L\hat R$.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115; p. 105

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_achievable

open MeasureTheory

namespace CrossLayerControl.ECCA

/-- **The optimal throughput Σᵢ r∗ᵢ.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115: "where Σi r∗i is the optimal throughput over
all possible policies"; p. 105: "The value c∗ = f∗ − g∗ can thus be interpreted as the optimal cost
over all S-only policies. For a large class of network flow problems, including the fairness
problems of the previous section and the energy problems to be presented in this section, c∗ is
also the optimal cost over all possible (perhaps not S-only) policies [116]."

`rStar M μ` is the supremum of `Σᵢ rᵢ` over the triples `(r, c, p)` in the closure of
`achievable M μ` with `rᵢ ≤ cᵢ` for every `i` (admitted rate at most service rate) and `p ≤ Pav`
(average power within budget).

**Formalization Note.** The paper does not define r∗ beyond "the optimal throughput over all
possible policies". This is the stationary randomized benchmark, relaxed to the closure; the
milestone `rStar_ge_admissible` shows that no admissible policy, causal or not, exceeds it. When `μ`
is the law of arrivals in `[0, R̂]^L` and (3.4) holds, the set is nonempty (the decision `R = 0`,
`P = 0` gives `Σᵢ rᵢ = 0`) and bounded above by `L·R̂`, so the real `sSup` is not a junk value. -/
noncomputable def rStar {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮)
    (μ : Measure ((Fin L → ℝ) × 𝒮)) : ℝ :=
  sSup {y : ℝ | ∃ q ∈ closure (achievable M μ),
    (∀ i, q.1 i ≤ q.2.1 i) ∧ q.2.2 ≤ M.Pav ∧ y = ∑ i, q.1 i}

end CrossLayerControl.ECCA


