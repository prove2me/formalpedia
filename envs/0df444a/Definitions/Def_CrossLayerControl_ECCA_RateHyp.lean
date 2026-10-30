-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_RateHyp
-- name    : CrossLayerControl_ECCA_RateHyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:18.863694+00:00
-- url     : https://prove2.me/theorems/3144dca3-ef5b-4216-8b8a-67f6617501d5
-- title:
--   Standing assumptions: signs and the rate bound (3.4)
-- statement:
--   The rate hypothesis on a downlink model asserts
--
--   1. $P_{av}\ge 0$, $P_{max}\ge 0$ and $\hat R\ge 0$;
--   2. for every feasible power vector $P$, every state $s$ and every link $i$,
--   $$0\le C_i(P,s)\le \mu_{max}.\tag{3.4}$$
--
--   The second item is the boundedness assumption (3.4) of the paper: rates are arbitrary, possibly discontinuous, but bounded.
--
--   **Formalization Note** The signs are implicit in the paper (a negative average power budget is unsatisfiable; $\hat R\ge 0$ follows from $0\le A_i(t)\le\hat R$ when $L\ge1$; $P_{max}\ge 0$ follows from $0\le P_{av}<P_{max}$). The paper's $P_{av}<P_{max}$ is not assumed. The bound (3.4) is only required at feasible power vectors.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, (3.4), p. 27; §6.3.1, p. 113

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower

namespace CrossLayerControl.ECCA

/-- **The standing assumptions on the downlink data: signs and the rate bound (3.4).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), (3.4), p. 27: "The function C(·,·) is arbitrary (possibly
discontinuous) and is only assumed to be bounded, so that for all links (a,b) and all I ∈ Is and
s ∈ S we have: 0 ≤ Cab(I,s) ≤ µmax." §6.3.1, p. 113: an average power constraint Pav, a peak power
Pmax, and arrivals Ai(t) ≤ R̂.

`RateHyp M` asserts
* `0 ≤ Pav`, `0 ≤ Pmax` and `0 ≤ R̂`;
* for every feasible power vector `P` (`IsFeasiblePower M P`), every state `s` and every link `i`,
  `0 ≤ Cᵢ(P, s) ≤ µmax`.

**Formalization Note.** The signs are implicit in the paper. A negative average power budget makes
the average power constraint unsatisfiable and the virtual queue (6.13) unbounded. A nonnegative R̂
is forced by `0 ≤ Aᵢ(t) ≤ R̂` as soon as there is one link, and is stated so that the case `L = 0`
is not degenerate. A nonnegative Pmax is implied by the paper's `0 ≤ Pav < Pmax`. The paper's
`Pav < Pmax` itself is not assumed. The bound (3.4) is required only at feasible power vectors,
the only ones any policy uses. -/
structure RateHyp {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) : Prop where
  Pav_nonneg : 0 ≤ M.Pav
  Pmax_nonneg : 0 ≤ M.Pmax
  Rhat_nonneg : 0 ≤ M.Rhat
  rate_nonneg : ∀ P, IsFeasiblePower M P → ∀ s i, 0 ≤ M.C i P s
  rate_le : ∀ P, IsFeasiblePower M P → ∀ s i, M.C i P s ≤ M.muMax

end CrossLayerControl.ECCA


