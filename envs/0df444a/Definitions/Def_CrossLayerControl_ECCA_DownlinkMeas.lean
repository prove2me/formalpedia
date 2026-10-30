-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_DownlinkMeas
-- name    : CrossLayerControl_ECCA_DownlinkMeas
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:36.442503+00:00
-- url     : https://prove2.me/theorems/c48036ae-6e27-4073-88c4-c8f1e278286c
-- title:
--   Measurability of the rate function
-- statement:
--   The rate function is measurable when, for every link $i$, the map $(P,s)\mapsto C_i(P,s)$ is measurable on $\mathbb R^L\times\mathcal S$.
--
--   It makes the expectations $\mathbb E\{C_i(P(t),S(t))\}$, used throughout the paper's drift analysis, well defined.
--
--   **Formalization Note** Lean's integral of a non-measurable function is $0$; the assumption is used only by the stochastic statements.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, (6.11), p. 109 (expectations of the rates)

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink

namespace CrossLayerControl.ECCA

/-- **Measurability of the rate function.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006): expectations of the rates Ci(P(t), S(t)) are taken throughout
§§3–6, e.g. in the drift bound (6.11), p. 109.

`DownlinkMeas M` asserts that for every link `i` the map `(P, s) ↦ Cᵢ(P, s)` is measurable on
`ℝ^L × 𝒮`.

**Formalization Note.** The paper takes expectations of the rates without comment (on a finite
state set). In Lean an integral of a non-measurable function is `0`, so measurability is stated;
only the stochastic statements use it. -/
def DownlinkMeas {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮) : Prop :=
  ∀ i, Measurable (fun q : (Fin L → ℝ) × 𝒮 => M.C i q.1 q.2)

end CrossLayerControl.ECCA


