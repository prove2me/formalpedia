-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
-- name    : CrossLayerControl_ECCA_IsFeasiblePower
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:35.556989+00:00
-- url     : https://prove2.me/theorems/c2f6279d-3dec-4c56-806a-1501cbc61c57
-- title:
--   Feasible power vectors
-- statement:
--   A power vector $P\in\mathbb R^L$ is feasible when
--   $$P_i\ge 0 \text{ for all } i \qquad\text{and}\qquad \sum_{i=1}^L P_i\le P_{max}.$$
--
--   This is the per-slot power constraint of §6.3.1 and of the power allocation problem (6.14).
--
--   **Formalization Note** The page writes only $\sum_i P_i\le P_{max}$; the nonnegativity of a power allocation is implicit and is stated explicitly.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, §6.3.1, p. 113; (6.14), p. 114

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink

namespace CrossLayerControl.ECCA

/-- **Feasible power vectors.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), §6.3.1, p. 113 (unnumbered): "Power is constrained so that
Σ_{i=1}^L Pi(t) ≤ Pmax for all t." and (6.14), p. 114: "Subject to: Σ_{i=1}^L Pi(t) ≤ Pmax."

`IsFeasiblePower M P` holds when every entry of `P` is nonnegative and `Σᵢ Pᵢ ≤ Pmax`.

**Formalization Note.** The page writes only `Σᵢ Pᵢ ≤ Pmax`; the nonnegativity `Pᵢ ≥ 0` of a power
allocation is implicit in the word "power" and is made explicit here. -/
def IsFeasiblePower {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (P : Fin L → ℝ) : Prop :=
  (∀ i, 0 ≤ P i) ∧ ∑ i, P i ≤ M.Pmax

end CrossLayerControl.ECCA


