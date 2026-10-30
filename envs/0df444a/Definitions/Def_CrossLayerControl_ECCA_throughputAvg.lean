-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_throughputAvg
-- name    : CrossLayerControl_ECCA_throughputAvg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:48:04.099986+00:00
-- url     : https://prove2.me/theorems/1901f4a6-8078-418a-97d0-757f45616de9
-- title:
--   Time-average expected throughput
-- statement:
--   For admitted-data processes $R_i(\tau)$ on a probability space,
--   $$\overline{R}(t)=\frac1t\sum_{\tau=0}^{t-1}\sum_{i=1}^L\mathbb E\{R_i(\tau)\}.$$
--
--   Theorem 6.3 bounds the $\liminf$ of this quantity from below.
--
--   **Formalization Note** The value at $t=0$ is $0$; only limits are used.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115

import Mathlib

open MeasureTheory

namespace CrossLayerControl.ECCA

/-- **The time-average expected throughput.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115: the quantity
"(1/t) Σ_{τ=0}^{t−1} Σ_{i=1}^L E{Ri(τ)}".

For admitted-data processes `R τ ω i` on a probability space `(Ω, Pr)`,
`throughputAvg Pr R t = (1/t) Σ_{τ<t} Σᵢ E[Rᵢ(τ)]`.

**Formalization Note.** At `t = 0` the value is `0` (Lean's `0⁻¹ = 0`); only limits as `t → ∞` are
used. -/
noncomputable def throughputAvg {L : ℕ} {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (R : ℕ → Ω → Fin L → ℝ) (t : ℕ) : ℝ :=
  (t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∑ i, ∫ ω, R τ ω i ∂Pr

end CrossLayerControl.ECCA


