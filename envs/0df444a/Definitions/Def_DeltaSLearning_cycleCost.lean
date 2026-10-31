-- Prove2me | Definitions.Def_DeltaSLearning_cycleCost
-- name    : DeltaSLearning_cycleCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:33.141996+00:00
-- url     : https://prove2.me/theorems/209c7125-9961-486e-b571-3a8e039d17f7
-- title:
--   Cycle pseudo cost $G(\delta,S)$
-- statement:
--   For a demand path $d_0,d_1,\dots$, a gap $\delta$ and a target $S$, let $L=L(\delta)$, $W_k=d_0+\dots+d_{k-1}$, the after-order levels $y_k=S-W_k$ $(k<L)$ and the ending inventory $x_{L+1}=(S-W_L)^+$. The cycle pseudo cost is
--   $$G(\delta,S) := \sum_{k=0}^{L-1}\bigl[h\,(y_k-d_k)^+-p\min(y_k,d_k)\bigr]+K+c\,(S-x_{L+1}).$$
--   It collects the newsvendor pseudo costs of one cycle of the $(\delta,S)$ policy started at $S$ and the order at the cycle's end, which brings the inventory back to $S$.
--
--   **Formalization Note** 0-based periods within the cycle. On the null set where the demands never reach $\delta$, $L$ is the junk $0$ (see the cycle length).
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), first line of eq. (48), p.37; definition after (7), p.11

import Mathlib
import Definitions.Def_DeltaSLearning_Params
import Definitions.Def_DeltaSLearning_cycleLength

namespace DeltaSLearning

/-- The cycle pseudo cost `G(δ, S)` of one cycle of a `(δ, S)` policy started at level `S`
and driven by the demands `d 0, d 1, …`: with `L = L(δ)`, the levels `y_k = S - (d 0 + ⋯ +
d (k-1))` and the ending inventory `x_{L+1} = (S - (d 0 + ⋯ + d (L-1)))⁺`,
`G = Σ_{k<L} [h (y_k - d k)⁺ - p min(y_k, d k)] + K + c (S - x_{L+1})`.
It includes the newsvendor cost of the cycle and the order at its end.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), first line of eq. (48), p.37, and the definition after (7), p.11.

**Formalization Note** 0-based periods within the cycle. On the null set where the demands never
reach `δ`, `L` is the junk `0` (see `cycleLength`). -/
noncomputable def cycleCost (cp : Params) (δ S : ℝ) (d : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (cycleLength δ d),
      (cp.h * max (S - ∑ i ∈ Finset.range k, d i - d k) 0
        - cp.p * min (S - ∑ i ∈ Finset.range k, d i) (d k)))
    + cp.K + cp.c * (S - max (S - ∑ i ∈ Finset.range (cycleLength δ d), d i) 0)

end DeltaSLearning


