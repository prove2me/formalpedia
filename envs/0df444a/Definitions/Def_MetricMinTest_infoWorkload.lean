-- Prove2me | Definitions.Def_MetricMinTest_infoWorkload
-- name    : MetricMinTest_infoWorkload
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:38.482418+00:00
-- url     : https://prove2.me/theorems/bc1c62f1-be07-4d2b-8d36-2635e14984fe
-- title:
--   Information workload $H_d(\gamma)$
-- statement:
--   The **information workload** is the value of the linear program
--   $$H=H_d(\gamma)=\min\Big\{\sum_j w_j : w\ge0,\ \sum_j w_j(\gamma-d(i,j))_+^2\ge1\ \text{for every } i\Big\}.\qquad(1.1)$$
--   Constraint $i$ represents a possible violation at $i$; its coefficient $(\gamma-d(i,j))_+^2$ measures the evidence a sample at $j$ supplies about it. One has $\gamma^{-2}\le H\le k\gamma^{-2}$.
--
--   **Formalization Note** The minimum is written as the infimum of the feasible masses; for a pseudometric and $\gamma>0$ the feasible set is nonempty and the infimum is attained (p.7).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Eq. (1.1), p.1; §3, p.7

import Mathlib

namespace MetricMinTest

/-- **Information workload `H = H_d(γ)`**, display (1.1). Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (1.1), p.1:
`H = min {∑ⱼ wⱼ : w ≥ 0, ∑ⱼ wⱼ (γ − d(i, j))₊² ≥ 1 for every i}`.

**Formalization Note.** The minimum is written as the real `sInf` of the set of feasible masses.
For a pseudometric and `γ > 0` the set is nonempty (`wⱼ = γ⁻²`, p.7) and bounded below by `0`, and
the paper shows the minimum is attained (p.7), so `sInf` is that minimum. `(x)₊ = max x 0`. -/
noncomputable def infoWorkload {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) : ℝ :=
  sInf {W : ℝ | ∃ w : ι → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = W ∧
    ∀ i, 1 ≤ ∑ j, w j * (max (γ - d i j) 0) ^ 2}

end MetricMinTest


