-- Prove2me | Definitions.Def_MetricMinTest_regionWorkload
-- name    : MetricMinTest_regionWorkload
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:57.286102+00:00
-- url     : https://prove2.me/theorems/5d47b8b8-c314-43ed-b156-f2a451704811
-- title:
--   Region workload $H_{Z,r}$
-- statement:
--   For $r\in[0,\gamma)$ and a nonempty $Z$, the region workload is
--   $$H_{Z,r}=\min\Big\{\sum_j w_j : w\ge0,\ \sum_j w_j(\gamma-r-d(z,j))_+^2\ge1\ \forall z\in Z\Big\}.$$
--   With $Z$ the whole index set and $r=0$ it is $H$.
--
--   **Formalization Note** Written as the infimum of the feasible masses.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 7.1, p.15

import Mathlib

namespace MetricMinTest

/-- **Region workload `H_{Z,r}`** (Definition 7.1). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 7.1, p.15:
`H_{Z,r} = min {∑ⱼ wⱼ : w ≥ 0, ∑ⱼ wⱼ (γ − r − d(z, j))₊² ≥ 1 ∀ z ∈ Z}`.

**Formalization Note.** Real `sInf` of the feasible masses (nonempty for `r < γ` and `Z` a set of
indices of a pseudometric; bounded below by `0`). -/
noncomputable def regionWorkload {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) (Z : Finset ι)
    (r : ℝ) : ℝ :=
  sInf {W : ℝ | ∃ w : ι → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = W ∧
    ∀ z ∈ Z, 1 ≤ ∑ j, w j * (max (γ - r - d z j) 0) ^ 2}

end MetricMinTest


