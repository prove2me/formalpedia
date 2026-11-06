-- Prove2me | Definitions.Def_MetricMinTest_certWorkload
-- name    : MetricMinTest_certWorkload
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:41.275467+00:00
-- url     : https://prove2.me/theorems/94cfb595-b2b6-4dc4-b8c2-54f6c84eb91b
-- title:
--   Certificate workload $F_d(\gamma)$
-- statement:
--   For each center $j$, list the distinct distances below $\gamma$ as $0=r_{j1}<\dots<r_{jq_j}<\gamma$, put $a_{j\ell}=\gamma-r_{j\ell}$ and $B_{j\ell}=B(j,r_{j\ell})$ with cost $a_{j\ell}^{-2}$. The **certificate workload** is the value of the fractional ball cover
--   $$F=F_d(\gamma)=\min\ \sum_{j,\ell}y_{j\ell}a_{j\ell}^{-2}\quad\text{subject to } y\ge0,\ \sum_{(j,\ell):\,i\in B_{j\ell}}y_{j\ell}\ge1\ \forall i.\qquad(2.1)$$
--
--   **Formalization Note** An indexed ball is a pair $(j,i)$ with $d(j,i)<\gamma$, standing for $B(j,d(j,i))$ at cost $(\gamma-d(j,i))^{-2}$. Repeated distances duplicate a ball at equal cost, which does not change the optimum.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, Eq. (2.1), p.6

import Mathlib

namespace MetricMinTest

/-- **Certificate workload `F = F_d(γ)`**, program (2.1). Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (2.1), p.6: for
each center `j`, the indexed balls are `B_{jℓ} = B(j, r_{jℓ})` for the distinct distances
`0 = r_{j1} < ⋯ < r_{jq_j} < γ` from `j`, at cost `a_{jℓ}⁻² = (γ − r_{jℓ})⁻²`, and
`F = min ∑_{j,ℓ} y_{jℓ} a_{jℓ}⁻²` subject to `y ≥ 0` and `∑_{(j,ℓ) : i ∈ B_{jℓ}} y_{jℓ} ≥ 1` for every `i`.

**Formalization Note.** An indexed ball is encoded by a pair `(j, i)` with `d j i < γ`: the ball
`B(j, d j i) = {i' : d i' j ≤ d j i}` at cost `(γ − d j i)⁻²`. Every distinct distance below `γ`
from `j` occurs (with `d j j = 0` the radius-zero ball); a repeated distance duplicates a ball at
the same cost, which leaves the optimum unchanged. The minimum is the real `sInf` of the feasible
costs, nonempty for `γ > 0` and bounded below by `0`. -/
noncomputable def certWorkload {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) : ℝ :=
  sInf {C : ℝ | ∃ y : ι × ι → ℝ, (∀ p, 0 ≤ y p) ∧
    (∑ p ∈ Finset.univ.filter (fun p : ι × ι => d p.1 p.2 < γ),
      y p * ((γ - d p.1 p.2) ^ 2)⁻¹) = C ∧
    ∀ i, 1 ≤ ∑ p ∈ Finset.univ.filter (fun p : ι × ι => d p.1 p.2 < γ ∧ d i p.1 ≤ d p.1 p.2), y p}

end MetricMinTest


