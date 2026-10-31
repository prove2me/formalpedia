-- Prove2me | Definitions.Def_TSPSDPGap_integralityGapSDP2
-- name    : TSPSDPGap_integralityGapSDP2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:54.405393+00:00
-- url     : https://prove2.me/theorems/01dc7217-13c6-4689-8777-a1565e777f64
-- title:
--   Integrality gap of SDP (2)
-- statement:
--   Fix, for every number $n+1$ of vertices, the indices $r(n),s(n)\in[n+1]$ of SDP (2). The **integrality gap of SDP (2)** is
--   $$
--   \sup_{n\ge2}\ \sup_{D\ \text{metric on } n+1 \text{ cities}}\ \frac{\mathrm{OPT}_{\mathrm{TSP}}(D)}{\mathrm{OPT}_{\mathrm{SDP}}(D)},
--   $$
--   where a cost matrix is **metric** if it is symmetric, has zero diagonal and satisfies the triangle inequality, and $\mathrm{OPT}_{\mathrm{TSP}}(D)$ is the cost of an optimal tour.
--
--   Any instance $D$ gives the lower bound $\mathrm{OPT}_{\mathrm{TSP}}(D)/\mathrm{OPT}_{\mathrm{SDP}}(D)$ on the gap.
--
--   **Formalization Note** Metric costs and the optimal tour are the published `MetricTSP.IsMetricCost` and `MetricTSP.tspOpt`. The ratio is taken in $[0,\infty]$ ($x/0=\infty$ for $x>0$, $0/0=0$). The supremum runs over instances with at least $3$ cities; a lower bound on it is a lower bound on the supremum over all instance sizes.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §2.1, p.5 (integrality gap); SDP (2), p.7

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_TSPSDPGap_sdp2Opt

open scoped ENNReal

namespace TSPSDPGap

/-- **The integrality gap of SDP (2).**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §2.1, p.5: "If 𝒟 is the set of all cost matrices corresponding to metric
and symmetric TSP instances, the integrality gap of the SDP is
sup_{D∈𝒟} OPT_TSP(D)/OPT_SDP(D)", for SDP (2) viewed on `n + 1` vertices (p.7).

Given rules `r, s` choosing the indices `r(n), s(n) ∈ [n + 1]` of SDP (2) for each number
`n + 1` of vertices, the gap is the supremum of `OPT_TSP(D) / OPT_SDP(2)(D)` over every
`n ≥ 2` and every metric cost matrix `D` on `n + 1` cities.

**Formalization Note.** Metric costs and the optimal tour cost are the published
`MetricTSP.IsMetricCost` (symmetric, zero diagonal, triangle inequality) and
`MetricTSP.tspOpt`. The ratio is computed in `ℝ≥0∞` (`x / 0 = ⊤` for `x ≠ 0`, `0 / 0 = 0`).
Instances have at least `3` cities (`n ≥ 2`); a lower bound on this supremum is a lower bound
on the supremum over all instance sizes. -/
noncomputable def integralityGapSDP2 (r s : (n : ℕ) → Fin (n + 1)) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : 2 ≤ n) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (_ : MetricTSP.IsMetricCost D),
    ENNReal.ofReal (MetricTSP.tspOpt D) / sdp2Opt n D (r n) (s n)

end TSPSDPGap


