-- Prove2me | Definitions.Def_DiffCtrlRobust_discCost
-- name    : DiffCtrlRobust_discCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:10.562011+00:00
-- url     : https://prove2.me/theorems/16648278-5c54-48b2-b9eb-8b847b93c08f
-- title:
--   The $\alpha$-discounted cost $\mathcal J^U_\alpha(x,c)$
-- statement:
--   The $\alpha$-discounted cost of an admissible control $U$ with state process $X$ is
--
--   $$
--   \mathcal J^U_\alpha(x,c):=\mathbb E^U_x\left[\int_0^\infty e^{-\alpha s}c(X_s,U_s)\,\mathrm ds\right],
--   $$
--
--   where $c(x,\mathrm v)$ is the relaxed cost. The same formula with $c_n$ and $X^n$ is the cost $\mathcal J^U_{\alpha,n}(x,c_n)$ of (2.17).
--
--   **Formalization Note** Both integrals are Bochner integrals. For a bounded continuous cost, $\alpha>0$, and an admissible pair, the integrand is jointly measurable and dominated by $Me^{-\alpha s}$, so nothing is a default value.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2.1, p.6, (2.2), and §2.2, p.8, (2.17)

import Definitions.Def_DiffCtrlRobust_relaxed
import Definitions.Def_EthierKurtz_SDEState

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The `α`-discounted cost (2.2), (2.17) of a control `u` with state process `X`
(arXiv:2205.05894v2, §2.1, p.6, and §2.2, p.8):
`𝔼[∫₀^∞ e^{-α s} c(X_s, u_s) ds]`, with `c(x, v)` the relaxed cost.

**Formalization Note.** Both integrals are Bochner integrals. For a bounded, continuous cost, an
admissible `u` and a continuous `X`, the integrand is jointly measurable and dominated by
`M e^{-α s}`, so for `α > 0` these are genuine integrals. -/
noncomputable def discCost {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Type*} [MeasurableSpace U]
    (P : Measure Ω) (α : ℝ) (c : SDEState d → U → ℝ)
    (u : ℝ≥0 → Ω → ProbabilityMeasure U) (X : ℝ≥0 → Ω → SDEState d) : ℝ :=
  ∫ ω, (∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-α * s) * relaxed c (X s.toNNReal ω) (u s.toNNReal ω)) ∂P

end DiffCtrlRobust


