-- Prove2me | Definitions.Def_PrideGuilt_benchOpt
-- name    : PrideGuilt_benchOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:54.142903+00:00
-- url     : https://prove2.me/theorems/9d937461-7e71-4983-abdd-5d0cd703ac9d
-- title:
--   Benchmark optimal profit $\Pi_0$
-- statement:
--   The benchmark optimal profit is
--
--   $$
--   \Pi_0=\sup\{\tilde\Pi(p) : p\in\mathbb R,\ \tilde D(p)\ge0\}.
--   $$
--
--   The manufacturer remanufactures only if this is beaten (Proposition 1).
--
--   **Formalization Note** The constraint $\tilde D\ge0$ matches the demand constraint in $\Pi^*$; under the standing assumption $1-b_1I_G-b_0c_n\ge0$ it does not bind.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), §4 and eq. (7), p.12

import Mathlib
import Definitions.Def_PrideGuilt_benchProfit

namespace PrideGuilt

/-- **The benchmark optimal profit `Π₀`, over prices with nonnegative demand.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, §4 and eq. (7), p.12 (PDF 13).

`Π₀ = sup {Π̃(p) : p ∈ ℝ, D̃(p) ≥ 0}`.

**Formalization Note.** The constraint `D̃ ≥ 0` matches the demand constraint of `optProfit`;
under the standing assumption `1 − b₁I_G − b₀c_n ≥ 0` the unconstrained maximizer `p₀` is
feasible, so the constraint does not change the value (`benchmark_optimum`). -/
noncomputable def benchOpt (P : Params) : ℝ :=
  sSup {π : ℝ | ∃ p : ℝ, 0 ≤ benchDemand P p ∧ π = benchProfit P p}

end PrideGuilt


