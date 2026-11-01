-- Prove2me | Definitions.Def_CloudCostOpt_resCost
-- name    : CloudCostOpt_resCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:06.667993+00:00
-- url     : https://prove2.me/theorems/472ecd67-2598-407d-838e-670f820ba2a0
-- title:
--   Per-period price $R_j$ of resource type $j$, with $R_0=0$
-- statement:
--   For a resource type $j\in\{0,1,\dots,J\}$, $R_j$ is the reserved price of type $j$ for $j\ge1$, and $R_0=0$ for the dummy resource. In the relaxed problems $\mathbb P_{LB}$ and $\hat{\mathbb P}_i$, $R_j$ is the price of one period of service on resource type $j$; idling is free.
--
--   **Formalization Note** Defined on `Fin (J+1)` by cases: `0` gives `0` and `j+1` gives `R j`.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.3 ("we define M₀ = ∞, R₀ = 0"); §3, p.12 (problem P̂ᵢ)

import Mathlib
import Definitions.Def_CloudCostOpt_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Per-period price `R_j` of resource type `j : Fin (J + 1)`** in the relaxed problems
`ℙ_LB` and `ℙ̂ᵢ`: `R₀ = 0` for the dummy resource and `R_{j}` for real type `j ≥ 1`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.3 ("we define `M₀ = ∞`, `R₀ = 0`"); §3, p.12 (`ℙ̂ᵢ`). -/
noncomputable def resCost (S : System) (j : Fin (S.J + 1)) : ℝ :=
  Fin.cases 0 S.R j

end CloudCostOpt


