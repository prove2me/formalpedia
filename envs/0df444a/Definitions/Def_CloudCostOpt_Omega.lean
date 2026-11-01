-- Prove2me | Definitions.Def_CloudCostOpt_Omega
-- name    : CloudCostOpt_Omega
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:07.19593+00:00
-- url     : https://prove2.me/theorems/381eff0e-e8f0-42a4-8180-74fa36aa03d3
-- title:
--   Sample space: arrival counts and step uniforms
-- statement:
--   The sample space consists of pairs $\omega=(N,U)$:
--
--   1. $N(i,t)\in\mathbb N$, the number of type-$i$ orders that arrive in period $t$;
--   2. $U(i,t,s,l,j,k)\in[0,1]$, the uniform variable deciding whether the $k$-th of the type-$i$ orders in order-state $(s,l)$ that are sent to resource type $j$ in period $t$ completes its step.
--
--   **Formalization Note** The arrival count with period index $0$ is never used.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.3 (Poisson arrivals); §3, pp.13–14, (4)–(5)

import Mathlib
import Definitions.Def_CloudCostOpt_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The sample space** of the model: arrival counts `N (i, t)` (the number of type-`i` orders
arriving in period `t`) and uniforms `U (i, t, s, l, j, k)` (the `k`-th order of cell `(i, s, l)`
sent to resource `j` in period `t` completes its step iff `U (i, t, s, l, j, k) < β_{i,j}`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.3 (Poisson arrivals, independent step outcomes), §3, pp.13–14, (4)–(5).

Formalization Note: index `t = 0` of the arrival counts is never used. -/
abbrev Omega (S : System) : Type :=
  (Fin S.I × ℕ → ℕ) × (Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)

end CloudCostOpt


