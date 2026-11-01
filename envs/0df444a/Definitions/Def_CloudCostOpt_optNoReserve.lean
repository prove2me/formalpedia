-- Prove2me | Definitions.Def_CloudCostOpt_optNoReserve
-- name    : CloudCostOpt_optNoReserve
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:11:27.913712+00:00
-- url     : https://prove2.me/theorems/05d9cfdb-42cc-4178-a72c-f46115f11ee6
-- title:
--   Optimal value $OPT(\infty,\mathbf R)$
-- statement:
--   $OPT(\infty,\mathbf R)$ is the optimal value of the variant of $\mathbb P$ in which reserved resources are infinitely expensive and an on-demand resource of type $j$ costs $R_j$ per period: the infimum of $f^\pi_{LB}$ over stable policies that reserve nothing ($M_j=0$ for all $j$).
--
--   **Formalization Note** A policy with some $M_j>0$ costs $+\infty$ per period in this variant, so it is the restriction of $\mathbb P(\mathbf R,\mathbf R)$ to $\mathbf M=0$.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.5 (the notation P(∞, R)); §3, p.12, (3)

import Mathlib
import Definitions.Def_CloudCostOpt_opt

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`OPT(∞, R)`**: the optimal value of `ℙ(∞, R)`, the variant of `ℙ` in which reserved
resources are infinitely expensive and on-demand type `j` costs `R_j`; equivalently the infimum of
`f^π_LB` over stable policies that reserve nothing (`M = 0`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.5 ("the notation `ℙ(∞, R)`"); §3, p.12, (3).

Formalization Note: with `M = 0` the reserved price does not enter the cost, so `ℙ(∞, R)` is the
restriction of `ℙ(R, R)` to `M = 0` (any `M ≠ 0` costs `+∞` per period). -/
noncomputable def optNoReserve (S : System) (lam : Fin S.I → ℝ≥0) : ℝ≥0∞ :=
  ⨅ (π : Policy S) (_ : IsStable S lam π) (_ : π.M = 0), avgCost S S.R S.R lam π

end CloudCostOpt


