-- Prove2me | Definitions.Def_EPRPharma_PolicyFeasible
-- name    : EPRPharma_PolicyFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:07:37.926219+00:00
-- url     : https://prove2.me/theorems/82de60dc-571c-43bc-a4a8-232502c89841
-- title:
--   Feasible policies of the social planner
-- statement:
--   A policy is a pair $y=(r,t)$ of real numbers.
--
--   1. Under EC, $y=(r_{EC},0)$ is feasible iff $0\le r_{EC}\le 1$ (the EC model has no fee).
--   2. Under SR, $y=(r_{SR},t)$ is feasible iff $0\le r_{SR}\le 1$ and $t\ge 0$.
--
--   **Formalization Note** EC policies are encoded with second component $0$; no EC quantity reads it.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered display)

import Mathlib
import Definitions.Def_EPRPharma_Model

namespace EPRPharma

/-- **Feasible policies of the social planner.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, pp. 12–13: the planner sets the
associated model parameter(s) y_P "such that 0 ≤ r_P ≤ 1, t ≥ 0 (if P = SR)"; y_EC = r_EC and
y_SR = (r_SR, t).

**Formalization Note.** A policy is a pair `y = (r, t)` of reals. An EC policy is encoded as
`(r_EC, 0)`: it is feasible iff 0 ≤ r ≤ 1 and t = 0, and no EC quantity reads `t`. An SR policy
`(r_SR, t)` is feasible iff 0 ≤ r ≤ 1 and 0 ≤ t. -/
def PolicyFeasible : Model → ℝ × ℝ → Prop
  | .EC, y => 0 ≤ y.1 ∧ y.1 ≤ 1 ∧ y.2 = 0
  | .SR, y => 0 ≤ y.1 ∧ y.1 ≤ 1 ∧ 0 ≤ y.2

end EPRPharma


