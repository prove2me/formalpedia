-- Prove2me | Definitions.Def_EPRPharma_DecisionFeasible
-- name    : EPRPharma_DecisionFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:07:01.251263+00:00
-- url     : https://prove2.me/theorems/0dd33428-2a93-4220-ba6e-cde911bc6741
-- title:
--   Feasible decisions of the producer
-- statement:
--   A decision $(p,\eta_d,\eta_p)$ is feasible if
--
--   1. $0\le\eta_d\le 1$ and $0\le\eta_p\le 1$, and
--   2. the doctor's utility at her prescription is nonnegative for every need: $U_d(q_p^*(\theta_n))\ge 0$ for all $\theta_n\in[0,1]$.
--
--   The price $p$ is unrestricted. These are the constraints of the producer's problem: he "maximizes his expected profit while maintaining a non-negative utility level for the doctor".
--
--   **Formalization Note** The participation constraint is imposed for every $\theta_n\in[0,1]$, following p. 15 ("we need $U_d(\theta_n)=(\eta_d+u_p-p)\theta_n\ge 0$").
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered display); p. 15

import Mathlib
import Definitions.Def_EPRPharma_doctorQ

namespace EPRPharma

/-- **Feasible producer decisions.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered display):
the producer's problem is subject to "0 ≤ η_d ≤ 1, 0 ≤ η_p ≤ 1, U_d(q*_p) ≥ 0" ("while
maintaining a non-negative utility level for the doctor, i.e., U_d ≥ 0").

**Formalization Note.** The doctor's participation U_d(q*_p) ≥ 0 is required for every need
θ_n ∈ [0, 1], following p. 15 ("we need U_d(θ_n) = (η_d + u_p − p)θ_n ≥ 0"). The price p is
unrestricted. -/
def DecisionFeasible (P : Params) (d : Decision) : Prop :=
  0 ≤ d.etaD ∧ d.etaD ≤ 1 ∧ 0 ≤ d.etaP ∧ d.etaP ≤ 1 ∧
    ∀ θn ∈ Set.Icc (0:ℝ) 1, 0 ≤ Ud P d θn (doctorQ P d θn)

end EPRPharma


