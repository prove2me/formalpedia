-- Prove2me | Definitions.Def_VolunteerEngage_Thresholds_Supplement_Psi
-- name    : VolunteerEngage_Thresholds_Supplement_Psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:03:52.967802+00:00
-- url     : https://prove2.me/theorems/1634d2e6-a247-4cc4-9fef-2e68b6d185ca
-- title:
--   The minimal maximizer ψ (67)
-- statement:
--   For the published engagement model, let $A=[\theta_0,\theta_L]$, $c$ be the cost (52), and $\phi$ its convex conjugate (66). Define the minimal maximizer by
--
--   $$\psi(y)=\inf\{x\in A:yx-c(x)=\phi(y)\},\qquad y\in\mathbb R.$$
--
--   This optimization definition is independent of the step formula (E8), which is a theorem target. Under the standing assumptions the maximizing set is a nonempty compact subset of $A$, so the infimum is its smallest member.
--
--   **Formalization Note** The cost and conjugate are imported unchanged from the published Thresholds Setting. Lean uses real `sInf`; on an empty set its default would be zero, but no theorem uses it without Standing, and (E8) explicitly asserts attainment.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 21, (66)–(67)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

namespace VolunteerEngage.Thresholds.Supplement

/-- The least maximizer (67), defined from the optimization problem, not (E8). -/
noncomputable def psi (M : Model) (y : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Set.Icc M.θ0 (M.θ M.L) ∧ y * x - cost M x = phi M y}

end VolunteerEngage.Thresholds.Supplement


