-- Prove2me | Definitions.Def_VolunteerEngage_Thresholds_Supplement_RelativeValue
-- name    : VolunteerEngage_Thresholds_Supplement_RelativeValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:05:38.762044+00:00
-- url     : https://prove2.me/theorems/6cbba4a0-4a1b-4029-bcda-2863bfab1b93
-- title:
--   The feedback policy (70) and relative value f (p. 22)
-- statement:
--   Let $(\beta,v)$ solve (68)–(69), let $p$ be the idleness cost rate and $\psi$ the minimal maximizer (67). The feedback drift and relative value function are
--
--   $$\theta^*(z)=\psi(p-v(z)),\qquad f(z)=\int_0^z v(s)\,ds-pz,\qquad z\ge0.$$
--
--   The integral constructs $f$ from $v$; the feedback function is defined independently of the threshold formula (72). Corollary 1 supplies the Bellman properties of $f$, and Theorem 2 identifies the feedback with the threshold policy.
--
--   **Formalization Note** These are real functions with their required properties stated on $[0,\infty)$. The ordinary time integral is an interval integral; continuity of a Bellman solution prevents a default value from nonintegrability.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 22, (70), definition of f before Corollary 1

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_Psi

namespace VolunteerEngage.Thresholds.Supplement

/-- The feedback policy (70), independently defined from the least maximizer. -/
noncomputable def feedback (M : Model) (v : ℝ → ℝ) (z : ℝ) : ℝ :=
  psi M (M.p - v z)

/-- The relative value function defined immediately before Corollary 1, p. 22. -/
noncomputable def relativeValue (M : Model) (v : ℝ → ℝ) (z : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..z, v s) - M.p * z

end VolunteerEngage.Thresholds.Supplement


