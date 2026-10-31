-- Prove2me | Definitions.Def_StochDepartSec_Policy_NeverAcceptsBy
-- name    : StochDepartSec_Policy_NeverAcceptsBy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:42.17802+00:00
-- url     : https://prove2.me/theorems/0ea14e24-378e-45c5-827f-eb9641b0731a
-- title:
--   Policies rejecting every candidate arrived until $t$
-- statement:
--   A policy **never accepts by time $t$** if every candidate it accepts arrives strictly after $t$. This is the class over which the paper's policy $\mathrm{pol}_t$ is optimal: "the best policy out of those that reject all candidates that arrive until time $t$ (including $t$)".
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §4, p.11

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_Policy

namespace StochDepartSec

/-- The policy never accepts a candidate that arrived until time `t` (including `t`).
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §4, p.11: "Let pol_t be the best policy out of those that reject all candidates that arrive
until time t (including t)."

**Formalization Note** This is the constraint class of `pol_t`; `rejValue` optimizes over it. -/
def Policy.NeverAcceptsBy {n : ℕ} (pol : Policy n) (t : ℝ) : Prop :=
  ∀ ω i, pol.Accepts ω i → t < arrival ω i

end StochDepartSec


