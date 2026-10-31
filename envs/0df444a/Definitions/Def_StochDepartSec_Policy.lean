-- Prove2me | Definitions.Def_StochDepartSec_Policy
-- name    : StochDepartSec_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:02.855442+00:00
-- url     : https://prove2.me/theorems/4ca67447-556c-4720-bce0-ee2084679a16
-- title:
--   Policies and acceptance
-- statement:
--   A **policy** for $n$ candidates assigns to every outcome $\omega$ and time $t$ a decision: either to accept nobody, or to accept one named candidate. Candidate $i$ is **accepted** in $\omega$ if the decision at its departure time $D_i$ names $i$.
--
--   At most one candidate is accepted per instant, even when several depart together. Which information a decision may depend on is fixed by admissibility; that only the first acceptance counts is part of the success event.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_dep

namespace StochDepartSec

/-- A policy for the stochastic departure secretary problem: at every time `t` and in every outcome
it names at most one candidate to accept (`none` = accept nobody). Candidate `i` is accepted in
`ω` (`Accepts`) iff, at its departure time, the policy names `i`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5: "Whenever a candidate leaves, the algorithm must irrevocably make a choice to accept or
reject based only on the history until time t."

**Formalization Note** Decisions are `Option (Fin n)`, so at most one candidate is accepted per
instant even when several depart together (generic at time 1). A name of a candidate that does not
depart at `t` has no effect. Only the first acceptance counts (see `Policy.success`), which
renders "irrevocably". Which information the decision may use is `Policy.Admissible`. -/
structure Policy (n : ℕ) where
  /-- The decision at time `t` in outcome `ω`. -/
  decide : Outcome n → ℝ → Option (Fin n)

/-- Candidate `i` is accepted by `pol` in `ω`: the decision at `i`'s departure time names `i`. -/
def Policy.Accepts {n : ℕ} (pol : Policy n) (ω : Outcome n) (i : Fin n) : Prop :=
  pol.decide ω (dep ω i) = some i

end StochDepartSec


