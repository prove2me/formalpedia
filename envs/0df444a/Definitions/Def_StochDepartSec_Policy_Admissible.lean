-- Prove2me | Definitions.Def_StochDepartSec_Policy_Admissible
-- name    : StochDepartSec_Policy_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:49.426985+00:00
-- url     : https://prove2.me/theorems/7ca6f868-40f1-49bb-a6a9-102b17a62f33
-- title:
--   Admissible (nonanticipating, measurable) policies
-- statement:
--   A policy is **admissible** if
--
--   1. its decision at every time $t$ depends only on the history until $t$: whenever $\omega$ and $\omega'$ have the same history until $t$, the decisions at $t$ coincide; and
--   2. for every candidate $i$ the event "$i$ is accepted" is measurable.
--
--   The class contains every history-dependent policy, possibly randomized through the seed and possibly using the labels of the candidates.
--
--   **Formalization Note** Measurability of the acceptance events makes the success event measurable, so success probabilities are defined.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5 ("based only on the history until time t")

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_HistEq
import Definitions.Def_StochDepartSec_Policy
open MeasureTheory

namespace StochDepartSec

/-- A policy is admissible if its decision at every time `t` depends only on the history until
`t` (it is constant on `HistEq t`-classes), and the acceptance events are measurable.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5: the choice is made "based only on the history until time t".

**Formalization Note** The class contains every history-dependent policy, possibly randomized
through the seed and possibly reading the candidates' labels. Measurability of the events
"candidate `i` is accepted" makes the success event measurable, so success probabilities are
measures and not outer measures. -/
def Policy.Admissible {n : ℕ} (pol : Policy n) : Prop :=
  (∀ (t : ℝ) (ω ω' : Outcome n), HistEq t ω ω' → pol.decide ω t = pol.decide ω' t) ∧
  ∀ i, MeasurableSet {ω : Outcome n | pol.Accepts ω i}

end StochDepartSec


