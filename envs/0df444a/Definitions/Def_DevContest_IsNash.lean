-- Prove2me | Definitions.Def_DevContest_IsNash
-- name    : DevContest_IsNash
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:52:55.252059+00:00
-- url     : https://prove2.me/theorems/60b090cd-64ae-4003-aed1-9a315ffd5748
-- title:
--   Nash equilibrium of the contest under a disclosure policy
-- statement:
--   A profile is a **Nash equilibrium** under a policy when both strategies are admissible and no agent can raise her expected utility by switching to another strategy admissible for her, the other agent's strategy being held fixed.
--
--   No symmetry is required, and no behaviour of an agent with one success is imposed.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, p.ec1

import Mathlib
import Definitions.Def_DevContest_payoff

open scoped ENNReal NNReal

namespace DevContest

/-- Nash equilibrium of the contest under the policy `D`, Khorasani, Körpeoğlu, Krishnan, *Dynamic
Development Contests*, author manuscript, p.ec1: both strategies are admissible, and no agent gains
from a deviation to another strategy admissible for her.

**Formalization Note.** Symmetry is not required, and no behaviour is imposed on an agent with one
success: a Nash equilibrium here is any profile with this property. -/
structure IsNash (lam c Rbar : ℝ) {U M : Type} [MeasurableSpace U] (D : Policy U M)
    (x : Fin 2 → Strategy U) : Prop where
  /-- Both strategies are admissible. -/
  admissible : ∀ i, IsAdmissible D i (x i)
  /-- No admissible deviation is profitable. -/
  best : ∀ (i : Fin 2) (y : Strategy U), IsAdmissible D i y →
    payoff lam c Rbar D (Function.update x i y) i ≤ payoff lam c Rbar D x i

end DevContest


