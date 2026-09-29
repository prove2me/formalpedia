-- Prove2me | Definitions.Def_CollatzMission
-- name    : CollatzMission
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-08T03:44:33.556239+00:00
-- url     : https://prove2.me/theorems/237a1ab6-a330-48a1-9ec5-eb84f0db1be8
-- title:
--   Collatz mission predicates
-- statement:
--   Defines the classical Collatz map and three mission interfaces: the conjecture restricted to positive odd inputs, one-avoiding eventually cyclic counterexamples, and one-avoiding non-eventually-cyclic counterexamples. The latter is a logical non-cycle branch and does not by itself assert unbounded growth.
-- source:
--   https://github.com/flound1129/collatz/blob/c0b24f073dcdc63d9d0974429bd8f3c522ed8eb4/lean/CollatzConjecture/Basic.lean#L11-L14 and https://github.com/flound1129/collatz/blob/c0b24f073dcdc63d9d0974429bd8f3c522ed8eb4/lean/CollatzConjecture/Formulations.lean#L26-L28, L154-L176

import Mathlib

namespace CollatzMission

/-- The classical Collatz step used by the mission's supporting reductions. -/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- The Collatz claim restricted to positive odd starting values. -/
def OddInputsConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ¬Even n → ∃ m : ℕ, collatzStep^[m] n = 1

/-- The forward orbit of `n` never visits `1`. -/
def OrbitAvoidsOne (n : ℕ) : Prop :=
  ∀ k : ℕ, collatzStep^[k] n ≠ 1

/-- A one-avoiding orbit which eventually repeats. -/
def EventualCycleCounterexample (n : ℕ) : Prop :=
  OrbitAvoidsOne n ∧
    ∃ start period : ℕ,
      0 < period ∧ collatzStep^[period] (collatzStep^[start] n) = collatzStep^[start] n

/-- A one-avoiding orbit which is not eventually cyclic. -/
def DivergentCounterexample (n : ℕ) : Prop :=
  OrbitAvoidsOne n ∧ ¬EventualCycleCounterexample n

/-- No positive starting value has a one-avoiding eventually cyclic orbit. -/
def NoEventualCycleCounterexamples : Prop :=
  ∀ n : ℕ, 0 < n → ¬EventualCycleCounterexample n

/-- No positive starting value has a one-avoiding non-cyclic orbit. -/
def NoDivergentCounterexamples : Prop :=
  ∀ n : ℕ, 0 < n → ¬DivergentCounterexample n

end CollatzMission


