-- Prove2me | Definitions.Def_AvoidPlast_HaltsWithin
-- name    : AvoidPlast_HaltsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:43:35.375954+00:00
-- url     : https://prove2.me/theorems/92112673-df76-4a98-9088-fbe161c5756e
-- title:
--   Halting within a time bound
-- statement:
--   The machine has reached a halting state after at most $t$ steps. Since halting configurations are fixed points, this is whether the configuration at step $t$ has a halting state.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_run

namespace AvoidPlast

/-- The machine has reached a halting state after at most `t` steps (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine
model; halting configurations are fixed points of `step`). -/
def HaltsWithin {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) (t : ℕ) : Prop :=
  M.halting (run M xs t).state = true

end AvoidPlast


