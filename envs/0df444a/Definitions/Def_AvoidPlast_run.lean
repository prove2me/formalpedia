-- Prove2me | Definitions.Def_AvoidPlast_run
-- name    : AvoidPlast_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:42:24.439149+00:00
-- url     : https://prove2.me/theorems/0b2d12a0-fd27-4e01-a6e7-0b0f25d0549d
-- title:
--   Machine runs
-- statement:
--   The configuration after $t$ steps on read-only inputs $(x_j)_j$, starting from the initial configuration.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Config
import Definitions.Def_AvoidPlast_initConfig
import Definitions.Def_AvoidPlast_step

namespace AvoidPlast

/-- The configuration after `t` steps on read-only inputs `xs` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine
model). -/
noncomputable def run {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) (t : ℕ) : Config M :=
  (step M xs)^[t] (initConfig M)

end AvoidPlast


