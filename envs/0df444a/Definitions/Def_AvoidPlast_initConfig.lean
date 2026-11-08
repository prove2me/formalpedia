-- Prove2me | Definitions.Def_AvoidPlast_initConfig
-- name    : AvoidPlast_initConfig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:40:48.098564+00:00
-- url     : https://prove2.me/theorems/0aa89fe6-d7c4-432a-a784-532a397c601f
-- title:
--   The initial configuration
-- statement:
--   The initial configuration has the start state, blank work tapes, every head on cell $0$ and an empty output.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Config

namespace AvoidPlast

/-- The initial configuration (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model): start state `0`, blank work
tapes, all heads on cell `0`, empty output. -/
def initConfig {r : ℕ} (M : Machine r) : Config M :=
  ⟨0, fun _ _ => none, fun _ => 0, fun _ => 0, []⟩

end AvoidPlast


