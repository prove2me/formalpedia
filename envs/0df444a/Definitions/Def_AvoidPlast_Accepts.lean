-- Prove2me | Definitions.Def_AvoidPlast_Accepts
-- name    : AvoidPlast_Accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:46:23.984196+00:00
-- url     : https://prove2.me/theorems/ab6d99f7-fb43-4b97-8120-f3b448492597
-- title:
--   Acceptance
-- statement:
--   The machine halts on the given inputs in an accepting state. A non-halting run does not accept.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_run
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_haltTime

namespace AvoidPlast

/-- The machine halts on `xs` in an accepting state (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model). A
non-halting run does not accept. -/
def Accepts {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) : Prop :=
  Halts M xs ∧ M.accepting (run M xs (haltTime M xs)).state = true

end AvoidPlast


