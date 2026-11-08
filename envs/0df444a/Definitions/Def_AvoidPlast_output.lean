-- Prove2me | Definitions.Def_AvoidPlast_output
-- name    : AvoidPlast_output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:46:18.073093+00:00
-- url     : https://prove2.me/theorems/817f1863-ddf2-43b3-9273-4ff6787b1a2b
-- title:
--   Output of a machine
-- statement:
--   The string on the write-only output tape when the machine halts. The transition function never reads this tape, so it cannot serve as work space.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_run
import Definitions.Def_AvoidPlast_haltTime

namespace AvoidPlast

/-- The string on the output tape when the machine halts (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model). The
output tape is write-only: the transition function never reads it. -/
noncomputable def output {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) : List Bool :=
  (run M xs (haltTime M xs)).out

end AvoidPlast


