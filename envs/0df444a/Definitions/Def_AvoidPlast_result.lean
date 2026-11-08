-- Prove2me | Definitions.Def_AvoidPlast_result
-- name    : AvoidPlast_result
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:28.695193+00:00
-- url     : https://prove2.me/theorems/3a7772ea-3561-4223-9901-56ce099f473d
-- title:
--   Result of a proof-printing machine
-- statement:
--   The result of a proof-printing machine: the printed string when the machine accepts, and $\bot$ when it rejects.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.12, p.27

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts

namespace AvoidPlast

open Classical in
/-- The result of a proof-printing machine (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.12, p.27): the printed string when the
machine accepts, and `⊥` (`none`) when it rejects. -/
noncomputable def result (M : Machine 1) (x : List Bool) : Option (List Bool) :=
  if Accepts M ![x] then some (output M ![x]) else none

end AvoidPlast


