-- Prove2me | Definitions.Def_AvoidPlast_Halts
-- name    : AvoidPlast_Halts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:44:51.777474+00:00
-- url     : https://prove2.me/theorems/2b9a8dcc-ba70-4c38-8ab9-057807b876b9
-- title:
--   Halting
-- statement:
--   The machine halts on the given inputs: it halts within some number of steps.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin

namespace AvoidPlast

/-- The machine halts on read-only inputs `xs` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model). -/
def Halts {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) : Prop :=
  ∃ t, HaltsWithin M xs t

end AvoidPlast


