-- Prove2me | Definitions.Def_AvoidPlast_PrBPstarLEqPrL
-- name    : AvoidPlast_PrBPstarLEqPrL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:48:54.252294+00:00
-- url     : https://prove2.me/theorems/3c8edb97-18af-4069-80ae-2cc809174ed7
-- title:
--   The hypothesis prBP$^*$L = prL
-- statement:
--   The derandomization hypothesis of the main theorem: the classes prBP$^*$L and prL of promise problems are equal, as sets of promise problems.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.14, p.29; Section 1.2, p.3

import Mathlib
import Definitions.Def_AvoidPlast_InPrL
import Definitions.Def_AvoidPlast_InPrBPstarL

namespace AvoidPlast

/-- The derandomization hypothesis `prBP*L = prL` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.14, p.29; p.3): the equality of
the two promise classes. -/
def PrBPstarLEqPrL : Prop :=
  {P | InPrBPstarL P} = {P | InPrL P}

end AvoidPlast


