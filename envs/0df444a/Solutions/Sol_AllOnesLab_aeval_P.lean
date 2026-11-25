-- Prove2me | solution 1 for AllOnesLab.aeval_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:03.056283+00:00
-- url     : https://prove2.me/submissions/e34a7237-69bc-4a70-ae9c-773ed10b693a

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution {L : Type*} [CommRing L] [Algebra (ZMod 2) L] (z : L) :
    aeval z P = z ^ 2 + z + 1 := by
  simp only [P, map_add, map_pow, aeval_X, map_one]
end AllOnesLab
