-- Prove2me | solution 1 for AllOnesLab.aeval_asPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:00.71255+00:00
-- url     : https://prove2.me/submissions/cd28e17c-e6cb-46d4-a424-99d11a5d2e48

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard

set_option autoImplicit true
open Polynomial
open AllOnesLab
variable {K : Type*} [Field K]
namespace AllOnesLab
theorem _root_.solution {L : Type*} [CommRing L] [Algebra K L] (a : K) (z : L) :
    aeval z (asPoly a) = z ^ 2 + z + algebraMap K L a := by
  simp only [asPoly, map_add, map_pow, aeval_X, aeval_C]
end AllOnesLab
