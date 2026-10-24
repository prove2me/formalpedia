-- Prove2me | Definitions.Def_OAI_PiExponent_ComponentLocalLength
-- name    : OAI_PiExponent_ComponentLocalLength
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-24T04:38:41.992214+00:00
-- url     : https://prove2.me/theorems/41f2cb5f-560b-401a-8265-8139d5a23b2c
-- title:
--   Extended length of a local component quotient
-- statement:
--   For ideals I and prime P in a commutative ring, define the extended module length of R_P/IR_P. Keeping infinity explicit avoids truncating a potentially infinite length.

import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace OAI.PiExponent.FormalInterpolation

/-- Length of the local quotient at a prime. The value is infinity when the
local quotient does not have finite length. -/
noncomputable def componentLocalLength {R : Type*} [CommRing R]
    (I P : Ideal R) [P.IsPrime] : ENat :=
  Module.length (Localization.AtPrime P)
    ((Localization.AtPrime P) ⧸
      I.map (algebraMap R (Localization.AtPrime P)))

end OAI.PiExponent.FormalInterpolation


