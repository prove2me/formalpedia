-- Prove2me | Definitions.Def_OWFLocalDesc_ratCode
-- name    : OWFLocalDesc_ratCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:11.904204+00:00
-- url     : https://prove2.me/theorems/c89e3c04-f09e-4ac6-9cb4-4dbab8eeca5a
-- title:
--   Binary encoding of a rational number
-- statement:
--   The **binary encoding** of a rational $\varepsilon$ lists its sign, the binary digits of the absolute value of its numerator and the binary digits of its positive denominator. Its length is, up to a constant, the combined bit length of numerator and denominator, the encoding length used in Theorem 4.3.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §4.1, p.17

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Binary encoding of a rational.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §4.1, p.17: "For a rational
accuracy parameter, its binary encoding length is the combined bit length of its numerator and
positive denominator." The code of `ε` is the tuple of the sign bit, the binary digits of
`|num ε|` and those of `den ε`. -/
def ratCode (ε : ℚ) : List Bool :=
  QuantumPRC.tupleCode [[decide (ε < 0)], Nat.bits ε.num.natAbs, Nat.bits ε.den]

end OWFLocalDesc


