-- Prove2me | Definitions.Def_FRouting_Supplement_encRat
-- name    : FRouting_Supplement_encRat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:19:09.639836+00:00
-- url     : https://prove2.me/theorems/30152637-3286-4be9-9063-94f977797b31
-- title:
--   Binary description of a rational number
-- statement:
--   A rational number $r=p/q$ in lowest terms, $q\ge1$, is described by a sign bit for $p$, then $|p|$ and $q$, each in self-delimiting binary. Since rationals are stored in lowest terms the description is injective, and it is self-delimiting: a binary string has at most one prefix that describes a rational.
--
--   This is the output format of the fidelity estimators of Theorems 6.3 and 7.10, which output a rational approximation $\widetilde F$.
--
--   **Formalization Note** The paper fixes no output format; any injective self-delimiting binary format of the rationals is computably equivalent to this one in linear time.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 6.3, p.23; Theorem 7.10, p.35

import Definitions.Def_FRouting_encCircuit

set_option autoImplicit false

namespace FRouting.Supplement

open QAlgorithms.Complexity

/-- An integer: a sign bit (`true` for negative), then its absolute value in self-delimiting binary. -/
def encInt (z : ℤ) : Str :=
  (if z < 0 then [true] else [false]) ++ encBin z.natAbs

/-- **The description of a rational number** `F̃`, the output of the fidelity estimators of Renard,
*Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorems 6.3 (p.23)
and 7.10 (p.35): the numerator, then the denominator of the reduced fraction, both self-delimiting.

**Formalization Note** The paper fixes no output format. Since `ℚ` stores reduced fractions this encoding
is injective, and it is self-delimiting, so a string has at most one prefix of this form. -/
def encRat (r : ℚ) : Str :=
  encInt r.num ++ encBin r.den

end FRouting.Supplement


