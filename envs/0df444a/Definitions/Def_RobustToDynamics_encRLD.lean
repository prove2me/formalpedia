-- Prove2me | Definitions.Def_RobustToDynamics_encRLD
-- name    : RobustToDynamics_encRLD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:06.647172+00:00
-- url     : https://prove2.me/theorems/91f1d378-44d3-443e-87ce-9fdd5aef2efd
-- title:
--   Binary encoding of an R-LD-LP instance $(A,b,c,G)$
-- statement:
--   An R-LD-LP instance is written as the encoding of its data $(A,b,G)$ followed by the encoded objective vector $c$.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, p.14; footnote 3, p.5

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_RobustToDynamics_encLD
import Definitions.Def_RobustToDynamics_RLDLP

namespace RobustToDynamics

/-- **Encoding of an R-LD-LP instance `(A, b, c, G)`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, p.14 (time
polynomial in `σ(A, b, c, G, ρ*)`) and footnote 3, p.5.

`encRLD I` is `encLD` of the data `(A, b, G)` followed by `encVec c`.

**Formalization Note.** Complexity questions are read in the standard Turing model (footnote 3,
p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` separates numerator and denominator, `3` separates items). Numbers are written in
binary with the published encodings `encNat`/`encRat`/`encVec` (rationals in lowest terms), so the
length of an encoding is polynomially related to the size σ of p.13. -/
def encRLD (I : RLDLP) : List OnlineCRS.Combine.Sym :=
  encLD I.data ++ OnlineCRS.Combine.encVec I.c

end RobustToDynamics


