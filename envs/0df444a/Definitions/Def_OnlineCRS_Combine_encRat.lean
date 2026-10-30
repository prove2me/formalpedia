-- Prove2me | Definitions.Def_OnlineCRS_Combine_encRat
-- name    : OnlineCRS_Combine_encRat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:20:44.866136+00:00
-- url     : https://prove2.me/theorems/76577621-6c08-4afd-811f-276915e8c1d1
-- title:
--   Encoding of a rational number
-- statement:
--   A rational number $q=p/d$ in lowest terms ($d\ge1$) is encoded as the encoding of the integer $p$, the separator $2$, and the binary encoding of $d$.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt

namespace OnlineCRS.Combine

/-- **Encoding of a rational number.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4 (efficiency): auxiliary encoding.

`encRat q` is the encoding of the reduced numerator, the separator `2`, and the binary encoding
of the denominator.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. -/
def encRat (q : ℚ) : List Sym := encInt q.num ++ [2] ++ encNat q.den

end OnlineCRS.Combine


