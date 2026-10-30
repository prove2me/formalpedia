-- Prove2me | Definitions.Def_OnlineCRS_Combine_encInt
-- name    : OnlineCRS_Combine_encInt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:19:38.908767+00:00
-- url     : https://prove2.me/theorems/d92f881b-e374-4b9b-aa04-743eceb00966
-- title:
--   Encoding of an integer
-- statement:
--   An integer $z$ is encoded by a sign bit ($1$ iff $z<0$) followed by the binary encoding of $|z|$.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat

namespace OnlineCRS.Combine

/-- **Encoding of an integer.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4 (efficiency): auxiliary encoding.

`encInt z` is a sign bit (`1` iff `z < 0`) followed by the binary encoding of `|z|`.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. -/
def encInt (z : ℤ) : List Sym := bit (decide (z < 0)) :: encNat z.natAbs

end OnlineCRS.Combine


