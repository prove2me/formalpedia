-- Prove2me | Definitions.Def_OnlineCRS_Combine_encNat
-- name    : OnlineCRS_Combine_encNat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:18:52.249984+00:00
-- url     : https://prove2.me/theorems/a4d164ca-e30d-4266-a4d3-6430a4bfbfe4
-- title:
--   Binary encoding of a natural number
-- statement:
--   A natural number $k$ is encoded by its binary representation (Mathlib's `Computability.encodeNat`), written in the alphabet $\{0,1,2,3\}$. Its length is $O(\log k)$.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit

namespace OnlineCRS.Combine

/-- **Binary encoding of a natural number.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4 (efficiency): auxiliary encoding.

`encNat k` is Mathlib's binary `Computability.encodeNat k`, written in `Sym`.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. -/
def encNat (k : ℕ) : List Sym := (Computability.encodeNat k).map bit

end OnlineCRS.Combine


