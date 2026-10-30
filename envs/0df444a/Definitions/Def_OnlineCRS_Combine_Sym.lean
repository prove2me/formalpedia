-- Prove2me | Definitions.Def_OnlineCRS_Combine_Sym
-- name    : OnlineCRS_Combine_Sym
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:48.680726+00:00
-- url     : https://prove2.me/theorems/101df28f-a01f-4bad-b416-607349e089d6
-- title:
--   Tape alphabet for the efficiency machines
-- statement:
--   The alphabet $\{0,1,2,3\}$ used to encode inputs of the machines in Definition 1.7: $0$ and $1$ are bits, $2$ separates the numerator and denominator of a rational number, and $3$ separates items.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib

namespace OnlineCRS.Combine

/-- **Tape alphabet for the machines of Definition 1.7.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4 (efficiency): auxiliary encoding for "a polynomial time algorithm".

`Sym = Fin 4`: symbols `0`, `1` are bits, `2` separates the numerator and denominator of a
rational, `3` separates items.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. -/
abbrev Sym : Type := Fin 4

end OnlineCRS.Combine


