-- Prove2me | Definitions.Def_OnlineCRS_Combine_bit
-- name    : OnlineCRS_Combine_bit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:18:14.809788+00:00
-- url     : https://prove2.me/theorems/a030708d-5c2c-405a-97e6-66fbc924d951
-- title:
--   A Boolean as a tape symbol
-- statement:
--   The symbol of a Boolean value: $\mathrm{true}\mapsto 1$, $\mathrm{false}\mapsto 0$ in the alphabet $\{0,1,2,3\}$.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym

namespace OnlineCRS.Combine

/-- **A Boolean as a tape symbol.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4 (efficiency): auxiliary encoding.

`bit true = 1`, `bit false = 0` in `Sym = Fin 4`.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. -/
def bit (b : Bool) : Sym := if b then 1 else 0

end OnlineCRS.Combine


