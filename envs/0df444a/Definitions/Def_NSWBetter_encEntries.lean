-- Prove2me | Definitions.Def_NSWBetter_encEntries
-- name    : NSWBetter_encEntries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:33.664281+00:00
-- url     : https://prove2.me/theorems/550a3409-9611-450e-b95c-0d4c09d548c0
-- title:
--   Encoding of a list of entries
-- statement:
--   The binary encoding of a list of entries: the length of the list followed by the words of each entry, joined by the separator $3$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 2.5, p.10

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_NSWBetter_Entry
import Definitions.Def_NSWBetter_tokEntry

namespace NSWBetter

/-- **Encoding of a configuration LP solution by its entries.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 2.5, p.10: "represented using a list of the non-zero entries".

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def encEntries (l : List Entry) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (ReserveLB.tokList tokEntry l)

end NSWBetter


