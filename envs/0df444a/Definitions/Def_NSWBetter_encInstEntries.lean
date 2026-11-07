-- Prove2me | Definitions.Def_NSWBetter_encInstEntries
-- name    : NSWBetter_encInstEntries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:59.576303+00:00
-- url     : https://prove2.me/theorems/2ea37b8b-0563-4252-a2b6-10ab66bf533b
-- title:
--   Encoding of an instance with a configuration LP solution
-- statement:
--   The binary encoding of an instance together with a configuration LP solution given by its list of entries.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 5.2, p.28; Theorem 6.1, p.36

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_tokInst
import Definitions.Def_NSWBetter_Entry
import Definitions.Def_NSWBetter_tokEntry

namespace NSWBetter

/-- **Input of the algorithms of Theorems 5.2 and 6.1.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 5.2, p.28; Theorem 6.1, p.36: the algorithms take the instance and the configuration LP solution `y`.

`encInstEntries (I, l)`: the words of `I` followed by the words of the entry list `l` of `y`, joined by `3`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def encInstEntries (x : Inst × List Entry) : List OnlineCRS.Combine.Sym :=
  [3].intercalate (tokInst x.1 ++ ReserveLB.tokList tokEntry x.2)

end NSWBetter


