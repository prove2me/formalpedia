-- Prove2me | Definitions.Def_NSWBetter_encInst
-- name    : NSWBetter_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:39.338374+00:00
-- url     : https://prove2.me/theorems/2e930d53-4176-45ae-a1ac-19708e4a1df4
-- title:
--   Binary encoding of an instance
-- statement:
--   The binary encoding $\langle I\rangle$ of an instance: the words of the instance joined by the separator symbol $3$. Its length is the input size with respect to which "efficient" (polynomial time) is measured.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_tokInst

namespace NSWBetter

/-- **Binary encoding of an instance.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 1.1, p.3: "efficient", i.e. polynomial in the input size.

`encInst I` joins the words `tokInst I` by the separator `3`. Its length is the input size of `I`.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, over the alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (`OnlineCRS.Combine.encNat`, `encRat`), so the length of an encoding is the usual bit size. Every list is preceded by its length and the words contain no `3`, so the encoding is injective (decoded in `Solutions/verification/NSWBetter_encodings.lean`). -/
def encInst (I : Inst) : List OnlineCRS.Combine.Sym := [3].intercalate (tokInst I)

end NSWBetter


