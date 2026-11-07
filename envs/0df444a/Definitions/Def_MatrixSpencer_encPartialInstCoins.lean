-- Prove2me | Definitions.Def_MatrixSpencer_encPartialInstCoins
-- name    : MatrixSpencer_encPartialInstCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:45:00.535538+00:00
-- url     : https://prove2.me/theorems/0ba703e6-c85e-478c-9101-4294856b58e3
-- title:
--   Encoding of a partial-coloring instance with coins
-- statement:
--   The encoding of the instance, the symbol $2$, and the coin string as bits.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11 (auxiliary encoding)

import Mathlib
import Definitions.Def_MatrixSpencer_encPartialInst
import Definitions.Def_OnlineCRS_Combine_bit

namespace MatrixSpencer

/-- **Encoding of a partial-coloring instance together with its coin string.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11.

The instance, the symbol `2`, and the coins as bits. -/
def encPartialInstCoins (x : PartialInst × List Bool) : List OnlineCRS.Combine.Sym :=
  encPartialInst x.1 ++ [2] ++ x.2.map OnlineCRS.Combine.bit

end MatrixSpencer


