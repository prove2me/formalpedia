-- Prove2me | Definitions.Def_MatrixSpencer_encMatInstCoins
-- name    : MatrixSpencer_encMatInstCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:47.624387+00:00
-- url     : https://prove2.me/theorems/d59c95e8-d9d0-40f4-9c36-6d1cc608d7db
-- title:
--   Encoding of a matrix instance with coins
-- statement:
--   The encoding of the instance, the symbol $2$, and the coin string as bits. The machine is deterministic on this pair, so its time bound holds on every coin string.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 1.3, p.12 (auxiliary encoding)

import Mathlib
import Definitions.Def_MatrixSpencer_encMatInst
import Definitions.Def_OnlineCRS_Combine_bit

namespace MatrixSpencer

/-- **Encoding of an instance together with its coin string.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), auxiliary encoding for "randomized polynomial time" (p.12).

The instance, the symbol `2`, and the coins as bits. The machine is deterministic on this pair, so its
time bound holds for **every** coin string. -/
def encMatInstCoins (x : MatInst × List Bool) : List OnlineCRS.Combine.Sym :=
  encMatInst x.1 ++ [2] ++ x.2.map OnlineCRS.Combine.bit

end MatrixSpencer


