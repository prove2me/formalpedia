-- Prove2me | Definitions.Def_DirKECC1549_Impl_MainMath
-- name    : DirKECC1549_Impl_MainMath
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T23:45:20.532537+00:00
-- url     : https://prove2.me/theorems/a304305f-2315-43c9-8050-e9a4b0e99215
-- title:
--   Arithmetic facts for the cost of Algorithm 3's main branch
-- statement:
--   Auxiliary arithmetic notions for the cost accounting of the main branch ($4^k\le k^{3k}$, $n\le\Delta^2$, $\log_2 n+1\le2\Delta$).
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Definitions.Def_DirKECC1549_Impl_GraphAux
import Definitions.Def_DirKECC1549_Main_Alg3

set_option autoImplicit false

open Classical Finset DirKECC1549.Main

noncomputable section

namespace DirKECC1549.Asm

variable {n m : ℕ}

end DirKECC1549.Asm


