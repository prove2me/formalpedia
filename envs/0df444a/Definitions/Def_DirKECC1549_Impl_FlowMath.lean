-- Prove2me | Definitions.Def_DirKECC1549_Impl_FlowMath
-- name    : DirKECC1549_Impl_FlowMath
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-16T06:50:30.961919+00:00
-- url     : https://prove2.me/theorems/6a965055-e9e7-43a6-970f-fbe0297b0690
-- title:
--   Lemma 3 on the word-RAM: residual cuts
-- statement:
--   The fact that a set with no residual edges leaving it is a cut whose out-degree equals the flow value.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Definitions.Def_DirKECC1549_Impl_SccMath

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

end DirKECC1549.Asm


