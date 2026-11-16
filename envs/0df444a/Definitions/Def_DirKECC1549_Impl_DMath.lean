-- Prove2me | Definitions.Def_DirKECC1549_Impl_DMath
-- name    : DirKECC1549_Impl_DMath
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-16T05:12:38.418186+00:00
-- url     : https://prove2.me/theorems/ca15f96a-6802-4689-a872-982e028faea3
-- title:
--   Exact computation of Δ: the integer characterization
-- statement:
--   The integer characterization of $\lceil m/n^{\varepsilon_k}\rceil$ as the least $d$ with $m^K\le n d^K$ ($K=2^{k-1}$) and Bernoulli's inequality.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3

set_option autoImplicit false

open Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main

end DirKECC1549.Asm


