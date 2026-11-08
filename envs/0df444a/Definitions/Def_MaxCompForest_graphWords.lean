-- Prove2me | Definitions.Def_MaxCompForest_graphWords
-- name    : MaxCompForest_graphWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:26.574966+00:00
-- url     : https://prove2.me/theorems/c16fd917-d837-49c2-81a9-c9dacb189327
-- title:
--   Binary encoding of an input graph
-- statement:
--   The input graph as a list of binary words: $n$, $m$, and for each label its two endpoints and its conductance. The conductance is written as a reduced numerator and denominator in binary, so its magnitude costs only logarithmically in the input length.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.14, p.15

import Mathlib
import Definitions.Def_MaxCompForest_RInst
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The words of an input graph**: `n`, `m`, then for each label its endpoints and its conductance, all
in binary.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.14 and p.15 ("total binary input length"). -/
def graphWords (I : RInst) : List (List Sym) :=
  [encNat I.n, encNat I.m] ++
    (List.finRange I.m).flatMap fun e => [encNat (I.head e), encNat (I.tail e), encRat (I.c e)]

end MaxCompForest


