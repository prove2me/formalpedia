-- Prove2me | Definitions.Def_MinBisectFPT_encodeTD
-- name    : MinBisectFPT_encodeTD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:34.665207+00:00
-- url     : https://prove2.me/theorems/4f422f47-ce4f-4933-8f41-697a48191139
-- title:
--   Bit encoding of a rooted decomposition
-- statement:
--   The output word of Theorem 1.3: the number of nodes, then for each node its parent ($0$ for none, $t+1$ for the node $t$) and its bag, through the encoding of integers and vertex sets of this mission.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Theorem 1.3, p.3

import Mathlib
import Definitions.Def_MinBisectFPT_encodeCounts
import Definitions.Def_MinBisectFPT_RootedTD

open scoped Classical

namespace MinBisectFPT

open ExponomialAssortment.FPTAS (encodeNat)

/-- **Output of Theorem 1.3**: `N`, then for each node its parent (`0` for none, `t + 1` for the node
`t`) and its bag. Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC 2027
submission (manuscript sha256 8db80a52…), p.3. -/
noncomputable def encodeTD {n : ℕ} (T : RootedTD n) : List Bool :=
  encodeNat T.N ++ (List.finRange T.N).flatMap fun t =>
    encodeNat ((T.parent t).elim 0 fun t' => t'.val + 1) ++ encodeSet (T.bag t)

end MinBisectFPT


