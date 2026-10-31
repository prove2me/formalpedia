-- Prove2me | Definitions.Def_PushInfoShare_onlyShares
-- name    : PushInfoShare_onlyShares
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:03.163149+00:00
-- url     : https://prove2.me/theorems/12177696-dff4-4a67-b3b6-f84ae71db260
-- title:
--   Partial sharing decision of case $P_i$
-- statement:
--   The decision of case $P_i$, in which only manufacturer $i$ shares. Case $F$ is the constant decision `true` and case $N$ the constant decision `false`.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.9

import Mathlib

namespace PushInfoShare

/-- The sharing decision of case `Pᵢ` of Jain, SSRN:3388957 (PDF of 2021-04-25), §3, p.9: only
manufacturer `i` shares. Case `F` is `fun _ => true` and case `N` is `fun _ => false`. -/
def onlyShares (i : Fin 2) : Fin 2 → Bool :=
  fun j => decide (j = i)

end PushInfoShare


