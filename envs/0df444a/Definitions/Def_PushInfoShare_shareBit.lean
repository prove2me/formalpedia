-- Prove2me | Definitions.Def_PushInfoShare_shareBit
-- name    : PushInfoShare_shareBit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:38.388974+00:00
-- url     : https://prove2.me/theorems/b173088f-1a66-4067-8e7c-db3bd0c24bff
-- title:
--   The binary sharing variable $\delta_i$
-- statement:
--   The sharing decision of manufacturer $i$ as the number $\delta_i\in\{0,1\}$. The paper's $\bar\delta_i$ is $1-\delta_i$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.8

import Mathlib

namespace PushInfoShare

/-- The binary variable `δᵢ` of Jain, SSRN:3388957 (PDF of 2021-04-25), §3, p.8, as a real number:
`1` if `i` shares and `0` otherwise. The paper's `δ̄ᵢ` is `1 - shareBit δ i`. -/
def shareBit (δ : Fin 2 → Bool) (i : Fin 2) : ℝ :=
  if δ i then 1 else 0

end PushInfoShare


