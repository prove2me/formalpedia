-- Prove2me | Definitions.Def_SteinerCutDominants_WSG_wR
-- name    : SteinerCutDominants_WSG_wR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:14.135336+00:00
-- url     : https://prove2.me/theorems/3354812b-88a6-48f4-957f-3b2036f6bc32
-- title:
--   The weights as a real vector
-- statement:
--   The vector $c$ of a weighted Steiner graph, viewed in $\mathbb R^{E(G)}$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, (auxiliary; no counterpart in the paper)

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG

namespace SteinerCutDominants

/-- The weight vector `c` of a weighted Steiner graph, as a real vector. -/
def WSG.wR (H : WSG) : H.G.edgeSet → ℝ := fun e => (H.c e : ℝ)

end SteinerCutDominants


