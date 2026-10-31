-- Prove2me | Definitions.Def_SteinerCutDominants_IsSubdivision
-- name    : SteinerCutDominants_IsSubdivision
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:04.384991+00:00
-- url     : https://prove2.me/theorems/d625d617-20a4-4f1a-a8a9-f49e2bccf4a9
-- title:
--   Subdivision
-- statement:
--   $(G,T)$ with weights $c$ arises from $(G',T')$ with weights $c'$ by a subdivision at some new node.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §5, p.8

import Mathlib
import Definitions.Def_SteinerCutDominants_IsSubdivisionAt

namespace SteinerCutDominants

/-- `H` is obtained from `H'` by a subdivision (Conforti, Kaibel, *Steiner Cut Dominants*,
arXiv:2209.14802v2, §5, p.8). -/
def IsSubdivision (H' H : WSG) : Prop := ∃ w : H.V, IsSubdivisionAt H' H w

end SteinerCutDominants


