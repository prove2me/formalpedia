-- Prove2me | Definitions.Def_SteinerCutDominants_IsRoot
-- name    : SteinerCutDominants_IsRoot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:50.887556+00:00
-- url     : https://prove2.me/theorems/2b60ff25-91e4-44c0-b26e-c20ca23d9110
-- title:
--   Root of a weighted Steiner graph
-- statement:
--   $\delta(S)$ is a **root** of the weighted Steiner graph $((G,T),c)$: a $T$-Steiner cut of $c$-weight $\gamma_c(G,T)$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wR
import Definitions.Def_SteinerCutDominants_IsRootOf

namespace SteinerCutDominants

/-- `δ(S)` is a root of the weight vector of `H` (Conforti, Kaibel, *Steiner Cut Dominants*,
arXiv:2209.14802v2, §2, p.4). -/
def IsRoot (H : WSG) (S : Finset H.V) : Prop := IsRootOf H.G H.T H.wR S

end SteinerCutDominants


