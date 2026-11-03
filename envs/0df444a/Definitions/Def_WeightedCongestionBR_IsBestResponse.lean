-- Prove2me | Definitions.Def_WeightedCongestionBR_IsBestResponse
-- name    : WeightedCongestionBR_IsBestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:25.282547+00:00
-- url     : https://prove2.me/theorems/02d65134-0f61-4266-9173-e66ba25148ea
-- title:
--   Best response $\mathcal{BR}_u(s)$
-- statement:
--   A strategy $t\in S_u$ is a best response of player $u$ at state $s$ if
--
--   $$
--   t\in\operatorname*{argmin}_{s'_u\in S_u} C_u(s_{-u},s'_u).
--   $$
--
--   The paper breaks ties arbitrarily; here every minimizer qualifies, and every statement about Algorithm 1 covers all of them.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §2, p.6

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- `t` is a **best response** of player `u` at state `s` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, p.6):
`BR_u(s) ∈ argmin_{s'_u ∈ S_u} C_u(s_{-u}, s'_u)`.

**Formalization Note** Ties are not broken: every minimizer is a best response, and the statements
that use this predicate quantify over all of them (the paper's "arbitrary selection"). -/
def IsBestResponse {n r : ℕ} (G : Game n r) (s : G.Profile) (u : Fin n) (t : G.Strategy u) :
    Prop :=
  ∀ t' : G.Strategy u,
    privateCost G (Function.update s u t) u ≤ privateCost G (Function.update s u t') u

end WeightedCongestionBR


