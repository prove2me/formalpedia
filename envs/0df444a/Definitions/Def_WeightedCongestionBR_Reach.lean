-- Prove2me | Definitions.Def_WeightedCongestionBR_Reach
-- name    : WeightedCongestionBR_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:22.664875+00:00
-- url     : https://prove2.me/theorems/a95d1b7d-9a83-4c1a-a068-5bd09884a5e8
-- title:
--   Reachable configurations of Algorithm 1
-- statement:
--   A configuration is reachable if a finite sequence of steps of Algorithm 1 leads to it from the initial configuration $(0,s_{\mathrm{init}},\emptyset)$ (Lines 4–5).
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_Config
import Definitions.Def_WeightedCongestionBR_AlgStep
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- A configuration is **reachable** by Algorithm 1 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, p.14) if some run of
`AlgStep` leads to it from the initial configuration `(0, s_init, ∅)` (Lines 4–5). -/
def Reach {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (c : Config G) : Prop :=
  Relation.ReflTransGen (AlgStep G d m sinit) ⟨0, sinit, ∅⟩ c

end WeightedCongestionBR


