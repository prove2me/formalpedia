-- Prove2me | Definitions.Def_WeightedCongestionBR_cfgMovers
-- name    : WeightedCongestionBR_cfgMovers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:19.795105+00:00
-- url     : https://prove2.me/theorems/7bdf4695-b14d-411c-adbb-ac96cb98e971
-- title:
--   Players that move, $R_i$
-- statement:
--   The set of players whose strategy changes between two consecutive configurations of a list. For the steps of phase $i$ this is $R_i$, the set of players selected at least once to make an improvement move in phase $i$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. A selected player always changes strategy, since it has a $\rho$-move with $\rho>1$ and costs are nonnegative.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §4.2, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_Config
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

open Classical in
/-- The players that move along a list of configurations: those whose strategy changes between two
consecutive configurations. Applied to the steps of phase `i`, this is the set `R_i` of players
"selected at least once by the algorithm to make an improvement move during phase `i`"
(Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.14).

**Formalization Note** In Algorithm 1 a selected player always changes strategy, since it has a
`ρ`-move with `ρ > 1` and costs are nonnegative, so "selected" and "changed strategy" agree. -/
noncomputable def cfgMovers {n r : ℕ} {G : Game n r} (l : List (Config G)) : Finset (Fin n) :=
  Finset.univ.filter (fun u => ∃ q ∈ l.zip l.tail, q.1.s u ≠ q.2.s u)

end WeightedCongestionBR


