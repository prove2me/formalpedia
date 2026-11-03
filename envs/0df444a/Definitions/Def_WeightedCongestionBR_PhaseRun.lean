-- Prove2me | Definitions.Def_WeightedCongestionBR_PhaseRun
-- name    : WeightedCongestionBR_PhaseRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:43.932262+00:00
-- url     : https://prove2.me/theorems/9abff231-f3fe-453b-aafd-cf82c0275dfd
-- title:
--   Complete phase of Algorithm 1
-- statement:
--   A complete phase is a prefix of phase $i$ whose last configuration takes the end-of-phase step. Its first state is $s^{i-1}$, its last state is $s^i$, the state immediately after the end of phase $i$, and its moving players are $R_i$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §4.2, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_Config
import Definitions.Def_WeightedCongestionBR_AlgStep
import Definitions.Def_WeightedCongestionBR_PhasePrefix
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- A **complete phase** of Algorithm 1 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.14): a `PhasePrefix` whose last configuration takes
the end-of-phase step (Line 6 or Line 9 exits). If the phase is `i`, its first state is `s^{i−1}`
and its last state is `s^i`, the state "immediately after the end of phase `i`", and its movers are
`R_i`. -/
def PhaseRun {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (l : List (Config G)) :
    Prop :=
  PhasePrefix G d m sinit l ∧
    ∃ cl c' : Config G, l.getLast? = some cl ∧ AlgStep G d m sinit cl c' ∧ c'.phase = cl.phase + 1

end WeightedCongestionBR


