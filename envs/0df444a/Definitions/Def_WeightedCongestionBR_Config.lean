-- Prove2me | Definitions.Def_WeightedCongestionBR_Config
-- name    : WeightedCongestionBR_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:19.019283+00:00
-- url     : https://prove2.me/theorems/96f32fff-cd75-4376-9a49-5d9c14d6ae4d
-- title:
--   Configuration of Algorithm 1
-- statement:
--   A configuration of Algorithm 1 records the current phase $i$ ($0$ for the preparatory loop of Line 6, $1\le i\le m-1$ for the loop of Line 9, $m$ when the for-loop is over), the current state $s$ and the set $N_{\mathrm{fixed}}$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- A configuration of Algorithm 1 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, p.14): the current phase `i` (`0` for the
preparatory while-loop of Line 6, `1 ≤ i ≤ m − 1` for the loop of Line 9, `m` once the for-loop is
over), the current state `s` and the set `N_fixed`.

**Formalization Note** The phase counter is a natural number; Line 12 is not a step but is
folded into the final fixed set (see `AlgStep`). -/
structure Config {n r : ℕ} (G : Game n r) where
  /-- The phase index `i`. -/
  phase : ℕ
  /-- The current state `s`. -/
  s : G.Profile
  /-- The set `N_fixed`. -/
  F : Finset (Fin n)

end WeightedCongestionBR


