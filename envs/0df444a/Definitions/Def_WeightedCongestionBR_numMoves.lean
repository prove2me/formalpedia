-- Prove2me | Definitions.Def_WeightedCongestionBR_numMoves
-- name    : WeightedCongestionBR_numMoves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:25.050078+00:00
-- url     : https://prove2.me/theorems/a69c0b1d-c517-4478-99d2-0d11fda5234b
-- title:
--   Number of best-response moves in a run
-- statement:
--   The number of best-response moves of a list of configurations is the number of consecutive pairs in the same phase. In a run, a best-response move keeps the phase and the end of a phase increases it by one, so this counts the moves $\tau$ of the proof of Theorem 4, summed over the phases.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, proof of Theorem 4, p.18

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_Config
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The number of **best-response moves** in a list of configurations (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, proof of Theorem 4,
p.18, where `τ` counts them per phase): consecutive pairs with the same phase. In a run, a move step
(`move0`, `moveI`) keeps the phase and an end-of-phase step (`end0`, `endI`) increases it. -/
def numMoves {n r : ℕ} {G : Game n r} (l : List (Config G)) : ℕ :=
  ((l.zip l.tail).filter (fun q => q.1.phase = q.2.phase)).length

end WeightedCongestionBR


