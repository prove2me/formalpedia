-- Prove2me | Definitions.Def_WeightedCongestionBR_IsRun
-- name    : WeightedCongestionBR_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:52.837904+00:00
-- url     : https://prove2.me/theorems/1612cccf-e1a8-465d-87d2-25402c70aec7
-- title:
--   Runs of Algorithm 1
-- statement:
--   A run is a finite list of configurations that starts at $(0,s_{\mathrm{init}},\emptyset)$ and in which every configuration is followed by one of its successors under the step relation of Algorithm 1. Runs need not be maximal; a run with $k$ steps has $k+1$ configurations.
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

/-- A **run** of Algorithm 1 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, p.14): a finite list of configurations starting at
`(0, s_init, ∅)` in which consecutive configurations are related by `AlgStep`.

**Formalization Note** Runs need not be maximal; the number of steps is `l.length − 1`. -/
def IsRun {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (l : List (Config G)) : Prop :=
  l.head? = some ⟨0, sinit, ∅⟩ ∧ l.IsChain (AlgStep G d m sinit)

end WeightedCongestionBR


