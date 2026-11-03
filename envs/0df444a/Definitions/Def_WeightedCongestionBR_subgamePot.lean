-- Prove2me | Definitions.Def_WeightedCongestionBR_subgamePot
-- name    : WeightedCongestionBR_subgamePot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:16.718228+00:00
-- url     : https://prove2.me/theorems/baa93a83-f598-4e31-ae9d-f1e8577066db
-- title:
--   Subgame potential $\Phi^R(s)$
-- statement:
--   The subgame potential of a group $R$ at state $s$ is
--
--   $$
--   \Phi^R(s)=\sum_{e\in E}\phi_e\big(x_{R,e}(s)\big).
--   $$
--
--   For $R=N$ it is the potential $\Phi(s)=\sum_e\phi_e(x_e(s))$ of the game.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. $\phi_e$ is `phiPoly (costPoly G e)`.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §4.1, pp.11–12

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_costPoly
import Definitions.Def_WeightedCongestionBR_phiPoly
import Definitions.Def_WeightedCongestionBR_groupLoad
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The **subgame potential** `Φ^R(s) := ∑_{e ∈ E} φ_e(x_{R,e}(s))` of a group `R` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §4.1,
p.12). For `R = N` it is the potential `Φ(s) := ∑_e φ_e(x_e(s))` of p.11.

**Formalization Note** `φ_e` is `phiPoly (costPoly G e)`. The potential of the game is
`subgamePot G Finset.univ s`. -/
noncomputable def subgamePot {n r : ℕ} (G : Game n r) (R : Finset (Fin n)) (s : G.Profile) : ℝ :=
  ∑ e : Fin r, phiPoly (costPoly G e) (groupLoad G s R e)

end WeightedCongestionBR


