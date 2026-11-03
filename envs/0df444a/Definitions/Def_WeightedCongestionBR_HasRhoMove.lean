-- Prove2me | Definitions.Def_WeightedCongestionBR_HasRhoMove
-- name    : WeightedCongestionBR_HasRhoMove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:00.992721+00:00
-- url     : https://prove2.me/theorems/71beb247-abd0-4383-9187-120ed35081d6
-- title:
--   Player $u$ has a $\rho$-move
-- statement:
--   A unilateral deviation of player $u$ from state $s$ to $s'_u\in S_u$ is a **$\rho$-move** if
--
--   $$
--   C_u(s) > \rho\cdot C_u(s_{-u},s'_u).
--   $$
--
--   The predicate says that $u$ has at least one $\rho$-move at $s$. Algorithm 1 lets a player move only if it has an $(\alpha+1/p)$-move or a $p$-move.
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

/-- Player `u` **has a `ρ`-move** at state `s` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, p.6): some unilateral deviation `s'_u ∈ S_u`
satisfies `C_u(s) > ρ · C_u(s_{-u}, s'_u)` (strict inequality, as printed).

**Formalization Note** The deviation state `(s_{-u}, s'_u)` is `Function.update s u t`. -/
def HasRhoMove {n r : ℕ} (G : Game n r) (ρ : ℝ) (s : G.Profile) (u : Fin n) : Prop :=
  ∃ t : G.Strategy u, privateCost G s u > ρ * privateCost G (Function.update s u t) u

end WeightedCongestionBR


