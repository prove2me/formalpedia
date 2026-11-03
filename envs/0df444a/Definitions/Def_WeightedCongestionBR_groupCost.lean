-- Prove2me | Definitions.Def_WeightedCongestionBR_groupCost
-- name    : WeightedCongestionBR_groupCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:53.894437+00:00
-- url     : https://prove2.me/theorems/aff76c70-db6a-4dfa-a0fc-1f27b896ac2d
-- title:
--   Group cost $C_R(s)$ and social cost $C(s)$
-- statement:
--   In a weighted congestion game the cost of player $u$ at state $s$ is $C_u(s)=w_u\sum_{e\in s_u}c_e(x_e(s))$, where $x_e(s)=\sum_{v: e\in s_v} w_v$ is the load of $e$. For a group $R\subseteq N$,
--
--   $$
--   C_R(s)=\sum_{u\in R} C_u(s),
--   $$
--
--   and the social cost is $C(s)=C_N(s)$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. $C_u$ is the published `HarksKlimm.Consistency.privateCost`, whose demand factor is the weight $w_u$.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §2, p.6

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The social cost of a group of players, `C_R(s) := ∑_{u ∈ R} C_u(s)`, and for `R = N` the social
cost `C(s)` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, p.6).

Here `C_u(s) = w_u ∑_{e ∈ s_u} c_e(x_e(s))` is the published `HarksKlimm.Consistency.privateCost`,
whose demand factor is the weight `w_u`.

**Formalization Note** Players are `Fin n`, resources `Fin r`. The social cost of the whole game
is `groupCost G Finset.univ s`. -/
noncomputable def groupCost {n r : ℕ} (G : Game n r) (R : Finset (Fin n)) (s : G.Profile) : ℝ :=
  ∑ u ∈ R, privateCost G s u

end WeightedCongestionBR


