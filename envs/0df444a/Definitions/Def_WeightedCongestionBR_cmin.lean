-- Prove2me | Definitions.Def_WeightedCongestionBR_cmin
-- name    : WeightedCongestionBR_cmin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:14.584203+00:00
-- url     : https://prove2.me/theorems/f96b98d0-60ab-4538-bb56-6089f2da78ed
-- title:
--   $c_{\min}$, Line 1 of Algorithm 1
-- statement:
--   $c_{\min}=\min_{u\in N}C_u(\mathbf 0_{-u},\mathcal{BR}_u(\mathbf 0))$, where $\mathbf 0$ is the fictitious empty state in which no player uses any resource. In that state player $u$ alone on strategy $t$ pays $w_u\sum_{e\in t}c_e(w_u)$, so
--
--   $$
--   c_{\min}=\min_{u\in N}\ \min_{t\in S_u}\ w_u\sum_{e\in t}c_e(w_u).
--   $$
--
--   It is a lower bound on the cost of any player in any state.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. The empty state need not be a state of the game, so the minimum over $S_u$ is written out.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, Line 1, and p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- `c_min := min_{u ∈ N} C_u(0_{-u}, BR_u(0))` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, Line 1, and p.14), where `0` is
the fictitious empty state in which every player uses no resource. In that state player `u` alone
on its strategy `t` pays `w_u ∑_{e ∈ t} c_e(w_u)`, so
`c_min = min_u min_{t ∈ S_u} w_u ∑_{e ∈ t} c_e(w_u)`.

**Formalization Note** The empty state is not a state of the game (`∅` need not be a strategy), so
the minimum over `S_u` is written out instead of extending the strategy sets. -/
noncomputable def cmin {n r : ℕ} (G : Game n r) : ℝ :=
  Finset.univ.inf' ⟨⟨0, G.players_pos⟩, Finset.mem_univ _⟩ (fun u =>
    (G.strategies u).inf' (G.strategies_nonempty u)
      (fun t => (G.demand u : ℝ) * ∑ e ∈ t, G.cost e (G.demand u)))

end WeightedCongestionBR


