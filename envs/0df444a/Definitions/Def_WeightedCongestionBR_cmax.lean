-- Prove2me | Definitions.Def_WeightedCongestionBR_cmax
-- name    : WeightedCongestionBR_cmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:28.082974+00:00
-- url     : https://prove2.me/theorems/ba14a4f2-bc21-4607-8d5f-8c60c7e26004
-- title:
--   $c_{\max}$, Line 1 of Algorithm 1
-- statement:
--   For an initial state $s_{\mathrm{init}}$,
--
--   $$
--   c_{\max}=\max_{u\in N} C_u(s_{\mathrm{init}}),
--   $$
--
--   the largest player cost at the start. It is the top boundary $b_0$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, Line 1, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- `c_max := max_{u ∈ N} C_u(s_init)` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, Line 1, p.14). -/
noncomputable def cmax {n r : ℕ} (G : Game n r) (sinit : G.Profile) : ℝ :=
  Finset.univ.sup' ⟨⟨0, G.players_pos⟩, Finset.mem_univ _⟩ (fun u => privateCost G sinit u)

end WeightedCongestionBR


