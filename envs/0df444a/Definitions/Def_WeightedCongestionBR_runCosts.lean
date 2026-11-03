-- Prove2me | Definitions.Def_WeightedCongestionBR_runCosts
-- name    : WeightedCongestionBR_runCosts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:13.587206+00:00
-- url     : https://prove2.me/theorems/4ec0f00a-e26c-493c-9535-2dda425fe8c8
-- title:
--   A sequence of unilateral deviations
-- statement:
--   For a state $s_0$ and a finite list of moves $(u_1,t_1),(u_2,t_2),\dots$, where move $(u,t)$ replaces the strategy of player $u$ by $t$, this returns the final state and, for each player $u$ that moved, its cost $C_u$ immediately after its last move (the paper's $C_u(i)$ when the list is phase $i$); players that never move get $0$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, proof of Lemma 8, p.15

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- A finite sequence of unilateral deviations applied to a state `s₀`, as used in the proof of
Lemma 8 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.15). Each element `⟨u, t⟩` of `mv` replaces the strategy of player `u` by `t`.
The first component is the final state; the second records, for each player `u` that moved, its
cost `C_u` immediately after its last move (the paper's `C_u(i)`), and `0` for the others.

**Formalization Note** Moves are applied left to right with `Function.update`. -/
noncomputable def runCosts {n r : ℕ} (G : Game n r) (s₀ : G.Profile)
    (mv : List (Σ u : Fin n, G.Strategy u)) : G.Profile × (Fin n → ℝ) :=
  mv.foldl
    (fun acc x => (Function.update acc.1 x.1 x.2,
      Function.update acc.2 x.1 (privateCost G (Function.update acc.1 x.1 x.2) x.1)))
    (s₀, fun _ => 0)

end WeightedCongestionBR


