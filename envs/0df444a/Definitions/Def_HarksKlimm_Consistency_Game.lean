-- Prove2me | Definitions.Def_HarksKlimm_Consistency_Game
-- name    : HarksKlimm_Consistency_Game
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:08.883518+00:00
-- url     : https://prove2.me/theorems/fee13a73-7477-4925-971d-1e14dcf883a3
-- title:
--   Weighted congestion games and feasible profiles
-- statement:
--   A weighted congestion game has nonempty finite player and facility sets $N,F$. Each player $i$ has a nonempty finite family $S_i$ of subsets of $F$, a strictly positive demand $d_i$, and each facility $f$ has a cost function $c_f:[0,\infty)\to\mathbb R$. A feasible profile is
--   $$s\in\prod_{i\in N}S_i.$$
--   This supplies the unrestricted game model used in consistency.
--
--   **Formalization Note** Players and facilities are indexed by `Fin n` and `Fin m` with positive sizes. Strategies are finite subsets; the empty subset is allowed. Demands are positive nonnegative reals. Continuity and monotonicity are not built into the model.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Definition 2.1 and §2, p. 422 (PDF p. 4)

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace HarksKlimm.Consistency

structure Game (n m : ℕ) where
  players_pos : 0 < n
  facilities_pos : 0 < m
  strategies : Fin n → Finset (Finset (Fin m))
  strategies_nonempty : ∀ i, (strategies i).Nonempty
  demand : Fin n → ℝ≥0
  demand_pos : ∀ i, 0 < demand i
  cost : Fin m → ℝ≥0 → ℝ

abbrev Game.Strategy {n m : ℕ} (G : Game n m) (i : Fin n) :=
  ↥(G.strategies i)

abbrev Game.Profile {n m : ℕ} (G : Game n m) :=
  ∀ i, G.Strategy i

end HarksKlimm.Consistency


