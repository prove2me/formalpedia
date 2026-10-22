-- Prove2me | Definitions.Def_HarksKlimm_Consistency_load
-- name    : HarksKlimm_Consistency_load
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:49.5681+00:00
-- url     : https://prove2.me/theorems/e424d87c-6ea6-4aae-91f9-15eee091715c
-- title:
--   Facility load
-- statement:
--   For a game $G$, a feasible profile $s$ and a facility $f$, its load is the total demand of its users:
--   $$\ell_f(s)=\sum_{j\in N:\ f\in s_j}d_j.$$
--   Unused facilities have load zero; this is the input to their cost functions.
--
--   **Formalization Note** The domain is the nonnegative real half-line, including zero; costs take arbitrary real values.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Definition 2.1, p. 422 (PDF p. 4)

import Definitions.Def_HarksKlimm_Consistency_Game
set_option autoImplicit false
open scoped NNReal

/- Imported Lean declaration context (code only; not new declarations):

import Mathlib
set_option autoImplicit false

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
-/

namespace HarksKlimm.Consistency

noncomputable def load {n m : ℕ} (G : Game n m) (s : G.Profile)
    (f : Fin m) : ℝ≥0 :=
  ∑ j : Fin n, if f ∈ (s j).val then G.demand j else 0

end HarksKlimm.Consistency


