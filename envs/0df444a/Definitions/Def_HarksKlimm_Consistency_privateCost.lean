-- Prove2me | Definitions.Def_HarksKlimm_Consistency_privateCost
-- name    : HarksKlimm_Consistency_privateCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:46:32.681273+00:00
-- url     : https://prove2.me/theorems/8a0423e7-ce05-44e9-a6a9-8b7eff7e4908
-- title:
--   Demand-weighted private cost
-- statement:
--   For a player $i$ in a game $G$ at feasible profile $s$, define private cost by
--   $$\pi_i(s)=\sum_{f\in s_i}d_i c_f(\ell_f(s)).$$
--   Players minimize this quantity. Choosing the empty strategy incurs zero cost, and negative facility costs remain permitted.
--
--   **Formalization Note** The domain is the nonnegative real half-line, including zero; costs take arbitrary real values.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Definition 2.1, p. 422 (PDF p. 4)

import Definitions.Def_HarksKlimm_Consistency_load
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

import Definitions.Def_HarksKlimm_Consistency_Game
set_option autoImplicit false



namespace HarksKlimm.Consistency

noncomputable def load {n m : ℕ} (G : Game n m) (s : G.Profile)
    (f : Fin m) : ℝ≥0 :=
  ∑ j : Fin n, if f ∈ (s j).val then G.demand j else 0

end HarksKlimm.Consistency
-/

namespace HarksKlimm.Consistency

noncomputable def privateCost {n m : ℕ} (G : Game n m) (s : G.Profile)
    (i : Fin n) : ℝ :=
  ∑ f ∈ (s i).val, (G.demand i : ℝ) * G.cost f (load G s f)

end HarksKlimm.Consistency


