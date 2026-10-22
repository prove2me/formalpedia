-- Prove2me | Definitions.Def_HarksKlimm_Consistency_ThreeConsistent
-- name    : HarksKlimm_Consistency_ThreeConsistent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:13.919447+00:00
-- url     : https://prove2.me/theorems/2b371677-ca01-4ff8-9654-ec08e5e041b8
-- title:
--   Pure-equilibrium consistency for exactly three players
-- statement:
--   A class $C$ is consistent for three-player games if every admissible game with exactly three players and all facility costs in $C$ has a pure Nash equilibrium:
--   $$\forall G\in\mathcal G(C)\text{ with }|N|=3,\quad \exists s\ \forall i,t_i,\ \pi_i(s)\le\pi_i(t_i,s_{-i}).$$
--   All positive demands, finite facility sets, and feasible strategy families remain universally quantified.
--
--   **Formalization Note** The three players are `Fin 3`. Payoffs are negative private costs; no inert player or special strategy configuration is required.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Proposition 5.1 and §2, p. 426 (PDF p. 8)

import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_agt_games
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

import Definitions.Def_HarksKlimm_Consistency_load
set_option autoImplicit false



namespace HarksKlimm.Consistency

noncomputable def privateCost {n m : ℕ} (G : Game n m) (s : G.Profile)
    (i : Fin n) : ℝ :=
  ∑ f ∈ (s i).val, (G.demand i : ℝ) * G.cost f (load G s f)

end HarksKlimm.Consistency

namespace AGT
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]
def IsPureNash (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ i (t : S i), u i (Function.update s i t) ≤ u i s
end AGT
-/

namespace HarksKlimm.Consistency

def ThreeConsistent (C : Set (ℝ≥0 → ℝ)) : Prop :=
  ∀ (m : ℕ) (G : Game 3 m), (∀ f, G.cost f ∈ C) →
    ∃ s : G.Profile, AGT.IsPureNash (fun i t => -privateCost G t i) s

end HarksKlimm.Consistency


