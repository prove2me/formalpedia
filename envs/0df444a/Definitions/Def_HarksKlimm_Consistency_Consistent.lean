-- Prove2me | Definitions.Def_HarksKlimm_Consistency_Consistent
-- name    : HarksKlimm_Consistency_Consistent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:25.16933+00:00
-- url     : https://prove2.me/theorems/2855361c-a771-4669-9f18-f5fc6291849b
-- title:
--   Universal pure-equilibrium consistency
-- statement:
--   A set $C$ of facility cost functions is consistent when every finite weighted congestion game using functions from $C$ admits a pure Nash equilibrium:
--   $$\forall G\in\mathcal G(C),\quad \exists s\in\prod_i S_i,\quad
--   \forall i\in N\ \forall t_i\in S_i,\quad \pi_i(s)\le\pi_i(t_i,s_{-i}).$$
--   The quantifier ranges over all positive demands, nonempty finite player and facility sets, and nonempty feasible strategy families.
--
--   **Formalization Note** The published payoff-maximizing `AGT.IsPureNash` is applied to $-\pi$. The class $C$ may be empty or infinite; no continuity, potential, or classification assumption is part of consistency.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, §2 following Definition 2.1, p. 422 (PDF p. 4)

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

def Consistent (C : Set (ℝ≥0 → ℝ)) : Prop :=
  ∀ (n m : ℕ) (G : Game n m), (∀ f, G.cost f ∈ C) →
    ∃ s : G.Profile, AGT.IsPureNash (fun i t => -privateCost G t i) s

end HarksKlimm.Consistency


