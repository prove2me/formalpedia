-- Prove2me | Definitions.Def_HarksKlimm_Consistency_FIPConsistent
-- name    : HarksKlimm_Consistency_FIPConsistent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:22.20009+00:00
-- url     : https://prove2.me/theorems/3241a806-8d61-4527-a448-e408db526848
-- title:
--   Universal finite-improvement consistency
-- statement:
--   A set $C$ is FIP-consistent if every finite weighted congestion game with facility costs in $C$ has no infinite sequence of strict unilateral cost reductions:
--   $$\forall G\in\mathcal G(C),\quad \nexists (s^k,i_k)_{k\ge0}\text{ with }s^{k+1}_{-i_k}=s^k_{-i_k},\quad \pi_{i_k}(s^{k+1})<\pi_{i_k}(s^k)\text{ for every }k.$$
--   This expresses termination of every strict improvement path.
--
--   **Formalization Note** The published `HasFIP` is applied to negative private costs. Its moves require an actual strategy change. Since every game's feasible profile space is finite, absence of infinite improvement paths is equivalent to the source's absence of improvement cycles. The class itself need not be finite or nonempty.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, §2, p. 422 (PDF p. 4)

import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_MondererShapley_Improvement_HasFIP
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

import Mathlib

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}


def IsStep (a b : ∀ i, Y i) (i : ι) : Prop := b i ≠ a i ∧ ∀ j, j ≠ i → b j = a j

end MondererShapley.ClosedPath

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsStep

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}


def HasFIP (u : ι → (∀ i, Y i) → ℝ) : Prop :=
  ¬ ∃ (y : ℕ → ∀ i, Y i) (d : ℕ → ι),
      ∀ k, MondererShapley.ClosedPath.IsStep (y k) (y (k + 1)) (d k) ∧
        u (d k) (y k) < u (d k) (y (k + 1))

end MondererShapley.Improvement
-/

namespace HarksKlimm.Consistency

def FIPConsistent (C : Set (ℝ≥0 → ℝ)) : Prop :=
  ∀ (n m : ℕ) (G : Game n m), (∀ f, G.cost f ∈ C) →
    MondererShapley.Improvement.HasFIP (fun i t => -privateCost G t i)

end HarksKlimm.Consistency


