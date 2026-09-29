-- Prove2me | Definitions.Def_r03_defs_809c83f713_sp05_port_balanced_slot_factor_lift_formalizatio
-- name    : r03_defs_809c83f713_sp05_port_balanced_slot_factor_lift_formalizatio
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:47.598145+00:00
-- url     : https://prove2.me/theorems/4c13f139-5b18-4580-b804-d4c9a9de5f47
-- title:
--   R03 P3-factor definition module: r03_defs_809c83f713_sp05_port_balanced_slot_factor_lift_formalizatio
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp05/sp05_port_balanced_slot_factor_lift_formalization_v1.lean; source SHA-256 1c41ef56f3bc84875d663d12e511fa7013c8f126a76a8fbe13202168e3b28bc9; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SlotHallLift

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

abbrev Center (C : Finset V) := {v // v ∈ C}
abbrev Leaf (C : Finset V) := {v // v ∉ C}
abbrev Slot (C : Finset V) := Center C × Fin 2

noncomputable section
open scoped Classical

def slotRel (R : V → Fin 2 → V → Prop) (C : Finset V)
    (s : Slot C) (w : Leaf C) : Prop := R s.1.1 s.2 w.1

def HallCondition (R : V → Fin 2 → V → Prop) (C : Finset V) : Prop :=
  ∀ A : Finset (Slot C),
    A.card ≤ (Finset.univ.filter
      (fun w : Leaf C => ∃ s ∈ A, slotRel R C s w)).card

def SlotMatching (R : V → Fin 2 → V → Prop) (C : Finset V) : Prop :=
  ∃ f : Slot C → Leaf C,
    Function.Injective f ∧ ∀ s, slotRel R C s (f s)

def BijectiveSlotMatching (R : V → Fin 2 → V → Prop) (C : Finset V) : Prop :=
  ∃ f : Slot C → Leaf C,
    Function.Bijective f ∧ ∀ s, slotRel R C s (f s)

def placeFun (C : Finset V) (eC : Fin C.card ≃ Center C) (f : Slot C ≃ Leaf C)
    (x : Fin C.card × Fin 3) : V :=
  if x.2 = 0 then (f (eC x.1, 0)).1
  else if x.2 = 1 then (eC x.1).1
  else (f (eC x.1, 1)).1

def GraphCenterHallCondition (G : SimpleGraph V) (C : Finset V) : Prop :=
  HallCondition (fun c _ w => G.Adj c w) C

def GraphCenterTwoExpansion (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ S : Finset (Center C),
    2 * S.card ≤ (Finset.univ.filter
      (fun w : Leaf C => ∃ c ∈ S, G.Adj c.1 w.1)).card

def GraphCenterTwoExpansionDefect (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ S : Finset (Center C),
    (Finset.univ.filter
      (fun w : Leaf C => ∃ c ∈ S, G.Adj c.1 w.1)).card < 2 * S.card

end
end R03SlotHallLift


