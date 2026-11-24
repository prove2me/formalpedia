-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
-- name    : Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:12:05.428457+00:00
-- url     : https://prove2.me/theorems/4c4999c4-40b1-4f0b-93e4-77b368d19faf
-- title:
--   Paired tournament arcs and their exact guard indexing
-- statement:
--   Defines the paired arc relation: macro arcs connect different macros, while internal arcs connect different rows within one macro. The corresponding check is a labeled singleton for an external arc and both destination sockets for an internal arc. pairedIndexing proves membership, nonemptiness, destination identity, and completeness of these checks for the actual paired guard family.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/HighHeadGuardBridge.lean lines 50–96; SHA256 a65d8b6636d5eefcc9838f6d69e96a55e7d1b20201ddaaac2d4b039d43d8cb22; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
The semantic bridge from actual high target sockets to tournament outdegree
budgets. It applies directly to the unary and clustered paired guard families.
Every destination has its own nonempty check, supported only on that row.
-/
namespace SensitivityHighHeadGuardBridge

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityGuardEvents
set_option autoImplicit false







def pairedArc {M B : Type} (macroArc : M → M → Prop)
    (internalArc : B → B → Prop) (v w : M × B) : Prop :=
  (w.1 ≠ v.1 ∧ macroArc v.1 w.1) ∨
    (w.1 = v.1 ∧ w.2 ≠ v.2 ∧ internalArc v.2 w.2)

def pairedCheck {M B : Type} (label : M → M → Bool) (v w : M × B) :
    Finset ((M × B) × Bool) :=
  if w.1 = v.1 then {(w,false),(w,true)} else {(w,label v.1 w.1)}

def pairedIndexing {M B : Type} [Fintype M] [Fintype B]
    (macroArc : M → M → Prop) (label : M → M → Bool)
    (internalArc : B → B → Prop) :
    GuardIndexing (pairedTournamentGuards macroArc label internalArc)
      (pairedArc macroArc internalArc) where
  check := pairedCheck label
  member := by
    intro v w hw
    rcases hw with hext | hint
    · rw [pairedCheck,if_neg hext.1]
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hext⟩,rfl⟩
    · rw [pairedCheck,if_pos hint.1]
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hint⟩,rfl⟩
  nonempty := by
    intro v w _
    unfold pairedCheck
    split
    · exact Finset.insert_nonempty _ _
    · exact Finset.singleton_nonempty _
  destination := by
    intro v w socket hsocket
    unfold pairedCheck at hsocket
    split at hsocket
    · rcases Finset.mem_insert.mp hsocket with hs | hs
      · exact congrArg Prod.fst hs
      · exact congrArg Prod.fst (Finset.mem_singleton.mp hs)
    · exact congrArg Prod.fst (Finset.mem_singleton.mp hsocket)
  complete := by
    intro v c hc
    rcases Finset.mem_union.mp hc with hext | hint
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hext
      have hp := (Finset.mem_filter.mp hw).2
      exact ⟨w,Or.inl hp,by simp only [pairedCheck,if_neg hp.1]⟩
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hint
      have hp := (Finset.mem_filter.mp hw).2
      exact ⟨w,Or.inr hp,by simp only [pairedCheck,if_pos hp.1]⟩












end
end SensitivityHighHeadGuardBridge


