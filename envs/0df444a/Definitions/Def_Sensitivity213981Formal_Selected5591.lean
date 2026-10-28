-- Prove2me | Definitions.Def_Sensitivity213981Formal_Selected5591
-- name    : Sensitivity213981Formal_Selected5591
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:25:20.105744+00:00
-- url     : https://prove2.me/theorems/2abe51c5-0281-40f9-a80f-0b84cfdd6759
-- title:
--   Selected5591 — sensitivity certificate definitions
-- statement:
--   The definitions for Selected5591 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.Labeling5591.outdegree`, `Sensitivity5591Labeling.Labeling5591.indegree`, `Sensitivity5591Labeling.Labeling5591.common_out`, `Sensitivity5591Labeling.Labeling5591.common_in`, `Sensitivity5591Labeling.Labeling5591.arc_transitive`, `Sensitivity5591Labeling.Labeling5591.triple_card_transport`, `Sensitivity5591Labeling.Labeling5591.exists_selected_labeling`, `Sensitivity5591Labeling.Labeling5591.selectedLabel`, `Sensitivity5591Labeling.Labeling5591.label`, `Sensitivity5591Labeling.Labeling5591.tournament`, `Sensitivity5591Labeling.Labeling5591.archiveLabel`, `Sensitivity5591Labeling.Labeling5591.Adj`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Selected5591.lean, lines 1–128.

import Definitions.Def_Sensitivity213981Formal_Label5591Joint
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Caps
import Definitions.Def_Sensitivity213981Formal_Paley5591
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_SelectedBoolCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal
section
/- The indexed Paley-5591 tournament and its jointly admissible label. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Sensitivity5591Labeling.Labeling5591
open Sensitivity10007Labeling ZL
open scoped Classical
noncomputable section
attribute [local irreducible] Sensitivity5591Labeling.core



def Adj (i j : Fin 5591) : Prop := Sensitivity5591Labeling.Adj i j

theorem irreflexive (i : Fin 5591) : ¬ Adj i i :=
  Sensitivity5591Labeling.irreflexive i

theorem edge_compl (i j : Fin 5591) (hij : i ≠ j) : Adj i j ↔ ¬ Adj j i :=
  Sensitivity5591Labeling.edge_compl i j hij

theorem filter_card_of_decision {W : Type} [Fintype W] (p : W → Prop)
    (d₁ d₂ : DecidablePred p) (n : ℕ)
    (h : (@Finset.filter W p d₁ Finset.univ).card=n) :
    (@Finset.filter W p d₂ Finset.univ).card=n := by
  have he : d₂=d₁ := Subsingleton.elim _ _
  rw [he]
  exact h

theorem outdegree (i : Fin 5591) : (Finset.univ.filter (Adj i)).card = 2795 :=
  filter_card_of_decision (Sensitivity5591Labeling.Adj i) _ _ _
    (Sensitivity5591Labeling.outdegree i)

theorem indegree (i : Fin 5591) : (Finset.univ.filter fun z => Adj z i).card = 2795 :=
  filter_card_of_decision (fun z => Sensitivity5591Labeling.Adj z i) _ _ _
    (Sensitivity5591Labeling.indegree i)

theorem common_out (i j : Fin 5591) (hij : i ≠ j) :
    (Finset.univ.filter fun z => Adj i z ∧ Adj j z).card = 1397 :=
  filter_card_of_decision (fun z => Sensitivity5591Labeling.Adj i z ∧ Sensitivity5591Labeling.Adj j z) _ _ _
    (Sensitivity5591Labeling.common_out i j hij)

theorem common_in (i j : Fin 5591) (hij : i ≠ j) :
    (Finset.univ.filter fun z => Adj z i ∧ Adj z j).card = 1397 :=
  filter_card_of_decision (fun z => Sensitivity5591Labeling.Adj z i ∧ Sensitivity5591Labeling.Adj z j) _ _ _
    (Sensitivity5591Labeling.common_in i j hij)

theorem arc_transitive (x y u v : Fin 5591) (hxy : Adj x y) (huv : Adj u v) :
    ∃ e : Fin 5591 ≃ Fin 5591,
      e x = u ∧ e y = v ∧ ∀ a b, Adj (e a) (e b) ↔ Adj a b :=
  Sensitivity5591Labeling.arc_transitive x y u v hxy huv

theorem triple_card_transport
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800)
    (M : Finset (Fin 5591)) (hm : M.card = 3) : (dominatedBy Adj M).card ≤  800 :=
  htriple M hm

theorem exists_selected_labeling
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    ∃ ell : Fin 5591 × Fin 5591 → Fin 2, Caps.JointExclusions Adj ell := by
  apply Caps.exists_joint_exclusions Adj
  · exact Fintype.card_fin 5591
  · exact irreflexive
  · exact edge_compl
  · exact outdegree
  · exact indegree
  · exact common_in
  · exact common_out
  · exact arc_transitive
  · exact triple_card_transport htriple

def selectedLabel
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    Fin 5591 × Fin 5591 → Fin 2 := Classical.choose (exists_selected_labeling htriple)



def label
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    Fin 5591 → Fin 5591 → Bool := Sensitivity10007BoolCaps.boolLabel (selectedLabel htriple)

def tournament : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament 5591 where
  Adj := Adj
  loopless := irreflexive
  edge_compl := fun {i j} h => edge_compl i j h

def archiveLabel
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    Fin 5591 → Fin 5591 → Fin 2 := fun v w => selectedLabel htriple (v,w)







end
end Sensitivity5591Labeling.Labeling5591




end
end Sensitivity213981Formal


