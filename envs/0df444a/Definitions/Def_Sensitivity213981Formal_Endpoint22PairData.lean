-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22PairData
-- name    : Sensitivity213981Formal_Endpoint22PairData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:06:00.675917+00:00
-- url     : https://prove2.me/theorems/51fae910-68e2-412a-ba0f-677246e184bc
-- title:
--   Endpoint22 Pair Data — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Pair Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Pairs.entry_lower_upper`, `ThreeBoundEndpoint22Pairs.pairData`, `ThreeBoundEndpoint22Pairs.entry_guard_le_threshold`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22PairData.lean, lines 1–86.

import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericRecipe
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
/- Concrete third-endpoint min/max pairing, independent of the chosen edge label. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint22Pairs
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxNumeric

theorem entry_guard_le_threshold (p : Fin 4) (l : Fin 22) (d : ℕ) :
    (Sensitivity5591Endpoint22.entry p l).guard ≤  (Sensitivity5591Endpoint22.entry p l).threshold d := by
  have ho := Sensitivity5591Endpoint22.entry_lower_order p l
  have hh := Sensitivity5591Endpoint22.Entry.threshold_monotone _ ho.1 ho.2.1 ho.2.2 (Nat.zero_le d)
  have hz : (Sensitivity5591Endpoint22.entry p l).threshold 0=(Sensitivity5591Endpoint22.entry p l).t0 := by
    simp [Sensitivity5591Endpoint22.Entry.threshold]
  rw [hz] at hh
  exact (Sensitivity5591Endpoint22.entry_guard_order p l).1.trans hh

theorem entry_lower_upper (p : Fin 4) (l : Fin 22) (d : ℕ)
    (hd : d ≤  (Sensitivity5591Endpoint22.entry p l).tolerance) :
    (Sensitivity5591Endpoint22.entry p l).threshold d ≤  (Sensitivity5591Endpoint22.entry p l).upper d := by
  have hd9 : d< 9 := by have hh := Sensitivity5591Endpoint22.entry_tolerance_bound p l; omega
  exact (Sensitivity5591Endpoint22.entry_guard_order p l).2 ⟨d,hd9⟩ hd

variable {I : Type} [Fintype I]

noncomputable def pairData (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ w, ¬Adj w w)
    (label : Fin 5591 → Fin 5591 → Bool) (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool)
    (i j : Fin 22) (hij : i ≤  j) :
    PairData ((Sensitivity5591Endpoint22.recipe Adj loopless label p).stage F) F i j where
  weakLower := (Sensitivity5591Endpoint22.entry p i).threshold
  weakUpper := (Sensitivity5591Endpoint22.entry p i).upper
  strongLower := (Sensitivity5591Endpoint22.entry p j).threshold
  strongUpper := (Sensitivity5591Endpoint22.entry p j).upper
  weakLowerMono := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).lower_mono i
  weakUpperMono := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).upper_mono i
  strongLowerMono := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).lower_mono j
  strongUpperMono := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).upper_mono j
  weakLowerUpper := entry_lower_upper p i
  strongLowerUpper := entry_lower_upper p j
  guards := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).guard hij
  tolerances := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).tolerance hij
  lowerOrder := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).lower_order i j hij
  upperOrder := (Sensitivity5591Endpoint22.recipe_ordered Adj loopless label p).upper_order i j hij
  weakDef _ _ _ := rfl
  strongDef _ _ _ := rfl
  weakGuardTarget d _ := entry_guard_le_threshold p i d
  guardTarget d _ := entry_guard_le_threshold p j d







end ThreeBoundEndpoint22Pairs




end
end Sensitivity213981Formal


