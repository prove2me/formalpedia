-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxPairData
-- name    : Sensitivity213981Formal_MinmaxPairData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:03:38.160536+00:00
-- url     : https://prove2.me/theorems/faabf1c8-97e5-42d3-bb2f-722b9ea0d169
-- title:
--   Minmax Pair Data — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Pair Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxTransfer.PairData`, `ThreeBoundMinmaxTransfer.mm`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxPairData.lean, lines 1–105.

import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinMaxNesting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_OrdinaryParentBridge
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
/- Shared actual-predicate interface for symmetric min/max transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def mm (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) : Bool :=
  F t x && F t y && (F u x || F u y)







structure PairData (S : Stage L I V) (F : L → (I → Bool) → Bool) (i j : L) where
  weakLower : ℕ → L
  weakUpper : ℕ → L
  strongLower : ℕ → L
  strongUpper : ℕ → L
  weakLowerMono : Monotone weakLower
  weakUpperMono : Monotone weakUpper
  strongLowerMono : Monotone strongLower
  strongUpperMono : Monotone strongUpper
  weakLowerUpper : ∀ b, b ≤  S.tolerance i → weakLower b ≤  weakUpper b
  strongLowerUpper : ∀ b, b ≤  S.tolerance j → strongLower b ≤  strongUpper b
  guards : S.guard j ≤  S.guard i
  tolerances : S.tolerance j ≤  S.tolerance i
  lowerOrder : ∀ b, b ≤  S.tolerance j → weakLower b ≤  strongLower b
  upperOrder : ∀ b, b ≤  S.tolerance j → weakUpper b ≤  strongUpper b
  weakDef : ∀ d x y, S.target i d x y = mm F (weakLower d) (weakUpper d) x y
  strongDef : ∀ d x y, S.target j d x y = mm F (strongLower d) (strongUpper d) x y
  weakGuardTarget : ∀ b, b ≤  S.tolerance i → S.guard i ≤  weakLower b
  guardTarget : ∀ b, b ≤  S.tolerance j → S.guard j ≤  strongLower b









end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal


