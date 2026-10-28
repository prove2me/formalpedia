-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxPairM
-- name    : Sensitivity213981Formal_MinmaxPairM
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:06:15.922+00:00
-- url     : https://prove2.me/theorems/a8c5f120-de10-4c6e-9647-a2ca3cc9b369
-- title:
--   Minmax Pair M — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Pair M in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxTransfer.orientedRow`, `ThreeBoundMinmaxTransfer.pairMTarget`, `ThreeBoundMinmaxTransfer.pairMCost`, `ThreeBoundMinmaxTransfer.orientedRowBool`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxPairM.lean, lines 1–232.

import Definitions.Def_Sensitivity213981Formal_MinmaxB
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
/- Conditional destruction of the actual oriented min/max witness row.
The selected orientation is a genuine component of the symmetric parent. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def orientedRow (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) : Prop :=
  F t (child x w (!c))=true ∧ F u (child x w c)=true ∧ (guardFailures S F g x w).card ≤  q

def orientedRowBool (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t u g : L) (q : ℕ) (w : V) (c : Bool) (x : ((V × Bool) × I) → Bool) : Bool :=
  decide (orientedRow S F t u g q x w c)











def pairMTarget (tj uj tk uk : L) (m0 m1 b0 b1 : ℕ) : ℕ :=
  max (if tj< tk ∧ uj< uk then m0+m1 else 0)
    (max (if tj< tk then m0+b1 else 0) (if uj< uk then b0+m1 else 0))

def pairMCost (degree q : ℕ) (tj uj tk uk gj gk : L) (a m0 m1 b0 b1 p : ℕ) : ℕ :=
  max (if tj< tk ∨ uj< uk then pairMTarget tj uj tk uk m0 m1 b0 b1+(degree-q)*a else 0)
    (if gk< gj then b0+b1+(degree-q-1)*a+p else 0)







end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal


