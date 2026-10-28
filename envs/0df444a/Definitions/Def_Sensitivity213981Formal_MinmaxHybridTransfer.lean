-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
-- name    : Sensitivity213981Formal_MinmaxHybridTransfer
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:10:10.419825+00:00
-- url     : https://prove2.me/theorems/6e2c4af8-f83e-430d-86bc-62bfe2464881
-- title:
--   Minmax Hybrid Transfer — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Hybrid Transfer in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxHybrid.CoreBounds`, `ThreeBoundMinmaxHybrid.ACovers`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxHybridTransfer.lean, lines 1–137.

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxRankRawTransfer
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
/- Literal parent A entries may be proved on a small covering set of intervals.
All remaining coordinates then use scalar conditional bounds. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxHybrid
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxRank (fullBExpr fullMExpr)
open ThreeBoundMinmaxNumeric (pCore dCore)
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def ACovers (w : Profile n) (seeds : List (Fin n × Fin n)) : Prop :=
  ∀ i j : Fin n, i ≤  j → ∃ pair ∈ seeds,
    i ≤  pair.1 ∧ pair.1 ≤  pair.2 ∧ pair.2 ≤  j ∧ w (.a pair.1 pair.2) ≤  w (.a i j)



structure CoreBounds (degree pcross : ℕ) (recipe : Fin n → ThreeBoundMinmaxNumeric.Entry)
    (v w : Profile n) : Prop where
  b : ∀ i j : Fin n, i ≤  j →
    (fullBExpr n degree (recipe i) (recipe j)).eval v ≤  w (.b i j)
  m : ∀ i j : Fin n, i ≤  j → j.val+1< n →
    (fullMExpr n degree (recipe i) (recipe j) (recipe (next j))).eval v ≤  w (.m i j)
  p : ∀ j l : Fin n, j <  l →
    pCore n pcross v (recipe j) (recipe (next j)) (recipe l) (w (.a (next j) l)) ≤  w (.p j l)
  d : ∀ i j l : Fin n, i ≤  j → j <  l →
    dCore n degree v (recipe i) (recipe j) (recipe (next j)) (recipe l)
      (w (.m i j)+w (.p j l)) ≤  w (.d i j l)





end
end ThreeBoundMinmaxHybrid




end
end Sensitivity213981Formal


