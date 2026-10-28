-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxRankData
-- name    : Sensitivity213981Formal_MinmaxRankData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:06:03.929112+00:00
-- url     : https://prove2.me/theorems/47fe16b2-fcf5-4fc9-a63b-1de2058cee95
-- title:
--   Minmax Rank Data — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Rank Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxRank.RowCapacityData`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxRankData.lean, lines 1–109.

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_MinmaxEntryMatch
import Definitions.Def_Sensitivity213981Formal_MinmaxPairM
import Definitions.Def_Sensitivity213981Formal_MinmaxRankExpressions
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
/- Actual winning rows supply all feasible rank-capacity data used by the oracle. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxRank
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundConditional
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]





structure RowCapacityData (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry)
    (x : ((V × Bool) × I) → Bool) (w : V) (rx ry : Fin n) : Prop where
  strong_pos : 0< capacityHeight c rx.val ry.val
  weak_pos : 0< capacityHeight a rx.val ry.val
  strong_tolerance : capacityHeight c rx.val ry.val-1≤ S.tolerance j
  weak_tolerance : capacityHeight a rx.val ry.val-1≤ S.tolerance i
  capacity_order : capacityHeight c rx.val ry.val-1≤ capacityHeight a rx.val ry.val-1
  guard_count : (failed S F j x w).card≤ capacityHeight c rx.val ry.val-1
  strong_target : mm F (P.strongLower (capacityHeight c rx.val ry.val-1))
    (P.strongUpper (capacityHeight c rx.val ry.val-1)) (child x w false) (child x w true)=true
  weak_target : mm F (P.weakLower (capacityHeight a rx.val ry.val-1))
    (P.weakUpper (capacityHeight a rx.val ry.val-1)) (child x w false) (child x w true)=true
  need_lower : need n a ry.val (capacityHeight c rx.val ry.val-1)≤ rx.val
  need_upper : need n a rx.val (capacityHeight c rx.val ry.val-1)≤ ry.val





end
end ThreeBoundMinmaxRank




end
end Sensitivity213981Formal


