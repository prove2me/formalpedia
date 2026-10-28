-- Prove2me | Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked6
-- name    : Sensitivity213981Formal_Label5591LoadMarked6
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:15:12.863185+00:00
-- url     : https://prove2.me/theorems/707f6617-48c2-4e0d-b24b-828e92c3153a
-- title:
--   Label5591 Load Marked6 — sensitivity certificate definitions
-- statement:
--   The definitions for Label5591 Load Marked6 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.Caps.marked_load_6`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Label5591LoadMarked6.lean, lines 1–14.

import Definitions.Def_Sensitivity213981Formal_Label5591Data
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
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

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
set_option exponentiation.threshold 1000000
namespace Sensitivity5591Labeling.Caps
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
theorem marked_load_6 : markedLoad 6≤ markedCeiling 6 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
end Sensitivity5591Labeling.Caps


end
end Sensitivity213981Formal


