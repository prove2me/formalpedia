-- Prove2me | Definitions.Def_Sensitivity213981Formal_Label5591Checks
-- name    : Sensitivity213981Formal_Label5591Checks
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:20:02.639241+00:00
-- url     : https://prove2.me/theorems/936ab8e7-6191-4b96-ae6d-866c42df1a57
-- title:
--   Label5591 Checks — sensitivity certificate definitions
-- statement:
--   The definitions for Label5591 Checks in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.Caps.marked_load`, `Sensitivity5591Labeling.Caps.ordinary_load`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Label5591Checks.lean, lines 1–54.

import Definitions.Def_Sensitivity213981Formal_Label5591ChecksBase
import Definitions.Def_Sensitivity213981Formal_Label5591LoadDominator
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked0
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked1
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked10
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked11
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked2
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked3
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked4
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked5
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked6
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked7
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked8
import Definitions.Def_Sensitivity213981Formal_Label5591LoadMarked9
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary0
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary1
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary2
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary3
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary4
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary5
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary6
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary7
import Definitions.Def_Sensitivity213981Formal_Label5591LoadOrdinary8
import Definitions.Def_Sensitivity213981Formal_Label5591LoadPerfect
import Definitions.Def_Sensitivity213981Formal_Label5591LoadSource
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
namespace Sensitivity5591Labeling.Caps
open Sensitivity10007Labeling
theorem ordinary_load(i:Fin 9) : ordinaryLoad i≤ ordinaryCeiling i := by
  fin_cases i
  · exact ordinary_load_0
  · exact ordinary_load_1
  · exact ordinary_load_2
  · exact ordinary_load_3
  · exact ordinary_load_4
  · exact ordinary_load_5
  · exact ordinary_load_6
  · exact ordinary_load_7
  · exact ordinary_load_8
theorem marked_load(i:Fin 12) : markedLoad i≤ markedCeiling i := by
  fin_cases i
  · exact marked_load_0
  · exact marked_load_1
  · exact marked_load_2
  · exact marked_load_3
  · exact marked_load_4
  · exact marked_load_5
  · exact marked_load_6
  · exact marked_load_7
  · exact marked_load_8
  · exact marked_load_9
  · exact marked_load_10
  · exact marked_load_11
end Sensitivity5591Labeling.Caps

end
end Sensitivity213981Formal


