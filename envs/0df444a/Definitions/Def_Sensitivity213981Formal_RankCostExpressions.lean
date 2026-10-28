-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankCostExpressions
-- name    : Sensitivity213981Formal_RankCostExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:25:25.705767+00:00
-- url     : https://prove2.me/theorems/2c13b751-a85f-4f0f-a059-a7d41897c25b
-- title:
--   Rank Cost Expressions — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Cost Expressions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankNumeric.rankAExpr`, `ThreeBoundRankNumeric.rawAExpr`, `ThreeBoundRankNumeric.highExpr`, `ThreeBoundRankNumeric.negativeExpr`, `ThreeBoundRankNumeric.recordCost`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankCostExpressions.lean, lines 1–64.

import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_MinmaxHeadLocal
import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankExpressions
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
import Mathlib.Data.Prod.Lex
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
/- A homogeneous rank transfer expression over q3 count records.
Converted arcs use the proved lower-target guard cost. -/


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped BigOperators

def highExpr (n : ℕ) (a c : Entry) (r : Record) : Expr n :=
  Expr.sum (List.ofFn fun k : Fin 11 =>
    (r k.val-r (12+2*k.val)-r (13+2*k.val))*rankCost n a c k 0+
    r (12+2*k.val)*rankCost n a c k 1+r (13+2*k.val)*rankCost n a c k 2)

def negativeExpr (n : ℕ) (caps : Caps) (perfect : ℕ) (c : Entry) (r : Record) (e : ℕ) : Expr n :=
  Expr.sum ((List.range (c.tolerance+1)).map fun q =>
    negativeCount caps perfect c.tolerance r e q*aExpr n c.guard (c.lowerAt q))

def recordCost (n : ℕ) (caps : Caps) (perfect : ℕ) (a c : Entry) (r : Record) (e : ℕ) : Expr n :=
  (r 11-e)*bExpr n c.guard a.guard+e*bExpr n c.guard (c.lowerAt 0)+
    negativeExpr n caps perfect c r e+highExpr n a c r

def rankAExpr (n : ℕ) (caps : Caps) (perfect : ℕ) (records : List (List ℕ))
    (a c : Entry) : Expr n :=
  Expr.maximum (records.flatMap fun xs =>
    let r := recordOfList xs
    if recordAllowed n caps a c r then
      (List.range (r 11+1)).map fun e => recordCost n caps perfect a c r e
    else [])

def rawAExpr (n : ℕ) (caps : Caps) (perfect : ℕ) (records : List (List ℕ))
    (a c : Entry) : Expr n :=
  if 4 ≤  c.tolerance then
    ordinaryAExpr n caps (a.lowerAt 0) a.guard a.tolerance (c.lowerAt 0) c.guard c.tolerance
  else rankAExpr n caps perfect records a c





end ThreeBoundRankNumeric



end
end Sensitivity213981Formal


