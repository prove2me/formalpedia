-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankCachedEvaluator
-- name    : Sensitivity213981Formal_RankCachedEvaluator
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:26:58.169153+00:00
-- url     : https://prove2.me/theorems/ba9512cd-4322-4fe3-9668-7a41a8017a74
-- title:
--   Rank Cached Evaluator — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Cached Evaluator in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankCached.MaskOK`, `ThreeBoundRankCached.instDecidableMaskOK`, `ThreeBoundRankCached.maskAllowed`, `ThreeBoundRankCached.staticAllowed`, `ThreeBoundRankCached.headSum`, `ThreeBoundRankCached.cachedRecordCost`, `ThreeBoundRankCached.PreparedValues`, `ThreeBoundRankCached.readNegative`, `ThreeBoundRankCached.CostValues`, `ThreeBoundRankCached.PreparedOK`, `ThreeBoundRankCached.instDecidablePreparedOK`, `ThreeBoundRankCached.preparedCost`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankCachedEvaluator.lean, lines 1–220.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_RecordSetLookup
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
/- Exact coefficient caching and filtered-tree bounds for the q3 rank transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps Expr aExpr bExpr recordOfList   maximum )
open ThreeBoundFullProfile ThreeBoundRankNumeric
open scoped BigOperators

structure CostValues where
  heads : Array ℕ
  guard : ℕ
  converted : ℕ
  negative : Array ℕ
  deriving Repr

def CostOK (n : ℕ) (v : Profile n) (a c : Entry) (values : CostValues) : Prop :=
  (∀ k : Fin 11, ∀ h : Fin 3,
    values.heads.getD (3*k.val+h.val) 0=(rankCost n a c k h.val).eval v) ∧
  values.guard=(bExpr n c.guard a.guard).eval v ∧
  values.converted=(bExpr n c.guard (c.lowerAt 0)).eval v ∧
  ∀ k : Fin (c.tolerance+1), values.negative.getD k.val 0=(aExpr n c.guard (c.lowerAt k.val)).eval v

instance _root_.Sensitivity213981Formal.ThreeBoundRankCached.instDecidableCostOK (n : ℕ) (v : Profile n) (a c : Entry) (values : CostValues) :
    Decidable (CostOK n v a c values) := by unfold CostOK; infer_instance



def MaskOK (n : ℕ) (a c : Entry) (mask : Array Bool) : Prop :=
  ∀ k : Fin 11, mask.getD k.val false=possible n a c k

instance _root_.Sensitivity213981Formal.ThreeBoundRankCached.instDecidableMaskOK (n : ℕ) (a c : Entry) (mask : Array Bool) : Decidable (MaskOK n a c mask) := by
  unfold MaskOK
  infer_instance



def maskAllowed (mask : Array Bool) (r : Record) : Bool :=
  (List.finRange 11).all fun k => r k.val=0 ∨ mask.getD k.val false

def staticAllowed (caps : Caps) (q : ℕ) (r : Record) : Bool :=
  (List.range (q+1)).all fun b => positivePrefix r b ≤  capPrefix caps r b



def headSum (values : CostValues) (r : Record) : ℕ :=
  (List.ofFn fun k : Fin 11 =>
    (r k.val-r (12+2*k.val)-r (13+2*k.val))*values.heads.getD (3*k.val) 0+
    r (12+2*k.val)*values.heads.getD (3*k.val+1) 0+
    r (13+2*k.val)*values.heads.getD (3*k.val+2) 0).sum

def cachedRecordCost (caps : Caps) (perfect q : ℕ) (values : CostValues) (r : Record) (e : ℕ) : ℕ :=
  (r 11-e)*values.guard+e*values.converted+
  ((List.range (q+1)).map fun k => negativeCount caps perfect q r e k*values.negative.getD k 0).sum+
  headSum values r





structure PreparedValues where
  feasible : Bool
  negative : Array (Array ℕ)
  deriving Repr

def readNegative (p : PreparedValues) (e k : ℕ) : ℕ := (p.negative.getD e #[]).getD k 0

def PreparedOK (caps : Caps) (perfect q : ℕ) (r : Record) (p : PreparedValues) : Prop :=
  p.feasible=staticAllowed caps q r ∧
  (p.feasible=true → ∀ e : Fin (r 11+1), ∀ k : Fin (q+1),
    readNegative p e.val k.val=negativeCount caps perfect q r e.val k.val)

instance _root_.Sensitivity213981Formal.ThreeBoundRankCached.instDecidablePreparedOK (caps : Caps) (perfect q : ℕ) (r : Record) (p : PreparedValues) :
    Decidable (PreparedOK caps perfect q r p) := by unfold PreparedOK; infer_instance



def preparedCost (q : ℕ) (p : PreparedValues) (values : CostValues) (r : Record) (e : ℕ) : ℕ :=
  (r 11-e)*values.guard+e*values.converted+
  ((List.range (q+1)).map fun k => readNegative p e k*values.negative.getD k 0).sum+
  headSum values r



def preparedRecordCheck (q : ℕ) (p : PreparedValues) (values : CostValues)
    (bound : ℕ) (xs : List ℕ) : Bool :=
  if p.feasible then (List.range (recordOfList xs 11+1)).all fun e =>
    preparedCost q p values (recordOfList xs) e≤ bound else true













end ThreeBoundRankCached




end
end Sensitivity213981Formal


