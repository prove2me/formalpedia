-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankFusedCoefficients
-- name    : Sensitivity213981Formal_RankFusedCoefficients
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:44:16.253982+00:00
-- url     : https://prove2.me/theorems/96af9f5a-7689-49db-a2b5-6cb1d8322e7f
-- title:
--   Rank Fused Coefficients — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Fused Coefficients in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankCached.stateHits`, `ThreeBoundRankCached.fusedHits`, `ThreeBoundRankCached.storedHits`, `ThreeBoundRankCached.fusedHeadCheck`, `ThreeBoundRankCached.HitValues`, `ThreeBoundRankCached.TailOK`, `ThreeBoundRankCached.instDecidableTailOK`, `ThreeBoundRankCached.fusedCoeffCheck`, `ThreeBoundRankCached.HitValues.get`, `ThreeBoundRankCached.zeroHits`, `ThreeBoundRankCached.maxHits`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankFusedCoefficients.lean, lines 1–145.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCachedEvaluator
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
/- One rank-state traversal computes all three head-hit coefficients.
Impossible kinds have an identically zero maximum and need no second scan. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Expr bExpr aExpr maximum    )
open ThreeBoundRankNumeric ThreeBoundFullProfile

structure HitValues where
  zero : ℕ
  one : ℕ
  two : ℕ
  deriving Repr, DecidableEq

def HitValues.get (values : HitValues) (h : Fin 3) : ℕ :=
  if h.val=0 then values.zero else if h.val=1 then values.one else values.two

def zeroHits : HitValues := ⟨0,0,0⟩

def maxHits (a b : HitValues) : HitValues :=
  ⟨max a.zero b.zero,max a.one b.one,max a.two b.two⟩





def stateHits (n : ℕ) (v : Profile n) (a c : Entry) (k : Fin 11) (x y : ℕ) : HitValues :=
  let p := positiveLevel k
  let ux := (rankUp n c p x y).eval v
  let uy := (rankUp n c p y x).eval v
  let jx := (rankJoint n c p x y).eval v
  let jy := (rankJoint n c p y x).eval v
  let c0 := ux+uy
  let c1 := max (if a.guard ≤  x then jx+uy else c0) (if a.guard ≤  y then ux+jy else c0)
  ⟨c0,max c0 c1,max (max c0 c1) (if a.guard ≤  x ∧ a.guard ≤  y then jx+jy else c0)⟩



def fusedHits (n : ℕ) (v : Profile n) (a c : Entry) (k : Fin 11) : HitValues :=
  ((List.range n).flatMap fun x => (List.range n).filterMap fun y =>
    if Possible a c k x y then some (stateHits n v a c k x y) else none).foldr maxHits zeroHits







def storedHits (values : CostValues) (k : Fin 11) : HitValues :=
  ⟨values.heads.getD (3*k.val) 0,values.heads.getD (3*k.val+1) 0,
    values.heads.getD (3*k.val+2) 0⟩



def fusedHeadCheck (n : ℕ) (v : Profile n) (a c : Entry) (mask : Array Bool)
    (values : CostValues) : Bool :=
  (List.finRange 11).all fun k =>
    if mask.getD k.val false then decide (storedHits values k=fusedHits n v a c k)
    else decide (storedHits values k=zeroHits)

def TailOK (n : ℕ) (v : Profile n) (a c : Entry) (values : CostValues) : Prop :=
  values.guard=(bExpr n c.guard a.guard).eval v ∧
  values.converted=(bExpr n c.guard (c.lowerAt 0)).eval v ∧
  ∀ k : Fin (c.tolerance+1), values.negative.getD k.val 0=(aExpr n c.guard (c.lowerAt k.val)).eval v

instance _root_.Sensitivity213981Formal.ThreeBoundRankCached.instDecidableTailOK (n : ℕ) (v : Profile n) (a c : Entry) (values : CostValues) :
    Decidable (TailOK n v a c values) := by unfold TailOK; infer_instance

def fusedCoeffCheck (n : ℕ) (v : Profile n) (a c : Entry) (mask : Array Bool)
    (values : CostValues) : Bool :=
  fusedHeadCheck n v a c mask values && decide (TailOK n v a c values)



end ThreeBoundRankCached



end
end Sensitivity213981Formal


