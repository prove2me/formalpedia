-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankPackedVariableCache
-- name    : Sensitivity213981Formal_RankPackedVariableCache
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:04:29.635152+00:00
-- url     : https://prove2.me/theorems/0b2a6835-977d-4d82-9892-99169961b862
-- title:
--   Rank Packed Variable Cache — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Packed Variable Cache in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Packed.VariableCache.check`, `ThreeBoundEndpoint22Packed.cachedCodeCheck`, `ThreeBoundEndpoint22Packed.Tree.cachedCheck`, `ThreeBoundEndpoint22Packed.VariableCache`, `ThreeBoundEndpoint22Packed.variableMaximum`, `ThreeBoundEndpoint22Packed.VariableCache.lookup`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankPackedVariableCache.lean, lines 1–135.

import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
/- Reuse a certified variable-cost maximum across all rows with the same
packed capcode and external count.  Lookups verify both arguments exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundNumeric (maximum)
open ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records

inductive VariableCache where
  | leaf (capcode external value : ℕ) : VariableCache
  | branch (pivot : ℕ) (left right : VariableCache) : VariableCache

def variableMaximum (q capcode : ℕ) (values : CostValues) (external : ℕ) : ℕ :=
  maximum ((List.range (external+1)).map fun e => packedVariableCost q capcode values external e)

def VariableCache.lookup : VariableCache → ℕ → ℕ → Option ℕ
  | .leaf capcode external value, code, ext =>
      if code=capcode ∧ ext=external then some value else none
  | .branch pivot left right, code, ext =>
      if code< pivot then left.lookup code ext else right.lookup code ext

def VariableCache.check (q : ℕ) (values : CostValues) : VariableCache → Bool
  | .leaf capcode external value => decide (variableMaximum q capcode values external≤ value)
  | .branch _ left right => left.check q values && right.check q values





def cachedCodeCheck (cache : VariableCache) (capcode : ℕ) (values : CostValues)
    (bound code : ℕ) : Bool :=
  match cache.lookup capcode (codeRecord code 11) with
  | none => false
  | some v => decide (headSum values (codeRecord code)+v≤ bound)



def Tree.cachedCheck (deny : ℕ) (cache : VariableCache) (values : CostValues)
    (bound : ℕ) (t : ThreeBoundRankAnnotated.Tree) : Bool :=
  if blockedFast deny t.mask then true else
    match t with
    | .leaf _ key code => cachedCodeCheck cache (convertedCodes.get key) values bound code
    | .branch _ _ left right => Tree.cachedCheck deny cache values bound left &&
        Tree.cachedCheck deny cache values bound right







end ThreeBoundEndpoint22Packed



end
end Sensitivity213981Formal


