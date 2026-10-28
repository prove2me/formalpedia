-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankPackedStrictCache
-- name    : Sensitivity213981Formal_RankPackedStrictCache
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:08:27.217369+00:00
-- url     : https://prove2.me/theorems/6d4db0a1-985e-4873-9f56-7da772bed017
-- title:
--   Rank Packed Strict Cache — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Packed Strict Cache in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Packed.Tree.strictCachedCheck`, `ThreeBoundEndpoint22Packed.strictCachedCodeCheck`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankPackedStrictCache.lean, lines 1–78.

import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictPacked
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankPackedVariableCache
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
/- Force the packed capcode once before the cache search, and use proved
bit-shift record access.  This changes evaluation order only. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records ThreeBoundEndpoint22Strict

def strictCachedCodeCheck (cache : VariableCache) (capcode : ℕ) (values : CostValues)
    (bound code : ℕ) : Bool :=
  withNat capcode fun cc =>
  withNat (fastRecord code 11) fun external =>
  match cache.lookup cc external with
  | none => false
  | some v => decide (headSum values (fastRecord code)+v≤ bound)



def Tree.strictCachedCheck (deny : ℕ) (cache : VariableCache) (values : CostValues)
    (bound : ℕ) (t : ThreeBoundRankAnnotated.Tree) : Bool :=
  if blockedFast deny t.mask then true else
    match t with
    | .leaf _ key code => strictCachedCodeCheck cache (convertedCodes.get key) values bound code
    | .branch _ _ left right => Tree.strictCachedCheck deny cache values bound left &&
        Tree.strictCachedCheck deny cache values bound right









end ThreeBoundEndpoint22Packed


end
end Sensitivity213981Formal


