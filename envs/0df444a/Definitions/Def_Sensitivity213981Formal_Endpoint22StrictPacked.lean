-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22StrictPacked
-- name    : Sensitivity213981Formal_Endpoint22StrictPacked
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:05:59.09892+00:00
-- url     : https://prove2.me/theorems/27a6ddb7-754d-435e-bc3f-16005d3d0762
-- title:
--   Endpoint22 Strict Packed — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Strict Packed in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Strict.fastCap`, `ThreeBoundEndpoint22Strict.strictNegativeCost`, `ThreeBoundEndpoint22Strict.withNat`, `ThreeBoundEndpoint22Strict.strictCodeCheck`, `ThreeBoundEndpoint22Strict.fastDigit`, `ThreeBoundEndpoint22Strict.fastRecord`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22StrictPacked.lean, lines 1–87.

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
/- Exact eager evaluation of the packed scalar arithmetic. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Strict
open ThreeBoundNumeric (maximum)
open ThreeBoundRankCached ThreeBoundEndpoint22Packed ThreeBoundEndpoint22Records

def withNat {α : Sort _} (n : ℕ) (f : ℕ → α) : α :=
  match n with | 0 => f 0 | k+1 => f (k+1)



def fastDigit (code k : ℕ) : ℕ := (code >>> (4*k)) &&& 15



def fastRecord (code k : ℕ) : ℕ :=
  if k< 41 then if fastDigit code k=15 then 1000000 else fastDigit code k else 0



def fastCap (code e k : ℕ) : ℕ := (code >>> (6*(4*e+k))) &&& 63



def strictNegativeCost (q code e : ℕ) (values : CostValues) : ℕ :=
  withNat (fastCap code e 0) fun c0 =>
  match q with
  | 0 => c0*values.negative.getD 0 0
  | 1 => withNat (fastCap code e 1) fun c1 =>
      withNat (min c0 c1) fun s0 =>
      s0*values.negative.getD 0 0+(c1-s0)*values.negative.getD 1 0
  | 2 => withNat (fastCap code e 1) fun c1 =>
      withNat (fastCap code e 2) fun c2 =>
      withNat (min c1 c2) fun s1 =>
      withNat (min c0 s1) fun s0 =>
      s0*values.negative.getD 0 0+(s1-s0)*values.negative.getD 1 0+
        (c2-s1)*values.negative.getD 2 0
  | _ => withNat (fastCap code e 1) fun c1 =>
      withNat (fastCap code e 2) fun c2 =>
      withNat (fastCap code e 3) fun c3 =>
      withNat (min c2 c3) fun s2 =>
      withNat (min c1 s2) fun s1 =>
      withNat (min c0 s1) fun s0 =>
      s0*values.negative.getD 0 0+(s1-s0)*values.negative.getD 1 0+
        (s2-s1)*values.negative.getD 2 0+(c3-s2)*values.negative.getD 3 0



def strictCodeCheck (q capcode : ℕ) (values : CostValues) (bound code : ℕ) : Bool :=
  withNat capcode fun cc =>
  withNat (fastRecord code 11) fun external =>
  withNat (headSum values (fastRecord code)) fun head =>
  decide (head+maximum ((List.range (external+1)).map fun e =>
    (external-e)*values.guard+e*values.converted+strictNegativeCost q cc e values)≤ bound)



end ThreeBoundEndpoint22Strict


end
end Sensitivity213981Formal


