-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22PackedPrepared
-- name    : Sensitivity213981Formal_Endpoint22PackedPrepared
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:57:22.325997+00:00
-- url     : https://prove2.me/theorems/5125d740-d730-4b6f-be11-d2f90243bab6
-- title:
--   Endpoint22 Packed Prepared — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Packed Prepared in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Packed.packedVariableCost`, `ThreeBoundEndpoint22Packed.packedCodeCheck`, `ThreeBoundEndpoint22Packed.packedCap`, `ThreeBoundEndpoint22Packed.packedNegativeCost`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22PackedPrepared.lean, lines 1–104.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ConvertedData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankFusedTree
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
/- Direct four-tier arithmetic avoids constructing nested temporary arrays. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundNumeric (maximum interval)
open ThreeBoundRankNumeric ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records

def packedCap (code e k : ℕ) : ℕ := code/(64^(4*e+k))%64

def packedNegativeCost (q code e : ℕ) (values : CostValues) : ℕ :=
  let c0:=packedCap code e 0
  let c1:=packedCap code e 1
  let c2:=packedCap code e 2
  let c3:=packedCap code e 3
  let a0:=values.negative.getD 0 0
  let a1:=values.negative.getD 1 0
  let a2:=values.negative.getD 2 0
  let a3:=values.negative.getD 3 0
  match q with
  | 0 => c0*a0
  | 1 => let s0:=min c0 c1
         s0*a0+(c1-s0)*a1
  | 2 => let s1:=min c1 c2
         let s0:=min c0 s1
         s0*a0+(s1-s0)*a1+(c2-s1)*a2
  | _ => let s2:=min c2 c3
         let s1:=min c1 s2
         let s0:=min c0 s1
         s0*a0+(s1-s0)*a1+(s2-s1)*a2+(c3-s2)*a3



def packedVariableCost (q capcode : ℕ) (values : CostValues) (external e : ℕ) : ℕ :=
  (external-e)*values.guard+e*values.converted+packedNegativeCost q capcode e values







def packedCodeCheck (q capcode : ℕ) (values : CostValues) (bound code : ℕ) : Bool :=
  let r:=codeRecord code
  decide (headSum values r+maximum ((List.range (r 11+1)).map fun e =>
    packedVariableCost q capcode values (r 11) e)≤ bound)



end ThreeBoundEndpoint22Packed


end
end Sensitivity213981Formal


