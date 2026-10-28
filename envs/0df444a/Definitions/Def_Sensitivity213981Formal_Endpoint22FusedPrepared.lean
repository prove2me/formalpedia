-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22FusedPrepared
-- name    : Sensitivity213981Formal_Endpoint22FusedPrepared
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:53:03.922358+00:00
-- url     : https://prove2.me/theorems/e5d3f5ac-02e5-4d20-993a-131a36403f34
-- title:
--   Endpoint22 Fused Prepared — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Fused Prepared in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankAnnotated.variablePreparedCost`, `ThreeBoundRankAnnotated.fusedCodePreparedCheck`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22FusedPrepared.lean, lines 1–59.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
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
/- Evaluate the head sum once, outside the finite external-count maximum. -/


set_option autoImplicit false
set_option maxHeartbeats 500000
namespace ThreeBoundRankAnnotated
open ThreeBoundNumeric (maximum  )
open ThreeBoundRankCached ThreeBoundRankNumeric
open ThreeBoundEndpoint22Records

def variablePreparedCost (q : ℕ) (p : PreparedValues) (values : CostValues)
    (external e : ℕ) : ℕ :=
  (external-e)*values.guard + e*values.converted +
    ((List.range (q+1)).map fun k => readNegative p e k*values.negative.getD k 0).sum



def fusedCodePreparedCheck (q : ℕ) (p : PreparedValues) (values : CostValues)
    (bound code : ℕ) : Bool :=
  if p.feasible then
    let r := codeRecord code
    decide (headSum values r +
      maximum ((List.range (r 11+1)).map fun e => variablePreparedCost q p values (r 11) e) ≤  bound)
  else true



end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal


