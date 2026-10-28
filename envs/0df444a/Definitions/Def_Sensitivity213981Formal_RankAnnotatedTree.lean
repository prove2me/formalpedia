-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
-- name    : Sensitivity213981Formal_RankAnnotatedTree
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:44:04.466407+00:00
-- url     : https://prove2.me/theorems/5fb751be-f8fd-478a-aa51-73176548d769
-- title:
--   Rank Annotated Tree — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Annotated Tree in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankAnnotated.Tree.checkMasks`, `ThreeBoundRankAnnotated.blocked`, `ThreeBoundRankAnnotated.Tree.AllPrepared`, `ThreeBoundRankAnnotated.codePreparedCheck`, `ThreeBoundRankAnnotated.Tree.preparedCheck`, `ThreeBoundRankAnnotated.Tree`, `ThreeBoundRankAnnotated.Tree.mask`, `ThreeBoundRankAnnotated.Tree.checkStatics`, `ThreeBoundRankAnnotated.Tree.erase`, `ThreeBoundRankAnnotated.prepared`, `ThreeBoundRankAnnotated.packedMaskCheck`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankAnnotatedTree.lean, lines 1–177.

import Definitions.Def_Sensitivity213981Formal_Endpoint22NibbleMask
import Definitions.Def_Sensitivity213981Formal_Endpoint22StaticProjection
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankConvertedPreparation
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
/- Certified common-kind masks skip whole impossible record subtrees. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace ThreeBoundRankAnnotated
open ThreeBoundNumeric (Caps recordOfList)
open ThreeBoundRankNumeric ThreeBoundRankCached ThreeBoundFullProfile
open ThreeBoundEndpoint22Records



inductive Tree where
  | leaf (mask key code : ℕ) : Tree
  | branch (mask : ℕ) (pivot : List ℕ) (left right : Tree) : Tree

def Tree.mask : Tree → ℕ
  | .leaf m _ _ => m
  | .branch m _ _ _ => m

def Tree.erase : Tree → ThreeBoundRecordLookup.Tree
  | .leaf _ _ code => .leaf (decodeRow 41 code)
  | .branch _ pivot left right => .branch pivot left.erase right.erase

def packedMaskCheck (bits code : ℕ) : Bool:=decide (bits &&& nibbleSpread code=bits)



def Tree.checkMasks : Tree → Bool
  | .leaf mask _ code => packedMaskCheck mask code
  | .branch mask _ left right => left.checkMasks && right.checkMasks &&
      decide (mask &&& left.mask=mask ∧ mask &&& right.mask=mask)



def blocked (mask : Array Bool) (bits : ℕ) : Bool :=
  (List.finRange 11).any fun k => bits.testBit (4*k.val) && !(mask.getD k.val false)



def Tree.AllPrepared (caps : Caps) (perfect q : ℕ) (pre : ℕ → PreparedValues) : Tree → Prop
  | .leaf _ key code => PreparedOK caps perfect q (codeRecord code) (pre key)
  | .branch _ _ left right => left.AllPrepared caps perfect q pre ∧ right.AllPrepared caps perfect q pre

def codePreparedCheck (q : ℕ) (p : PreparedValues) (values : CostValues)
    (bound code : ℕ) : Bool :=
  if p.feasible then (List.range (codeRecord code 11+1)).all fun e =>
    preparedCost q p values (codeRecord code) e≤ bound else true



def Tree.preparedCheck (mask : Array Bool) (q : ℕ) (pre : ℕ → PreparedValues)
    (values : CostValues) (bound : ℕ) (t : Tree) : Bool :=
  if blocked mask t.mask then true else
    match t with
    | .leaf _ key code => codePreparedCheck q (pre key) values bound code
    | .branch _ _ left right => left.preparedCheck mask q pre values bound &&
        right.preparedCheck mask q pre values bound





def Tree.checkStatics (codes : ℕ → ℕ) (count : ℕ) : Tree → Bool
  | .leaf _ key code => decide (key< count) &&
      decide (staticKeyCode code=codes key)
  | .branch _ _ left right => left.checkStatics codes count && right.checkStatics codes count

def prepared (codes : ℕ → ℕ) (values : ℕ → ConvertedValues) (q key : ℕ) : PreparedValues :=
  preparedFromConverted q (staticCodeRecord (codes key) 11) (values key)



end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal


