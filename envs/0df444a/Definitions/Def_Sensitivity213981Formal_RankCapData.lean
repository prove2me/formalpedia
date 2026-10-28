-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankCapData
-- name    : Sensitivity213981Formal_RankCapData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:28:31.16676+00:00
-- url     : https://prove2.me/theorems/a3533a52-470f-4576-8a51-08943e7890fb
-- title:
--   Rank Cap Data — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Cap Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankNumeric.eligibleCount`, `ThreeBoundRankNumeric.tighten`, `ThreeBoundRankNumeric.capPrefix`, `ThreeBoundRankNumeric.convertedCap`, `ThreeBoundRankNumeric.suffixCapacity`, `ThreeBoundRankNumeric.negativeCount`, `ThreeBoundRankNumeric.recordAllowed`, `ThreeBoundRankNumeric.CapsSound`, `ThreeBoundRankNumeric.Record`, `ThreeBoundRankNumeric.headCount`, `ThreeBoundRankNumeric.guardCount`, `ThreeBoundRankNumeric.positivePrefix`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankCapData.lean, lines 1–181.

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankExpressions
import Definitions.Def_Sensitivity213981Formal_RankSmallAverage
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Exact q3 prefix caps and converted-arc refinements. The record fields
are counts of actual high heads, incoming hits, and residual prefixes. -/


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open ThreeBoundNumeric
open scoped BigOperators

abbrev Record := ℕ → ℕ

def headCount (r : Record) : ℕ := ∑ k : Fin 11, r k.val
def guardCount (r : Record) : ℕ := ∑ k : Fin 11,
  if ThreeBoundHighTypes.isGuard 3 k then r k.val else 0
def positivePrefix (r : Record) (q : ℕ) : ℕ := ∑ k : Fin 11,
  if ThreeBoundHighTypes.positivePrefix 3 q k then r k.val else 0
def lowCount (r : Record) (q : ℕ) : ℕ := ∑ k : Fin 11,
  if ThreeBoundHighTypes.positivePrefix 3 q k=false ∧ ThreeBoundHighTypes.budget 3 k ≤  q
  then r k.val else 0
def nextCount (r : Record) (q : ℕ) : ℕ := ∑ k : Fin 11,
  if ThreeBoundHighTypes.positivePrefix 3 q k=false ∧ ThreeBoundHighTypes.budget 3 k ≤  q+1
  then r k.val else 0
def eligibleCount (r : Record) (q : ℕ) : ℕ := ∑ k : Fin 11,
  if ThreeBoundHighTypes.budget 3 k ≤  q+1 then r k.val else 0

def tighten (base cap : ℕ) (p : Prop) [Decidable p] : ℕ := if p then min base cap else base



def capPrefix (caps : Caps) (r : Record) (q : ℕ) : ℕ :=
  let c0 := min (Caps.at caps.ordinary q-1-lowCount r q) (Caps.at caps.ordinary q-nextCount r q)
  let c1 := tighten c0 (positivePrefix r q+caps.pcross+r 34) (q=0 ∧ 1 ≤  headCount r)
  let c2 := tighten c1 (positivePrefix r q+Caps.at caps.zero 2+r 35) (q=0 ∧ 2 ≤  headCount r)
  let c3 := tighten c2 (Caps.at caps.marked (q-1)-1+(1-nextCount r q)) (q≠0 ∧ 1 ≤  eligibleCount r q)
  let c4 := tighten c3 (Caps.at caps.marked (if q=1 then 4 else 5)-1+(2-nextCount r q)) (q≠0 ∧ q ≤  2 ∧ 2 ≤  eligibleCount r q)
  let c5 := tighten c4 (positivePrefix r q+(Caps.at caps.marked 6-1)+r 36) (q=1 ∧ 3 ≤  headCount r)
  let c6 := tighten c5 (positivePrefix r q+(Caps.at caps.marked 7-1)+r 37) (q=2 ∧ 4 ≤  headCount r)
  let c7 := tighten c6 (positivePrefix r q+(Caps.at caps.marked 8-1)+r 38) (q=3 ∧ 5 ≤  headCount r)
  let c8 := tighten c7 (positivePrefix r q+(Caps.at caps.marked 9-1)+r 39) (q=3 ∧ 6 ≤  headCount r)
  let c9 := tighten c8 (positivePrefix r q+(Caps.at caps.marked 11-1)+r 40) (q=3 ∧ 7 ≤  headCount r)
  c9

def convertedCap (caps : Caps) (perfect : ℕ) (r : Record) (e q : ℕ) : ℕ :=
  let c0 := capPrefix caps r q-positivePrefix r q
  let c1 := tighten c0 (caps.pcross+allowance 1 e (guardCount r)) (q=0 ∧ 1 ≤  guardCount r)
  let c2 := tighten c1 (Caps.at caps.zero 2+allowance 2 e (guardCount r)) (q=0 ∧ 2 ≤  guardCount r)
  let c3 := tighten c2 (perfect+allowance 3 e (guardCount r)) (q=0 ∧ 3 ≤  guardCount r)
  let c4 := tighten c3 (Caps.at caps.marked 6-1+allowance 3 e (guardCount r)) (q=1 ∧ 3 ≤  guardCount r)
  let c5 := tighten c4 (Caps.at caps.marked 7-1+allowance 4 e (guardCount r)) (q=2 ∧ 4 ≤  guardCount r)
  let c6 := tighten c5 (Caps.at caps.marked 8-1+allowance 5 e (guardCount r)) (q=3 ∧ 5 ≤  guardCount r)
  let c7 := tighten c6 (Caps.at caps.marked 9-1+allowance 6 e (guardCount r)) (q=3 ∧ 6 ≤  guardCount r)
  let c8 := tighten c7 (Caps.at caps.marked 11-1+allowance 7 e (guardCount r)) (q=3 ∧ 7 ≤  guardCount r)
  c8

def suffixCapacity (caps : Caps) (perfect q : ℕ) (r : Record) (e k : ℕ) : ℕ :=
  ((interval k (q+1)).map fun j => convertedCap caps perfect r e j).foldl min
    (convertedCap caps perfect r e q)

def negativeCount (caps : Caps) (perfect q : ℕ) (r : Record) (e k : ℕ) : ℕ :=
  if k=0 then suffixCapacity caps perfect q r e 0 else
    suffixCapacity caps perfect q r e k-suffixCapacity caps perfect q r e (k-1)

def recordAllowed (n : ℕ) (caps : Caps) (a c : Entry) (r : Record) : Bool :=
  ((List.finRange 11).all fun k => r k.val=0 ∨ possible n a c k) &&
  ((List.range (c.tolerance+1)).all fun q => positivePrefix r q ≤  capPrefix caps r q)

structure CapsSound {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) (ell : V → V → Bool)
    (caps : Caps) (perfect : ℕ) : Prop where
  ordinary : ∀ q, q ≤  3 → CandidateCoherence.NoOrdinary R ell q (Caps.at caps.ordinary q)
  source : ResidualCaps.DominatorCardBound R ell 1 (caps.pcross+1)
  double : ResidualCaps.DominatorCardBound R ell 2 (Caps.at caps.zero 2+1)
  triple : ResidualCaps.DominatorCardBound R ell 3 (perfect+1)
  markedOne : ∀ q, 1 ≤  q → q ≤  3 →
    ResidualCaps.MarkedCardBound R ell q 1 (q+1) (Caps.at caps.marked (q-1))
  markedTwo : ∀ q, 1 ≤  q → q ≤  2 →
    ResidualCaps.MarkedCardBound R ell q 2 (2*(q+1)) (Caps.at caps.marked (if q=1 then 4 else 5))
  zeroThree : ResidualCaps.MarkedCardBound R ell 1 3 0 (Caps.at caps.marked 6)
  zeroFour : ResidualCaps.MarkedCardBound R ell 2 4 0 (Caps.at caps.marked 7)
  zeroFive : ResidualCaps.MarkedCardBound R ell 3 5 0 (Caps.at caps.marked 8)
  zeroSix : ResidualCaps.MarkedCardBound R ell 3 6 0 (Caps.at caps.marked 9)
  zeroSeven : ResidualCaps.MarkedCardBound R ell 3 7 0 (Caps.at caps.marked 11)





end ThreeBoundRankNumeric




end
end Sensitivity213981Formal


