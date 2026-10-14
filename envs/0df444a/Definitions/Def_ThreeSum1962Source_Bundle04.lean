-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle04
-- name    : ThreeSum1962Source_Bundle04
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:07:06.060273+00:00
-- url     : https://prove2.me/theorems/e4ca1d31-80ba-4f59-830b-05948b0addd3
-- title:
--   Subset enumeration, reporting frontiers, and bucket layouts
-- statement:
--   This bundle defines cardinality-layer and downset enumeration, mask decoding, Pascal-table storage, partial subset-transform stages, signed-leaf tables, and the ordered reporting frontier. For incidences \(I\), words \(w_i\), and natural weights \(a_i\), the prefix mass is
--   $$
--   M(k,u)=\sum_{\substack{i\in I\\\operatorname{take}_k(w_i)=u}}a_i.
--   $$
--   The frontier recursively extends prefixes and retains positive-query entries. Other definitions specify thresholded traversal budgets, block-source memory banks, stable residue-bucket positions and storage predicates, Boolean cover scores, coloring indices, and original-value bucket-pair scans. The bundle also supplies the remainder, logarithm, halving and merge routine bodies used by these components.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandEnumeration.lean#L16-L75
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BinomialEntropy.lean#L22-L253
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BooleanGreedy.lean#L12-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BoxStages.lean#L17-L43
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ColorParameters.lean#L14-L50
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandLookup.lean#L20-L150
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceBatchLayout.lean#L16-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorIndex.lean#L28-L42
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverScores.lean#L16-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDownsetEnumeration.lean#L18-L67
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMaskMinimum.lean#L18-L36
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightPascal.lean#L18-L90
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingBucketPairs.lean#L20-L73
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingGatherPair.lean#L11-L16
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSignedLeafBatch.lean#L26-L37
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSignedLeafTable.lean#L23-L36
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketSelect.lean#L19-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetEnumeration.lean#L18-L49
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalGraph.lean#L22-L126
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/MaskDecode.lean#L16-L63
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RadixKeyLists.lean#L17-L100
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Reporting.lean#L21-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedTraversalCostBounds.lean#L23-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedTraversalPrefixCosts.lean#L17-L49
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBuckets.lean#L22-L138
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceControlCosts.lean#L9-L12
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetStages.lean#L16-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L31-L125
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L42-L249
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L57-L153

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedTraversalCostBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Polynomial overhead of the actual traversal operations

All logarithmic residue costs are bounded before the binomial work terms
are charged. This prevents an endpoint magnitude from being used as a
running-time bound. The final scalar overhead is polynomial in the block
dimensions and will therefore have exponent zero at the prescribed scales.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Light LocalCoverBounds LightBlockQuery ReportingHostLevelData
open SubsetAddress
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

def size (h J : ℕ) : ℕ := (J+1)*(2048*h+20)
def overhead (h J : ℕ) : ℕ := 200000*(size h J)^4





























































































































































































end ThreeSum.SharedTraversalCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedTraversalPrefixCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Summing the actual dense-guard branches in physical slot order

The counter at slot i is the mass of slots before i. The expensive branch
is charged only when adding the current mass still fits the threshold.
These charges sum to at most that threshold, including when a later slot
crosses it. No bound on the mass of the crossing slot is required.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset
open scoped BigOperators

def prefixMass (mass : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, mass i

def guardedMass (mass : ℕ → ℕ) (threshold n : ℕ) : ℕ :=
  ∑ i ∈ range n, if threshold < prefixMass mass i+mass i then 0 else mass i


























def guardedBudget (mass : ℕ → ℕ) (threshold initial work n : ℕ) : ℕ :=
  ∑ i ∈ range n, (initial+
    if threshold < prefixMass mass i+mass i then 0 else mass i*work)




































end ThreeSum.SharedTraversalCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSumApsp_Lang_Lib_Emod
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod

/-- The local variables of emod: the arguments x, M and fr (the result replaces x), what is left
of |x|, the number of entries of the table, and the next multiple of M. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Modulus : ℕ := 1
@[inherit_doc Arg] abbrev Free : ℕ := 2
@[inherit_doc Arg] abbrev Rest : ℕ := 3
@[inherit_doc Arg] abbrev Count : ℕ := 4
@[inherit_doc Arg] abbrev Mult : ℕ := 5

end Emod

open Emod in
/-- One entry of the table: the multiple is written to the table and doubled. -/
def emodTableRound : Stmt :=
  (Light.Stmt.seq
    (.store ((Light.Expr.op Light.Op.add) (v Free) (v Count)) (v Mult))
    (Light.Stmt.seq (.set Count ((Light.Expr.op Light.Op.add) (v Count) (k 1)))
      (.set Mult ((Light.Expr.op Light.Op.add) (v Mult) (v Mult)))))

open Emod in
/-- The table: M, 2M, 4M, … are written to the free pointer as long as they are at most |x|. -/
def emodTable : Stmt := .while ((Light.Cond.le (v Mult) (v Rest))) emodTableRound

open Emod in
/-- The last entry of the table that has not been tried is subtracted if possible. -/
def emodReduceRound : Stmt :=
  (Light.Stmt.seq (.set Count ((Light.Expr.op Light.Op.sub) (v Count) (k 1)))
    (.ite
      (Light.Cond.le (M ((Light.Expr.op Light.Op.add) (v Free) (v Count)))
        (v Rest))
      (.set Rest
        ((Light.Expr.op Light.Op.sub) (v Rest)
          (M ((Light.Expr.op Light.Op.add) (v Free) (v Count)))))
      .skip))

open Emod in
/-- The entries of the table are subtracted, from the largest down, where possible. -/
def emodReduce : Stmt := .while ((Light.Cond.lt (k 0) (v Count))) emodReduceRound

open Emod in
/-- The sign: the remainder r of |x| gives the remainder of x. -/
def emodSign : Stmt :=
  .ite ((Light.Cond.lt (v Arg) (k 0)))
    (.ite ((Light.Cond.eq (v Rest) (k 0))) (.set Arg (k 0)) (.set Arg (((Light.Expr.op Light.Op.sub) (v Modulus) (v Rest)))))
    (.set Arg (v Rest))

open Emod in
/-- emod(x, M, fr). -/
def emodBody : Stmt :=
  (Light.Stmt.seq
    (.ite (Light.Cond.lt (v Arg) (k 0))
      (.set Rest ((Light.Expr.op Light.Op.sub) (k 0) (v Arg)))
      (.set Rest (v Arg)))
    (Light.Stmt.seq (.set Count (k 0))
      (Light.Stmt.seq (.set Mult (v Modulus))
        (Light.Stmt.seq emodTable (Light.Stmt.seq emodReduce emodSign)))))

/-- The number of doublings: the least k with a < M 2^k. -/
def emodRounds (a M : ℕ) : ℕ := Nat.size (a / M)

/-- The time of emod, for a = |x|. -/
@[simp] def emodTime (a M : ℕ) : ℕ := 43 * emodRounds a M + 34




























namespace Emod

/-- What emod asks of the limits, for a modulus M ≥ 1, numbers up to V and the free pointer fr. -/
structure Pre (lim : Limits) (Mo V fr : ℕ) : Prop where
  mod_pos : 1 ≤ Mo
  space : (lim.space : ℤ) ≤ lim.word
  word : (4 * V + 4 * Mo + 16 : ℤ) ≤ lim.word
  free : fr + (Nat.log 2 (V + 1) + 2) ≤ lim.space

/-- The first i entries of the table are in place, and no cell below the free pointer has changed.
-/
def Table (μ μ' : ℕ → ℤ) (Mo fr i : ℕ) : Prop :=
  (∀ j < i, μ' (fr + j) = ((Mo * 2 ^ j : ℕ) : ℤ)) ∧ Kept μ μ' fr

variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}










































































































































end Emod

end Light

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSumApsp_Lang_Lib_Logs
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light.Logs
end Light.Logs


/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs





@[inherit_doc Arg] abbrev Power : ℕ := 2

end Logs

open Logs

/-! ## The logarithm, rounded down -/

/-- log2(x): the candidate is L, and the power is 2^(L + 1). -/
def log2Body : Stmt :=
  (Light.Stmt.seq (.set Cand (k 0))
    (Light.Stmt.seq (.set Power (k 2))
      (Light.Stmt.seq
        (.while (Light.Cond.le (v Power) (v Arg))
          (Light.Stmt.seq
            (.set Power ((Light.Expr.op Light.Op.add) (v Power) (v Power)))
            (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1)))))
        (.set Arg (v Cand)))))

/-- The time of log2. -/
@[simp] def log2Time (x : ℕ) : ℕ := 14 * Nat.log 2 x + 12



































/-! ## The logarithm, rounded up -/

/-- clog2(x): the candidate is L, and the power is 2^L. -/
def clog2Body : Stmt :=
  (Light.Stmt.seq (.set Cand (k 0))
    (Light.Stmt.seq (.set Power (k 1))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v Power) (v Arg))
          (Light.Stmt.seq
            (.set Power ((Light.Expr.op Light.Op.add) (v Power) (v Power)))
            (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1)))))
        (.set Arg (v Cand)))))

/-- The time of clog2. -/
@[simp] def clog2Time (x : ℕ) : ℕ := 12 * Nat.clog 2 x + 10






























/-! ## The cube root, rounded up -/



































































































/-! ## Halves, rounded up -/

/-- half(h): the candidate is r. -/
def halfBody : Stmt :=
  (Light.Stmt.seq (.set Cand (k 0))
    (Light.Stmt.seq
      (.while
        (Light.Cond.lt ((Light.Expr.op Light.Op.add) (v Cand) (v Cand)) (v Arg))
        (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1))))
      (.set Arg (v Cand))))

/-- The time of half. -/
@[simp] def halfTime (h : ℕ) : ℕ := 10 * ((h + 1) / 2) + 10























end Light

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSumApsp_Lang_Lib_Merge
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Merging two segments

merge(a, na, b, nb, dst) writes the merge of the na cells from a and the nb cells from b to the na +
nb cells from dst, within `mergeTime (na + nb)` steps (`merge_meets`).  The model is `List.merge`:
the next output is the head of the first list unless the head of the second list is smaller.
Nothing is assumed about the order of the two lists.  Numbers are only compared and copied, so their
size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Merge

/-! ## The pure side: one step of List.merge on the rests of two lists -/

variable {l r : List ℤ} {i j : ℕ}



















end Merge

/-! ## The program -/

namespace Merge

/-- The local variables of merge: the arguments a, na, b, nb, dst, and the numbers i and j of cells
already taken from the first and the second list. -/
abbrev ListA : ℕ := 0
@[inherit_doc ListA] abbrev LenA : ℕ := 1
@[inherit_doc ListA] abbrev ListB : ℕ := 2
@[inherit_doc ListA] abbrev LenB : ℕ := 3
@[inherit_doc ListA] abbrev Dest : ℕ := 4
@[inherit_doc ListA] abbrev DoneA : ℕ := 5
@[inherit_doc ListA] abbrev DoneB : ℕ := 6

end Merge

open Merge in
/-- The next output is the head of the first list: dst[i + j] := a[i]; i := i + 1. -/
def mergeTakeLeft : Stmt :=
  (Light.Stmt.seq
    (.store
      ((Light.Expr.op Light.Op.add)
        ((Light.Expr.op Light.Op.add) (v Dest) (v DoneA)) (v DoneB))
      (M ((Light.Expr.op Light.Op.add) (v ListA) (v DoneA))))
    (.set DoneA ((Light.Expr.op Light.Op.add) (v DoneA) (k 1))))

open Merge in
/-- The next output is the head of the second list: dst[i + j] := b[j]; j := j + 1. -/
def mergeTakeRight : Stmt :=
  (Light.Stmt.seq
    (.store
      ((Light.Expr.op Light.Op.add)
        ((Light.Expr.op Light.Op.add) (v Dest) (v DoneA)) (v DoneB))
      (M ((Light.Expr.op Light.Op.add) (v ListB) (v DoneB))))
    (.set DoneB ((Light.Expr.op Light.Op.add) (v DoneB) (k 1))))

open Merge in
/-- merge(a, na, b, nb, dst). -/
def mergeBody : Stmt :=
  (Light.Stmt.seq (.set DoneA (k 0))
    (Light.Stmt.seq (.set DoneB (k 0))
      (.while
        (Light.Cond.lt ((Light.Expr.op Light.Op.add) (v DoneA) (v DoneB))
          ((Light.Expr.op Light.Op.add) (v LenA) (v LenB)))
        (.ite (Light.Cond.lt (v DoneA) (v LenA))
          (.ite (Light.Cond.lt (v DoneB) (v LenB))
            (.ite
              (Light.Cond.lt
                (M ((Light.Expr.op Light.Op.add) (v ListB) (v DoneB)))
                (M ((Light.Expr.op Light.Op.add) (v ListA) (v DoneA))))
              mergeTakeRight mergeTakeLeft)
            mergeTakeLeft)
          mergeTakeRight))))

namespace Merge

/-- What merge assumes: the two lists lie in the memory, and the output region is within the memory
and meets neither of them. -/
structure Pre (lim : Limits) (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  segL : Seg μ a l
  segR : Seg μ b r
  spaceL : a + l.length ≤ lim.space
  spaceR : b + r.length ≤ lim.space
  spaceD : dst + (l.length + r.length) ≤ lim.space
  sepL : Apart a l.length dst (l.length + r.length)
  sepR : Apart b r.length dst (l.length + r.length)

/-- The state after i cells of the first list and j cells of the second have been taken: they stand,
merged, in the first i + j cells of dst, and no cell outside dst has changed. -/
def Inv (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (i j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (out : List ℤ), σ = ⟨frame [a, l.length, b, r.length, dst, i, j], μ'⟩ ∧
    i ≤ l.length ∧ j ≤ r.length ∧ SameOutside μ μ' dst (l.length + r.length) ∧
    out.length = i + j ∧ Seg μ' dst out ∧ out ++ (l.drop i).merge (r.drop j) = l.merge r

/-- The invariant of the loop: t cells have been taken. -/
def Taken (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ i j, i + j = t ∧ Inv μ a b dst l r i j σ

variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

































/-- The time of merge, for n = na + nb numbers. -/
@[simp] def _root_.Light.mergeTime (n : ℕ) : ℕ := 40 * n + 12










































end Merge

end Light

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandLookup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress


/-!
# Division-free binary interval lookup in actual machine syntax

The search descends a constructed powers-of-two table and extends a known
prefix by one power at a time. Every tested endpoint is an explicit bounded
memory load. Neither natural-number division nor a function-valued memory
oracle is a machine operation. `search_meets` identifies its returned prefix
with any valid sorted partition, and hence with `BinarySearch.upperBound`.
-/

namespace ThreeSum.LightBandLookup

open Light ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: lower-endpoint base, length, query, powers base, remaining
width, accepted prefix. Locals 6 and 7 hold the next bit and candidate. -/
def searchBody (pSelf : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 4)))
    ((Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.sub) (v 4) (k 1)))
       (Light.Stmt.seq
         (.set 7
           ((Light.Expr.op Light.Op.add) (v 5)
             (M ((Light.Expr.op Light.Op.add) (v 3) (v 6)))))
         (.ite (Light.Cond.le (v 7) (v 1))
           (.ite
             (Light.Cond.lt (v 2)
               (M
                 ((Light.Expr.op Light.Op.sub)
                   ((Light.Expr.op Light.Op.add) (v 0) (v 7)) (k 1))))
             (.call pSelf [v 0, v 1, v 2, v 3, v 6, v 5] 0)
             (.call pSelf [v 0, v 1, v 2, v 3, v 6, v 7] 0))
           (.call pSelf [v 0, v 1, v 2, v 3, v 6, v 5] 0)))))
    (.set 0 (v 5))

def searchTime (L : ℕ) : ℕ := 120*L+30






























































































/-- `0` represents a miss; `i+1` represents interval number `i`. -/
def result (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ) : ℕ :=
  ((BinarySearch.locate lo hi n x).map Nat.succ).getD 0











/-- Arguments: lower base, upper base, size, query, powers base, width. -/
def body (pSearch : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSearch [v 0, v 2, v 3, v 4, v 5, k 0] 6)
    (.ite (Light.Cond.lt (k 0) (v 6))
      (.ite
        (Light.Cond.lt
          (M
            ((Light.Expr.op Light.Op.sub)
              ((Light.Expr.op Light.Op.add) (v 1) (v 6)) (k 1)))
          (v 3))
        (.set 0 (k 0)) (.set 0 (v 6)))
      (.set 0 (k 0))))

def time (L : ℕ) : ℕ := searchTime L+100




























































end ThreeSum.LightBandLookup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandEnumeration.Family
end ThreeSum.BandEnumeration.Family


/-!
# Enumeration of sorted-band triples through their quadratic owner set

Each owner is inverted with one binary interval lookup.  A final constant-size
test checks relevance and ownership.  No cubic list of triples is formed.
-/

namespace ThreeSum.BandEnumeration

structure Family where
  size : ℕ
  lower : ℕ → ℤ
  upper : ℕ → ℤ
  nonempty : ∀ i < size, lower i ≤ upper i
  sorted : ∀ i j, i ≤ j → j < size → lower i ≤ lower j
  separated : ∀ i j, i < j → j < size → upper i < lower j

namespace Family

abbrev Index (A : Family) := Fin A.size

def lo (A : Family) (i : A.Index) : ℤ := A.lower i
def hi (A : Family) (i : A.Index) : ℤ := A.upper i

def lookup (A : Family) (x : ℤ) : Option A.Index := do
  let i ← BinarySearch.locate A.lower A.upper A.size x
  if h : i < A.size then some ⟨i, h⟩ else none





















end Family

open Family

abbrev Triple (A B C : Family) := A.Index × (B.Index × C.Index)
abbrev Owner (A B C : Family) := (B.Index × C.Index) ⊕ (A.Index × (B.Index ⊕ C.Index))

def relevant (A B C : Family) (t : Triple A B C) : Prop :=
  Bands.Relevant A.lo A.hi B.lo B.hi C.lo C.hi t

instance (A B C : Family) (t : Triple A B C) : Decidable (relevant A B C t) :=
  inferInstanceAs (Decidable (Bands.Relevant A.lo A.hi B.lo B.hi C.lo C.hi t))

def owner (A B C : Family) (t : Triple A B C) : Owner A B C :=
  Bands.tripleOwner A.lo B.lo B.hi C.lo t

/-- Exactly one interval lookup for every candidate owner. -/
def candidate (A B C : Family) : Owner A B C → Option (Triple A B C)
  | .inl (j, k) => (A.lookup (C.lo k - B.hi j)).map fun i => (i, j, k)
  | .inr (i, .inl j) => (C.lookup (A.lo i + B.lo j)).map fun k => (i, j, k)
  | .inr (i, .inr k) => (B.lookup (C.lo k - A.lo i)).map fun j => (i, j, k)















































































































































end ThreeSum.BandEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BinomialEntropy


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# A finite entropy certificate for every binomial coefficient

The proof uses the mode of the exact binomial expansion with integral weights `k`
and `n-k`. It does not invoke Stirling's formula or introduce an asymptotic assumption.
-/

noncomputable section

namespace ThreeSum.BinomialEntropy

open Finset Real Set Filter
open scoped Topology

set_option maxRecDepth 10000

def weight (n k j : ℕ) : ℝ :=
  (n.choose j : ℝ) * (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - j)

theorem weight_nonneg (n k j : ℕ) : 0 ≤ weight n k j := by
  unfold weight
  positivity

theorem weight_recurrence {n k j : ℕ} (hj : j < n) :
    weight n k (j + 1) * ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) =
      weight n k j * ((n - j : ℕ) : ℝ) * (k : ℝ) := by
  have hc : (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hp : ((n - k : ℕ) : ℝ) ^ (n - j) =
      ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * ((n - k : ℕ) : ℝ) := by
    rw [show n - j = n - (j + 1) + 1 by omega, pow_succ]
  unfold weight
  rw [pow_succ, hp]
  calc
    _ = ((n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * k * (n - k : ℕ) := by ring
    _ = ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) *
        (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * k * (n - k : ℕ) := by rw [hc]
    _ = _ := by ring

theorem weight_step_up {n k j : ℕ} (hk : k < n) (hj : j < k) :
    weight n k j ≤ weight n k (j + 1) := by
  have hrec := weight_recurrence (k := k) (lt_trans hj hk)
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  have hcpos : 0 < ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by positivity
  have hfactor : ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) ≤
      ((n - j : ℕ) : ℝ) * (k : ℝ) := by
    rw [Nat.cast_sub hk.le, Nat.cast_sub (lt_trans hj hk).le, Nat.cast_add, Nat.cast_one]
    have hkj : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hkj)]
  have hmul := mul_le_mul_of_nonneg_left hfactor (weight_nonneg n k j)
  apply (mul_le_mul_iff_of_pos_right hcpos).mp
  nlinarith

theorem weight_step_down {n k j : ℕ} (hk : k < n) (hj : k ≤ j) :
    weight n k (j + 1) ≤ weight n k j := by
  by_cases hjn : j < n
  · have hrec := weight_recurrence (k := k) hjn
    have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
    have hcpos : 0 < ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by positivity
    have hfactor : ((n - j : ℕ) : ℝ) * (k : ℝ) ≤
        ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk.le, Nat.cast_sub hjn.le, Nat.cast_add, Nat.cast_one]
      have hkj : (k : ℝ) ≤ j := by exact_mod_cast hj
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.le
      have hn : 0 ≤ (n : ℝ) := by positivity
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hkj)]
    have hmul := mul_le_mul_of_nonneg_left hfactor (weight_nonneg n k j)
    apply (mul_le_mul_iff_of_pos_right hcpos).mp
    nlinarith
  · have hz : weight n k (j + 1) = 0 := by
      simp [weight, Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]
    rw [hz]
    exact weight_nonneg n k j

theorem weight_mode {n k j : ℕ} (hk : k < n) : weight n k j ≤ weight n k k := by
  by_cases hj : j ≤ k
  · have hu : ∀ {a b : ℕ}, a ≤ b → b ≤ k → weight n k a ≤ weight n k b := by
      intro a b hab
      induction hab with
      | refl => intro _; exact le_rfl
      | @step b hab ih =>
          intro hbk
          exact (ih (by omega)).trans (weight_step_up hk (by omega))
    exact hu hj le_rfl
  · have hd : AntitoneOn (weight n k) {i | k ≤ i} :=
      antitoneOn_nat_Ici_of_succ_le (fun i hi => weight_step_down hk hi)
    have hkj : k ≤ j := by omega
    exact hd (a := k) (by simp) (b := j) hkj hkj

theorem sum_weight {n k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ range (n + 1), weight n k j = (n : ℝ) ^ n := by
  have h := add_pow (k : ℝ) ((n - k : ℕ) : ℝ) n
  rw [← Nat.cast_add, Nat.add_sub_of_le hk] at h
  rw [h]
  apply sum_congr rfl
  intro j _
  unfold weight
  ring

theorem weight_bounds {n k : ℕ} (hk : k < n) :
    weight n k k ≤ (n : ℝ) ^ n ∧
      (n : ℝ) ^ n ≤ (n + 1 : ℝ) * weight n k k := by
  constructor
  · rw [← sum_weight hk.le]
    exact single_le_sum (fun j _ => weight_nonneg n k j) (mem_range.mpr (by omega))
  · rw [← sum_weight hk.le]
    calc
      _ ≤ ∑ _j ∈ range (n + 1), weight n k k := sum_le_sum (fun _ _ => weight_mode hk)
      _ = _ := by simp

theorem weight_positive {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    0 < weight n k k := by
  have hc : 0 < n.choose k := Nat.choose_pos hk.le
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  unfold weight
  positivity

theorem log_weight {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    Real.log (weight n k k) = Real.log (n.choose k : ℝ) +
      (k : ℝ) * Real.log k + ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by
  have hc : 0 < n.choose k := Nat.choose_pos hk.le
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  unfold weight
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]

theorem entropy_numerator {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) = (n : ℝ) * Real.log n -
      (k : ℝ) * Real.log k - ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by
  have hn : (n : ℝ) ≠ 0 := by have : 0 < n := lt_trans hk0 hk; positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  have hsub' : ((n - k : ℕ) : ℝ) ≠ 0 := by positivity
  have hcomp : (1 : ℝ) - (k : ℝ) / n = ((n - k : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hk.le]
    field_simp
  unfold Real.binEntropy
  simp only [Real.log_inv]
  rw [hcomp, Real.log_div hk' hn, Real.log_div hsub' hn]
  rw [Nat.cast_sub hk.le]
  field_simp
  ring

theorem log_choose_entropy_bounds_interior {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  have hn : 0 < n := lt_trans hk0 hk
  have hw := weight_bounds hk
  have hup := Real.log_le_log (weight_positive hk0 hk) hw.1
  have hlo := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n) hw.2
  rw [Real.log_pow, log_weight hk0 hk] at hup
  rw [Real.log_pow, Real.log_mul (by positivity : (n + 1 : ℝ) ≠ 0)
    (weight_positive hk0 hk).ne', log_weight hk0 hk] at hlo
  rw [entropy_numerator hk0 hk]
  constructor <;> linarith

/-- Finite entropy bounds, including zero and full layers. -/
theorem log_choose_entropy_bounds {n k : ℕ} (hk : k ≤ n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  have hl : 0 ≤ Real.log (n + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.choose_zero_right, Nat.cast_zero, zero_div, Real.binEntropy_zero,
      mul_zero, Nat.cast_one, Real.log_one, zero_sub]
    exact ⟨by linarith, le_rfl⟩
  by_cases hkn : k = n
  · subst k
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp only [Nat.choose_self, div_self hn, Real.binEntropy_one, mul_zero,
      Nat.cast_one, Real.log_one, zero_sub]
    exact ⟨by linarith, le_rfl⟩
  exact log_choose_entropy_bounds_interior (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkn)

/-- Exact finite error on an integer multiple of a rational-proportion layer. -/
theorem fixed_ratio_bounds {c r m : ℕ} (hc : 0 < c) (hr : r ≤ c) (hm : 0 < m) :
    (c : ℝ) * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) / m ≤
        Real.log ((c * m).choose (r * m) : ℝ) / m ∧
      Real.log ((c * m).choose (r * m) : ℝ) / m ≤
        (c : ℝ) * Real.binEntropy ((r : ℝ) / c) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have h := log_choose_entropy_bounds (Nat.mul_le_mul_right m hr)
  have hp : (((r * m : ℕ) : ℝ) / ((c * m : ℕ) : ℝ)) = (r : ℝ) / c := by
    push_cast
    field_simp
  rw [hp, Nat.cast_mul] at h
  constructor
  · apply (le_div_iff₀ hm').mpr
    have heq : ((c : ℝ) * Real.binEntropy ((r : ℝ) / c) -
        Real.log (c * m + 1 : ℝ) / m) * m =
        (c : ℝ) * m * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) := by
      field_simp
    rw [heq]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h.1
  · apply (div_le_iff₀ hm').mpr
    nlinarith [h.2]

theorem logarithmic_error_tendsto_zero {c : ℕ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.log (c * m + 1 : ℝ) / m) atTop (𝓝 0) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hn : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun m : ℕ => (c : ℝ) * m + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (hn.const_mul_atTop hc')
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  have hi := hn.inv_tendsto_atTop
  have hprod := hl.mul ((tendsto_const_nhds (x := (c : ℝ))).add hi)
  have heq : (fun m : ℕ => Real.log (c * m + 1 : ℝ) / m) =ᶠ[atTop]
      (fun m : ℕ => (Real.log (c * m + 1 : ℝ) / (c * m + 1)) * ((c : ℝ) + (m : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hm)
    field_simp
  apply Tendsto.congr' heq.symm
  simpa only [Function.comp_apply, id_eq, zero_mul, Pi.inv_apply] using hprod

/-- The entropy rate follows from the explicit logarithmic finite error. -/
theorem fixed_ratio_tendsto {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / m) atTop
      (𝓝 ((c : ℝ) * Real.binEntropy ((r : ℝ) / c))) := by
  have herr := logarithmic_error_tendsto_zero hc
  have hlo := (tendsto_const_nhds (x := (c : ℝ) * Real.binEntropy ((r : ℝ) / c))).sub herr
  have hbounds : ∀ᶠ m : ℕ in atTop,
      (c : ℝ) * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) / m ≤
          Real.log ((c * m).choose (r * m) : ℝ) / m ∧
        Real.log ((c * m).choose (r * m) : ℝ) / m ≤
          (c : ℝ) * Real.binEntropy ((r : ℝ) / c) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact fixed_ratio_bounds hc hr (by omega)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hlo) tendsto_const_nhds (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem fixed_ratio_bits_tendsto {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 ((c : ℝ) * ThreeSum.Parameters.entropy ((r : ℝ) / c))) := by
  have h := (fixed_ratio_tendsto hc hr).div_const (Real.log 2)
  simpa [div_div, ThreeSum.Parameters.entropy, mul_div_assoc] using h

/-- The actual local output count has exponent `2 E` relative to `D=2^mu`. -/
theorem output_table_rate :
    Tendsto (fun m : ℕ => Real.log ((256 * m).choose m : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 (2 * ThreeSum.Parameters.E)) := by
  have h := fixed_ratio_bits_tendsto (c := 256) (r := 1) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [ThreeSum.Parameters.E] <;> ring



























end ThreeSum.BinomialEntropy

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LocalGraph


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts


/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph

variable {α : Type*} [DecidableEq α]

def leftWord (s : Finset α) : α → Bool := fun i => decide (i ∈ s)

def rightWord (v : Finset α) : α → Bool := fun i => decide (i ∉ v)




















































section ConcreteGraph

open LayerCounts

/-- The enumerated ordered pairs of disjoint `h`-subsets are the edge type. -/
abbrev Edge (L h : ℕ) := {p // p ∈ edgeSet L h}

variable {L h : ℕ}

def left (e : Edge L h) : Fin L → Bool := leftWord e.val.1

def right (e : Edge L h) : Fin L → Bool := rightWord e.val.2

def output (e : Edge L h) : Finset (Fin L) := e.val.1 ∪ e.val.2

def equalityMask (e : Edge L h) : Fin L → Bool := fun i => left e i == right e i

theorem edge_data (e : Edge L h) :
    e.val.1.card = h ∧ e.val.2.card = h ∧ Disjoint e.val.1 e.val.2 :=
  mem_edgeSet.mp e.property

theorem output_card (e : Edge L h) : (output e).card = 2 * h := by
  rw [output, Finset.card_union_of_disjoint (edge_data e).2.2,
    (edge_data e).1, (edge_data e).2.1]
  omega




















def leftVertices (L h : ℕ) : Finset (Fin L → Bool) :=
  (vertices L h).image leftWord

def rightVertices (L h : ℕ) : Finset (Fin L → Bool) :=
  (vertices L h).image rightWord












































































end ConcreteGraph

end ThreeSum.LocalGraph

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BooleanGreedy


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators

def covers (matrix : ℕ → ℕ → ℕ) (row col : ℕ) : Prop := matrix row col = 1

instance (matrix : ℕ → ℕ → ℕ) : DecidableRel (covers matrix) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

def state (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : Finset ℕ :=
  Cover.greedyState (List.range rows) (covers matrix) (range cols) t

def active (matrix : ℕ → ℕ → ℕ) (rows cols t j : ℕ) : ℕ :=
  if j ∈ state matrix rows cols t then 1 else 0

def choice (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : ℕ :=
  Cover.selectMap (List.range rows) (covers matrix) (state matrix rows cols t)

def choices (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : List ℕ :=
  Cover.greedyChoices (List.range rows) (covers matrix) (range cols) t
































































































end ThreeSum.BooleanGreedy

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_RadixKeyLists


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists

variable {α β : Type*}

theorem flatMap_length_uniform (xs : List α) (f : α → List β) (q : ℕ)
    (h : ∀ x ∈ xs, (f x).length=q) : (xs.flatMap f).length=xs.length*q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,
      h x (by simp),ih (by intro a ha; exact h a (by simp [ha]))]
    ring

def step (p : ℤ) (base prev : List ℤ) : List ℤ :=
  base.flatMap fun x => prev.map fun y => x+p*y











def values (p : ℤ) (base : List ℤ) : ℕ → List ℤ
  | 0 => [0]
  | j+1 => step p base (values p base j)







/-- Original records, before taking integer keys. Distinct records remain
distinct even if their keys coincide. -/
def tuples (base : List α) : ℕ → List (List α)
  | 0 => [[]]
  | j+1 => base.flatMap fun a => (tuples base j).map (List.cons a)

theorem tuples_length (base : List α) (j : ℕ) :
    (tuples base j).length=base.length^j := by
  induction j with
  | zero => simp [tuples]
  | succ j ih =>
    rw [tuples,flatMap_length_uniform base _ (base.length^j) (by simp [ih]),pow_succ']

theorem mem_tuples (base : List α) (j : ℕ) (xs : List α) :
    xs ∈ tuples base j ↔ xs.length=j ∧ ∀ a ∈ xs, a ∈ base := by
  induction j generalizing xs with
  | zero => cases xs <;> simp [tuples]
  | succ j ih =>
    cases xs with
    | nil => simp [tuples]
    | cons a xs =>
      simp only [tuples,List.mem_flatMap,List.mem_map,List.cons.injEq,
        ih,List.length_cons,Nat.add_right_cancel_iff,List.mem_cons,forall_eq_or_imp]
      constructor
      · rintro ⟨b,hb,ys,⟨hlen,hsub⟩,rfl,rfl⟩
        exact ⟨hlen,hb,hsub⟩
      · rintro ⟨hlen,hb,hsub⟩
        exact ⟨a,hb,xs,⟨hlen,hsub⟩,rfl,rfl⟩















theorem values_eq_map (p : ℤ) (raw : α → ℤ) (base : List α) (j : ℕ) :
    values p (base.map raw) j = (tuples base j).map (Radix.positionalHash p raw) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [values,step,tuples,List.flatMap_map,List.map_flatMap,List.map_map,ih]
    apply List.flatMap_congr
    intro a ha
    simp only [Function.comp_def,Radix.positionalHash]




























end ThreeSum.RadixKeyLists

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BoxStages


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Canonical sparse boxes as stored prefix-zeta stages

A global coordinate prefix intersects each flagged set in an initial
segment. Storing those initialCoords stages uses only a polynomial factor more
than the compact downset. The resulting entries are exactly the signed
box sums used by the sparse-query partition.
-/

namespace ThreeSum.BoxStages

open Finset

def initialCoords (L j : ℕ) : Finset (Fin L) := univ.filter fun a => a.val < j













def nextCoord {L : ℕ} (j : ℕ) (hj : j < L) : Fin L := ⟨j,hj⟩










def stageValue {L : ℕ} (f : Finset (Fin L) → ℤ) (j : ℕ) : Finset (Fin L) → ℤ :=
  Subset.partialZeta (initialCoords L j) f













































































































end ThreeSum.BoxStages

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Reporting


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Executable positive-prefix reporting

The routine enumerates children of the current positive frontier and discards
zero counts. Its correctness interface asks for exact natural prefix counts;
the subset-transform identities supply those counts in the application.
No bound on the cost of obtaining a count is assumed or proved here.
-/

namespace ThreeSum.Reporting

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq α]

def mass (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) : ℕ :=
  Subset.fiberMass I (fun i => (word i).take k) weight pre














/-- Children are supplied in an explicit order; no choice-based ordering or
advice is used. `query` is the exact-count procedure's value interface. -/
def frontier (children : ℕ → List α) (query : ℕ → List α → ℕ) : ℕ → List (List α)
  | 0 => if 0 < query 0 [] then [[]] else []
  | k + 1 =>
      ((frontier children query k).flatMap fun pre =>
        (children k).map fun x => pre ++ [x]).filter fun pre => 0 < query (k + 1) pre






















































































































end ThreeSum.Reporting

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SubsetStages


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Canonical suffix stages of a compact zeta table

Stage `j` has processed exactly the last `j` coordinates. Advancing one
stage is one ordinary zeta pass. Every value and every predecessor used
by these stages remains inside the same cardinality downset.
-/

namespace ThreeSum.SubsetStages

open Finset

/-- The last `j` coordinates of the width-`L` universe. -/
def suffix (L j : ℕ) : Finset (Fin L) := univ.filter fun a => L-j ≤ a.val













def nextCoord {L : ℕ} (j : ℕ) (hj : j < L) : Fin L := ⟨L-1-j,by omega⟩











def stageValue {L : ℕ} (f : Finset (Fin L) → ℤ) (j : ℕ) : Finset (Fin L) → ℤ :=
  Subset.partialZeta (suffix L j) f




















































end ThreeSum.SubsetStages

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceBatchLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout

open SubsetAddress LightZetaStages

def family (W cut : ℕ) : ℕ := (W+1)*downsetCap W cut
def stride (W cut : ℕ) : ℕ := 5*downsetCap W cut+2*W+2+2*family W cut
def banks (base count : ℕ) : ℕ := base+2*count
def slot (base count W cut i : ℕ) : ℕ := banks base count+i*stride W cut
def coeff0 (base count W cut i : ℕ) : ℕ := slot base count W cut i+downsetCap W cut
def coeff1 (base count W cut i : ℕ) : ℕ := coeff0 base count W cut i+W
def rawLeft (base count W cut i : ℕ) : ℕ := coeff1 base count W cut i+W
def rawRight (base count W cut i : ℕ) : ℕ := rawLeft base count W cut i+downsetCap W cut
def flags (base count W cut i : ℕ) : ℕ := rawRight base count W cut i+downsetCap W cut
def leftBase (base count W cut i : ℕ) : ℕ := flags base count W cut i+2*downsetCap W cut+2
def rightBase (base count W cut i : ℕ) : ℕ := leftBase base count W cut i+family W cut
def maskBase (base count W cut : ℕ) : ℕ := slot base count W cut count
def bitBase (base count W cut : ℕ) : ℕ := maskBase base count W cut+downsetCap W cut
def rowOut (base count W cut : ℕ) : ℕ := bitBase base count W cut+W
def work (base count W cut : ℕ) : ℕ := rowOut base count W cut+2




















































































































end ThreeSum.LightBlockSourceBatchLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDownsetEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Sequential enumeration of a compact downset

This routine invokes the guarded layer enumerator for the successive
cardinalities. Each layer starts immediately after the preceding layer;
the only traversal besides the emitted masks is polynomial in the bit
width. All power-table reads are shared across the layer calls.
-/

namespace ThreeSum.LightDownsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def layers (L : ℕ) : ℕ → List ℕ
  | 0 => []
  | j+1 => layers L j ++ enumerateLayer L j



















def budget (L cut : ℕ) : ℕ := 150*((4*L+1)*downsetCap L cut+1)












def roundBody (pEnum : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pEnum [v 0, v 4, k 0, (Light.Expr.op Light.Op.add) (v 2) (v 5), v 3] 6)
    (.set 5 ((Light.Expr.op Light.Op.add) (v 5) (v 6))))

def body (pEnum : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 (k 0))
    (Light.Stmt.seq
      (.for 4 ((Light.Expr.op Light.Op.add) (v 1) (k 1)) (roundBody pEnum))
      (.set 0 (v 5))))

def time (L cut : ℕ) : ℕ := (cut+1)*(budget L cut+70)+40

def Inv (μ : ℕ → ℤ) (L cut dst powers j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,dst,powers,j,layerOffset L j,r],μ'⟩ ∧
    SegN μ' dst (layers L j) ∧ SameOutside μ μ' dst (layerOffset L j)












































































































end ThreeSum.LightDownsetEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSignedLeafBatch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Initial signed-product table writes on one actual mask layer -/

namespace ThreeSum.LightSignedLeafBatch

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode

variable {lim : Limits} {P : Program}















/-- Width, source cutoff, suffix stage, both prefix cardinalities and masks,
layer cardinality, number of masks, mask base, source bases, output, scratch. -/
def body (pCell : ℕ) : Stmt :=
  .for 14 (v 8)
    (.call pCell [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,M (((Light.Expr.op Light.Op.add) (v 9) (v 14))),
      v 10,v 11,v 12,v 13] 15)



def values {W : ℕ} (μ : ℕ → ℤ) (dst : ℕ) (masks : List ℕ)
    (weight : Finset (Fin W) → ℤ) (S : Finset (Fin W)) : ℤ :=
  if subsetMask S ∈ masks then weight S else μ (dst+subsetRank S)
































































































































end ThreeSum.LightSignedLeafBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSignedLeafTable


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Constructing the compact initial signed-product table

This program enumerates each stored cardinality layer, evaluates every
leaf through actual source-stage reads, and writes its exact compact
address. It allocates a downset-sized mask buffer and polynomial scratch.
-/

namespace ThreeSum.LightSignedLeafTable

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}





def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnumSetup [v 0, v 13, v 11, v 12] 14)
    (.call pBatch
      [v 0, v 1, v 3, v 4, v 5, v 6, v 7, v 13, v 14, v 11, v 8, v 9, v 10, v 12]
      15))

/-- Width, source and box cutoffs, suffix stage, two prefix cardinalities and
masks, source bases, destination, mask buffer, polynomial scratch. -/
def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 13 (((Light.Expr.op Light.Op.add) (v 2) (k 1))) (roundBody pEnumSetup pBatch)



def stageValues {W : ℕ} (μ : ℕ → ℤ) (dst j : ℕ)
    (weight : Finset (Fin W) → ℤ) (S : Finset (Fin W)) : ℤ :=
  if S.card < j then weight S else μ (dst+subsetRank S)
















































































































































































































end ThreeSum.LightSignedLeafTable

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSubsetEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def output (L k pref : ℕ) : List ℤ :=
  (enumerateLayer L k).map (fun m => ((pref+m : ℕ) : ℤ))

















/-- Arguments: remaining width, cardinality, pref, output base, powers base.
The pref contains the already selected high bits. -/
def body (pSelf : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (v 1) (k 1)))
    ((Light.Stmt.seq (.store (v 3) (v 2)) (.set 0 (k 1))))
    (.ite ((Light.Cond.lt (v 0) (v 1)))
      (.set 0 (k 0))
      ((Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.sub) (v 0) (k 1)))
         (Light.Stmt.seq (.call pSelf [v 5, v 1, v 2, v 3, v 4] 6)
           (Light.Stmt.seq
             (.call pSelf
               [v 5, (Light.Expr.op Light.Op.sub) (v 1) (k 1),
                 (Light.Expr.op Light.Op.add) (v 2)
                   (M ((Light.Expr.op Light.Op.add) (v 4) (v 5))),
                 (Light.Expr.op Light.Op.add) (v 3) (v 6), v 4]
               7)
             (.set 0 ((Light.Expr.op Light.Op.add) (v 6) (v 7))))))))

def time (L k : ℕ) : ℕ := 150*enumerationWork L k









































































































































































end ThreeSum.LightSubsetEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_MaskDecode


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# The inverse interpretation of enumerated subset masks

Decoding is used only to state the meaning of machine table cells. The
enumeration itself is the guarded cardinality-layer routine.
-/

namespace ThreeSum.MaskDecode

open Finset
open scoped BigOperators
open SubsetAddress

def decode (L m : ℕ) : Finset (Fin L) := univ.filter fun i => i.val ∈ m.bitIndices

 theorem bitIndices_subset {L m : ℕ} (hm : m < 2^L) :
    m.bitIndices.toFinset ⊆ Finset.range L := by
  intro i hi
  have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
  apply Finset.mem_range.mpr
  by_contra hn
  have hh : 2^L ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hn)
  omega

theorem natPositions_decode {L m : ℕ} (hm : m < 2^L) :
    natPositions (decode L m) = m.bitIndices.toFinset := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
    rw [← he]
    exact List.mem_toFinset.mpr (Finset.mem_filter.mp hj).2
  · intro hi
    have hiL := Finset.mem_range.mp (bitIndices_subset hm hi)
    apply Finset.mem_map.mpr
    refine ⟨⟨i, hiL⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact List.mem_toFinset.mp hi

theorem subsetMask_decode {L m : ℕ} (hm : m < 2^L) : subsetMask (decode L m) = m := by
  rw [subsetMask, natPositions_decode hm, maskOf]
  exact Finset.sum_toFinset_bitIndices_two_pow m

theorem decode_subsetMask {L : ℕ} (s : Finset (Fin L)) : decode L (subsetMask s) = s := by
  apply subsetMask_injective L
  exact subsetMask_decode (subsetMask_isMask s).1

theorem decode_card {L m : ℕ} (hm : m < 2^L) : (decode L m).card = weight L m := by
  have h := (subsetMask_isMask (decode L m)).2
  rw [subsetMask_decode hm] at h
  exact h.symm

theorem decode_card_layer {L k m : ℕ} (hm : m ∈ enumerateLayer L k) :
    (decode L m).card = k := by
  have h := (mem_enumerateLayer L k m).mp hm
  rw [decode_card h.1, h.2]

theorem decoded_layer_complete {L k : ℕ} (s : Finset (Fin L)) (hs : s.card = k) :
    s ∈ (enumerateLayer L k).map (decode L) := by
  apply List.mem_map.mpr
  refine ⟨subsetMask s, (mem_enumerateLayer L k _).mpr ?_, decode_subsetMask s⟩
  simpa only [hs] using subsetMask_isMask s





end ThreeSum.MaskDecode

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ColorParameters


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# A literal small coloring-parameter order

There are exactly 81*W² integer slots. Four ternary digits select the
color map, and the remaining quotient selects its two binary coordinates.
The inverse code proves that every separating parameter is present.
-/

namespace ThreeSum.ColorParameters

def count (W : ℕ) : ℕ := 81*W^2

def colorMap (a b c d : Fin 3) : (Bool × Bool) → Fin 3
  | (false,false) => a
  | (false,true) => b
  | (true,false) => c
  | (true,true) => d

def data (W t : ℕ) : List ℤ :=
  [t/81/W,t/81%W,t/27%3,t/9%3,t/3%3,t%3]

theorem width_pos {W t : ℕ} (ht : t < count W) : 0 < W := by
  by_contra hn
  have hw : W=0 := by omega
  simp [count,hw] at ht

theorem coordinate_bounds {W t : ℕ} (ht : t < count W) :
    t/81/W < W ∧ t/81%W < W := by
  have hw := width_pos ht
  have hq : t/81 < W*W := (Nat.div_lt_iff_lt_mul (by decide : 0 < 81)).mpr (by
    simpa only [count,pow_two,Nat.mul_comm] using ht)
  exact ⟨(Nat.div_lt_iff_lt_mul hw).mpr hq,Nat.mod_lt _ hw⟩

def parameter {W t : ℕ} (ht : t < count W) : Coloring.Parameter W :=
  ((⟨t/81/W,(coordinate_bounds ht).1⟩,⟨t/81%W,(coordinate_bounds ht).2⟩),
    colorMap ⟨t/27%3,Nat.mod_lt _ (by decide)⟩ ⟨t/9%3,Nat.mod_lt _ (by decide)⟩
      ⟨t/3%3,Nat.mod_lt _ (by decide)⟩ ⟨t%3,Nat.mod_lt _ (by decide)⟩)

def fields {W : ℕ} (p : Coloring.Parameter W) : List ℤ :=
  [p.1.1.val,p.1.2.val,(p.2 (false,false)).val,(p.2 (false,true)).val,
    (p.2 (true,false)).val,(p.2 (true,true)).val]



def index {W : ℕ} (p : Coloring.Parameter W) : ℕ :=
  ((((p.1.1.val*W+p.1.2.val)*3+(p.2 (false,false)).val)*3+
    (p.2 (false,true)).val)*3+(p.2 (true,false)).val)*3+(p.2 (true,true)).val





















































end ThreeSum.ColorParameters

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightPascal


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def tableSize (L : ℕ) : ℕ := (L+1)^2

def Table (μ : ℕ → ℤ) (dst L : ℕ) : Prop :=
  ∀ i ≤ L, ∀ j ≤ L, μ (dst + i*(L+1) + j) = (i.choose j : ℤ)

def rowBody (pLinear : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pLinear
      [v 0, (Light.Expr.op Light.Op.add) (v 0) (k 1),
        (Light.Expr.op Light.Op.add) (v 1) (k 1), v 2, k 1]
      3)
    (.store (v 1) (k 1)))

def rowTime (L : ℕ) : ℕ := LightArray.linearTime L + 20

















































def buildBody (pFill pRow : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 2 ((Light.Expr.op Light.Op.add) (v 1) (k 1)))
    (Light.Stmt.seq (.call pFill [v 0, v 2, k 0] 4)
      (Light.Stmt.seq (.store (v 0) (k 1))
        (.for 3 (v 1)
          (.call pRow
            [(Light.Expr.op Light.Op.add) (v 0)
                ((Light.Expr.op Light.Op.mul) (v 3) (v 2)),
              (Light.Expr.op Light.Op.add) (v 0)
                ((Light.Expr.op Light.Op.mul)
                  ((Light.Expr.op Light.Op.add) (v 3) (k 1)) (v 2)),
              v 1]
            4)))))

def buildTime (L : ℕ) : ℕ := fillTime (L+1) + L*(rowTime L+100)+100

def Inv (μ : ℕ → ℤ) (dst L i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [dst,L,L+1,i,r],μ'⟩ ∧
    (∀ a ≤ i, ∀ j ≤ L, μ' (dst+a*(L+1)+j) = (a.choose j : ℤ)) ∧
      SameOutside μ μ' dst (tableSize L)

















































































end ThreeSum.LightPascal

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceControlCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts

open Scales TrimScales StageBounds CostLedger BandScales

def factor (h J : ℕ) : ℕ :=
  1400*(J*(512*h)+1)^2+20*J+
    14*Nat.log 2 ((512*h)*LocalCoverBounds.localPrime h+1)+
    14*Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+2044

































































end ThreeSum.SourceControlCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCoverScores


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Computing all local-cover candidate scores

The input is a row-major Boolean cover matrix and an active-target vector.
This literal loop calls the checked Boolean scan once per row and stores
the negative count. A subsequent minimum scan selects the first maximum.
-/

namespace ThreeSum.LightCoverScores

open Light

def score (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ) (cols row : ℕ) : ℕ :=
  LightBooleanDot.dot (matrix row) active cols

def body (pDot : ℕ) : Stmt :=
  .for 5 (v 4) (
    (Light.Stmt.seq
      (.call pDot
        [(Light.Expr.op Light.Op.add) (v 0)
            ((Light.Expr.op Light.Op.mul) (v 5) (v 3)),
          v 1, v 3]
        6)
      (.store ((Light.Expr.op Light.Op.add) (v 2) (v 5))
        ((Light.Expr.op Light.Op.sub) (k 0) (v 6)))))

def time (rows cols : ℕ) : ℕ := rows*(LightBooleanDot.time cols+70)+6

def Inv (μ : ℕ → ℤ) (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (src activePtr dst rows cols i : ℕ) (σ : State) : Prop :=
  ∃ (v : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src,activePtr,dst,cols,rows,i,v],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = -(score matrix active cols j : ℤ)) ∧
    SameOutside μ μ' dst rows

variable {lim : Limits} {P : Program} {d : ℕ}
























































































end ThreeSum.LightCoverScores

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBucketSelect


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Constant-time independent-flag-aware bucket header access

The procedure reads two computed prefix headers and returns the absolute
start address and the selected count. A false endpoint flag returns count
zero. The original arrays, bucket data, and retained transform tables are
preserved when placed before the two output cells.
-/

namespace ThreeSum.LightSourceBucketSelect

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-- Arguments: offsets, flat index array, residue, independent flag, two-cell
output, residue count, original incidence count. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 0) (v 2))))
    (Light.Stmt.seq
      (.set 8
        (M
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 0) (v 2))
            (k 1))))
      (Light.Stmt.seq (.store (v 4) ((Light.Expr.op Light.Op.add) (v 1) (v 7)))
        (.ite (Light.Cond.eq (v 3) (k 1))
          (.store ((Light.Expr.op Light.Op.add) (v 4) (k 1))
            ((Light.Expr.op Light.Op.sub) (v 8) (v 7)))
          (.store ((Light.Expr.op Light.Op.add) (v 4) (k 1)) (k 0))))))

def countSelected (key : ℕ → ℕ) (N r flag : ℕ) : ℕ :=
  if flag=1 then count key r N else 0


















variable {lim : Limits} {P : Program} {d : ℕ}





















































end ThreeSum.LightSourceBucketSelect

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBuckets


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram


/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets

open Finset LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def offset (key : ℕ → ℕ) (N r : ℕ) : ℕ := ∑ s ∈ range r, count key s N



































def position (key : ℕ → ℕ) (N i : ℕ) : ℕ := offset key N (key i)+count key (key i) i









































































/-- Concrete array contract produced by prefix offsets and cursor scatter. -/
structure Stored (μ : ℕ → ℤ) (key : ℕ → ℕ) (N M offsets flat : ℕ) : Prop where
  offsets : ∀ r ≤ M, μ (offsets+r) = (offset key N r : ℤ)
  indices : ∀ i < N, μ (flat+position key N i) = (i : ℤ)

def bucketList (μ : ℕ → ℤ) (flat start length : ℕ) : List ℕ :=
  List.ofFn (fun t : Fin length => (μ (flat+start+t.val)).toNat)



















































end ThreeSum.SourceBuckets

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorIndex


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress


/-!
# Actual evaluation of one member of the deterministic coloring family

Two calls to the checked mask-coordinate routine inspect the selected bits
of an original array index. Four literal color arguments determine the map
from bit patterns to the three colors. The cost is linear in the binary
width and independent of the numeric index magnitude.
-/

namespace ThreeSum.LightColorIndex

open Light LightSubsetAddress

variable {lim : Limits} {P : Program}









def color {W : ℕ} (p : Coloring.Parameter W) (m : ℕ) : ℕ :=
  (p.2 (m.testBit p.1.1.val,m.testBit p.1.2.val)).val




/-- Width, index, two bit coordinates, four color-map entries, powers base. -/
def body (pErase : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pErase [v 0, v 2, v 1, v 0, v 8] 9)
    (Light.Stmt.seq (.call pErase [v 0, v 3, v 1, v 0, v 8] 10)
      (.ite (Light.Cond.eq (v 9) (v 1))
        (.ite (Light.Cond.eq (v 10) (v 1)) (.set 0 (v 4)) (.set 0 (v 5)))
        (.ite (Light.Cond.eq (v 10) (v 1)) (.set 0 (v 6)) (.set 0 (v 7))))))

def time (W : ℕ) : ℕ := 2*LightMaskErase.time W+150



















































































end ThreeSum.LightColorIndex

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightMaskMinimum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Computing the least coordinate of a nonempty mask

The program constructs its own powers table, scans the bit positions,
and uses the verified mask-deletion test. Its work is quadratic in the
width and its scratch is linear. It never scans mask values.
-/

namespace ThreeSum.LightMaskMinimum

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def best {L : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty) (j : ℕ) : ℕ :=
  if (S.min' hS).val < j then (S.min' hS).val else L

def roundBody (pErase : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pErase [v 0, v 5, v 1, v 0, v 2] 6)
    (.ite (Light.Cond.lt (v 6) (v 1))
      (.ite (Light.Cond.lt (v 5) (v 4)) (.set 4 (v 5)) .skip) .skip))

/-- Arguments: width, nonempty mask, scratch base. -/
def body (pPowers pErase : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 2, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 3)
    (Light.Stmt.seq (.set 4 (v 0))
      (Light.Stmt.seq (.for 5 (v 0) (roundBody pErase)) (.set 0 (v 4)))))

def time (L : ℕ) : ℕ := powTableTime (L+1)+L*(LightMaskErase.time L+100)+100

def Inv {L : ℕ} (μ : ℕ → ℤ) (S : Finset (Fin L)) (hS : S.Nonempty)
    (work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [L,subsetMask S,work,powRet,best S hS j,j,r],μ⟩
















































































































end ThreeSum.LightMaskMinimum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingBucketPairs


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Exact original-value testing of a retained Cartesian bucket pair

Every pair of retained physical indices is tested using the original integer
arrays. The result counts exactly the pairs with `a+b=c`. An empty right
fiber skips the entire left scan, so the verified cost is linear in the
actual Cartesian pair mass plus one, including empty fibers.
-/

namespace ThreeSum.LightReportingBucketPairs

open Light Finset
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def count (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) : ℕ :=
  ∑ i ∈ range nL, LightReportingBucketRow.count (a+left (indexL i)) right indexR nR































def roundBody (pRow : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 11
      (M
        ((Light.Expr.op Light.Op.add) (v 1)
          (M ((Light.Expr.op Light.Op.add) (v 3) (v 10))))))
    (Light.Stmt.seq (.set 12 ((Light.Expr.op Light.Op.add) (v 0) (v 11)))
      (Light.Stmt.seq (.call pRow [v 12, v 2, v 4, v 6, v 8] 13)
        (.set 9 ((Light.Expr.op Light.Op.add) (v 9) (v 13))))))

/-- A value, original left/right arrays, retained left/right index arrays,
selected left/right lengths, original left/right lengths. -/
def body (pRow : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 9 (k 0))
    (Light.Stmt.seq
      (.ite (Light.Cond.lt (k 0) (v 6)) (.for 10 (v 5) (roundBody pRow)) .skip)
      (.set 0 (v 9))))

def time (nL nR : ℕ) : ℕ := 240*nL*nR+100


def Inv (μ : ℕ → ℤ) (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ)
    (srcL srcR indicesL indicesR nL nR NL NR i : ℕ) (σ : State) : Prop :=
  ∃ l target ret : ℤ,
    σ=⟨frame [a,(srcL : ℤ),(srcR : ℤ),(indicesL : ℤ),(indicesR : ℤ),(nL : ℤ),(nR : ℤ),
      (NL : ℤ),(NR : ℤ),(count a left right indexL indexR nR i : ℤ),(i : ℤ),l,target,ret],μ⟩

variable {lim : Limits} {P : Program} {d : ℕ}





















































































end ThreeSum.LightReportingBucketPairs

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingGatherPair


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Actual aligned gathering of both selected reporting-prefix mask arrays -/

namespace ThreeSum.LightReportingGatherPair

open Light

variable {lim : Limits}

def body (pGather : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pGather [v 0, v 1, v 5, v 3, v 4] 7)
    (.call pGather [v 0, v 2, v 6, v 3, v 4] 0))

def program : Program := LightReportingGather.program ++ [body 0]
def time (t : ℕ) : ℕ := 2*LightReportingGather.time t+60






































end ThreeSum.LightReportingGatherPair

end


