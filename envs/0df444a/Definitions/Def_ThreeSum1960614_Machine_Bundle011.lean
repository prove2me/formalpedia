-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle011
-- name    : ThreeSum1960614_Machine_Bundle011
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:26:55.73243+00:00
-- url     : https://prove2.me/theorems/cc8fbb94-08ff-4637-a3b3-9b7d6feb2251
-- title:
--   Sorting, source normalization, global sizes, and the top-level solver wrapper
-- statement:
--   This bundle defines several program interfaces needed to turn a costed Light task solver into a word-RAM solution in the final input layout. The merge-sort program recursively sorts two halves, merges them into scratch memory, and copies back. Its output predicate requires a sorted permutation of the input list and preservation of all cells below the free pointer except the input segment. A subsequent normalization routine removes adjacent equal values within a separated color class.
--
--   For a problem $Q$, a task, and a decision/output mode, the wrapper data give solver arguments, the task instance, the free pointer, input and output correctness conditions, a bound of the form $c(n^2+1)$ on layout size, and evaluation-safety obligations. For each polynomial input-bound exponent $k\in\mathbb N$, the outer procedure reads the size $n$, handles $n=0$ explicitly, computes $U=n^k$ by multiplication, and invokes the solver. Auxiliary definitions record wrapper overhead, execution limits, available room, and what it means for the final state to answer $Q$ correctly.
--
--   Other procedures append matching residue fibers as original-index pairs, gather selected coefficient rows while preserving repeated selections, build consecutive band endpoints, compute a power-of-two capacity by doubling, score all local-cover candidates, and fold a polynomial product into cyclic correlation. For natural local output count $C$, prime $p$, block count $J$, and inner size $m$, the global-size routine actually computes $C^J$, $p^J$, the rounded square-root capacity, the band divisor, and the ceiling-divided band size. Its time and word-bound functions retain the arithmetic and quotient-loop costs.
--
--   The pair-key and flag constructor visits every pair of local vertices and tests disjointness and bucket caps. The primality procedure tests divisors from $2$ to $n-1$ for $n\ge2$ using the remainder routine; radix-digit extraction uses two natural quotient calls. Invariants record exact completed output prefixes and preservation outside each destination.
--
--   Together these definitions provide the actual preprocessing, normalization, size computation, and final-layout connection used in the complete deterministic integer 3SUM runtime proof. The merge-sort components retain their pinned upstream provenance.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWantedRow.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWeightGather.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/TopProcedure.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandPartition.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCapacity.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCoverScores.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCyclic.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightGlobalSizes.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightNormalize.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightPairFlags.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightPrimality.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightRadixDigit.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Light
end Light
namespace Light.MergeSort
end Light.MergeSort
namespace Light.Wrap
end Light.Wrap
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBandPartition
end ThreeSum.LightBandPartition
namespace ThreeSum.LightCapacity
end ThreeSum.LightCapacity
namespace ThreeSum.LightCoverScores
end ThreeSum.LightCoverScores
namespace ThreeSum.LightCyclic
end ThreeSum.LightCyclic
namespace ThreeSum.LightGlobalSizes
end ThreeSum.LightGlobalSizes
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightNormalize
end ThreeSum.LightNormalize
namespace ThreeSum.LightPairFlags
end ThreeSum.LightPairFlags
namespace ThreeSum.LightPrimality
end ThreeSum.LightPrimality
namespace ThreeSum.LightRadixDigit
end ThreeSum.LightRadixDigit
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightWantedRow
end ThreeSum.LightWantedRow
namespace ThreeSum.LightWeightGather
end ThreeSum.LightWeightGather
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.MergeSort
end ThreeSum1960614.Machine.Light.MergeSort
namespace ThreeSum1960614.Machine.Light.Wrap
end ThreeSum1960614.Machine.Light.Wrap
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPartition
end ThreeSum1960614.Machine.ThreeSum.LightBandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightCapacity
end ThreeSum1960614.Machine.ThreeSum.LightCapacity
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverScores
end ThreeSum1960614.Machine.ThreeSum.LightCoverScores
namespace ThreeSum1960614.Machine.ThreeSum.LightCyclic
end ThreeSum1960614.Machine.ThreeSum.LightCyclic
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
end ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightNormalize
end ThreeSum1960614.Machine.ThreeSum.LightNormalize
namespace ThreeSum1960614.Machine.ThreeSum.LightPairFlags
end ThreeSum1960614.Machine.ThreeSum.LightPairFlags
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimality
end ThreeSum1960614.Machine.ThreeSum.LightPrimality
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixDigit
end ThreeSum1960614.Machine.ThreeSum.LightRadixDigit
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedRow
end ThreeSum1960614.Machine.ThreeSum.LightWantedRow
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightGather
end ThreeSum1960614.Machine.ThreeSum.LightWeightGather
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

/-!
# Append an entire matching residue fiber as original-position pairs

The row performs exactly one iteration per matching right index. It writes
interleaved original left/right positions and preserves every earlier row.
-/

namespace ThreeSum.LightWantedRow
open _root_.ThreeSum.LightWantedRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 900000

/-- Left position, right-index array, fiber start/length, output base,
and number of pairs already written. -/
def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 6 (_root_.ThreeSum1960614.Machine.Light.v 3) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 6))))))



def Inv (μ : ℕ → ℤ) (left src start n dst previous j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ ν : ℕ → ℤ, σ=⟨_root_.Light.frame [left,src,start,n,dst,previous,j],ν⟩ ∧
    (∀ t < j, ν (dst+2*(previous+t))=(left : ℤ) ∧
      ν (dst+2*(previous+t)+1)=μ (src+start+t)) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν (dst+2*previous) (2*n)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightWantedRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Gathering selected coefficient rows

The selection array contains ordinary candidate indices. This fixed program
reads each selected index and copies its whole coefficient row into the
corresponding schedule occurrence. Repeated selections are retained.
-/

namespace ThreeSum.LightWeightGather
open _root_.ThreeSum.LightWeightGather


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000

def body (pCopy : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 3) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCopy [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 4)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 4)), _root_.ThreeSum1960614.Machine.Light.v 4] 7)))




def Inv (μ : ℕ → ℤ) (indices src dst rows width : ℕ) (select : ℕ → ℕ)
    (i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (x r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [indices,src,dst,rows,width,i,x,r],μ'⟩ ∧
    (∀ j < i, ∀ a < width, μ' (dst+j*width+a) = μ (src+select j*width+a)) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (rows*width)

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCopy : ℕ
  copy : P[pCopy]? = some _root_.ThreeSum1960614.Machine.Light.copyBody
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightGather.body pCopy)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightWeightGather

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Merge sort

sort(n, a, fr) sorts the n cells from a in place, in ascending order (`sort_meets`).  It is the
recursive merge sort: sort the first ⌈n/2⌉ cells, sort the rest, merge the two halves into the n
cells from the free pointer fr, and copy them back.  It calls half, merge and copy.

The proof is an induction on n.  `body_ends` treats the body of the procedure, given that the
procedure sorts the lists of half the length, and `join_ends` its last two calls; `sorted_merge`
says that what the four calls leave is a sorted permutation of the list.  The number of steps,
`sortTime n`, is of the order n log n (`clog_split`, `time_split`), and the calls are nested
⌈log₂ n⌉ + 1 deep.  Numbers are only compared and copied, so their size does not matter.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

namespace MergeSort
open _root_.Light.MergeSort








end MergeSort

open _root_.Light.MergeSort
open _root_.ThreeSum1960614.Machine.Light.MergeSort in
/-- The two sorted halves are merged into the cells from fr and copied back. -/
def sortJoin (pMerge pCopy : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMerge [_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Start, _root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Half, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Start) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Half), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Len) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Half), _root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Free] _root_.Light.MergeSort.Unused) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCopy [_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Free, _root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Start, _root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Len] _root_.Light.MergeSort.Unused))

open _root_.Light.MergeSort
open _root_.ThreeSum1960614.Machine.Light.MergeSort in
/-- sort(n, a, fr).  The parameters are the procedure numbers of sort itself, half, merge and
copy. -/
def sortBody (pSort pHalf pMerge pCopy : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 1) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Len))) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHalf [_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Len] _root_.Light.MergeSort.Half) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSort [_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Half, _root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Start, _root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Free] _root_.Light.MergeSort.Unused) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSort [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Len) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Half), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Start) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Half), _root_.ThreeSum1960614.Machine.Light.v _root_.Light.MergeSort.Free] _root_.Light.MergeSort.Unused) (_root_.ThreeSum1960614.Machine.Light.sortJoin pMerge pCopy))))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip



namespace MergeSort
open _root_.Light.MergeSort




/-- The program holds the four procedures. -/
structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pSort pHalf pMerge pCopy : ℕ) : Prop where
  sort : P[pSort]? = some (_root_.ThreeSum1960614.Machine.Light.sortBody pSort pHalf pMerge pCopy)
  half : P[pHalf]? = some _root_.ThreeSum1960614.Machine.Light.halfBody
  merge : P[pMerge]? = some _root_.ThreeSum1960614.Machine.Light.mergeBody
  copy : P[pCopy]? = some _root_.ThreeSum1960614.Machine.Light.copyBody



/-- What sort leaves: a sorted permutation of the list L at a; of the cells below fr only those of
the list may have changed. -/
def Sorted (μ : ℕ → ℤ) (a fr : ℕ) (L : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∃ L' : List ℤ, _root_.ThreeSum1960614.Machine.Light.Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' fr a L.length





variable {pSort pHalf pMerge pCopy : ℕ}







end MergeSort

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From a solver of a task to a program for the layout of the end statement

A solver gets its size, the bound on the numbers and its addresses as arguments.  A problem of the
end statement has a fixed layout: cell 0 holds the size n, then comes the input, then the output;
the bound U = n^κ is not in the memory.  For every κ one more procedure, `topBody`, is appended to
the program of the solver.  It reads n.  At size 0 it answers at once.  Otherwise it forms U = n^κ
by κ multiplications and n², computes the addresses, calls the solver, and returns the result of
the solver (for a decision problem) or 1.

`Wrap` collects what has to be said about a problem and a task for this to work.  `Wrap.body_ends`
and `Wrap.body_ends_zero` follow the procedure through its text, `Wrap.small` bounds the word size,
the memory and the depth that the run needs by a polynomial in n, and `Wrap.realized` is the
conclusion: if the task is solved in time T, then the problem is solved on the word RAM within a
constant times T.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-- Local 2 is multiplied κ times by local 1. -/
def powStmt : ℕ → _root_.ThreeSum1960614.Machine.Light.Stmt
  | 0 => _root_.ThreeSum1960614.Machine.Light.Stmt.skip
  | κ + 1 => (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (powStmt κ) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 1))))

/-- The outermost procedure.  Local 1 is n, the content of cell 0.  At size 0 the result is 0 for a
decision problem and 1 for a problem with an output.  Otherwise local 2 is U = n^κ, local 3 is n²,
and the arguments of the solver are expressions in these three; for a problem with an output the
result of the solver is replaced by 1. -/
def topBody (κ p : ℕ) (args : List _root_.ThreeSum1960614.Machine.Light.Expr) (dec : Bool) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 1 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.k 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.iteNe (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.powStmt κ) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args 0) (if dec then _root_.ThreeSum1960614.Machine.Light.Stmt.skip else _root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k (if dec then 0 else 1)))))







/-! ## The problems of `EndStatement` -/

section OfEnd

variable {Q : _root_.EndStatement.Problem} (x : _root_.ThreeSumApsp.WordRam.Bounded Q)







end OfEnd

/-! ## Polynomials in the size -/



/-- What connects a problem in the layout of the end statement with a task. -/
structure Wrap (Q : _root_.EndStatement.Problem) (task : _root_.Light.Task) (dec : Bool) where
  /-- The input and the output take at most cst (n² + 1) cells. -/
  cst : ℕ := 8
  cst_pos : 1 ≤ cst := by omega
  /-- The arguments of the solver, the free pointer last, as expressions in the locals 1 (n), 2 (U)
  and 3 (n²). -/
  args : List _root_.ThreeSum1960614.Machine.Light.Expr
  /-- The instance of the task. -/
  inst : _root_.ThreeSumApsp.WordRam.Bounded Q → task.Inst
  /-- The free pointer: the first cell after the output. -/
  fr : _root_.ThreeSumApsp.WordRam.Bounded Q → ℕ
  size_eq : ∀ x : _root_.ThreeSumApsp.WordRam.Bounded Q, task.size (inst x) = x.n
  bound_eq : ∀ x : _root_.ThreeSumApsp.WordRam.Bounded Q, task.bound (inst x) = x.U
  fr_pos : ∀ x : _root_.ThreeSumApsp.WordRam.Bounded Q, 1 ≤ fr x
  fr_le : ∀ x : _root_.ThreeSumApsp.WordRam.Bounded Q, fr x ≤ cst * (x.n * x.n + 1)
  /-- The expressions have the values that the solver expects. -/
  vals : ∀ (x : _root_.ThreeSumApsp.WordRam.Bounded Q) (σ : _root_.ThreeSum1960614.Machine.Light.State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → args.map (·.val σ) = task.args (inst x) ++ [(fr x : ℤ)]
  /-- They may be evaluated as soon as the addresses of the input and the output fit in a word. -/
  safe : ∀ (x : _root_.ThreeSumApsp.WordRam.Bounded Q) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (σ : _root_.ThreeSum1960614.Machine.Light.State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → ((cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ e ∈ args, e.Safe lim σ
  /-- At size 0 it is right to reject, for a decision problem, and to accept, whatever the output
  cells hold, for a problem with an output. -/
  zero : ∀ x : _root_.ThreeSumApsp.WordRam.Bounded Q, x.n = 0 → ∀ out, (_root_.ThreeSumApsp.WordRam.ofEnd Q).IsAnswer x (!dec) out
  /-- The input meets the precondition of the task. -/
  pre : ∀ x : _root_.ThreeSumApsp.WordRam.Bounded Q, 1 ≤ x.n → 1 ≤ x.U →
    task.Pre (inst x) (_root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x)) (fr x)
  /-- What the task promises is a right answer. -/
  post : ∀ (x : _root_.ThreeSumApsp.WordRam.Bounded Q) r μ', 1 ≤ x.n →
    task.Post (inst x) (_root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x)) (fr x) r μ' →
    (_root_.ThreeSumApsp.WordRam.ofEnd Q).IsAnswer x (_root_.Light.verdictOf dec (if dec then r else 1)) fun i =>
      μ' (((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x).length + i)

namespace Wrap
open _root_.Light.Wrap


variable {Q : _root_.EndStatement.Problem} {task : _root_.Light.Task} {dec : Bool}

/-- The steps of the outermost procedure, beside those of the solver. -/
def bodySteps (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) (κ : ℕ) : ℕ := 4 * κ + (w.args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 20

/-- The steps of the outermost procedure and of its call, beside those of the solver. -/
def extra (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) (κ : ℕ) : ℕ := w.bodySteps κ + 4

/-- The limits of the run on an instance. -/
def limits (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) (need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need) (x : _root_.ThreeSumApsp.WordRam.Bounded Q) : _root_.ThreeSum1960614.Machine.Light.Limits :=
  { word := ((need x.n x.U).word + (w.fr x + (need x.n x.U).cells) + w.cst * (x.n * x.n + 1) +
      x.U + x.n + 1 : ℕ)
    space := w.fr x + (need x.n x.U).cells
    depth := (need x.n x.U).depth + 2 }

/-- What the run asks of the limits. -/
structure Room (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) (need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need) (x : _root_.ThreeSumApsp.WordRam.Bounded Q) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) :
    Prop where
  /-- The addresses of the input and the output fit in a word. -/
  cells : ((w.cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word
  /-- The bound on the numbers, and 1, fit in a word. -/
  bound : ((x.U + 1 : ℕ) : ℤ) ≤ lim.word
  space : 1 ≤ lim.space
  depth : 2 ≤ lim.depth
  /-- The solver, called at depth 2 with the free pointer behind the output, has what it needs. -/
  solver : (need x.n x.U).Ok lim (w.fr x) 2



/-- The final state holds a right answer to the instance. -/
abbrev Answered (x : _root_.ThreeSumApsp.WordRam.Bounded Q) (dec : Bool) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  (_root_.ThreeSumApsp.WordRam.ofEnd Q).IsAnswer x (_root_.Light.verdictOf dec (σ.loc 0)) fun i => σ.mem (((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x).length + i)













end Wrap

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing consecutive band endpoints in actual memory

The program computes the number of bands itself. Its quotient loop is charged
linearly in that number, and both endpoint passes issue bounded-address
loads from the sorted source. Output arrays reserve `n` cells each; only the
computed band count is populated.
-/

namespace ThreeSum.LightBandPartition
open _root_.ThreeSum.LightBandPartition


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def lowerBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.pass 4 (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 3)))))





def upperBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 4) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.v 1)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.k 1)))))))





def body (pDivide pLower pUpper : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 1)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 2] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLower [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 2] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pUpper [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 4] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 4))))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))











end ThreeSum.LightBandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing the polynomial capacity in the benchmark language

This is the doubling loop used by the upstream `clog2` procedure, with its
power returned instead of its exponent. The actual machine therefore computes
the requested power-of-two capacity; the capacity is not supplied as advice.
-/

namespace ThreeSum.LightCapacity
open _root_.ThreeSum.LightCapacity


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 1 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 1 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 2)))))









end ThreeSum.LightCapacity

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing all local-cover candidate scores

The input is a row-major Boolean cover matrix and an active-target vector.
This literal loop calls the checked Boolean scan once per row and stores
the negative count. A subsequent minimum scan selects the first maximum.
-/

namespace ThreeSum.LightCoverScores
open _root_.ThreeSum.LightCoverScores


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



def body (pDot : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 4) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDot [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 3)), _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 5)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 6)))))



def Inv (μ : ℕ → ℤ) (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (src activePtr dst rows cols i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (v : ℤ) (μ' : ℕ → ℤ), σ = ⟨_root_.Light.frame [src,activePtr,dst,cols,rows,i,v],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = -(_root_.ThreeSum.LightCoverScores.score matrix active cols j : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst rows

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightCoverScores

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed folding of the verified polynomial product

The ordinary linear array procedure adds coefficients `r` and `r+p` for
each output residue. Its specification is the exact natural cyclic
correlation, including histogram multiplicities.
-/

namespace ThreeSum.LightCyclic
open _root_.ThreeSum.LightCyclic


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





/-- Arguments: capacity, left array, right array, product array, output
array, Karatsuba scratch, and cyclic modulus. -/
def body (pMultiply pLinear : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMultiply [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 5] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLinear [_root_.ThreeSum1960614.Machine.Light.v 3, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 6), _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.k 1] 7))















end ThreeSum.LightCyclic

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing global powers and rounded band sizes

This routine consumes the already computed local output count, local prime,
block count, and total inner size. All global powers, the square-root
rounding, and the final ceiling division are actual Light computations.
The square-root loop and quotient loop are included in the stated time.
-/

namespace ThreeSum.LightGlobalSizes
open _root_.ThreeSum.LightGlobalSizes


set_option maxHeartbeats 1000000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

def exponent (mu : ℕ) : ℕ := 62656016*mu/1000000000
def divisor (mu : ℕ) : ℕ := 2^_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent mu

def numerator (C J mu : ℕ) : ℕ := _root_.ThreeSum.LightGlobalSizes.root C J+_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu-1
def band (C J mu : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu/_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu

def values (C p J mu : ℕ) : List ℤ :=
  [((C^J : ℕ) : ℤ),((p^J : ℕ) : ℤ),_root_.ThreeSum.LightGlobalSizes.root C J,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.band C J mu]

def body (pPower pDiv pSqrt : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPower [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPower [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDiv [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 62656016) (_root_.ThreeSum1960614.Machine.Light.v 3), _root_.ThreeSum1960614.Machine.Light.k 1000000000] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPower [_root_.ThreeSum1960614.Machine.Light.k 2, _root_.ThreeSum1960614.Machine.Light.v 7] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSqrt [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDiv [_root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 8] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 10)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 6)))))))))))))))

def time (C J mu : ℕ) : ℕ := 2*_root_.ThreeSum.LightNatPower.time J+
  _root_.ThreeSum.LightSmallDivide.time (62656016*mu) 1000000000+_root_.ThreeSum.LightNatPower.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent mu)+_root_.Light.sqrtTime (C^J-1)+
  _root_.ThreeSum.LightSmallDivide.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu)+300

def word (C p J mu : ℕ) : ℕ := 2000000000*(C+p+J+mu+C^J+p^J+_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu+1)

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pPower : ℕ
  pDiv : ℕ
  pSqrt : ℕ
  power : P[pPower]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body
  divide : P[pDiv]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body
  sqrt : P[pSqrt]? = some _root_.ThreeSum1960614.Machine.Light.sqrtBody
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.body pPower pDiv pSqrt)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}












def localCount (n : ℕ) : ℕ :=
  _root_.ThreeSum.LocalCoverBounds.outputCount (464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))







end ThreeSum.LightGlobalSizes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Sorting and deduplicating a single already separated color class

The merge-sort implementation and proof are reused unchanged from the
attached upstream `ThreeSumApsp/Lang/Lib/Merge{,Sort}.lean` sources. The new
linear procedure removes adjacent repeats from the sorted output. The
original membership equivalence is retained, which is the witness needed
by the three-color reduction. Duplicates are removed only inside a class.
-/

namespace ThreeSum.LightNormalize
open _root_.ThreeSum.LightNormalize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def emitBody (pSelf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))))

/-- Arguments: sorted source, length, output. The last occurrence of each
value is retained, matching `List.dedup`. -/
def dedupBody (pSelf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 1)))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 1) (_root_.ThreeSum1960614.Machine.Light.v 1)))
      (_root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)))))
        (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)),_root_.ThreeSum1960614.Machine.Light.v 2] 0)
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.emitBody pSelf))
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.emitBody pSelf))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))









/-- Arguments: class source, class length, normalized output, merge scratch. -/
def body (pSort pDedup : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSort [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDedup [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2] 0))




structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pSort : ℕ
  pHalf : ℕ
  pMerge : ℕ
  pCopy : ℕ
  pDedup : ℕ
  sort : _root_.ThreeSum1960614.Machine.Light.MergeSort.Procs P pSort pHalf pMerge pCopy
  dedup : P[pDedup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedupBody pDedup)
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.body pSort pDedup)











end ThreeSum.LightNormalize

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing every candidate pair's key and trimming flag

All pairs of enumerated local vertices are visited. A zero coordinate-row
inner product tests disjointness; the two actual bucket counts determine
whether the pair survives. The local exhaustive scan is intentionally
unoptimized and its entire arithmetic and lookup cost is charged.
-/

namespace ThreeSum.LightPairFlags
open _root_.ThreeSum.LightPairFlags


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000





def roundBody (pDivide pDot pTrim : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 6] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 11) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDot [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 7)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 7)), _root_.ThreeSum1960614.Machine.Light.v 7] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 12)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 13)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTrim [_root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 15)), _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 16)), _root_.ThreeSum1960614.Machine.Light.v 9] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 11)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.v 16))) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.v 17)))))))))

def body (pDivide pDot pTrim : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.for 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.roundBody pDivide pDot pTrim)))





def Inv (μ : ℕ → ℤ) (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (a b c e f g : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap,dst+n*n,i,a,b,c,e,f,g],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (_root_.ThreeSum.LightPairFlags.pairKey n p left right j : ℤ)) ∧
    (∀ j < i, μ' (dst+n*n+j) = (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount j : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (2*(n*n))

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightPairFlags

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A costed elementary primality test

For `2 ≤ n`, this fixed program tests the integers from 2 through `n-1`
using the verified division-free remainder procedure. The deliberately
elementary running time is suitable for a subpolynomial prime window.
-/

namespace ThreeSum.LightPrimality
open _root_.ThreeSum.LightPrimality


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000















/-- Arguments: the integer to test and a scratch pointer. -/
def body (pEmod : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.v 0, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 2), _root_.ThreeSum1960614.Machine.Light.v 1] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 (_root_.ThreeSum1960614.Machine.Light.k 0)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 2))))





def Inv (μ : ℕ → ℤ) (n free i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [(n : ℤ),free,_root_.ThreeSum.LightPrimality.flag n i,i,rval],ν⟩ ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pEmod : ℕ
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimality.body pEmod)
  emod : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody









end ThreeSum.LightPrimality

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # An actual radix digit using two local counting divisions -/

namespace ThreeSum.LightRadixDigit
open _root_.ThreeSum.LightRadixDigit


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def body (pDivide : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 2] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 2))))))




variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightRadixDigit

end ThreeSum1960614.Machine


