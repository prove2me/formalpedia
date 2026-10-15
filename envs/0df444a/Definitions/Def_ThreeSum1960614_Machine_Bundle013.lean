-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle013
-- name    : ThreeSum1960614_Machine_Bundle013
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:31:24.496601+00:00
-- url     : https://prove2.me/theorems/9bc25c96-210b-49fc-949a-38381d5f6ce6
-- title:
--   Concrete cover selection, residue buckets, and positional-key programs
-- statement:
--   This library defines light-language programs for balancing offsets, band lookup, block coefficients, local cover selection, local cover rows, bit-mask erasure, modulo counts, recursive mask hash evaluation, prime-pool construction, positional-key products, retained bucket-pair testing, selected-index gathering, and physical residue-bucket construction. Procedure-number parameters identify the helper bodies to be called; the accompanying invariants relate current loop counters, local frames, written array prefixes, and preserved memory to the corresponding finite mathematical objects.
--
--   For a positive scale $y$, the prime-pool program tests the integers in $(y,4y]$ and appends the accepted primes in increasing order. For a residue-key map $k$ on $N$ original positions and $M$ buckets, prefix offsets and cursor scatter construct contiguous fibers. Each original position is written once, including positions carrying equal values. Bucket selection reads adjacent offsets and returns their difference when its independent endpoint flag is true, and zero otherwise. The retained-pair tester counts exact equalities $a+b=c$ over the selected physical fibers; an empty right fiber bypasses the left scan. Positional-key products retain every record sequence and repeated key.
--
--   These executable interfaces implement the cover, key, and bucket operations required by the deterministic integer 3SUM reporting argument. They make iteration counts and memory preservation explicit rather than assuming constant-time access to a semantically specified enumeration.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBalancedOffset.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandLookup.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockCoefficients.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCoverSelect.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverRow.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskErase.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightModuloCounts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOneHot.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightPrimePool.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightRadixKeys.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingBucketPairs.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingGather.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketOffsets.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketScatter.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketSelect.lean

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBalancedOffset
end ThreeSum.LightBalancedOffset
namespace ThreeSum.LightBandLookup
end ThreeSum.LightBandLookup
namespace ThreeSum.LightBlockCoefficients
end ThreeSum.LightBlockCoefficients
namespace ThreeSum.LightCoverSelect
end ThreeSum.LightCoverSelect
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightLocalCoverRow
end ThreeSum.LightLocalCoverRow
namespace ThreeSum.LightMaskErase
end ThreeSum.LightMaskErase
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
namespace ThreeSum.LightOneHot
end ThreeSum.LightOneHot
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.LightRadixKeys
end ThreeSum.LightRadixKeys
namespace ThreeSum.LightReportingBucketPairs
end ThreeSum.LightReportingBucketPairs
namespace ThreeSum.LightReportingGather
end ThreeSum.LightReportingGather
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceBucketOffsets
end ThreeSum.LightSourceBucketOffsets
namespace ThreeSum.LightSourceBucketScatter
end ThreeSum.LightSourceBucketScatter
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
end ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightBandLookup
end ThreeSum1960614.Machine.ThreeSum.LightBandLookup
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
end ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverSelect
end ThreeSum1960614.Machine.ThreeSum.LightCoverSelect
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskErase
end ThreeSum1960614.Machine.ThreeSum.LightMaskErase
namespace ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
end ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightOneHot
end ThreeSum1960614.Machine.ThreeSum.LightOneHot
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
end ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingGather
end ThreeSum1960614.Machine.ThreeSum.LightReportingGather
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

namespace ThreeSum1960614.Machine

/-!
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset
open _root_.ThreeSum.LightBalancedOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
open _root_.Finset
open scoped _root_.BigOperators







def body (pCyclic pMinimum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCyclic [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMinimum [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6] 0))



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightBalancedOffset

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Division-free binary interval lookup in actual machine syntax

The search descends a constructed powers-of-two table and extends a known
prefix by one power at a time. Every tested endpoint is an explicit bounded
memory load. Neither natural-number division nor a function-valued memory
oracle is a machine operation. `search_meets` identifies its returned prefix
with any valid sorted partition, and hence with `BinarySearch.upperBound`.
-/

namespace ThreeSum.LightBandLookup
open _root_.ThreeSum.LightBandLookup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

/-- Arguments: lower-endpoint base, length, query, powers base, remaining
width, accepted prefix. Locals 6 and 7 hold the next bit and candidate. -/
def searchBody (pSelf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 4)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 6))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.le (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 5] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7] 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 5] 0)))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 5))









/-- Arguments: lower base, upper base, size, query, powers base, width. -/
def body (pSearch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSearch [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.k 0] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.v 3)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))))









end ThreeSum.LightBandLookup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients
open _root_.ThreeSum.LightBlockCoefficients


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





def roundBody (pScale : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 8)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScale [_root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 8))] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScale [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 8))] 13)))))

/-- Arguments: number of blocks, block width, radix, occurrence array,
map-coefficient array, output-zero row, output-one row, scratch. -/
def body (pPowers pScale : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 7, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 2] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.for 8 (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.roundBody pScale)))





def Inv (μ : ℕ → ℤ) (J L p occ maps dst0 dst1 work : ℕ)
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (s a b r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [J,L,p,occ,maps,dst0,dst1,work,j,s,a,b,r0,r1],ν⟩ ∧
    _root_.ThreeSum.LightBlockCoefficients.Rows ν dst0 dst1 L p sel w0 w1 j ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst0 ∧ _root_.ThreeSum.LightBlockCoefficients.Powers ν work J p













end ThreeSum.LightBlockCoefficients

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual first-maximum candidate selection from a Boolean cover matrix -/

namespace ThreeSum.LightCoverSelect
open _root_.ThreeSum.LightCoverSelect


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def body (pScores pMinimum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScores [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 3] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMinimum [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3] 0))



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pScores : ℕ
  pDot : ℕ
  pMinimum : ℕ
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverSelect.body pScores pMinimum)
  scores : P[pScores]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverScores.body pDot)
  dot : P[pDot]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.body
  minimum : P[pMinimum]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.body







end ThreeSum.LightCoverSelect

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of one retained local-cover row

The program constructs all pair keys and trimming flags, clears the output
row, and marks exactly the keys with retained representations. Repeated
representations are handled by the support operation. Earlier matrix rows
and inputs below the scratch boundary are preserved.
-/

namespace ThreeSum.LightLocalCoverRow
open _root_.ThreeSum.LightLocalCoverRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def body (pPair pSupport : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPair [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSupport [_root_.ThreeSum1960614.Machine.Light.v 10, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 6)), _root_.ThreeSum1960614.Machine.Light.v 5, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 6), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 8)] 11))



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pPair : ℕ
  pDivide : ℕ
  pDot : ℕ
  pTrim : ℕ
  pSupport : ℕ
  pFill : ℕ
  pair : P[pPair]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.body pDivide pDot pTrim)
  divide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body
  dot : P[pDot]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.body
  trim : P[pTrim]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest.body
  support : P[pSupport]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.body pFill)
  fill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow.body pPair pSupport)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightLocalCoverRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine deletion of one mask coordinate

Each call decreases the remaining width. Powers of two are table reads;
there is no division, advice, or loop proportional to the mask value.
-/

namespace ThreeSum.LightMaskErase
open _root_.ThreeSum.LightMaskErase


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

/-- Arguments are remaining width, coordinate, mask, original width, power
base. Local 5 retains the next bit index across the recursive call. -/
def body (pSelf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 0)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 5))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 1, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 5))), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 5))) (_root_.ThreeSum1960614.Machine.Light.v 0))))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))









end ThreeSum.LightMaskErase

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete modular triple-counting procedure

Starting with three arrays of original signed integers and a positive modulus,
this fixed procedure computes its own power-of-two capacity, builds two padded
histograms, multiplies them with Karatsuba, folds the product into a correlation,
and looks up the residues of the A array. The result is exactly the modular
triple count used by the prime-score construction, including all multiplicities.
-/

namespace ThreeSum.LightModuloCounts
open _root_.ThreeSum.LightModuloCounts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-- Arguments: A, B, C, their three lengths, modulus, maximum length, scratch.
Local 9 holds the computed capacity; 10--14 are scratch-region pointers. -/
def body (pCapacity pHist pCyclic pResidues pLookup : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCapacity [_root_.ThreeSum1960614.Machine.Light.v 6] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 9)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 9)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 5) (_root_.ThreeSum1960614.Machine.Light.v 9)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHist [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.k 1)] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHist [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.k 1] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCyclic [_root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 6] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pResidues [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.k 1] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLookup [_root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6] 0)))))))))))









/-- Every procedure reference is tied to concrete syntax, including the
recursive multiplication closure. This structure contains no semantic oracle. -/
structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pCyclic : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pFill : ℕ
  pLookup : ℕ
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.body pCapacity pHist pCyclic pResidues pLookup)
  capacity : P[pCapacity]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.body
  hist : P[pHist]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody pEmod)
  emod : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody
  histogram : P[pHistogram]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody pFill)
  cyclic : P[pCyclic]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body pMultiply pLinear)
  multiply : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  lookup : P[pLookup]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightLookupSum.body









end ThreeSum.LightModuloCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A fixed word-RAM one-hot hash evaluator

The recursive procedure visits the mask's bit positions in decreasing order,
reads the selected coefficient, and adds it. Its time is linear in the width,
independent of the mask's numeric magnitude. The public wrapper constructs
its own powers-of-two table and preserves both coefficient arrays.
-/

namespace ThreeSum.LightOneHot
open _root_.ThreeSum.LightOneHot


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.OneHotMask
open _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

/-- Arguments are current width, mask, original width, power table, and the
two coefficient arrays. Local 6 retains the current coordinate. -/
def body (pSelf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 0)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 6)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 6, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 6))), _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 6)))))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))



















end ThreeSum.LightOneHot

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool
open _root_.ThreeSum.LightPrimePool


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000













































/-- Arguments: lower endpoint and first free address. The output occupies
at most `3*y` cells; the primality helper reuses the scratch beyond them. -/
def body (pTest : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 3)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTest [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 2)))))





def Inv (μ : ℕ → ℤ) (y free i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (cval rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [(y : ℤ),free,(_root_.ThreeSum.LightPrimePool.scanned y i).length,i,cval,rval,free+3*y],ν⟩ ∧
      _root_.ThreeSum1960614.Machine.Light.SegN ν free (_root_.ThreeSum.LightPrimePool.scanned y i) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pTest : ℕ
  test : _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimality.Procs P pTest
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.body pTest)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.body 1,_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimality.body 2,_root_.ThreeSum1960614.Machine.Light.emodBody]

def program_procs : _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.program 0 where
  pTest := 1
  test := ⟨2,rfl,rfl⟩
  main := rfl



end ThreeSum.LightPrimePool

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete positional-key product construction

The three fixed procedures build every product stage. Each stage has a
computed length header followed by its literal key array. The recursive
caller reads the previous header and appends Cartesian rows. Its final
array contains every record sequence, retaining repeated keys.
-/

namespace ThreeSum.LightRadixKeys
open _root_.ThreeSum.LightRadixKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000


















/-- Source local keys and count, product length, radix, first output cell. -/
def body (pSelf pRows : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 2)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 5))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 7) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRows [_root_.ThreeSum1960614.Machine.Light.v 0, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 3] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 7))))))))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 4)))))

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







end ThreeSum.LightRadixKeys

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-value testing of a retained Cartesian bucket pair

Every pair of retained physical indices is tested using the original integer
arrays. The result counts exactly the pairs with `a+b=c`. An empty right
fiber skips the entire left scan, so the verified cost is linear in the
actual Cartesian pair mass plus one, including empty fibers.
-/

namespace ThreeSum.LightReportingBucketPairs
open _root_.ThreeSum.LightReportingBucketPairs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000













def roundBody (pRow : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 10)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 11))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRow [_root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 8] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 13))))))

/-- A value, original left/right arrays, retained left/right index arrays,
selected left/right lengths, original left/right lengths. -/
def body (pRow : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.for 10 (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.roundBody pRow)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 9))))




def Inv (μ : ℕ → ℤ) (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ)
    (srcL srcR indicesL indicesR nL nR NL NR i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ l target ret : ℤ,
    σ=⟨_root_.Light.frame [a,(srcL : ℤ),(srcR : ℤ),(indicesL : ℤ),(indicesR : ℤ),(nL : ℤ),(nR : ℤ),
      (NL : ℤ),(NR : ℤ),(_root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR i : ℤ),(i : ℤ),l,target,ret],μ⟩

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightReportingBucketPairs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual indexed gathering of selected reporting masks

The index array and source array can lie on either side of the destination.
This supports reusable high-address child scratch and low-address frontier
storage without scanning discarded children or overwriting retained input.
-/

namespace ThreeSum.LightReportingGather
open _root_.ThreeSum.LightReportingGather


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def body : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.pass 5 (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5))))))
def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGather.body]






end ThreeSum.LightReportingGather

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual prefix offsets and initial scatter cursors

One linear scan of the retained count histogram writes all M+1 bucket
offsets and the M initial cursors. Original arrays before the output remain
untouched; no bucket is found by searching its original indices.
-/

namespace ThreeSum.LightSourceBucketOffsets
open _root_.ThreeSum.LightSourceBucketOffsets


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5)))))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 3)) (_root_.ThreeSum1960614.Machine.Light.v 6))))



def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (hist offsets cursor M N j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ ν : ℕ → ℤ, σ = ⟨_root_.Light.frame [hist,offsets,cursor,M,N,j,_root_.ThreeSum.SourceBuckets.offset key N j],ν⟩ ∧
    (∀ r < j, ν (offsets+r) = (_root_.ThreeSum.SourceBuckets.offset key N r : ℤ) ∧
      ν (cursor+r) = (_root_.ThreeSum.SourceBuckets.offset key N r : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν offsets (cursor+M-offsets)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceBucketOffsets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual linear scatter of original indices into residue buckets

Each original physical index is stored exactly once at its current bucket
cursor; that cursor is incremented. The position proof supplies complete,
duplicate-free fibers and charges one constant-time iteration per input.
-/

namespace ThreeSum.LightSourceBucketScatter
open _root_.ThreeSum.LightSourceBucketScatter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 3) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 6)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1)))))))



def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (keys cursor flat N M i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (k q : ℤ) (ν : ℕ → ℤ), σ = ⟨_root_.Light.frame [keys,cursor,flat,N,M,i,k,q],ν⟩ ∧
    (∀ r < M, ν (cursor+r) = ((_root_.ThreeSum.SourceBuckets.offset key N r+_root_.ThreeSum.LightHistogram.count key r i : ℕ) : ℤ)) ∧
    (∀ j < i, ν (flat+_root_.ThreeSum.SourceBuckets.position key N j) = (j : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν cursor (flat+N-cursor)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceBucketScatter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constant-time independent-flag-aware bucket header access

The procedure reads two computed prefix headers and returns the absolute
start address and the selected count. A false endpoint flag returns count
zero. The original arrays, bucket data, and retained transform tables are
preserved when placed before the two output cells.
-/

namespace ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum.LightSourceBucketSelect


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-- Arguments: offsets, flat index array, residue, independent flag, two-cell
output, residue count, original incidence count. -/
def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.k 0))))))









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceBucketSelect

end ThreeSum1960614.Machine


