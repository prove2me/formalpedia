-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle018
-- name    : ThreeSum1960614_Machine_Bundle018
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:43:14.069112+00:00
-- url     : https://prove2.me/theorems/1204715a-d2aa-4bdc-9a66-e905c493d4d5
-- title:
--   Parameter initialization, prime chains, and compact reporting primitives
-- statement:
--   The library defines concrete programs for testing an original-position triple, decoding radix digits, initializing all integer parameters, executing a contracting prime chain, deciding a retained reporting leaf, constructing sorted band headers, preparing residue buckets, building trimmed source tables, testing independent row flags, and performing a compact subset-zeta coordinate pass. An original triple test decodes three physical indices and returns true precisely for three distinct indices whose original integer values sum to zero. Radix decoding writes digits in forward, big-endian order while dividing the running quotient through a verified helper.
--
--   Given input length $n$, the parameter initializer constructs the block schedule, local graph parameters, selected prime and cap, global output count, radix, rounded band size, and prime window. Its placement record identifies every helper in a fixed finite program. A prime-chain level runs an explicit minimum-score search and multiplies the current modulus by the selected prime. Sorted-band data specify a strictly increasing list with the original value membership, its length, its band count, and its endpoint arrays. Source flags independently test the two orientations against actual retained bucket counts. A compact zeta pass enumerates each required cardinality layer rather than all numeric masks.
--
--   The associated invariants, memory predicates, local-mask interfaces, mass scales, and output-record interfaces connect these programs to the finite objects used in the deterministic integer 3SUM proof. Runtime and resource claims are established by the dependent theorems.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOriginalTripleRow.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOutputDecodeDigits.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightParameterInit.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightPrimeChain.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingLeaf.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSortedBands.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketSetup.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBuild.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceRowFlag.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightZetaPass.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LocalMaskHashes.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/MassScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/OutputDecodeRecords.lean

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
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
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Lean
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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

namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BruteTripleIndex
end ThreeSum.BruteTripleIndex
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightOriginalTripleRow
end ThreeSum.LightOriginalTripleRow
namespace ThreeSum.LightOutputDecodeDigits
end ThreeSum.LightOutputDecodeDigits
namespace ThreeSum.LightParameterInit
end ThreeSum.LightParameterInit
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightPrimeChain
end ThreeSum.LightPrimeChain
namespace ThreeSum.LightReportingLeaf
end ThreeSum.LightReportingLeaf
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSortedBands
end ThreeSum.LightSortedBands
namespace ThreeSum.LightSourceBucketSetup
end ThreeSum.LightSourceBucketSetup
namespace ThreeSum.LightSourceBuild
end ThreeSum.LightSourceBuild
namespace ThreeSum.LightSourceRowFlag
end ThreeSum.LightSourceRowFlag
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LightZetaPass
end ThreeSum.LightZetaPass
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
end ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow
end ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits
namespace ThreeSum1960614.Machine.ThreeSum.LightParameterInit
end ThreeSum1960614.Machine.ThreeSum.LightParameterInit
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimeChain
end ThreeSum1960614.Machine.ThreeSum.LightPrimeChain
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
end ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf
end ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSortedBands
end ThreeSum1960614.Machine.ThreeSum.LightSortedBands
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaPass
end ThreeSum1960614.Machine.ThreeSum.LightZetaPass
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore

namespace ThreeSum1960614.Machine

/-! # Execute one exact original-position triple test -/

namespace ThreeSum.LightOriginalTripleRow
open _root_.ThreeSum.LightOriginalTripleRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BruteTripleIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pDivide : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 1] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 1] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))))))))))))))




variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow.body 1,_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body]

end ThreeSum.LightOriginalTripleRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual big-endian radix digit arrays

The running quotient is divided by the radix once per coordinate, using
the checked binary quotient routine. Digits are written backwards into a
forward-order array. This works for an arbitrary positive radix, including
the occurrence-only radix used by the shared source catalog.
-/

namespace ThreeSum.LightOutputDecodeDigits
open _root_.ThreeSum.LightOutputDecodeDigits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pDivide : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 6 (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 5) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.v 7)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 5))))





def Inv (μ : ℕ → ℤ) (k J m dst work i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (q r : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [k,J,m,dst,work,(k/m^i : ℕ),i,q,r],ν⟩ ∧
    (∀ j < i, ν (dst+J-1-j)=(((k/m^j)%m : ℕ) : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}







end ThreeSum.LightOutputDecodeDigits

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# One fixed integer-parameter initializer from the input length

The program starts with only `n`, an output pointer, and a scratch pointer.
It constructs the exact block schedule, local graph counts, selected local
prime, cap, typed global output count, radix, rounded band size, and prime
window. Every helper in the fixed program has an operational contract.
-/

namespace ThreeSum.LightParameterInit
open _root_.ThreeSum.LightParameterInit


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000



def values (n : ℕ) : List ℤ :=
  ((_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n ++ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values (_root_.ThreeSum.LightParameterInit.half n)) ++
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)) ++ [(_root_.ThreeSum.Scales.primeWindow n : ℤ)]

def body (pCore pLocal pGlobal pSqrt pPower : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCore [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLocal [_root_.ThreeSum1960614.Machine.Light.v 4, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 5), _root_.ThreeSum1960614.Machine.Light.v 2] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pGlobal [_root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 3, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 13)] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSqrt [_root_.ThreeSum1960614.Machine.Light.v 9] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPower [_root_.ThreeSum1960614.Machine.Light.k 2, _root_.ThreeSum1960614.Machine.Light.v 11] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 18)) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 8)))))))))))))

def time (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time n+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.time (_root_.ThreeSum.LightParameterInit.half n)+
  _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+
  _root_.Light.sqrtTime (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum.LightNatPower.time (_root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n))+400

def space (work n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.space work (_root_.ThreeSum.LightParameterInit.half n)

def word (n : ℕ) : ℕ := 35000000000*(n+1)+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.word (_root_.ThreeSum.LightParameterInit.half n)+
  _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+100*(_root_.ThreeSum.Scales.primeWindow n+_root_.ThreeSum.Scales.inputBits n+1)

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCore : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pSqrt : ℕ
  pPower : ℕ
  core : _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.Procs P pCore
  localParams : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.Procs P pLocal
  globalSizes : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.Procs P pGlobal
  sqrt : P[pSqrt]? = some _root_.ThreeSum1960614.Machine.Light.sqrtBody
  power : P[pPower]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.body pCore pLocal pGlobal pSqrt pPower)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.body 1 6 20 16 21,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.body 2 3 4 5,_root_.ThreeSum1960614.Machine.Light.log2Body,_root_.ThreeSum1960614.Machine.Light.cbrtCeilBody,_root_.ThreeSum1960614.Machine.Light.halfBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.body 7 15 5,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.body 8,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.body 9 13 14,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildBody 10 11,_root_.ThreeSum1960614.Machine.Light.fillBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.rowBody 12,_root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody,
    _root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rankBody 14,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.body 16 17,_root_.ThreeSum1960614.Machine.Light.sqrtBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.body 18,_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimality.body 19,_root_.ThreeSum1960614.Machine.Light.emodBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.body 21 5 16,_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body]

def procs : _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program 0 :=
  ⟨1,6,20,16,21,
    ⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨7,15,5,⟨8,9,10,11,12,13,14,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
      ⟨16,17,rfl,⟨18,⟨19,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨21,5,16,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩



end ThreeSum.LightParameterInit

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing a deterministic chain of contracting moduli

Each level runs the concrete prime-score minimum program and multiplies the
current modulus by its returned prime. The exact finite contraction theorem
applies to this executed choice, with all original triple multiplicities.
-/

namespace ThreeSum.LightPrimeChain
open _root_.ThreeSum.LightPrimeChain


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

















/-- Arguments: A, B, C, their lengths, maximum length, prime array, its length,
number of levels, and the first free address. The prefix moduli occupy the
next `levels+1` cells. Every helper reuses the region beyond those cells. -/
def body (pMinimum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 12 (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMinimum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 14] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 11))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 11))))))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pMinimum : ℕ
  minimum : _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum.Procs P pMinimum
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimeChain.body pMinimum)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}















end ThreeSum.LightPrimeChain

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executable residue selection and original-value leaf decision

The host reduces the two actual endpoint values, selects the independently
trimmed physical buckets, and tests original values. Its Boolean result has
a memory-independent physical-index specification, suitable for sequential
candidate batching with the exact sum of the selected pair costs.
-/

namespace ThreeSum.LightReportingLeaf
open _root_.ThreeSum.LightReportingLeaf


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000



def body (pEmod pTest : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 13, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 4)] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 13, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 4)] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTest [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 17)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.program ++ [_root_.ThreeSum1960614.Machine.Light.emodBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.body 4 3]





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingLeaf

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Normalizing one color class and constructing all its band endpoints

This closed eleven-procedure program joins the actual merge sort, adjacent
deduplication, quotient computation, and endpoint passes. It writes the
distinct-value length and band count in a two-cell header. The following
cells are the lower endpoints and, after the distinct-value length, the
upper endpoints. The membership witness still refers to the original class.
-/

namespace ThreeSum.LightSortedBands
open _root_.ThreeSum.LightSortedBands


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



def Prepared (μ : ℕ → ℤ) (values endpoints g : ℕ) (original : List ℤ) : Prop :=
  ∃ L : List ℤ,
    _root_.ThreeSum1960614.Machine.Light.Seg μ values L ∧ L.Pairwise (· < ·) ∧ L.length ≤ original.length ∧
    (∀ z, z ∈ L ↔ z ∈ original) ∧
    μ endpoints = (L.length : ℤ) ∧ μ (endpoints+1) = (_root_.ThreeSum.BandPartition.size L.length g : ℤ) ∧
    (∀ i < _root_.ThreeSum.BandPartition.size L.length g, μ (endpoints+2+i) = L.getD (_root_.ThreeSum.BandPartition.start g i) 0) ∧
    (∀ i < _root_.ThreeSum.BandPartition.size L.length g, μ (endpoints+2+L.length+i) = L.getD (_root_.ThreeSum.BandPartition.stop L.length g i-1) 0)

/-- Arguments: class source and length, band size, values output, endpoint
header, merge scratch. -/
def body (pNormalize pPartition : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pNormalize [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 5] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPartition [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 2, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 2)] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 7))))))




structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pNormalize : ℕ
  pPartition : ℕ
  pDivide : ℕ
  pLower : ℕ
  pUpper : ℕ
  normalize : _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs P pNormalize
  partition : P[pPartition]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.body pDivide pLower pUpper)
  divide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body
  lower : P[pLower]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.lowerBody
  upper : P[pUpper]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.upperBody
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.body pNormalize pPartition)





















end ThreeSum.LightSortedBands

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Packed generic residue buckets from four scalar arguments

Only the code-array base, item count, positive residue count, and free pointer are
supplied. The program computes every histogram/offset/cursor/index address
and returns the next free address. Its exact fibers serve both source
reporting and the wanted-record residue join.
-/

namespace ThreeSum.LightSourceBucketSetup
open _root_.ThreeSum.LightSourceBucketSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000







def body (pBuild : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBuild [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 7)))))))



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pBuild : ℕ
  build : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.Procs P pBuild
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.body pBuild)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.body 1,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.body 2 4,_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody 3,_root_.ThreeSum1960614.Machine.Light.fillBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram.body 5 6,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter.body]

def programProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.program 0 :=
  ⟨1,⟨2,3,4,rfl,rfl,⟨5,6,rfl,rfl,rfl⟩,rfl⟩,rfl⟩





end ThreeSum.LightSourceBucketSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Building a trimmed source array from original signed inputs

The host first constructs the two-modulus original-input histogram, then
gathers it at the actual endpoint residues. All original input incidences
are counted once, and every subset-mask entry receives its exact independent
trimmed source multiplicity. Both stages share remainder scratch.
-/

namespace ThreeSum.LightSourceBuild
open _root_.ThreeSum.LightSourceBuild


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: original source and count; endpoint and flag arrays and count;
first modulus, global modulus, histogram, output, key scratch, remainder
scratch, and signed carry offset. -/
def body (pHistogram pGather : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHistogram [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pGather [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 10] 12))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pHistogram : ℕ
  pGather : ℕ
  histogram : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs P pHistogram
  gather : P[pGather]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceGather.body histogram.pEmod)
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBuild.body pHistogram pGather)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceBuild

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag
open _root_.ThreeSum.LightSourceRowFlag


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000





/-- Arguments: Boolean row, coefficient-zero, coefficient-one, width,
required cardinality, left and right bucket tables, local modulus, cap,
two-cell flag output, and reusable scratch. -/
def body (pRow pEmod pFlag : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRow [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 10] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 1)), _root_.ThreeSum1960614.Machine.Light.v 7, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 3)] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 2)), _root_.ThreeSum1960614.Machine.Light.v 7, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 3)] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pFlag [_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 10), _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 12)), _root_.ThreeSum1960614.Machine.Light.v 8] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pFlag [_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 10), _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 13)), _root_.ThreeSum1960614.Machine.Light.v 8] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 15))))))))







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightSourceRowFlag

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete coordinate pass over a compact downset

For each stored cardinality the fixed procedure constructs its layer of
masks, then runs the compact-cell update on that layer. Only the compact
downset and polynomial workspace are allocated; the program never visits
all integers below `2^L`. The source table remains unchanged throughout
the pass.
-/

namespace ThreeSum.LightZetaPass
open _root_.ThreeSum.LightZetaPass


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







def roundBody (pEnumSetup pBatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnumSetup [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBatch [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6] 9))

/-- Arguments: width, cutoff, coordinate, source, destination,
mask workspace, polynomial workspace. -/
def body (pEnumSetup pBatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 7 (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass.roundBody pEnumSetup pBatch)





def Inv {L : ℕ} (μ : ℕ → ℤ) (cut src dst maskBase work : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [L,cut,a.val,src,dst,maskBase,work,j,n,r],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut) ∧
    _root_.ThreeSum.LightZetaCell.TableAt μ' dst cut (_root_.ThreeSum.LightZetaPass.stageValues μ dst j a f)











end ThreeSum.LightZetaPass

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes
open _root_.ThreeSum.LocalMaskHashes


open _root_.Finset
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {h L k : ℕ}

def coeff (b : Bool) (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) : ℕ → ℕ :=
  _root_.ThreeSum.OneHotMask.extend (fun i => (w (i,b)).val)



def leftCode (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k i : ℕ) : ℕ :=
  _root_.ThreeSum.LightHashHistogram.code L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum.LocalMaskGraph.maskAt L k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff false w) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff true w) i

def rightCode (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k i : ℕ) : ℕ :=
  _root_.ThreeSum.LightHashHistogram.code L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum.LocalMaskGraph.maskAt L k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff true w) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff false w) i



















end ThreeSum.LocalMaskHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales
open _root_.ThreeSum.MassScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def wantedNumerator (n : ℕ) : ℕ :=
  9 * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ^ 2 * _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n

def rawTripleBound (n : ℕ) : ℕ := 3 * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ^ 2 * _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ^ 3

def falseNumerator (k n : ℕ) : ℕ :=
  _root_.ThreeSum.Scales.candidateCount n * _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n

















noncomputable section

def wantedMajorant (n : ℕ) : ℝ := (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n

def falseMajorant (k n : ℕ) : ℝ := (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n































end
end ThreeSum.MassScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A physical global-record index decodes to the original occurrence and mask rows -/

namespace ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.OutputDecodeRecords


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def layerCount (h : ℕ) : ℕ := _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h
def localCount (h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h

theorem layerCount_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h := Nat.choose_pos (by omega)
theorem schedule_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize _root_.ThreeSum.LocalHashMoments.scheduleLength
  positivity



def blockDefault (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.OutputBlock h :=
  (⟨0,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h⟩,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h ⟨0,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h⟩)

def outputDefault (h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J := fun _ => _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h



def localIndex (h J k j : ℕ) : ℕ := (_root_.ThreeSum.OutputDecodeOrder.indices (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h) J k).getD j 0
def occurrenceIndex (h J k j : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localIndex h J k j/_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h
def maskIndex (h J k j : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localIndex h J k j%_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h









theorem globalRecords_length' (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).length=_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords_length]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount,mul_pow]











theorem original_global_key {h J k : ℕ} (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J).getD k 0 =
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys_eq_map]
  exact _root_.List.getD_map_of_lt _ (by rwa [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.globalRecords_length']) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J) 0

end ThreeSum.OutputDecodeRecords

end ThreeSum1960614.Machine


