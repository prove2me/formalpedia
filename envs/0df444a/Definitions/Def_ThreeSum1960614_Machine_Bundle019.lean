-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle019
-- name    : ThreeSum1960614_Machine_Bundle019
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:47:34.678658+00:00
-- url     : https://prove2.me/theorems/e6f97c09-eb63-4aff-a895-0a58f705bec8
-- title:
--   Global keys, retained zeta stages, and physical reporting batches
-- statement:
--   This library defines the next executable assembly layer: candidate-band rows, original-index band rows, truncated band-length queries, global output-key construction, header-driven owner tables, local cover-matrix construction, original-triple fallback scans, output-record decoding, terminal reporting batches, occurrence-vector arrays, and independent source trimming. It also specifies block source endpoint bounds and the retained compact zeta-stage tables.
--
--   For subset width $L$ and cardinality cutoff $c$, the zeta-stage constructor stores all $L+1$ stages in consecutive compact tables with stride $\operatorname{downsetCap}(L,c)$. Its loop invariant preserves every completed stage and restricts changes to the designated destination and scratch regions. The global-key builder constructs the actual output-mask layer, all local keys, and their full positional product from selected coefficient rows. A terminal batch reads the endpoint and independent-flag arrays for each retained candidate, evaluates the physical bucket-pair test, and accumulates a Boolean disjunction. Source trimming multiplies separately computed left and right Boolean flags across selected blocks. The finite fallback scans original triples using the explicit single-triple test.
--
--   These definitions retain physical indices and actual stored arrays throughout the deterministic integer 3SUM construction. They provide the exact program texts and loop invariants needed to charge successful reporting work by the sum of physical fiber costs and to reuse the finite library without enumeration assumptions.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostBlockBucketTest.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandCandidatesRow.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandRawARow.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandWeightedScoreSlice.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceBuild.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBoxStages.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightGlobalKeys.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightHeaderBands.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverMatrix.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOriginalTripleScan.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOutputDecodeStep.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingLeafBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceOccurrenceArray.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceTrim.lean

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.Range
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
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BoxStages
end ThreeSum.BoxStages
namespace ThreeSum.BruteTripleIndex
end ThreeSum.BruteTripleIndex
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBandCandidatesRow
end ThreeSum.LightBandCandidatesRow
namespace ThreeSum.LightBandRawARow
end ThreeSum.LightBandRawARow
namespace ThreeSum.LightBandWeightedScoreSlice
end ThreeSum.LightBandWeightedScoreSlice
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightBoxStages
end ThreeSum.LightBoxStages
namespace ThreeSum.LightGlobalKeys
end ThreeSum.LightGlobalKeys
namespace ThreeSum.LightHeaderBands
end ThreeSum.LightHeaderBands
namespace ThreeSum.LightLocalCoverMatrix
end ThreeSum.LightLocalCoverMatrix
namespace ThreeSum.LightOriginalTripleScan
end ThreeSum.LightOriginalTripleScan
namespace ThreeSum.LightOutputDecodeStep
end ThreeSum.LightOutputDecodeStep
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingLeafBatch
end ThreeSum.LightReportingLeafBatch
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.LightSourceOccurrenceArray
end ThreeSum.LightSourceOccurrenceArray
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightSourceTrim
end ThreeSum.LightSourceTrim
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostBlockBucketTest
end ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BoxStages
end ThreeSum1960614.Machine.ThreeSum.BoxStages
namespace ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
end ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow
end ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawARow
end ThreeSum1960614.Machine.ThreeSum.LightBandRawARow
namespace ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice
end ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightBoxStages
end ThreeSum1960614.Machine.ThreeSum.LightBoxStages
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
end ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightHeaderBands
end ThreeSum1960614.Machine.ThreeSum.LightHeaderBands
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan
end ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray
end ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
end ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Original endpoint semantics and exact Cartesian-test cost

The selected physical lengths are the original independently trimmed source
weights, after transport by the original-index enumeration. Thus the actual
tuple tester's pair charge is exactly the raw leaf weight.
-/

namespace ThreeSum.ReportingHostBlockBucketTest
open _root_.ThreeSum.ReportingHostBlockBucketTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def leftResidue {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) : ℕ :=
  _root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 1 (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o S)

def rightResidue {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) : ℕ :=
  _root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 1 (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S)

def leftFlag {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) : ℕ :=
  if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S then 1 else 0

def rightFlag {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) : ℕ :=
  if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o S then 1 else 0









end ThreeSum.ReportingHostBlockBucketTest

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One actual row of flagged band-owner records -/

namespace ThreeSum.LightBandCandidatesRow
open _root_.ThreeSum.LightBandCandidatesRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

def body (pCell : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 4 (_root_.ThreeSum1960614.Machine.Light.v 2) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCell [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 4) (_root_.ThreeSum1960614.Machine.Light.v 4))] 6)))



def Inv (μ : ℕ → ℤ) (mode : _root_.ThreeSum.BandCandidateRows.Mode) (f : ℕ → ℕ)
    (src dst n outer j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (x r : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [src,dst,n,outer,j,x,r],ν⟩ ∧
    (∀ k < j, _root_.ThreeSum1960614.Machine.Light.Seg ν (dst+4*k) (_root_.ThreeSum.BandCandidateRows.make mode outer k (f k)).cells) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (4*n)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst n outer U : ℕ} {f : ℕ → ℕ}



end ThreeSum.LightBandCandidatesRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# One actual A-band incidence row

Values are copied from the retained sorted A segment. Parallel arrays
receive the physical owner slot and the sorted-array coordinate.
-/

namespace ThreeSum.LightBandRawARow
open _root_.ThreeSum.LightBandRawARow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

/-- Source, value output, owner output, position output, length, owner, start. -/
def body (pCopy pFill : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCopy [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 4] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pFill [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 7) (_root_.ThreeSum1960614.Machine.Light.pass 8 (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 8)))))



def KeptOthers (μ ν : ℕ → ℤ) (values owners positions n : ℕ) : Prop :=
  _root_.ThreeSum1960614.Machine.Light.SameOn (fun a => _root_.Light.Outside values n a ∧ _root_.Light.Outside owners n a ∧ _root_.Light.Outside positions n a) μ ν

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src values owners positions n owner start : ℕ}





end ThreeSum.LightBandRawARow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Constant-time exact truncated band lengths for weighted-score calls -/

namespace ThreeSum.LightBandWeightedScoreSlice
open _root_.ThreeSum.LightBandWeightedScoreSlice


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 900000

def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.v 1)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 4)))))



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}







end ThreeSum.LightBandWeightedScoreSlice

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original block-source multiplicities from the costed constructor

These contracts specialize the actual histogram-and-gather program to the
unchanged block encoding. Endpoint bounds follow from the constructed
coefficient rows; they are not extra semantic assumptions about the encoder.
The original input enumeration explicitly retains individual incidences.
-/

namespace ThreeSum.LightBlockSourceBuild
open _root_.ThreeSum.LightBlockSourceBuild


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 1500000

def endpointBound (h J : ℕ) : ℕ := J*(464*h)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightBlockSourceBuild

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Building and retaining every compact prefix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for canonical
sparse-box queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightBoxStages
open _root_.ThreeSum.LightBoxStages


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BoxStages
open _root_.ThreeSum1960614.Machine.ThreeSum.BoxStages
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





def roundBody (pPass : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.call pPass [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 6,
    ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 5))),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 5))),_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4] 7

/-- Arguments: width, cutoff, base of all stage tables,
mask workspace, polynomial workspace. Stage zero initially holds `f`. -/
def body (pSize pPass : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSize [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 4] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.for 6 (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBoxStages.roundBody pPass)))



def Inv {L : ℕ} (μ : ℕ → ℤ) (cut base maskBase work : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [L,cut,base,maskBase,work,_root_.ThreeSum.SubsetAddress.downsetCap L cut,j,r],μ'⟩ ∧
    _root_.ThreeSum.LightBoxStages.StoredThrough μ' base cut f j ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase base ((L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut)

















end ThreeSum.LightBoxStages

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From selected coefficient rows to every original global output key

The fixed program constructs the output-mask layer, all signed local keys,
and the full positional product. Its output is the literal occurrence-aware
`GlobalKeyEnumeration.globalKeys` array. No input key or mask table is assumed.
-/

namespace ThreeSum.LightGlobalKeys
open _root_.ThreeSum.LightGlobalKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 600000
set_option maxRecDepth 10000

/-- L, layer cardinality, schedule length, radix, block count, coefficient rows,
layer size, and first free address. Sizes are read from the parameter initializer. -/
def body (pEnum pLocal pGlobal : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 10] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLocal [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pGlobal [_root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 10] 0))))))

def localCount (h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h
def scratch (free h : ℕ) : ℕ := free+_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h+_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h

def space (free h J : ℕ) : ℕ :=
  max (_root_.ThreeSum.LightLocalKeyRow.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h) (464*h) (_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h))
    (_root_.ThreeSum.LightRadixKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J)

def word (h J : ℕ) : ℕ := 2^(464*h+1)+
  _root_.ThreeSum.LightLocalKeys.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)+
  _root_.ThreeSum.LightRadixKeys.word (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) J+J+464

def time (h J : ℕ) : ℕ := _root_.ThreeSum.LightSubsetEnumerationSetup.time (464*h) (2*h)+
  _root_.ThreeSum.LightLocalKeys.time (464*h) (_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)+
  _root_.ThreeSum.LightRadixKeys.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J+200











structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pLayer : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pRows : ℕ
  pAffine : ℕ
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.body pEnum pLocal pGlobal)
  enum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body pPowers pLayer)
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  layer : P[pLayer]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pLayer)
  locals : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeys.Procs P pLocal
  globalProc : P[pGlobal]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.body pGlobal pRows)
  rows : P[pRows]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.body pAffine)
  affine : P[pAffine]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightGlobalKeys

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Running the owner tables directly from constructed class headers

This wrapper reads the three stored distinct-value lengths and band counts.
All six endpoint pointers and all three counts passed to the owner-table
program are therefore obtained by actual RAM expressions.
-/

namespace ThreeSum.LightHeaderBands
open _root_.ThreeSum.LightHeaderBands


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def At (μ : ℕ → ℤ) (header n : ℕ) (A : _root_.ThreeSum.BandEnumeration.Family) : Prop :=
  μ header = (n : ℤ) ∧ μ (header+1) = (A.size : ℤ) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ (header+2) (header+2+n) A

/-- Arguments: three endpoint-header addresses and output address. -/
def body (pEnumerate : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.call pEnumerate
    [((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 2)),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 0))),
      ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 2)),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 1))),
      ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 2)),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 2))),
      _root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1))),_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1))),_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1))),_root_.ThreeSum1960614.Machine.Light.v 3] 0



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pEnumerate : ℕ
  enumerate : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs P pEnumerate
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.body pEnumerate)









end ThreeSum.LightHeaderBands

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing every candidate coefficient, histogram, and cover-matrix row

One literal loop visits the radix candidates in increasing index order.
Temporary raw/residue buffers are reused. All candidate coefficient rows,
both histogram tables, and all Boolean matrix rows remain in memory.
-/

namespace ThreeSum.LightLocalCoverMatrix
open _root_.ThreeSum.LightLocalCoverMatrix


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

def body (pCandidate : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.for 14 (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCandidate [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0))), _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 1)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 1)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 16)), _root_.ThreeSum1960614.Machine.Light.v 13] 15)))



def Tables (μ : ℕ → ℤ) (L n p cap maps hist0 hist1 dst : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ j < N,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightDecode.Rows μ (maps+j*(2*L)) L p j ∧
    (∀ r < p,
      μ (hist0+j*p+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask (w0 j) (w1 j)) r n : ℤ) ∧
      μ (hist1+j*p+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask (w1 j) (w0 j)) r n : ℤ)) ∧
    (∀ r < p*p, μ (dst+j*(p*p)+r) = (_root_.ThreeSum.LightLocalCoverCandidate.entry L n p cap mask bits (w0 j) (w1 j) r : ℤ))

def Inv (μ : ℕ → ℤ) (L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work,i,r,p*p],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 i ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' maps

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCandidate : ℕ
  candidate : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs P pCandidate
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.body pCandidate)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightLocalCoverMatrix

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Execute the exact finite fallback scan over original triples -/

namespace ThreeSum.LightOriginalTripleScan
open _root_.ThreeSum.LightOriginalTripleScan


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BruteTripleIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def body (pSelf pRow : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 2)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRow [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan.body 2 0]

end ThreeSum.LightOriginalTripleScan

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# One actual output-record decoding step

A local record digit is split into its occurrence and layer indices by
the checked logarithmic quotient routine. The layer mask is read from the
existing table, both output cells are written, and the occurrence-only
source-bank code is updated. Every other cell below the scratch pointer
is preserved, so separate output rows can be filled in any order.
-/

namespace ThreeSum.LightOutputDecodeStep
open _root_.ThreeSum.LightOutputDecodeStep


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pDivide : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 8] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 9)))))))))





def KeptOthers (μ ν : ℕ → ℤ) (work outOcc outMask : ℕ) : Prop :=
  _root_.ThreeSum1960614.Machine.Light.SameOn (fun a => a < work ∧ a ≠ outOcc ∧ a ≠ outMask) μ ν



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {x T M masks acc power outOcc outMask work V U : ℕ} {f : ℕ → ℕ}









end ThreeSum.LightOutputDecodeStep

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal-candidate batch with a sum of physical pair charges

All endpoint and independent flag arrays are read from retained memory.
The recursion evaluates each candidate and retains a Boolean disjunction.
Its cost sums the actual leaf costs instead of multiplying a worst fiber
size by the number of candidates.
-/

namespace ThreeSum.LightReportingLeafBatch
open _root_.ThreeSum.LightReportingLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 2600000
set_option maxRecDepth 10000









/-- a, source and bucket pointers, source lengths, modulus, four retained
endpoint/flag arrays, candidate count, and scratch. -/
def body (pSelf pLeaf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 14)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 15] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLeaf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 15] 22) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 22))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0)))))))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.body 6 5]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingLeafBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual big-endian occurrence-vector array

The finite loop decodes each physical bank index once, using the verified
logarithmic quotient routine. Its contiguous rows contain exactly J radix
digits. The shared source catalog consumes these rows without supplying an
enumeration oracle or running a loop over output subsets.
-/

namespace ThreeSum.LightSourceOccurrenceArray
open _root_.ThreeSum.LightSourceOccurrenceArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pDigits : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 0) (
    _root_.ThreeSum1960614.Machine.Light.Stmt.call pDigits [_root_.ThreeSum1960614.Machine.Light.v 5,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 2,((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 1))),_root_.ThreeSum1960614.Machine.Light.v 4] 6)



def Inv (μ : ℕ → ℤ) (N J m dst work i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [N,J,m,dst,work,i,r],ν⟩ ∧
    (∀ j < i, ∀ s < J, ν (dst+j*J+s)=((_root_.ThreeSum.OutputDecodeOrder.indices m J j).getD s 0 : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceOccurrenceArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim
open _root_.ThreeSum.LightSourceTrim


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000





def roundBody (pRowFlag : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRowFlag [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 1)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 16)))), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 16))))) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 16))))) (_root_.ThreeSum1960614.Machine.Light.v 3)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 16))))) (_root_.ThreeSum1960614.Machine.Light.v 3)), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 11)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 1)))))))

/-- Arguments: block count, width, required row size, modulus, cap,
occurrence indices, selected-map coefficient rows, occurrence-to-candidate
indices, both candidate bucket tables, Boolean rows, two-cell row scratch,
remainder scratch, and two-cell final output. -/
def body (pRowFlag : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 16 (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.roundBody pRowFlag)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 15))))))



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pRowFlag : ℕ
  pRow : ℕ
  pEmod : ℕ
  pFlag : ℕ
  rowFlagDef : P[pRowFlag]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.body pRow pEmod pFlag)
  row : P[pRow]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.body
  emod : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody
  flag : P[pFlag]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.body
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.body pRowFlag)

def Inv (μ : ℕ → ℤ) (J L h p cap occ maps candidates histL histR bitBase rowOut work dst : ℕ)
    (sel candidate bits : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [J,L,h,p,cap,occ,maps,candidates,histL,histR,bitBase,rowOut,work,dst,
      _root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) j,
      _root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) j,j,r],ν⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.Kept μ ν rowOut

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightSourceTrim

end ThreeSum1960614.Machine


