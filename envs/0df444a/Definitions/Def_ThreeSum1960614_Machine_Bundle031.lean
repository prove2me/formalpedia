-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle031
-- name    : ThreeSum1960614_Machine_Bundle031
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:23:59.459705+00:00
-- url     : https://prove2.me/theorems/38c09e63-f2e9-4a2d-b5cf-1761d3763875
-- title:
--   Positive reporting masks, terminal completions, and retained source data
-- statement:
--   Fix natural microblock parameter $h$, block count $J$, a global output $q$, and a reporting depth $k$. The positive-child index list selects exactly those enumerated children whose original raw-prefix count is positive. For a list of parent prefixes, the partial accumulation is the ordered concatenation of the positive children of the first parents. The positive-expansion program constructs children, performs physical catalog lookup and exact queries, selects positive results, and gathers aligned left/right mask arrays; below its scratch boundary only those output intervals may change.
--
--   A terminal completion chooses exactly $(J-k)h$ of the remaining output coordinates. Its two full endpoint masks combine that subset and its complement with the fixed prefix endpoints. The associated pair mass is the product of the independently trimmed left and right original-input histogram counts. The terminal work expression sums the actual bucket-test costs over the unchanged enumeration order; each test charges physical selected pairs rather than the entire Cartesian product.
--
--   The bundle also defines a closed source-control host program and its literal procedure records, along with finite source-control costs. Its retained-data predicates record computed controls, contiguous original-index buckets and source-transform banks for the same normalized B/C lists. The normalization predicate exposes the three strictly increasing lists, equality of their represented value sets with the color classes, band tables, owner records, and flattened A-incidence arrays. A selected-color prime wrapper reads dimensions from those normalized headers; a result writer stores the compact eight-cell result after retained source data.
--
--   These definitions preserve original raw incidences and their multiplicities while turning abstract positive frontiers and terminal completions into physical mask arrays. They support exact cost charging and reuse of the same normalized witnesses throughout the complete deterministic integer 3SUM proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPositiveMasks.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceControlsHostProgram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostPositiveBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostTerminalChoices.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPositiveExpand.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingTerminalMasks.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostTerminalCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceControlCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceFiniteData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorPrime.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorResult.lean

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
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
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightEncodedColorPrime
end ThreeSum.LightEncodedColorPrime
namespace ThreeSum.LightEncodedColorResult
end ThreeSum.LightEncodedColorResult
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPositiveExpand
end ThreeSum.LightReportingPositiveExpand
namespace ThreeSum.LightReportingPositiveMasks
end ThreeSum.LightReportingPositiveMasks
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSourceControlsHostProgram
end ThreeSum.LightSourceControlsHostProgram
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPositiveBatch
end ThreeSum.ReportingHostPositiveBatch
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.ReportingHostTerminalCosts
end ThreeSum.ReportingHostTerminalCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceControlCosts
end ThreeSum.SourceControlCosts
namespace ThreeSum.SourceFiniteData
end ThreeSum.SourceFiniteData
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorResult
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorResult
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand
end ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram
end ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositiveBatch
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositiveBatch
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
end ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-! # Actual gathered positive mask arrays are the exact original next-prefix list -/

namespace ThreeSum.LightReportingPositiveMasks
open _root_.ThreeSum.LightReportingPositiveMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def selectedIndices {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k < J) : List ℕ :=
  _root_.ThreeSum.LightReportingFilter.selected (fun i => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt w.2.2 pre hk i)) (_root_.ThreeSum.LocalCoverBounds.groupSize h)





end ThreeSum.LightReportingPositiveMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Closed original source program with computed bank dimensions -/

namespace ThreeSum.LightSourceControlsHostProgram
open _root_.ThreeSum.LightSourceControlsHostProgram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHostProgram.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body 66 73,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.body 67 71 72,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildBody 68 69,_root_.ThreeSum1960614.Machine.Light.fillBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.rowBody 70,_root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody,
    _root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rankBody 72,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body,_root_.ThreeSum1960614.Machine.Light.log2Body,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsSpan.body 76,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.body 74 65 75 77,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.body 78 64]

def retainedProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩

def batchProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 42 := ⟨41,⟨0,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.retainedProcs,rfl⟩,rfl⟩

def banksProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 49 :=
  ⟨46,47,48,45,rfl,rfl,rfl,⟨44,⟨43,42,rfl,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.batchProcs,rfl⟩,rfl⟩,rfl⟩

def originalProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOriginal.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 50 :=
  ⟨51,56,⟨52,53,54,55,rfl,rfl,rfl,rfl,rfl⟩,⟨57,58,rfl,rfl,rfl⟩,rfl⟩

def setupProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandSetup.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 62 :=
  ⟨61,60,rfl,⟨59,⟨50,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.originalProcs,rfl⟩,rfl⟩,rfl⟩

def pairProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandPair.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 63 := ⟨62,55,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.setupProcs,rfl,rfl⟩

def sourceProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 64 := ⟨63,49,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.pairProcs,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.banksProcs,rfl⟩

def controlProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 78 :=
  ⟨74,65,75,77,76,66,67,68,69,70,71,72,73,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩

def programProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program 79 := ⟨78,64,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.controlProcs,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.sourceProcs,rfl⟩



end ThreeSum.LightSourceControlsHostProgram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact ordered accumulation for the actual multi-parent reporting loop -/

namespace ThreeSum.ReportingHostPositiveBatch
open _root_.ThreeSum.ReportingHostPositiveBatch


open _root_.Finset
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive

set_option linter.unusedSectionVars false



variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def parentAt {h : ℕ} (pres : List (List (Finset (Fin (464*h))))) (i : ℕ) := pres[i]?.getD []



def through {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pres : List (List (Finset (Fin (464*h))))) (hk : k < J) (j : ℕ) :
    List (List (Finset (Fin (464*h)))) :=
  (pres.take j).flatMap (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk)











end ThreeSum.ReportingHostPositiveBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite terminal completions in the actual mask enumerator's order

At any valid reporting prefix, a full balanced endpoint needs exactly
`(J-k)*h` of the remaining query coordinates. Enumerating that one layer
contains every retained completion and costs no more than the terminal
Boolean-cube allowance. The selected bucket pair masses sum to at most the
unchanged original raw prefix count.
-/

namespace ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.ReportingHostTerminalChoices


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def choices {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) : List (Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :=
  (_root_.ThreeSum.QueryCoordinates.missingSets (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)) ((J-k)*h)).map _root_.ThreeSum.BlockIndex.unindexSet

















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def pairMass {h J : ℕ} (P shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (464*h)))) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b (_root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ S)*
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P shift C c
      (_root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
        (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ S))



end ThreeSum.ReportingHostTerminalChoices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual parent expansion returning compact positive-prefix mask arrays

All child construction, physical catalog lookup, exact querying, positive
selection, and aligned mask gathering are executed by this closed program.
Only the actual positive output intervals may change below child scratch.
-/

namespace ThreeSum.LightReportingPositiveExpand
open _root_.ThreeSum.LightReportingPositiveExpand


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pExpand pGather : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pExpand [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25] 28) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pGather [_root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 28, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 27] 29) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 28))))

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program ++
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.body 46 48]

def time (h J k t : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time h J k t+_root_.ThreeSum.LightReportingGatherPair.time (_root_.ThreeSum.LocalCoverBounds.groupSize h)+120

abbrev KeptOutputs (μ ν : ℕ → ℤ) (bound outL outR n : ℕ) : Prop :=
  _root_.ThreeSum1960614.Machine.Light.SameOn (fun i => i < bound ∧ _root_.Light.Outside outL n i ∧ _root_.Light.Outside outR n i) μ ν





end ThreeSum.LightReportingPositiveExpand

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum.LightReportingTerminalMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def choiceAt {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k i : ℕ) : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k)[i]?.getD ∅

def leftAt {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (464*h)))) (i : ℕ) : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)) :=
  _root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt q k i

def rightAt {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (464*h)))) (i : ℕ) : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)) :=
  _root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
    (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt q k i)


def time (h J k : ℕ) : ℕ := _root_.ThreeSum.LightBlockChildren.time (J*(464*h)) ((J-k)*(2*h)) ((J-k)*h)
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.program









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}





end ThreeSum.LightReportingTerminalMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charging actual terminal scans to the original raw prefix mass

The actual independent bucket tester costs `240` per selected physical pair
plus `700` per terminal candidate. This file sums those exact verified costs
over the enumerator's unchanged order. It also proves conservation of raw
mass across the actual positive frontier at any partial depth.
-/

namespace ThreeSum.ReportingHostTerminalCosts
open _root_.ThreeSum.ReportingHostTerminalCosts


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000



variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def actualTestWork {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : ℕ :=
  ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).map fun S =>
    _root_.ThreeSum.LightReportingBucketTest.time
      (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i)) (fun j => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right j)) NL NR
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftResidue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ S))
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightResidue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
        (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ S)))
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ S))
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
        (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ S)))).sum









end ThreeSum.ReportingHostTerminalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts
open _root_.ThreeSum.SourceControlCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

def factor (h J : ℕ) : ℕ :=
  1400*(J*(464*h)+1)^2+20*J+
    14*Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+
    14*Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+2044











end ThreeSum.SourceControlCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained source banks for the concrete normalized finite arrays -/

namespace ThreeSum.SourceFiniteData
open _root_.ThreeSum.SourceFiniteData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA

structure Stored (μ : ℕ → ℤ) (base g p h J cut : ℕ) (B C : List ℤ) (shift r : ℤ) : Prop where
  returned : r=(_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base B.length C.length g h J cut : ℤ)
  controls : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values h J cut)
  buckets : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) B.length C.length g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift
  banks : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) B.length C.length g h J)
    B.length C.length g h J cut
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) B.length C.length g h J)
    (p : ℤ) shift





/-- The actual color/band payload with its normalized lists exposed, so
the owner records and finite source banks use the very same B/C witnesses. -/
def Normalized (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g)
    (originalA originalB originalC A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) (r : ℤ) : Prop :=
  let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC
  r=((_root_.ThreeSum.BandRawA.items A.length g rs).length : ℤ) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ tables
      (_root_.ThreeSum.BandPartition.family (fun i => A.getD i 0) A.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsA))
      (_root_.ThreeSum.BandPartition.family (fun i => B.getD i 0) B.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsB))
      (_root_.ThreeSum.BandPartition.family (fun i => C.getD i 0) C.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsC)) ∧
    _root_.ThreeSum1960614.Machine.Light.Seg μ rec (_root_.ThreeSum.BandCandidateRows.cells rs) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals (_root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g)
      (_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g) (fun i => A.getD i 0) (_root_.ThreeSum.BandRawA.items A.length g rs)





end ThreeSum.SourceFiniteData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Read the actual normalized band headers and construct one common prime -/

namespace ThreeSum.LightEncodedColorPrime
open _root_.ThreeSum.LightEncodedColorPrime


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000





def body (pCore : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 5))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 16)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 15))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 16)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCore [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10] 0))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.body 23]







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}



end ThreeSum.LightEncodedColorPrime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Write the compact selected-color result after all retained source data -/

namespace ThreeSum.LightEncodedColorResult
open _root_.ThreeSum.LightEncodedColorResult


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 3)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 5)) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 6)) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 7)) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 5)))))))))))











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightEncodedColorResult

end ThreeSum1960614.Machine


