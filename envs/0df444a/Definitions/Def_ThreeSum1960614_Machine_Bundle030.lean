-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle030
-- name    : ThreeSum1960614_Machine_Bundle030
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:19:01.039734+00:00
-- url     : https://prove2.me/theorems/0da765b3-2d2c-4bfd-b4a5-d9c0ff2fe6dd
-- title:
--   Positive-frontier expansion, source controls, and the finite color driver
-- statement:
--   This library defines programs for batching exact reporting counts, expanding a parent through a shared suffix catalog, and retaining the positive children in stable order. A candidate supplies its constructed prefix masks; physical sorted lookup selects its cached suffix box, and the sparse-query program writes its exact count. Positive compaction then records the selected child positions. The stored source and complete shared catalog are retained across these calls.
--
--   For block dimensions $h,J$ and stored local schedule controls, source-control initialization computes the occurrence count, compact downset capacity, and exact bank stride using explicit powering, downset-size, logarithm, and span-arithmetic routines. Three persistent control cells precede the full source host; scratch used to construct the capacity is subsequently reused. The color-driver assembly appends a six-cell decoder, scalar division helper, recursive short-circuit scan, and parameter-header reader to a supplied concrete color program. Threshold and switch cost interfaces retain their finite overheads. The positive-frontier data relate stable gathering to the recursively defined reporting order and raw-incidence charges.
--
--   The library supplies the executable plumbing that connects finite color search and exact source controls to the deterministic integer 3SUM reporter. Its definitions preserve the actual query order and multiplicity so later cost theorems can charge positive parents and terminal fibers precisely.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightDenseSetupCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandHostProgram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSwitchCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceControlLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightColorScanHost.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogLevel.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceControlsSpan.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogExpand.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceControls.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumColorDriver.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceControlsHost.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostPositive.lean

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
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
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
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightColorScanHost
end ThreeSum.LightColorScanHost
namespace ThreeSum.LightDenseSetupCosts
end ThreeSum.LightDenseSetupCosts
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogBatch
end ThreeSum.LightReportingCatalogBatch
namespace ThreeSum.LightReportingCatalogExpand
end ThreeSum.LightReportingCatalogExpand
namespace ThreeSum.LightReportingCatalogLevel
end ThreeSum.LightReportingCatalogLevel
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSourceBandHostProgram
end ThreeSum.LightSourceBandHostProgram
namespace ThreeSum.LightSourceControls
end ThreeSum.LightSourceControls
namespace ThreeSum.LightSourceControlsHost
end ThreeSum.LightSourceControlsHost
namespace ThreeSum.LightSourceControlsSpan
end ThreeSum.LightSourceControlsSpan
namespace ThreeSum.LightSwitchCosts
end ThreeSum.LightSwitchCosts
namespace ThreeSum.LightThreeSumColorDriver
end ThreeSum.LightThreeSumColorDriver
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceControlLayout
end ThreeSum.SourceControlLayout
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
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
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightColorScanHost
end ThreeSum1960614.Machine.ThreeSum.LightColorScanHost
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts
end ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandHostProgram
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandHostProgram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceControls
end ThreeSum1960614.Machine.ThreeSum.LightSourceControls
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost
end ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceControlsSpan
end ThreeSum1960614.Machine.ThreeSum.LightSourceControlsSpan
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts
end ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceControlLayout
end ThreeSum1960614.Machine.ThreeSum.SourceControlLayout
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Charge the actual threshold construction

One final aggregate score is covered by the existing executed arithmetic
budget. Computing the cap and storing its product adds only O(J) work.
This is a cost theorem for this concrete stage, not a full solver claim.
-/

namespace ThreeSum.LightDenseSetupCosts
open _root_.ThreeSum.LightDenseSetupCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000



def timeBudget (k n : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget k n+20*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+570



open _root_.Filter
open _root_.Real
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open scoped _root_.Topology

noncomputable section









end
end ThreeSum.LightDenseSetupCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual raw-count batching through the physical suffix-box catalog

Each candidate supplies only its two constructed prefix masks. A real sorted
lookup chooses its cached suffix box, and the actual sparse query stores the
original raw prefix count. The catalog is shared and preserved by all calls.
-/

namespace ThreeSum.LightReportingCatalogBatch
open _root_.ThreeSum.LightReportingCatalogBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
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

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def roundBody (pQuery : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 22)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.v 22)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pQuery [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21] 25) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 19) (_root_.ThreeSum1960614.Machine.Light.v 22)) (_root_.ThreeSum1960614.Machine.Light.v 25)))))

def body (pQuery : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.for 22 (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.roundBody pQuery)

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.body 35]

def time (h J k t n : ℕ) : ℕ := n*(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time h J k t+180)+30

def Inv (μ : ℕ → ℤ) (counts : ℕ → ℕ)
    (h J k t Qmask baseL baseR boxCut indexBase ptrBase inL inR n dst maskBase work j : ℕ)
    (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (a b r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,_root_.ThreeSum.LightBlockQuery.sourceCut h J,_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*h,k*h,
      _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*(464*h),_root_.ThreeSum.LightBlockQuery.residualSize h J k,Qmask,t,baseL,baseR,
      boxCut,indexBase,ptrBase,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,inL,inR,n,dst,maskBase,work,j,a,b,r],μ'⟩ ∧
    (∀ i < j, μ' (dst+i) = (counts i : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase dst n





end ThreeSum.LightReportingCatalogBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Closed original-array-to-shared-source-bank program -/

namespace ThreeSum.LightSourceBandHostProgram
open _root_.ThreeSum.LightSourceBandHostProgram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanksProgram.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOriginal.body 51 56,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.body 52 54,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.body 53,_root_.ThreeSum1960614.Machine.Light.emodBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody 55,_root_.ThreeSum1960614.Machine.Light.fillBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram.body 57 58,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.body 50,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.body 59,_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandSetup.body 61 60,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandPair.body 62 55,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.body 63 49]

















end ThreeSum.LightSourceBandHostProgram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform finite and exponent bounds for the actual switch controls -/

namespace ThreeSum.LightSwitchCosts
open _root_.ThreeSum.LightSwitchCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.Filter
open scoped _root_.Topology

def timeBudget (n : ℕ) : ℕ := 200*(_root_.ThreeSum.Scales.inputBits n+1)+100
















noncomputable section









end
end ThreeSum.LightSwitchCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Arithmetic dimensions of the original shared source bank -/

namespace ThreeSum.SourceControlLayout
open _root_.ThreeSum.SourceControlLayout


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress















def values (h J cut : ℕ) : List ℤ :=
  [_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut]

end ThreeSum.SourceControlLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Load the actual index width and run the entire coloring family -/

namespace ThreeSum.LightColorScanHost
open _root_.ThreeSum.LightColorScanHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pScan : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 81) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScan [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 0)))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pScan : ℕ
  scan : _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScan.Procs P pScan
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.body pScan)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



end ThreeSum.LightColorScanHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual shared-catalog queries followed by stable positive compaction -/

namespace ThreeSum.LightReportingCatalogLevel
open _root_.ThreeSum.LightReportingCatalogLevel


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
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

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pBatch pFilter : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBatch [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21] 23) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pFilter [_root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 22] 0))

def suffix : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.body 36 37]
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.program ++ _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.suffix

def time (h J k t n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time h J k t n+_root_.ThreeSum.LightReportingFilter.time n+100





end ThreeSum.LightReportingCatalogLevel

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual arithmetic computation of the exact source-bank span -/

namespace ThreeSum.LightSourceControlsSpan
open _root_.ThreeSum.LightSourceControlsSpan


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceControlLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

/-- J, total width, compact capacity, occurrence count, and the two
logarithms needed by the retained stage workspace. -/
def body (pMax : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMax [_root_.ThreeSum1960614.Machine.Light.v 7, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 2)] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMax [_root_.ThreeSum1960614.Machine.Light.v 8, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 5)] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMax [_root_.ThreeSum1960614.Machine.Light.v 9, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 5) (_root_.ThreeSum1960614.Machine.Light.v 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.k 4)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.v 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 10)))))))))

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceControlsSpan

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete parent expansion through an actual shared shrinking-suffix catalog

This program constructs every ordered child mask pair, locates its own cached
box through the physical sorted index, runs the exact original raw-count
query, and stably compacts positive child positions. It requires no supplied
per-child box addresses and retains the complete source/catalog storage.
-/

namespace ThreeSum.LightReportingCatalogExpand
open _root_.ThreeSum.LightReportingCatalogExpand


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

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pChildren pLevel : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pChildren [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9] 26) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLevel [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 23] 0))

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.program ++
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.body 0 45]

def time (h J k t : ℕ) : ℕ :=
  _root_.ThreeSum.LightBlockChildren.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (2*h) h+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.time h J (k+1) t (_root_.ThreeSum.LocalCoverBounds.groupSize h)+150





end ThreeSum.LightReportingCatalogExpand

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual occurrence count, compact capacity, and exact bank stride

Only the block dimensions and previously constructed local schedule controls
are supplied. Scalar powering, the compact downset-size program, two actual
logarithms, and exact span arithmetic construct all three source controls.
-/

namespace ThreeSum.LightSourceControls
open _root_.ThreeSum.LightSourceControls


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def spanWord (h J cut : ℕ) : ℕ :=
  _root_.ThreeSum.SourceControlLayout.word J (J*(464*h)) (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1))
    (Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1))

def word (h J cut : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord h J cut+(J*(464*h)+1)*2^(J*(464*h)+1)+(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1)^(J+1)+
    2*((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+2*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+J+464*h+_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+cut+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+J*(464*h)+50

def space (work h J : ℕ) : ℕ := work+_root_.ThreeSum.LightPascal.tableSize (J*(464*h))+(J*(464*h)+1)

def time (h J : ℕ) : ℕ :=
  _root_.ThreeSum.LightNatPower.time J+_root_.ThreeSum.LightDownsetSize.time (J*(464*h))+
    _root_.Light.log2Time ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+_root_.Light.log2Time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+2000

/-- J, local width, local prime, cutoff, schedule size, original local
prime power, three-cell destination, and polynomial scratch. -/
def body (pPower pDownset pLog pSpan : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPower [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 0] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDownset [_root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 7] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLog [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.k 1)] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLog [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 9) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.k 1)] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSpan [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 10)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 13)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 13)))))))))))

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pPower : ℕ
  pDownset : ℕ
  pLog : ℕ
  pSpan : ℕ
  pMax : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  pOffset : ℕ
  power : P[pPower]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body
  downset : P[pDownset]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset)
  setup : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body
  log : P[pLog]?=some _root_.ThreeSum1960614.Machine.Light.log2Body
  span : P[pSpan]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsSpan.body pMax)
  maximum : P[pMax]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax.body
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.body pPower pDownset pLog pSpan)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightSourceControls

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Close the actual color decoder and scan around a concrete color program

The supplied program stays at its original indices. Four actual procedures
are appended: the six-cell decoder, scalar division, recursive short-circuit
scan, and parameter-header reader. The resulting program can then be
relocated by the already verified general relocation theorem.
-/

namespace ThreeSum.LightThreeSumColorDriver
open _root_.ThreeSum.LightThreeSumColorDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

def extra (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightColorParameters.body (colorProgram.length+1),_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScan.body (colorProgram.length+2) colorProgram.length pColor,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.body (colorProgram.length+2)]

def program (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) : _root_.ThreeSum1960614.Machine.Light.Program := colorProgram++_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.extra colorProgram pColor



def procs (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.Procs (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program colorProgram pColor) (colorProgram.length+3) where
  pScan := colorProgram.length+2
  scan := {
    pParameters := colorProgram.length
    pDivide := colorProgram.length+1
    pColor := pColor
    main := by apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add; rfl
    parameters := by
      change (colorProgram++_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.extra colorProgram pColor)[colorProgram.length+0]?=_
      apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
      rfl
    divide := by apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add; rfl }
  main := by apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add; rfl



end ThreeSum.LightThreeSumColorDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Shared source construction with its size controls computed by the program

Three persistent control cells precede the complete source host. The
capacity initializer's polynomial scratch is reclaimed by the source host.
Occurrence count, compact capacity, and bank stride are read from the
constructed cells or the initializer result, never supplied as arguments.
-/

namespace ThreeSum.LightSourceControlsHost
open _root_.ThreeSum.LightSourceControlsHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000



def finish (base NL NR g h J cut : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.finish (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g h J cut

def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.space (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) h J)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.space (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g p h J cut U D)

def word (NL NR g p h J cut U D : ℕ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word h J cut) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.word NL NR g p h J U D)

def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.time h J+_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.time NL NR g p h J cut U D+500

/-- The source host's original inputs and local schedule size; none of
the occurrence count, compact capacity, or bank span is an input. -/
def body (pControls pSource : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.k 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pControls [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 20] 21) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 18))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSource [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 21] 24) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 24)))))))

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pControls : ℕ
  pSource : ℕ
  controls : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.Procs P pControls
  source : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.Procs P pSource
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.body pControls pSource)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightSourceControlsHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive
open _root_.ThreeSum.ReportingHostPositive


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
open scoped _root_.BigOperators

set_option linter.unusedSectionVars false







variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def positiveChildren {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k < J) :
    List (List (Finset (Fin (464*h)))) :=
  (_root_.ThreeSum.LightReportingFilter.selected (fun i => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt w.2.2 pre hk i))
    (_root_.ThreeSum.LocalCoverBounds.groupSize h)).map (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt w.2.2 pre hk)













end ThreeSum.ReportingHostPositive

end ThreeSum1960614.Machine


