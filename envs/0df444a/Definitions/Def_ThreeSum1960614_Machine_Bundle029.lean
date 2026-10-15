-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle029
-- name    : ThreeSum1960614_Machine_Bundle029
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:16:57.151053+00:00
-- url     : https://prove2.me/theorems/27363a40-4a25-4f39-9729-cd524cc51322
-- title:
--   Shared source-bank catalogs and physical suffix-query lookup
-- statement:
--   This library defines the complete interfaces for selecting original source bands, constructing the shared occurrence catalog, sorting physical lookup keys, and querying retained suffix boxes. Source selection reads the stored band, stage-bank, and cover headers and materializes the fifteen controls needed by a wanted query. Its reads precede its writes. For original source lengths $N_B,N_C$, band size $g$, local size $h$, block count $J$, and output base $b$, the source-bank constructor builds one occurrence table and both retained source-stage families for each common padded band and occurrence. Its header records the bank base, count, stride, next free address, and occurrence-row pointer.
--
--   A sorted catalog packs the physical prefix masks and original catalog index into integer keys, preserving multiplicities and payload pointers. The query recovers its catalog position through an actual sorted lookup and invokes the stored suffix-box program. Finite-input records connect these operations to the normalized original arrays and the constructed wanted output. The library also defines the shared-construction cost quantities and a recursive finite coloring search that reuses a six-cell parameter row and skips later calls once an accepting color is found.
--
--   These interfaces support reuse across many wanted queries without reconstructing histograms or source transforms. Their role in the deterministic integer 3SUM proof is to expose actual packed storage, query access, and compositional color calls; the required execution and resource bounds are proved separately.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSourceSelect.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandBankBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceFiniteInputs.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorWantedHeader.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSortedCatalog.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandBanks.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogIndex.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandBanksProgram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogQuery.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandHost.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceBandBanksCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightColorScan.lean

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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.ColorScan
end ThreeSum.ColorScan
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightColorScan
end ThreeSum.LightColorScan
namespace ThreeSum.LightEncodedColorWantedHeader
end ThreeSum.LightEncodedColorWantedHeader
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogIndex
end ThreeSum.LightReportingCatalogIndex
namespace ThreeSum.LightReportingCatalogQuery
end ThreeSum.LightReportingCatalogQuery
namespace ThreeSum.LightReportingSortedCatalog
end ThreeSum.LightReportingSortedCatalog
namespace ThreeSum.LightReportingSourceSelect
end ThreeSum.LightReportingSourceSelect
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSourceBandBankBatch
end ThreeSum.LightSourceBandBankBatch
namespace ThreeSum.LightSourceBandBanks
end ThreeSum.LightSourceBandBanks
namespace ThreeSum.LightSourceBandBanksProgram
end ThreeSum.LightSourceBandBanksProgram
namespace ThreeSum.LightSourceBandHost
end ThreeSum.LightSourceBandHost
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
namespace ThreeSum.SourceBandBankData
end ThreeSum.SourceBandBankData
namespace ThreeSum.SourceBandBanksCosts
end ThreeSum.SourceBandBanksCosts
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.ColorScan
end ThreeSum1960614.Machine.ThreeSum.ColorScan
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightColorScan
end ThreeSum1960614.Machine.ThreeSum.LightColorScan
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedHeader
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedHeader
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSourceSelect
end ThreeSum1960614.Machine.ThreeSum.LightReportingSourceSelect
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankBatch
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanksProgram
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanksProgram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
end ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
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

/-!
# Actual constant-time selection of both independent source bands

The procedure reads the retained band, stage-bank and cover headers. It
materializes the fifteen controls consumed by wanted reporting, including
physical bucket pointers and the shared occurrence row, without scanning
any source or reconstructing a transform. All reads precede all writes.
-/

namespace ThreeSum.LightReportingSourceSelect
open _root_.ThreeSum.LightReportingSourceSelect


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

/-- Pair header, source-bank header, cover, original B/C bases, independent
B/C band indices, decoded occurrence code, J, and the fifteen-cell output. -/
def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 15))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 16))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 17))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 21))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 27 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 13))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 28 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 13))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 27))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 30 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 28))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 31 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 8)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 32 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 12)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 33 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 13)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 34 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 14)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 35 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 15)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 25)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 26)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 19)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 20)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 23)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 5)) (_root_.ThreeSum1960614.Machine.Light.v 24)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 6)) (_root_.ThreeSum1960614.Machine.Light.v 18)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 7)) (_root_.ThreeSum1960614.Machine.Light.v 22)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 8)) (_root_.ThreeSum1960614.Machine.Light.v 29)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 9)) (_root_.ThreeSum1960614.Machine.Light.v 30)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 10)) (_root_.ThreeSum1960614.Machine.Light.v 31)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 11)) (_root_.ThreeSum1960614.Machine.Light.v 32)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 12)) (_root_.ThreeSum1960614.Machine.Light.v 33)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 13)) (_root_.ThreeSum1960614.Machine.Light.v 34)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 14)) (_root_.ThreeSum1960614.Machine.Light.v 35)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 9)))))))))))))))))))))))))))))))))))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSourceSelect.body]





end ThreeSum.LightReportingSourceSelect

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual source-bank catalog loop over common padded band indices -/

namespace ThreeSum.LightSourceBandBankBatch
open _root_.ThreeSum.LightSourceBandBankBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def body (pStep : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 18 (_root_.ThreeSum1960614.Machine.Light.v 16) (
    _root_.ThreeSum1960614.Machine.Light.Stmt.call pStep [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 2,_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4,_root_.ThreeSum1960614.Machine.Light.v 5,_root_.ThreeSum1960614.Machine.Light.v 6,_root_.ThreeSum1960614.Machine.Light.v 7,_root_.ThreeSum1960614.Machine.Light.v 8,_root_.ThreeSum1960614.Machine.Light.v 9,_root_.ThreeSum1960614.Machine.Light.v 10,_root_.ThreeSum1960614.Machine.Light.v 11,_root_.ThreeSum1960614.Machine.Light.v 12,
      ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 17))),_root_.ThreeSum1960614.Machine.Light.v 14,_root_.ThreeSum1960614.Machine.Light.v 15,_root_.ThreeSum1960614.Machine.Light.v 18] 19)

def time (NL NR g h J cut : ℕ) : ℕ :=
  _root_.ThreeSum.SourceBandPairSlices.count NL NR g*(_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.time h J cut+200)+20

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pStep : ℕ
  step : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.Procs P pStep
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankBatch.body pStep)

def Inv (μ : ℕ → ℤ) (fL fR : ℕ → ℤ)
    (pair NL NR g p h J cut occ maps candidates histL histR base : ℕ) (shift : ℤ)
    (i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,occ,maps,candidates,
      histL,histR,pair,base,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J,
      _root_.ThreeSum.SourceBandPairSlices.count NL NR g,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut,i,r],ν⟩ ∧
    (∀ j < i, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.At ν fL fR base NL NR g h J cut (p : ℤ) shift j) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightSourceBandBankBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs
open _root_.ThreeSum.SourceFiniteInputs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule

def maps (free h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps (_root_.ThreeSum.LightLocalCoverInit.base free) h
def candidates (free h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates (_root_.ThreeSum.LightLocalCoverInit.base free) h
def leftCounts (free h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 (_root_.ThreeSum.LightLocalCoverInit.base free) h
def rightCounts (free h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 (_root_.ThreeSum.LightLocalCoverInit.base free) h

















end ThreeSum.SourceFiniteInputs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Recover the wanted-header address from the retained cover controls -/

namespace ThreeSum.LightEncodedColorWantedHeader
open _root_.ThreeSum.LightEncodedColorWantedHeader


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Cover header, block count, and original incidence count. -/
def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 18)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 9 (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 6))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 2))))))))))))











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightEncodedColorWantedHeader

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual packed-key construction and sorted catalog index

The powers table supplies the physical mask radix. A linear pass retains the
original catalog index as a low digit, and the benchmark's verified merge
sort orders these records without changing their multiplicity or payload.
-/

namespace ThreeSum.LightReportingSortedCatalog
open _root_.ThreeSum.LightReportingSortedCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def body (pPowers pPack pSort : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 5, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPack [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 4] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSort [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 0))))

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys.body,_root_.ThreeSum1960614.Machine.Light.sortBody 2 3 4 5,_root_.ThreeSum1960614.Machine.Light.halfBody,_root_.ThreeSum1960614.Machine.Light.mergeBody,_root_.ThreeSum1960614.Machine.Light.copyBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog.body 0 1 2]











end ThreeSum.LightReportingSortedCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# One occurrence catalog reused across all original source bands

The physical B/C band counts determine the loop length. A single radix
decoder loop constructs the occurrence rows. The bank loop then selects
retained histograms and builds exactly two families per common band and
occurrence. The result header stores the first bank base, band count, band
stride, next free address, and occurrence-row pointer.
-/

namespace ThreeSum.LightSourceBandBanks
open _root_.ThreeSum.LightSourceBandBanks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
open _root_.ThreeSum.SourceBandBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData

set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

def afterCountBody (pRows pBanks : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 5))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 19) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRows [_root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 20] 21) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 19)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 18)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 17)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 20)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBanks [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 17] 21) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 20)))))))))))

def body (pRows pBanks : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.k 3)))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.afterCountBody pRows pBanks)))

def afterTime (NL NR g h J cut : ℕ) : ℕ :=
  _root_.ThreeSum.LightSourceOccurrenceArray.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) J+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankBatch.time NL NR g h J cut+1000

def time (NL NR g h J cut : ℕ) : ℕ :=
  _root_.ThreeSum.LightSourceOccurrenceArray.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) J+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankBatch.time NL NR g h J cut+1200

def space (base NL NR g h J cut : ℕ) : ℕ :=
  max (_root_.ThreeSum.LightOutputDecodeDigits.space (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NL NR g h J cut) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J))
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut)

def word (NL NR h J : ℕ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.word NL NR h J)
    (_root_.ThreeSum.LightOutputDecodeDigits.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) J)

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pRows : ℕ
  pDigits : ℕ
  pDivide : ℕ
  pBanks : ℕ
  rows : P[pRows]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray.body pDigits)
  digits : P[pDigits]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body
  banks : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankBatch.Procs P pBanks
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.body pRows pBanks)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceBandBanks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete actual suffix catalog with a sorted physical lookup index

The returned header and both array addresses are obtained from the previous
actual constructor. The program then constructs the sorted packed index,
retaining every original box pointer and source/table cell.
-/

namespace ThreeSum.LightReportingCatalogIndex
open _root_.ThreeSum.LightReportingCatalogIndex


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def body (pCatalog pIndex : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCatalog [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19] 21) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 21))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 21) (_root_.ThreeSum1960614.Machine.Light.v 14))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 23)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 21) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pIndex [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 19] 26) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 21))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog.program ++
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.body 43 50]

def time (h J k boxCut : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.time h J k boxCut+
  _root_.ThreeSum.LightReportingSortedCatalog.time (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+250



end ThreeSum.LightReportingCatalogIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Closed program for one shared occurrence table and all original source banks -/

namespace ThreeSum.LightSourceBandBanksProgram
open _root_.ThreeSum.LightSourceBandBanksProgram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchProgram.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.body 43 42,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankBatch.body 44,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray.body 47,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.body 48,_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.body 46 45]









end ThreeSum.LightSourceBandBanksProgram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual indexed suffix-box query with exact original raw-count semantics

The machine recovers the complete-catalog index from the two physical prefix
masks, reads its stored box pointer, and executes the suffix-local sparse
query. The original prefix is used only to state and prove its specification;
neither a catalog position nor a table pointer is supplied to this machine.
-/

namespace ThreeSum.LightReportingCatalogQuery
open _root_.ThreeSum.LightReportingCatalogQuery


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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pLookup pQuery : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLookup [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 19] 20) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 20)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pQuery [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19] 0)))

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost.program ++
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.body 3 34]

def time (h J k t : ℕ) : ℕ :=
  _root_.ThreeSum.LightReportingCatalogLookup.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+
    _root_.ThreeSum.LightReportingSuffixQueryHost.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+100





end ThreeSum.LightReportingCatalogQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original normalized source arrays to the complete shared source-bank host

The first call reads physical normalized headers and the selected offset,
and constructs the retained histograms and original-position buckets once.
The second call constructs one occurrence table and all common-band source
banks. The complete host assumes no precomputed source histogram or stage.
-/

namespace ThreeSum.LightSourceBandHost
open _root_.ThreeSum.LightSourceBandHost


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

def occurrenceBase (base NL NR g h J : ℕ) : ℕ :=
  _root_.ThreeSum.SourceBandPairData.next base NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)

def bankHeader (base NL NR g h J : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase base NL NR g h J+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*J

def finish (base NL NR g h J cut : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader base NL NR g h J) NL NR g h J cut

def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (_root_.ThreeSum.LightSourceBandPair.space base NL NR g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) U D)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader base NL NR g h J) NL NR g h J cut)

def word (NL NR g p h J U D : ℕ) : ℕ :=
  max (_root_.ThreeSum.LightSourceBandPair.word NL NR g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) U D)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.word NL NR h J)

def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  _root_.ThreeSum.LightSourceBandPair.time NL NR g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) U D+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.time NL NR g h J cut+500

/-- J,L,h,local prime/cap,cut,modulus,cover arrays, original source value and
endpoint pointers,g,selected original prime,offset cell,free pointer,and
the ordinary compact-capacity/occurrence-count/schedule-size/band-stride controls. -/
def body (pPair pBanks : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPair [_root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18] 23) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 20) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBanks [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22] 25) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 25)))))

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pPair : ℕ
  pBanks : ℕ
  pair : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandPair.Procs P pPair
  banks : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBanks.Procs P pBanks
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.body pPair pBanks)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightSourceBandHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts
open _root_.ThreeSum.SharedReportingCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000


def blocks (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)
def localWidth (n : ℕ) : ℕ := 464*_root_.ThreeSum.SharedReportingCosts.half n
def width (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n
def localCount (n : ℕ) : ℕ := _root_.ThreeSum.LightReportingPrefixArrays.localCount (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) (_root_.ThreeSum.SharedReportingCosts.half n)

def overhead (n : ℕ) : ℕ :=
  100000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)^5+5000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n+1)^2*(_root_.ThreeSum.Scales.localSearch 257 n+1)+
    1200*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n+1)+2000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)+1050

def time (n k : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.time (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) k
  (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k)





















end ThreeSum.SharedReportingCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts
open _root_.ThreeSum.SourceBandBanksCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress























def storageFactor (n : ℕ) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+2*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+7)*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+3+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))







end ThreeSum.SourceBandBanksCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute the finite coloring search

The recursive driver reuses one six-cell parameter row and all subsequent
per-color scratch. Once a color accepts, later color calls are skipped.
This is a compositional execution theorem: the concrete selected-color
decision procedure must supply the explicit per-color call contract below.
It does not assert existence of that still-being-integrated solver.
-/

namespace ThreeSum.LightColorScan
open _root_.ThreeSum.LightColorScan


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.ColorScan
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorScan

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Source, length, persistent parameter header, reusable row, width, prefix length. -/
def body (pSelf pParameters pColor : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 5)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pParameters [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 3] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pColor [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 6)] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 9))))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pParameters : ℕ
  pDivide : ℕ
  pColor : ℕ
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorScan.body pMain pParameters pColor)
  parameters : P[pParameters]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorParameters.body pDivide)
  divide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



end ThreeSum.LightColorScan

end ThreeSum1960614.Machine


