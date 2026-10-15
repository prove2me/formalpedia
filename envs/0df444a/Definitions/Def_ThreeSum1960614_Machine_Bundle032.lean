-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle032
-- name    : ThreeSum1960614_Machine_Bundle032
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:41:40.611978+00:00
-- url     : https://prove2.me/theorems/ec88cf2c-04e4-45f8-80dd-c4dabd062071
-- title:
--   Physical frontier layout and terminal reporting contracts
-- statement:
--   The frontier-step program reads each stored parent mask pair, executes the complete positive expansion and appends its positive children to aligned output arrays. For a finite raw-incidence set $I$ and wanted label $w$, write $m_0$ for its raw-prefix mass at depth zero and $G(h)$ for the local child count. The allocated frontier capacity is
--
--   $$\operatorname{capacity}(I,w)=(m_0+1)G(h).$$
--
--   A slot contract stores the exact frontier length, residual query mask, and left/right prefix-mask arrays at each depth. Terminal interfaces define full endpoint hashes and independent trim flags in the exact completion order, together with the literal batch cost and original-value hit predicate. The prepared-terminal program builds these endpoints and flags and scans only their selected physical bucket products.
--
--   The finite source host has explicit original-size time, space, finish-address and word budgets. Its normalized-data contract retains the normalized color arrays, band headers, owner records and actual flattened A-incidence count. The source constructor reads its destination and every cover pointer from previously written headers, computes the J-fold modulus, and invokes the complete shared source host.
--
--   The dense-stop mass of a visited wanted-label list is the sum of its root raw masses; this definition supports cumulative stopping before proportional traversal. For the level loop, a catalog record contains switch parameter, box cutoff and box/index/pointer bases. Its storage contracts specify sorted prefix codes, exact box pointers, local transformed box values, and complete source transforms. Separate bounds place every retained array below the ownership boundary, while scratch constraints cover enumeration masks, Pascal/power tables, remainder computation, lookup magnitudes and all queried values.
--
--   These definitions are the concrete memory and resource interfaces used by the complete deterministic integer 3SUM reporting loop. The stored catalog supplies data for an actual query program rather than assuming a query oracle, and the physical frontier retains the original combinatorial order.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingFrontierStep.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceFinitePrepared.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostFrontierLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostTerminalBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceFiniteCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/DenseGuard.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorNormalizedData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorSources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingTerminalPrepared.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostLevelData.lean

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
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
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
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
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.DenseGuard
end ThreeSum.DenseGuard
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightEncodedColorSources
end ThreeSum.LightEncodedColorSources
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingFrontierStep
end ThreeSum.LightReportingFrontierStep
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightReportingTerminalPrepared
end ThreeSum.LightReportingTerminalPrepared
namespace ThreeSum.LightSourceFinitePrepared
end ThreeSum.LightSourceFinitePrepared
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostTerminalBatch
end ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.SourceFiniteCosts
end ThreeSum.SourceFiniteCosts
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
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
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.DenseGuard
end ThreeSum1960614.Machine.ThreeSum.DenseGuard
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep
end ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand
end ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPrepared
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPrepared
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFinitePrepared
end ThreeSum1960614.Machine.ThreeSum.LightSourceFinitePrepared
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
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
# Actual multi-parent reporting frontier step

The loop reads each stored parent mask pair, executes the complete positive
expansion, and appends only the returned positive masks to aligned output
arrays. The accumulated output is the literal ordered concatenation used by
the original raw-incidence reporting frontier.
-/

namespace ThreeSum.LightReportingFrontierStep
open _root_.ThreeSum.LightReportingFrontierStep


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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositiveBatch
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand

set_option maxHeartbeats 3500000
set_option maxRecDepth 10000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def roundBody (pExpand : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 31 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 24) (_root_.ThreeSum1960614.Machine.Light.v 30)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 32 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 25) (_root_.ThreeSum1960614.Machine.Light.v 30)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pExpand [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 31, _root_.ThreeSum1960614.Machine.Light.v 32, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 27) (_root_.ThreeSum1960614.Machine.Light.v 29), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 28) (_root_.ThreeSum1960614.Machine.Light.v 29)] 33) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 29) (_root_.ThreeSum1960614.Machine.Light.v 33))))))

def body (pExpand : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 30 (_root_.ThreeSum1960614.Machine.Light.v 26) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.roundBody pExpand)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 29))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.body 49]
def time (h J k t n : ℕ) : ℕ := n*(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.time h J k t+200)+100

def Inv {h J k : ℕ} (μ : ℕ → ℤ) (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pres : List (List (Finset (Fin (464*h))))) (hk : k < J)
    (t baseL baseR boxCut indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work j : ℕ)
    (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (a b r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame (([_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,h,_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hk⟩,_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)),
      masks,dstL,dstR,work,_root_.ThreeSum.LightBlockQuery.sourceCut h J,_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1),(k+1)*h,_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1),
      t,baseL,baseR,boxCut,indexBase,ptrBase,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1),_root_.ThreeSum.LocalCoverBounds.groupSize h,dst,selected,maskBase,(k+1)*(464*h),
      inL,inR,pres.length,outL,outR,(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositiveBatch.through I w pres hk j).length,j] : List ℕ).map
      (fun n => (n : ℤ)) ++ [a,b,r]),ν⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.SegN ν outL ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositiveBatch.through I w pres hk j).map fun pre => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))) ∧
    _root_.ThreeSum1960614.Machine.Light.SegN ν outR ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositiveBatch.through I w pres hk j).map fun pre =>
      _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.KeptOutputs μ ν masks outL outR (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositiveBatch.through I w pres hk j).length





end ThreeSum.LightReportingFrontierStep

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual source construction from the retained prepared outputs -/

namespace ThreeSum.LightSourceFinitePrepared
open _root_.ThreeSum.LightSourceFinitePrepared


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs

def args (free base bv be cv ce g p h J cut len : ℕ) : List ℤ :=
  [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.maps free h,_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.candidates free h,_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.leftCounts free h,_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.rightCounts free h,
    bv,be,cv,ce,g,p,_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free h J len+3,base,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightSourceFinitePrepared

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.ReportingHostFrontierLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
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
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false




















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

abbrev rootMass {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w 0 []



def capacity {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w+1)*_root_.ThreeSum.LocalCoverBounds.groupSize h













def leftMasks {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (k : ℕ) : List ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).map fun pre => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))

def rightMasks {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (k : ℕ) : List ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).map fun pre =>
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))








structure At {h J : ℕ} (μ : ℕ→ℤ) (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (base cap k : ℕ) : Prop where
  count : μ (_root_.ThreeSum.ReportingHostFrontierLayout.slot base cap k)=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length : ℤ)
  query : μ (_root_.ThreeSum.ReportingHostFrontierLayout.slot base cap k+1)=(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) : ℤ)
  left : _root_.ThreeSum1960614.Machine.Light.SegN μ (_root_.ThreeSum.ReportingHostFrontierLayout.left base cap k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.leftMasks I w k)
  right : _root_.ThreeSum1960614.Machine.Light.SegN μ (_root_.ThreeSum.ReportingHostFrontierLayout.right base cap k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rightMasks I w k)



end ThreeSum.ReportingHostFrontierLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-encoding semantics and cost of the executed terminal batch

This is the specialization of the actual seven-procedure batch to the full
endpoint masks emitted at a valid partial prefix. The precise ordered
candidate sum is charged to raw prefix mass plus the terminal cube term.
-/

namespace ThreeSum.ReportingHostTerminalBatch
open _root_.ThreeSum.ReportingHostTerminalBatch


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
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open scoped _root_.BigOperators

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

def endpointsLeft {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : ℕ→ℤ :=
  fun i => _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt q k pre i)
def endpointsRight {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : ℕ→ℤ :=
  fun i => _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt q k pre i)
def flagsLeft {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : ℕ→ℕ :=
  fun i => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt q k pre i)
def flagsRight {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : ℕ→ℕ :=
  fun i => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt q k pre i)

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : ℕ :=
  _root_.ThreeSum.LightReportingLeafBatch.time
    (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i)) (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right i))
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.flagsLeft q k pre) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.flagsRight q k pre) NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.endpointsLeft q k pre) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.endpointsRight q k pre) (_root_.ThreeSum.LightReportingTerminalMasks.count h J k)

def Hit {h J : ℕ} (a : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : Prop :=
  _root_.ThreeSum.LightReportingLeafBatch.Hit a (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.endpointsLeft q k pre) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.endpointsRight q k pre) left right
    (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i)) (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right i))
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.flagsLeft q k pre) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.flagsRight q k pre) NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum.LightReportingTerminalMasks.count h J k)





variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







end ThreeSum.ReportingHostTerminalBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts
open _root_.ThreeSum.SourceFiniteCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

def time (n p U D : ℕ) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.factor (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)+
    2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+5705)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+4859

def space (base n p U D : ℕ) : ℕ :=
  base+(29+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor n+
      (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)^2+(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1))*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+
    Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n+1)+
    max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19

def finish (base n : ℕ) : ℕ :=
  base+(29+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor n)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+17

def word (n p U D : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.word n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
    (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U D











end ThreeSum.SourceFiniteCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Sound cumulative dense stopping on visited wanted labels

Distinct wanted labels have disjoint raw-incidence fibers. Therefore any
visited prefix already exceeding the exact representation-times-false-score
threshold certifies an original equation, before proportional traversal.
-/

namespace ThreeSum.DenseGuard
open _root_.ThreeSum.DenseGuard


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def mass {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (visited : List (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)) : ℕ := (visited.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I)).sum













end ThreeSum.DenseGuard

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum.EncodedColorNormalizedData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout

def incidences (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List ℤ :=
  _root_.ThreeSum.BandRawA.values (fun j => A.getD j 0)
    (_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)) (x : Fin n → ℤ) : Prop :=
  _root_.ThreeSum1960614.Machine.Light.Seg μ free (_root_.ThreeSum.EncodedColorLayout.normalizedHeads free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) ∧
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    μ (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))=((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized μ (_root_.ThreeSum.EncodedColorLayout.av free n) (_root_.ThreeSum.EncodedColorLayout.ae free n) (_root_.ThreeSum.EncodedColorLayout.bv free n) (_root_.ThreeSum.EncodedColorLayout.be free n) (_root_.ThreeSum.EncodedColorLayout.cv free n) (_root_.ThreeSum.EncodedColorLayout.ce free n)
      (_root_.ThreeSum.EncodedColorLayout.tables free n) (_root_.ThreeSum.EncodedColorLayout.rec free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
      (_root_.ThreeSum.ColorClassLists.classList color x 0 1) (_root_.ThreeSum.ColorClassLists.classList color x 1 1) (_root_.ThreeSum.ColorClassLists.classList color x 2 (-1))
      A B C hsA hsB hsC ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ)









end ThreeSum.EncodedColorNormalizedData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Source banks from the actual cover and wanted output headers

The program reads its reusable destination from wanted+2, reads all local
source controls and pointers from the constructed cover header, computes
localPrime^J with the existing scalar-power procedure, and invokes the
complete shared source host. No source dimension or cover pointer is an
externally supplied control.
-/

namespace ThreeSum.LightEncodedColorSources
open _root_.ThreeSum.LightEncodedColorSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

def sourceBase (free p M h J : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  _root_.ThreeSum.EncodedColorWantedData.nextFree (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free h J xs.length) M
    (_root_.ThreeSum.LightGuardedWanted.left p xs) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M p xs h J : ℤ)

/-- h,J,cut,B value/header,C value/header,g,P,wanted header,cover header. -/
def body (pPower pSource : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPower [_root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 1] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 8)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 12)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 13)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 14)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 15)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSource [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 17] 0))))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHostProgram.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources.body 74 79]



def time (NL NR g p h J cut U M : ℕ) : ℕ :=
  _root_.ThreeSum.LightNatPower.time J+_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.time NL NR g p h J cut U M+1000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}



end ThreeSum.LightEncodedColorSources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executed terminal preparation followed by the exact original-value batch

The closed program constructs both endpoint and independent flag arrays
from the retained selected maps, then scans only their selected physical
bucket products. Every library call is an exact relocation of an already
verified implementation.
-/

namespace ThreeSum.LightReportingTerminalPrepared
open _root_.ThreeSum.LightReportingTerminalPrepared


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild

set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def body (pPrepare pBatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrepare [_root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 26] 27) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 28 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 11))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 28)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 4) (_root_.ThreeSum1960614.Machine.Light.v 22))) (_root_.ThreeSum1960614.Machine.Light.k 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 30 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 28)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 31 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.v 29)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 28))) (_root_.ThreeSum1960614.Machine.Light.v 22))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 32 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 28))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 22)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 33 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.v 29)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 28))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 22)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBatch [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 30, _root_.ThreeSum1960614.Machine.Light.v 31, _root_.ThreeSum1960614.Machine.Light.v 32, _root_.ThreeSum1960614.Machine.Light.v 33, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 26] 0))))))))

def libraries : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPrepared.libraries ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPrepared.body 17 24]

def space (work h J : ℕ) : ℕ :=
  max (_root_.ThreeSum.LightSourcePreparation.space work J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h))
    (work+4+(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+2))
def word (h J : ℕ) : ℕ :=
  _root_.ThreeSum.LightSourcePreparation.word J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    ((464*h).choose h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)+4*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+4*_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+16
def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.time h J (_root_.ThreeSum.LightReportingTerminalMasks.count h J k)+
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.time p shift left right NL NR q k pre+700

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingTerminalPrepared

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact retained catalog and scratch interfaces for the level loop

These records collect the memory assertions already produced by the actual
prefix-catalog constructor. They contain no assumed query procedure. The
query adapter below invokes the existing closed, verified catalog program.
-/

namespace ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostLevelData


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

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

structure Catalog where
  t : ℕ
  boxCut : ℕ
  boxBase : ℕ
  indexBase : ℕ
  ptrBase : ℕ

/-- The fields actually consumed by the level machine, including the computed
prefix count. The box base remains a semantic ownership bound. -/
def Catalog.record (D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (h k : ℕ) : List ℕ :=
  [D.t,D.boxCut,D.indexBase,D.ptrBase,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

structure Sources {h J : ℕ} (μ : ℕ→ℤ) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (baseL baseR : ℕ) : Prop where
  left : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (_root_.ThreeSum.LightBlockQuery.sourceCut h J) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)
  right : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (_root_.ThreeSum.LightBlockQuery.sourceCut h J) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)

structure Stored {h J k : ℕ} (μ : ℕ→ℤ) (D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hk : k≤J)
    (pMod shift : ℤ) (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) : Prop where
  index : ∃ S : List ℤ, _root_.ThreeSum1960614.Machine.Light.Seg μ D.indexBase S ∧
    S.Perm (_root_.ThreeSum.ReportingHostPackedCatalog.codes (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J k) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)) ∧
    S.Pairwise (· ≤ ·)
  pointers : _root_.ThreeSum1960614.Machine.Light.SegN μ D.ptrBase (List.ofFn fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) =>
    D.boxBase+i.val*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) D.boxCut)
  boxes : ∀ i<_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, _root_.ThreeSum.LightBoxStages.StoredThrough μ
    (D.boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) D.boxCut) D.boxCut
    (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c q)
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i)) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)

structure Bounds (h J k : ℕ) (D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (baseL baseR stop : ℕ) : Prop where
  left : baseL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J)≤ stop
  right : baseR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J)≤ stop
  index : D.indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k≤ stop
  pointers : D.ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k≤ stop
  boxes : D.boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) D.boxCut≤ stop

structure Scratch (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (h J k : ℕ) (D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (bCard cCard maskBase work : ℕ) : Prop where
  masks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) D.t≤work
  space : work+1+_root_.ThreeSum.LightPascal.tableSize (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)≤lim.space
  powers : work+(2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+2)≤lim.space
  emod : work+(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+1)+2)≤lim.space
  word : (((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) : ℕ) : ℤ)≤lim.word
  lookup : (_root_.ThreeSum.LightReportingCatalogLookup.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) : ℤ)≤lim.word
  values : (_root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
    (_root_.ThreeSum.LightBlockQuery.residualSize h J k) D.t bCard cCard : ℤ)≤lim.word
  t : D.t≤_root_.ThreeSum.LightBlockQuery.residualSize h J k+1
  cut : D.boxCut≤_root_.ThreeSum.LightBlockQuery.residualSize h J k
  flags : _root_.ThreeSum.LightBlockQuery.residualSize h J k-D.t≤D.boxCut









end ThreeSum.ReportingHostLevelData

end ThreeSum1960614.Machine


