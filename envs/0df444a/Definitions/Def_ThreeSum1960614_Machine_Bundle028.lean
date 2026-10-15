-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle028
-- name    : ThreeSum1960614_Machine_Bundle028
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:14:28.583121+00:00
-- url     : https://prove2.me/theorems/c723e0db-e088-439c-876d-d5e26063279f
-- title:
--   Shared prefix products, packed lookup keys, and retained band banks
-- statement:
--   This bundle defines the physical catalogs used to share reporting preprocessing. The local pair-row program enumerates each balanced left subset and every disjoint balanced right subset. A common Cartesian tuple list supplies both positional mask arrays, retaining separate records when one projection happens to coincide. The prefix-order interface maps this exact tuple order to the semantic left and right global prefix sets.
--
--   The prefix-catalog program constructs both mask arrays, reads their actual count, and builds all corresponding shrinking-suffix box tables. For $h,k\in\mathbb N$, its count is the $k$th power of the number of local ordered disjoint balanced pairs. Source-catalog cost definitions count two stage families per original band and occurrence vector, with decoder and loop overhead included.
--
--   The original-band pair constructor reads normalized $B,C$ lengths and counts, builds the two source catalogs using zero and selected shifts, and constructs an empty histogram row. A band-bank step selects one common band's retained histograms and constructs every occurrence bank. Stored bank data retain the header, all bank tables, and the big-endian occurrence rows; exact span and finish functions describe their memory layout.
--
--   For a bit width $W$, a catalog count $N$, masks $\ell_i,r_i$, and original position $i$, the packing pass stores
--   $$((\ell_i+2^W r_i)(N+1)+i).$$
--   The sorted-lookup program builds its own power table, performs a binary search for the requested pair-key interval, and uses binary remainder to recover the original catalog position. Thus lookup uses the stored sorted keys while preserving the original record identity.
--
--   These definitions supply concrete shared-prefix preprocessing and logarithmic catalog access for the deterministic integer 3SUM reporting algorithm, together with the retained original-source bank layout and explicit construction costs.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceCatalogProgram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPairRows.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostPrefixMasks.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BlockSourceCatalogCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPrefixArrays.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostPrefixOrder.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPrefixCatalog.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandPair.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceBandBankLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandBankStep.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostPackedCatalog.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceBandBankData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogLookup.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPackKeys.lean

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
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
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
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
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightBlockSourceCatalogProgram
end ThreeSum.LightBlockSourceCatalogProgram
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogLookup
end ThreeSum.LightReportingCatalogLookup
namespace ThreeSum.LightReportingPackKeys
end ThreeSum.LightReportingPackKeys
namespace ThreeSum.LightReportingPairRows
end ThreeSum.LightReportingPairRows
namespace ThreeSum.LightReportingPrefixArrays
end ThreeSum.LightReportingPrefixArrays
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSourceBandBankStep
end ThreeSum.LightSourceBandBankStep
namespace ThreeSum.LightSourceBandPair
end ThreeSum.LightSourceBandPair
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.ReportingHostPrefixMasks
end ThreeSum.ReportingHostPrefixMasks
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandBankData
end ThreeSum.SourceBandBankData
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys
end ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows
end ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandPair
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandPair
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-! # Literal program and finite cost of the constructed source catalog -/

namespace ThreeSum.LightBlockSourceCatalogProgram
open _root_.ThreeSum.LightBlockSourceCatalogProgram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000









def factor (h J : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.factor h J+1120+
    300*(J+1)*(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)+2)



end ThreeSum.LightBlockSourceCatalogProgram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual direct construction of all local balanced row pairs

An own-power layer enumerator constructs the left subsets. For each left
subset, an actual output-sensitive query enumerator constructs its disjoint
right subsets, and an affine pass writes the matching repeated left mask.
-/

namespace ThreeSum.LightReportingPairRows
open _root_.ThreeSum.LightReportingPairRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration

set_option maxHeartbeats 1800000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def roundBody (pQuery pAffine : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 9)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 10))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pQuery [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 1, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 8), _root_.ThreeSum1960614.Machine.Light.v 5] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pAffine [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 8), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 8), _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.k 0] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 12)))))))

def body (pLayer pQuery pAffine : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLayer [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 5] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 9 (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.roundBody pQuery pAffine)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 8))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body 2 4,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.body 5 0 6]





def Inv (μ : ℕ → ℤ) (L h srcS dstL dstR work j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (a b nr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [L,h,srcS,dstL,dstR,work,L.choose h,_root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L)),
      j*(L-h).choose h,j,a,b,nr,r],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.SegN μ' srcS (_root_.ThreeSum.SubsetAddress.enumerateLayer L h) ∧
    (∀ i < j, ∀ l < (L-h).choose h,
      μ' (dstL+i*(L-h).choose h+l) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) : ℤ) ∧
      μ' (dstR+i*(L-h).choose h+l) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.rightAt L h i l) : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcS





end ThreeSum.LightReportingPairRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Positional products are the physical masks of the complete shared prefix catalog

Both left and right products use one common tuple list. Every original valid
prefix has a key in that list, and the tuple encodes exactly its original
row-major global masks.
-/

namespace ThreeSum.ReportingHostPrefixMasks
open _root_.ThreeSum.ReportingHostPrefixMasks


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open scoped _root_.BigOperators

set_option maxHeartbeats 500000

variable {α : Type*}





def tuple {h k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) : List (Finset (Fin (464*h)) × Finset (Fin (464*h))) :=
  List.ofFn fun i => (p i).val















def ofTuple {h k : ℕ} (xs : List (Finset (Fin (464*h)) × Finset (Fin (464*h))))
    (hlen : xs.length = k) (hmem : ∀ q ∈ xs, q ∈ _root_.ThreeSum.ReportingHostPairEnumeration.pairs (464*h) h) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k :=
  fun i => ⟨xs[i.val]'(by rw [hlen]; exact i.isLt),
    (_root_.ThreeSum.ReportingHostPairEnumeration.pairs_mem _).mp (hmem _ (List.getElem_mem (by rw [hlen]; exact i.isLt)))⟩







end ThreeSum.ReportingHostPrefixMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts
open _root_.ThreeSum.BlockSourceCatalogCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout

















def work (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.time
  (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)



/-- Occurrence rows and persistent bank records, excluding reusable scratch. -/
def catalogCells (n : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum.LightBlockSourceBatchLayout.stride (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+2)



end ThreeSum.BlockSourceCatalogCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both complete prefix-mask product arrays in the same record order

The local pair arrays are built directly, then the verified positional-key
host is used twice with radix 2^L. Both results share the literal tuple order,
including separate entries for pairs with equal left or right projections.
-/

namespace ThreeSum.LightReportingPrefixArrays
open _root_.ThreeSum.LightReportingPrefixArrays


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum.ReportingHostPairSegments
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



def body (pPairs pPowers pKeys : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPairs [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 8] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 8, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pKeys [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 6] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pKeys [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 7] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 12)))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.body 8 9,_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.body 6,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.body 7 2 8]







end ThreeSum.LightReportingPrefixArrays

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete shared prefix records in the physical product-constructor order

The semantic list is obtained from the actual tuple list, without filtering,
reordering, or coalescing equal left/right projections. It connects both
constructed integer arrays to every exact global prefix-mask pair.
-/

namespace ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostPrefixOrder


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks
open _root_.ThreeSum.ReportingHostPairSegments
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments

set_option maxHeartbeats 600000

/-- The exact record order shared by both physical positional products. -/
def prefixes (h k : ℕ) : List (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :=
  (_root_.ThreeSum.RadixKeyLists.tuples (_root_.ThreeSum.ReportingHostPairEnumeration.pairs (464*h) h) k).attach.map fun t =>
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.ofTuple t.val ((_root_.ThreeSum.RadixKeyLists.mem_tuples _ _ _).mp t.property).1
      ((_root_.ThreeSum.RadixKeyLists.mem_tuples _ _ _).mp t.property).2









def leftSets (h J k : ℕ) : List (Finset (Fin (J*(464*h)))) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (J := J))

def rightSets (h J k : ℕ) : List (Finset (Fin (J*(464*h)))) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (J := J))

def preL (h J k i : ℕ) : Finset (Fin (J*(464*h))) := ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.leftSets h J k)[i]?).getD ∅
def preR (h J k i : ℕ) : Finset (Fin (J*(464*h))) := ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.rightSets h J k)[i]?).getD ∅

















end ThreeSum.ReportingHostPrefixOrder

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingPrefixCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def count (h k : ℕ) : ℕ := (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h)^k

def body (pPrefixes pCatalog : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrefixes [_root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 19] 20) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 20))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 20) (_root_.ThreeSum1960614.Machine.Light.v 14))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 22))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 20) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCatalog [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19] 27) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 20))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalogSetup.program ++
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.body 10 42]

def time (h J k boxCut : ℕ) : ℕ :=
  _root_.ThreeSum.LightReportingPrefixArrays.time (464*h) h k+
    _root_.ThreeSum.LightReportingSuffixCatalogSetup.time (J*(464*h)) ((J-k)*(464*h)) boxCut (k*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+500











end ThreeSum.LightReportingPrefixCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual B/C source catalogs from retained normalized headers

The program reads both physical lengths and band counts, and reads the C
shift from its supplied result cell. It constructs the B catalog with shift
zero, then the C catalog, then one shared empty histogram/offset row. The
eight-cell result header retains both catalog pointers and counts, the
empty-row pointer, the next free address, and both original lengths.
-/

namespace ThreeSum.LightSourceBandPair
open _root_.ThreeSum.LightSourceBandPair


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

/-- Values B, endpoint header B, values C, endpoint header C, band size,
prime, residue count, selected-shift cell, and result header. -/
def body (pSetup pFill : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSetup [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.v 14] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSetup [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 15] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pFill [_root_.ThreeSum1960614.Machine.Light.v 16, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 0] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 15)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 13)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 16)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 5)) (_root_.ThreeSum1960614.Machine.Light.v 18)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 6)) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 7)) (_root_.ThreeSum1960614.Machine.Light.v 10)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 18))))))))))))))))))))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pSetup : ℕ
  pFill : ℕ
  setup : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandSetup.Procs P pSetup
  fill : P[pFill]?=some _root_.ThreeSum1960614.Machine.Light.fillBody
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandPair.body pSetup pFill)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceBandPair

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout
open _root_.ThreeSum.SourceBandBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder

def span (h J cut : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space
    (_root_.ThreeSum.LightBlockSourceBatchLayout.work 0 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut) h J

def baseAt (base h J cut i : ℕ) : ℕ := base+i*_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut















def At (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut : ℕ) (p shift : ℤ) (i : ℕ) : Prop :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.Stored μ h J (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt base h J cut i) cut p shift
    (_root_.ThreeSum.SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
    (_root_.ThreeSum.SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)





end ThreeSum.SourceBandBankLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Construct every occurrence bank for one common original-band index -/

namespace ThreeSum.LightSourceBandBankStep
open _root_.ThreeSum.LightSourceBandBankStep


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
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

/-- The twelve retained-source controls and cover pointers, pair catalog,
output bank base, compact capacity, occurrence count, and common band index. -/
def body (pSelect pBatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelect [_root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 13] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 5) (_root_.ThreeSum1960614.Machine.Light.v 14)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 18))) (_root_.ThreeSum1960614.Machine.Light.k 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.v 14)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 15)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 20) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 19)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 21) (_root_.ThreeSum1960614.Machine.Light.v 14))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 22) (_root_.ThreeSum1960614.Machine.Light.v 18))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.k 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBatch [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 13), _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 1)), _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24] 25)))))))))

def time (h J cut : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) h J cut+1500

def word (NL NR h J : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J+2*NL+2*NR+32

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pSelect : ℕ
  pBatch : ℕ
  select : P[pSelect]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.body
  batch : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs P pBatch
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBankStep.body pSelect pBatch)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightSourceBandBankStep

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum.ReportingHostPackedCatalog


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder

set_option maxHeartbeats 600000

























def prefixKey (h J k i : ℕ) : ℕ :=
  _root_.ThreeSum.ReportingHostPackedCatalog.pairKey (2^(J*(464*h))) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i)) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i))







end ThreeSum.ReportingHostPackedCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained common-band source catalog with one occurrence table -/

namespace ThreeSum.SourceBandBankData
open _root_.ThreeSum.SourceBandBankData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords


def finish (base NL NR g h J cut : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt (_root_.ThreeSum.SourceBandBankData.first base) h J cut (_root_.ThreeSum.SourceBandPairSlices.count NL NR g)

def header (base NL NR g h J cut occ : ℕ) : List ℤ :=
  [_root_.ThreeSum.SourceBandBankData.first base,_root_.ThreeSum.SourceBandPairSlices.count NL NR g,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut,
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NL NR g h J cut,occ]

structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut occ : ℕ) (p shift : ℤ) : Prop where
  heads : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header base NL NR g h J cut occ)
  banks : ∀ i < _root_.ThreeSum.SourceBandPairSlices.count NL NR g,
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.At μ fL fR (_root_.ThreeSum.SourceBandBankData.first base) NL NR g h J cut p shift i
  rows : ∀ k < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J, ∀ j < J,
    μ (occ+k*J+j)=((_root_.ThreeSum.OutputDecodeOrder.indices (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) J k).getD j 0 : ℤ)







end ThreeSum.SourceBandBankData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual logarithmic lookup of an original prefix-catalog index

The program constructs its own powers, forms the physical query pair key,
performs division-free binary search over the sorted packed records, and
uses the benchmark's binary remainder algorithm to recover the original
catalog position. No full-catalog scan or index oracle occurs.
-/

namespace ThreeSum.LightReportingCatalogLookup
open _root_.ThreeSum.LightReportingCatalogLookup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}












def body (pPowers pSearch pEmod : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 5, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.k 2), _root_.ThreeSum1960614.Machine.Light.k 2] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 4))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSearch [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 5, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 0] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.v 10, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 5] 0))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody 1,_root_.ThreeSum1960614.Machine.Light.emodBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.body 0 1 2]





end ThreeSum.LightReportingCatalogLookup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The actual linear pass that packs prefix keys and original catalog indices -/

namespace ThreeSum.LightReportingPackKeys
open _root_.ThreeSum.LightReportingPackKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightArray
open _root_.ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.pass 5 (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 4)
    (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 5))))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.v 5)))











end ThreeSum.LightReportingPackKeys

end ThreeSum1960614.Machine


