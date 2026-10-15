-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle038
-- name    : ThreeSum1960614_Machine_Bundle038
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:14:08.94501+00:00
-- url     : https://prove2.me/theorems/37cbfa97-e99a-41df-b704-6ec2cfae4c58
-- title:
--   Wanted-slot dispatch and polynomial reporting resources
-- statement:
--   For input size $n$, the reporting-resource interfaces specialize the microblock half-width, block count, local prime and shared-bank dimensions to the executable schedule. A component-bound record places every local/global width, level count, prefix count, power, occurrence count, prime power, radix power and switch intermediate below a common positive magnitude. The resulting word, extent and depth bounds define a procedure need and are treated separately from the exact shared-box time budget. The selected-color resource scale additionally includes its local envelope, arithmetic modulus bound, prime window and $n$.
--
--   A physical wanted-slot dispatcher first constructs its scratch layout, decodes the wanted record and selects the owner's source arrays and per-level catalogs, then loads two packed records into the guarded reporter's arguments. Its compositional interface retains the reporter postcondition. The selection record contains twenty source/owner controls, while the layout supplies fourteen scratch pointers. The subsequent ascending scan visits slots in physical order and returns immediately on the first successful guard or original-value test.
--
--   For global width $W$, the shared-query scratch uses a mask span $2^W$ and a polynomial work span $(W+1)^2+8(W+1)+8$; its word envelope includes compact lookup keys and signed transform values with both source cardinalities bounded by the physical band size. The selected-color pipeline need explicitly reserves its word budget, $3000S(n)^5+U$ cells and its call depth, where $S$ is the resource scale and $U$ bounds the original input magnitudes.
--
--   The retained setup contract combines the same normalized A/B/C witnesses, encoded source payload, shared reporting catalogs and initialized dense counter. Setup adapters read their parameters and pointers from the existing headers and construct the shared bank and dense state through actual procedures.
--
--   These definitions provide size-only scalar bounds and affine-in-free-address allocations for the complete deterministic integer 3SUM machine. Each retained pointer is bounded individually, avoiding an artificial dependence of a size-only bound on translated memory addresses.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWantedRecordCall.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostWantedRecordData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsPolynomial.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorResourceScale.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWantedDispatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsQuery.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumReportingSetupData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorPipelineResources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWantedScan.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumReportingSetupBank.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumReportingSetupDense.lean

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
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
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_ThreeSum1962Source_Bundle18
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
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightReportingWantedDispatch
end ThreeSum.LightReportingWantedDispatch
namespace ThreeSum.LightReportingWantedRecordCall
end ThreeSum.LightReportingWantedRecordCall
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.LightThreeSumReportingSetupBank
end ThreeSum.LightThreeSumReportingSetupBank
namespace ThreeSum.LightThreeSumReportingSetupDense
end ThreeSum.LightThreeSumReportingSetupDense
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedRecordData
end ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

namespace ThreeSum1960614.Machine

/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000


def blocks (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)


def envelope (n : ℕ) : ℕ := _root_.ThreeSum.SharedReportingBankResourceBounds.polynomialPart n+(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^96
def scaledWord (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
def scaledExtent (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) n
def scaledDepth (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.depth (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)

structure Components (n : ℕ) : Prop where
  positive : 1 ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  localWidthBound : 464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n+1 ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  blocksBound : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+1 ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  levelsBound : _root_.ThreeSum.SharedReportingBankHeader.levels (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1 ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  widthBound : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1 ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  prefixBound : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.prefixCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  localPower : 2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n+1) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  pairsPower : 2^(2*(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  widthPower : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  indexPower : 2^(2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  occurrence : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  prime : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  primePower : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  radixPower : (2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1)^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  switchBase : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+1000000001 ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n
  depthWord : _root_.ThreeSum.LightSwitchDepth.word (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n























end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute the guarded reporter from the two concrete packed records

This procedure loads the twenty-cell owner/source selection and fourteen
computed scratch pointers, reads the retained prime and trim cap, and
passes exactly the verified guarded reporter's forty-four arguments.
Its compositional law retains the supplied reporter postcondition unchanged.
-/

namespace ThreeSum.LightReportingWantedRecordCall
open _root_.ThreeSum.LightReportingWantedRecordCall


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls

set_option maxHeartbeats 5500000
set_option maxRecDepth 24000
set_option linter.unusedVariables false

def body (pWanted : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 8)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 9)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 11)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 12)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 13)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 14)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 15)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 16)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 18)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 27 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 19)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 28 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 30 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 31 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 32 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 33 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 34 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 35 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 36 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 8)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 37 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 9)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 38 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 39 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 11)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 40 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 12)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 41 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 13)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 42 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 43 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 44 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 464) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 45 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 46 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 18)) (_root_.ThreeSum1960614.Machine.Light.v 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 47 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 38)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pWanted [_root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 44, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 42, _root_.ThreeSum1960614.Machine.Light.v 43, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 28, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 47, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 29, _root_.ThreeSum1960614.Machine.Light.v 30, _root_.ThreeSum1960614.Machine.Light.v 31, _root_.ThreeSum1960614.Machine.Light.v 32, _root_.ThreeSum1960614.Machine.Light.v 33, _root_.ThreeSum1960614.Machine.Light.v 34, _root_.ThreeSum1960614.Machine.Light.v 41, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.v 45, _root_.ThreeSum1960614.Machine.Light.v 35, _root_.ThreeSum1960614.Machine.Light.v 36, _root_.ThreeSum1960614.Machine.Light.v 37, _root_.ThreeSum1960614.Machine.Light.v 38, _root_.ThreeSum1960614.Machine.Light.v 39, _root_.ThreeSum1960614.Machine.Light.v 40, _root_.ThreeSum1960614.Machine.Light.v 46, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7] 0)))))))))))))))))))))))))))))))))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.program++[_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.body 137]

def numericExtra (h J K : ℕ) : ℕ :=
  J+464*h+K+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+_root_.ThreeSum.LightBlockQuery.sourceCut h J+
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h+1024

/-- Separate translated addresses from the size-only scalar envelope. -/
def space (selectionHeader layoutHeader cover counter h J K : ℕ) : ℕ :=
  max (max (selectionHeader+20) (layoutHeader+38+3*J))
    (max (max (cover+8) (counter+2)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.numericExtra h J K))



end ThreeSum.LightReportingWantedRecordCall

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-domain facts carried by the two actual wanted records

All source stages, buckets, occurrence rows, and per-level catalogs below
come from the retained concrete constructors. The decoder supplies the
unaltered original Q masks used by the guarded reporter.
-/

namespace ThreeSum.ReportingHostWantedRecordData
open _root_.ThreeSum.ReportingHostWantedRecordData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

def selected (fA : ℕ→ℤ) (n NB NC g pair bank cover h J occ srcB srcC report : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) (output : ℕ) : _root_.ThreeSum.ReportingHostWantedControls.Selection :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess fA n g rs w.1.val pair bank cover NB NC h J (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ
    (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output) srcB srcC report

def catalogs (n NB NC g report h J : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) (output k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog report h J NB NC g
    (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output)
    (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c k







section Stored

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
  {n NB NC g pair bank cover h J p occ srcB srcC report output : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ} (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs))















end Stored



end ThreeSum.ReportingHostWantedRecordData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open scoped _root_.Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section















def need (n _U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need := ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaledWord n,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaledExtent n,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaledDepth n⟩





end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000


def blocks (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)
def width (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n*(464*_root_.ThreeSum.EncodedColorResources.half n)

def scale (n : ℕ) : ℕ := _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+_root_.ThreeSum.EncodedColorResources.localEnvelope n+
  _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+_root_.ThreeSum.Scales.primeWindow n+n+100























noncomputable section





end
end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute one physical wanted slot from the reusable retained controls

The actual pointer constructor runs first. Its returned work pointer feeds
the actual wanted decoder and owner/source/catalog selector. The concrete
two-record loader then invokes the guarded original-value reporter.
-/

namespace ThreeSum.LightReportingWantedDispatch
open _root_.ThreeSum.LightReportingWantedDispatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls

set_option maxHeartbeats 2600000
set_option maxRecDepth 22000











def body (pLayout pDecode pRecord : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLayout [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 1] 23) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 14))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 18)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDecode [_root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 25] 26) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRecord [_root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9] 0)))))

def baseLibraries : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program

def libraries : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.baseLibraries _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.libraries++[_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.body 1 11 150]

def time (C : _root_.ThreeSum.LightReportingWantedDispatch.Config) (V reportTime : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.time C.h C.J+
    _root_.ThreeSum.LightReportingWantedDecodeAccess.time C.J V+reportTime+4500



end ThreeSum.LightReportingWantedDispatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete scratch limits for queries into the retained shared catalog bank

One mask span of `2^W` works for every prescribed level. The remaining
workspace is polynomial in W, including the exact packed-key remainder
workspace. Both source cardinalities are bounded independently by the
physical band size, and the switch and cut are the executed bank values.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def queryMaskSpan (h J : ℕ) : ℕ := 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)
def queryWorkSpan (h J : ℕ) : ℕ := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J+1)^2+8*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J+1)+8
def queryWord (h J g : ℕ) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J+1)+
    _root_.ThreeSum.LightReportingCatalogLookup.word (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J) (2^(2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J))+
    (2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)+1)*(2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)*((2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)*g)*(2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)*g)))















end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.ThreeSumReportingSetupData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

local instance instNeZeroNatRadix (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) := ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩

def reportBase (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8

def counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC)
    (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)

def shift (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℤ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))

def Catalog (μ : ℕ → ℤ) (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC)
    (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)

structure Stored (μ : ℕ → ℤ) (free n : ℕ) (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1))
    (x : Fin n → ℤ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop where
  encoded : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC
  catalog : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC
  dense : _root_.ThreeSum.LightDenseSetup.Stored μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC)
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC)









end ThreeSum.ThreeSumReportingSetupData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial Need for the exact closed selected-color pipeline -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000







def need (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word n U,3000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5+U,_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth n⟩

def envelope (n : ℕ) : ℕ := 1000000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^10



noncomputable section





end





end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Ascending physical wanted scan with immediate successful return

The recursive prefix runs before slot n-1. A positive prefix result returns
immediately; otherwise exactly the next physical slot is dispatched. The
counter is the exact mass of the executed prefix, including the first slot
whose guard or original-value test succeeds.
-/

namespace ThreeSum.LightReportingWantedScan
open _root_.ThreeSum.LightReportingWantedScan


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.LightReportingWantedDispatch
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch

set_option maxHeartbeats 2600000
set_option maxRecDepth 24000















def body (pSelf pDispatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 0)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22] 23) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 23)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDispatch [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22] 0))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.program++[_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.body 152 151]



end ThreeSum.LightReportingWantedScan

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Run shared reporting precomputation from the encoded color header -/

namespace ThreeSum.LightThreeSumReportingSetupBank
open _root_.ThreeSum.LightThreeSumReportingSetupBank


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 2100000
set_option maxRecDepth 14000



/-- Input length, parameter header, normalized header, encoded result header. -/
def body (pBank : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBank [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9] 0)))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.body 74]



def time (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget n+400



end ThreeSum.LightThreeSumReportingSetupBank

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Initialize the actual dense counter using the retained original arrays -/

namespace ThreeSum.LightThreeSumReportingSetupDense
open _root_.ThreeSum.LightThreeSumReportingSetupDense


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA

set_option maxHeartbeats 2600000
set_option maxRecDepth 16000



/-- n, parameter header, normalized header, encoded result header, counter. -/
def body (pDense : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 11))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 19) (_root_.ThreeSum1960614.Machine.Light.v 20)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 19))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 20)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDense [_root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 4] 0))))))))))))))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.program++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.body 19]



def time (n U R : ℕ) : ℕ :=
  _root_.ThreeSum.LightDenseSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) R (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n))
    U (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+1600

def word (n U : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) U (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+
    n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+
    _root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)+20







end ThreeSum.LightThreeSumReportingSetupDense

end ThreeSum1960614.Machine


