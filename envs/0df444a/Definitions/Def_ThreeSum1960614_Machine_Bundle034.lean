-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle034
-- name    : ThreeSum1960614_Machine_Bundle034
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:52:48.918462+00:00
-- url     : https://prove2.me/theorems/755f859a-af20-4c8c-b1c8-caabc712e8ca
-- title:
--   Retained reporting levels, shared catalog entries, and terminal-frontier execution
-- statement:
--   This library defines the retained state and executable control for reporting levels. Root initialization reads the sorted catalog and selected cover headers, computes the empty-prefix dimensions, and obtains the root mass and capacity from the actual query and initializer. The bounded recursive level host loads persistent level records and executes the requested number of expansions. Its declared time is the sum of the level-specific costs rather than a worst-level bound multiplied by the number of levels.
--
--   For local block size $h$, block count $J$, independent source bands, and a decoded occurrence, one shared entry loads two retained source pointers, constructs the existing suffix catalog, and writes a five-cell level record. Its layout reserves both prefix arrays, the pointer row, suffix boxes, sorted index, and polynomial scratch. Physical wanted data identify the length-preserving transport from mapped $A$ values to original owner-incidence labels, retaining positions with equal integer values. Terminal-frontier execution reads the aligned stored prefix masks and runs the full terminal procedure for each prefix, reusing scratch while preserving source buckets, occurrence rows, and cover data.
--
--   These definitions connect the selected color's retained prime and source arrays to the actual reporting order used in the deterministic integer 3SUM proof. They expose the per-prefix costs and physical labels needed for exact original-mass charging and completeness.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorPrimeHost.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingInitializeStored.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingLevels.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSharedReportingEntry.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostTerminalFrontier.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostWantedPhysical.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankSources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorWantedSources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingTerminalFrontier.lean

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
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
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
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightEncodedColorPrimeHost
end ThreeSum.LightEncodedColorPrimeHost
namespace ThreeSum.LightEncodedColorWantedSources
end ThreeSum.LightEncodedColorWantedSources
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingInitializeStored
end ThreeSum.LightReportingInitializeStored
namespace ThreeSum.LightReportingLevels
end ThreeSum.LightReportingLevels
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingTerminalFrontier
end ThreeSum.LightReportingTerminalFrontier
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSharedReportingEntry
end ThreeSum.LightSharedReportingEntry
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostTerminalFrontier
end ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
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
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored
end ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLevels
end ThreeSum1960614.Machine.ThreeSum.LightReportingLevels
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-! # Original selected color to its retained common prime and physical arrays -/

namespace ThreeSum.LightEncodedColorPrimeHost
open _root_.ThreeSum.LightEncodedColorPrimeHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 15000

def body (pNormalize pPrime : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pNormalize [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 14)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 18)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrime [_root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 6] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 6)))))))))))))))

def joined : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.program _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.program
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.joined ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.body 45 70]









def depth (n : ℕ) : ℕ := max
  (_root_.ThreeSum.LightBandRawAColor.depth (_root_.ThreeSum.Scales.inputBits n+1) n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+3)
  (Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)+11)

def inputTime (n U : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.time n+
  _root_.ThreeSum.LightEncodedColorPrime.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) U+600

def inputSpace (free n U : ℕ) : ℕ := max (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.space free n)
  (_root_.ThreeSum.LightEncodedColorPrimeCore.space (_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) U)

def inputWord (n U : ℕ) : ℕ := max (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.word n U)
  (_root_.ThreeSum.LightEncodedColorPrime.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) U)+
    _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+_root_.ThreeSum.Scales.primeWindow n+100

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}






end ThreeSum.LightEncodedColorPrimeHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Root initialization from retained catalog and cover headers

The root query reads its sorted-catalog controls and the selected cover's
actual group-size cell. The empty-prefix dimensions are computed directly
from the common source width and cut; root mass and capacity are returned
by the executed query and initializer.
-/

namespace ThreeSum.LightReportingInitializeStored
open _root_.ThreeSum.LightReportingInitializeStored


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

/-- Width, source cut, source stages, catalog bank, packed query mask,
retained cover, root output, mask scratch, and work. -/
def body (pInit : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pInit [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 10] 0)))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitialize.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.body 36]
def time (h J t : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitialize.time h J t+500

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



end ThreeSum.LightReportingInitializeStored

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual bounded sequence of reporting levels

The recursive host executes only the requested number of levels, loading
all catalogs from persistent records. Its exact cost is the sum of the
actual level costs, with no multiplication by a worst-level query bound.
-/

namespace ThreeSum.LightReportingLevels
open _root_.ThreeSum.LightReportingLevels


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
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
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def body (pSelf pStep : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 3)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18] 19) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pStep [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18] 0)))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 8)))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.body 52 51]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (D : ℕ→_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) : ℕ→ℕ
  | 0 => 30
  | stageIndex+1 => time I w D stageIndex+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time h J stageIndex (D (stageIndex+1)).t (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w stageIndex).length+200

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingLevels

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Load two retained source pointers and construct one shared catalog record

The two sources may come from independent B and C bands. The occurrence
code is already represented by the supplied physical pointer cells. This
program loads those cells, runs the complete existing catalog constructor,
reads its computed prefix count, and writes the five-cell level record.
-/

namespace ThreeSum.LightSharedReportingEntry
open _root_.ThreeSum.LightSharedReportingEntry


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

/-- The catalog's twenty-one arguments, with arguments 6 and 7 now source
pointer cells, followed by the exact switch and record destination. -/
def body (pCatalog : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCatalog [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20] 25) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 25))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 22) (_root_.ThreeSum1960614.Machine.Light.v 21)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 22) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 22) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 20)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 22) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 16)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 22) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 26)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 26)))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.body 51]

def time (h J k boxCut : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.time h J k boxCut+500





end ThreeSum.LightSharedReportingEntry

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact terminal-prefix order, summed cost, and original completeness

The prefix batch consumes the actual retained frontier order. Every local
scan keeps its own selected-pair charge; their sum is bounded by the exact
original raw mass at the partial depth.
-/

namespace ThreeSum.ReportingHostTerminalFrontier
open _root_.ThreeSum.ReportingHostTerminalFrontier


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open scoped _root_.BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

def prefixAt {h : ℕ} (pres : List (List (Finset (Fin (464*h))))) (i : ℕ) : List (Finset (Fin (464*h))) :=
  pres[i]?.getD []



def Hit {h J : ℕ} (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (464*h))))) (n : ℕ) : Prop :=
  ∃ i<n, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit av p shift left right NL NR q k (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt pres i)





def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (464*h))))) : ℕ→ℕ
  | 0 => 30
  | n+1 => time p shift left right NL NR q k pres n+
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR q k (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt pres n)+300



def charge (h J k : ℕ) : ℕ :=
  _root_.ThreeSum.LightReportingBinomial.time ((J-k)*(2*h))+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.time h J k+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.time h J (_root_.ThreeSum.LightReportingTerminalMasks.count h J k)+
    (2*_root_.ThreeSum.LightResidues.residueBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+1300)*2^((J-k)*(2*h))+1830

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





end ThreeSum.ReportingHostTerminalFrontier

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual wanted array on physical owner-incidence indices

The key constructor uses the mapped A-value list. The reporter and dense
owner domains use physical positions in the incidence-label list. Their
length-preserving transport keeps every physical position, lift and full
output record, including positions holding equal integer values.
-/

namespace ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.ReportingHostWantedPhysical


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 2100000
set_option maxRecDepth 10000







def transport {α β : Type*} {h J : ℕ} (e : α≃β)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J β := (e w.1,w.2)





section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*(_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)

def wantedAt (slot : Fin (μ free).toNat) : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin (_root_.ThreeSum.BandRawA.items n g rs).length) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport (_root_.ThreeSum.ReportingHostWantedPhysical.incidenceIndices f n g rs) (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt H slot)





















end Actual

end ThreeSum.ReportingHostWantedPhysical

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

def localWidth (h : ℕ) : ℕ := 464*h
def width (h J : ℕ) : ℕ := J*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth h
def suffixWidth (h J k : ℕ) : ℕ := (J-k)*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth h
def localChoose (h : ℕ) : ℕ := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth h).choose h
def localPairs (h : ℕ) : ℕ := _root_.ThreeSum.LightReportingPrefixArrays.localCount (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth h) h
def prefixSpan (h k : ℕ) : ℕ := _root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h) k+1+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k
def cap (h J k boxCut : ℕ) : ℕ := _root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth h J k) boxCut

def pairL (base h : ℕ) : ℕ := base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h
def pairR (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h
def stageL (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h
def stageR (base h k : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k
def pointers (base h k : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k
def boxes (base h k : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k
def masks (base h J k boxCut : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth h J k) boxCut
def index (base h J k boxCut : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut
def work (base h J k boxCut : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k
def finish (base h J k boxCut : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut+2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth h+2+1+_root_.ThreeSum.LightPascal.tableSize (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)+(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J+1)+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k
def cellSize (h J k boxCut : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish 0 h J k boxCut

def catalog (base h J k boxCut t : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog :=
  ⟨t,boxCut,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index base h J k boxCut,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k⟩

























def levelOffset (h J : ℕ) (boxCut : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | stageIndex+1 => levelOffset h J boxCut stageIndex+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize h J stageIndex (boxCut stageIndex)







end ThreeSum.SharedReportingBankLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Independent source bands and exact reuse for every decoded output -/

namespace ThreeSum.SharedReportingBankSources
open _root_.ThreeSum.SharedReportingBankSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

def bankBase (base h J cut band : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt (_root_.ThreeSum.SourceBandBankData.first base) h J cut band

def leftCell (base h J cut band occurrence : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut band+2*occurrence
def rightCell (base h J cut band occurrence : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut band+2*occurrence+1

def leftBase (base h J cut band occurrence : ℕ) : ℕ :=
  _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut band)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut occurrence

def rightBase (base h J cut band occurrence : ℕ) : ℕ :=
  _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut band)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut occurrence











end ThreeSum.SharedReportingBankSources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Execute wanted records and shared original source banks consecutively -/

namespace ThreeSum.LightEncodedColorWantedSources
open _root_.ThreeSum.LightEncodedColorWantedSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

set_option maxHeartbeats 2500000
set_option maxRecDepth 13000

/-- h,J,cut,A-incidences,length,P,M,cover base,B value/header,C value/header,g. -/
def body (pWanted pSources : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pWanted [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSources [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 7] 0))

def joined : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.program _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorSources.program
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.joined ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.body 98 179]



def args (a free bv be cv ce n p M len : ℕ) : List ℤ :=
  [_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n),_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n),_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n,a,len,p,M,free,bv,be,cv,ce,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n]

def time (n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.time p M (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) U xs+
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n p U M+400

def space (free n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.space free p M (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) U xs)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs) n p U M)

def word (n p M U len : ℕ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.word p M (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) U len)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word n p U M)

def depth (n M len : ℕ) : ℕ :=
  max (464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+Nat.clog 2 M+3*len+13)
    (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+18)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}



end ThreeSum.LightEncodedColorWantedSources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executed terminal iteration over the retained prefix arrays

The recursion reads the two aligned prefix masks from retained memory and
runs the complete terminal program for each prefix. Its cost is the sum of
the actual prefix costs. Reused scratch never changes the prefix arrays or
the original source buckets, occurrence rows, and selected cover data.
-/

namespace ThreeSum.LightReportingTerminalFrontier
open _root_.ThreeSum.LightReportingTerminalFrontier


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
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000

/-- The terminal host's 31 arguments, with arguments 22 and 23 now the
retained prefix-array pointers, followed by the number of prefixes. -/
def body (pSelf pTerminal : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 31)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 28, _root_.ThreeSum1960614.Machine.Light.v 29, _root_.ThreeSum1960614.Machine.Light.v 30, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 31) (_root_.ThreeSum1960614.Machine.Light.k 1)] 32) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 33 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 31) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 34 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 22) (_root_.ThreeSum1960614.Machine.Light.v 33)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 35 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.v 33)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTerminal [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 34, _root_.ThreeSum1960614.Machine.Light.v 35, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 28, _root_.ThreeSum1960614.Machine.Light.v 29, _root_.ThreeSum1960614.Machine.Light.v 30] 36) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 32) (_root_.ThreeSum1960614.Machine.Light.v 36))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0)))))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier.body 39 38]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingTerminalFrontier

end ThreeSum1960614.Machine


