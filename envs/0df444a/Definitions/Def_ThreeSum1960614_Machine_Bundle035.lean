-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle035
-- name    : ThreeSum1960614_Machine_Bundle035
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:58:14.186487+00:00
-- url     : https://prove2.me/theorems/63b62f5f-889a-423a-a05b-43d234e5ac44
-- title:
--   Shared reporting catalogs and original-owner wanted initialization
-- statement:
--   The wanted-initialization program packs decoded query rows, initializes the root frontier from persistent catalogs, and updates the cumulative raw-mass counter before proportional traversal. It returns the actual comparison with the stored dense threshold. A shared-catalog cell computes the residual compact capacity and every payload address before invoking the entry constructor once. The local count constructor reads an actual Pascal table to obtain $\binom{464h}{h}$ and $\binom{464h}{2h}\binom{2h}{h}$ for natural microblock parameter $h$.
--
--   Each physical wanted slot identifies an A incidence and a permanent owner record. That record determines its own truncated B and C bands, their original signed-value maps and their lengths. The global raw-incidence domain uses all owner products; the local domain restricts to the wanted slot's own owner product. At depth $k$, the terminal predicate asserts a hit in at least one positive prefix of that local domain, tested against the original A value and those original B/C bands.
--
--   For $J$ blocks and depth $k$, the shared-bank switch is the executable integer quartic switch on residual size $2h(J-k)$, and the box cutoff is that residual size minus the switch. Five-cell catalog records and variable-size payloads are packed by explicit level offsets. The level loop maintains the exact prefix count and span, constructs each catalog once, and preserves completed payloads. Its resources separately bound state values, powers, radix keys, indices, signed transform values, switch arithmetic, space and nested calls; its time budget is the finite sum of the actual per-level budgets.
--
--   The selected-color pipeline storage predicate assembles the same normalized strictly increasing A/B/C lists, prime-chain data, cover tables, balanced wanted records, original A-key lifts and shared source banks. It records the output header and the exact bound $M\,|\mathrm{wanted}|\le3|\mathrm{incidences}|\,|\mathrm{globalKeys}|$, where $M$ is the chosen radix modulus. Explicit wanted time/space envelopes include offset computation and the physical pair output. The terminal adapter reads its frontier count, capacity and mask pointers from retained headers before running the original-value scan.
--
--   These definitions connect the actual wanted array to disjoint original-owner fibers and reusable catalogs in the complete deterministic integer 3SUM proof. They make cumulative dense stopping and terminal correctness statements refer to the same physical incidences, rather than to an unconstrained substitute domain.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWantedInitialize.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSharedReportingCell.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSharedReportingCounts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostWantedOriginal.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankLevels.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorPipelineData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorWantedCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingTerminalStored.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSharedReportingLevels.lean

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
namespace ThreeSum.EncodedColorPipelineData
end ThreeSum.EncodedColorPipelineData
namespace ThreeSum.EncodedColorWantedCosts
end ThreeSum.EncodedColorWantedCosts
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightReportingTerminalStored
end ThreeSum.LightReportingTerminalStored
namespace ThreeSum.LightReportingWantedInitialize
end ThreeSum.LightReportingWantedInitialize
namespace ThreeSum.LightSharedReportingCell
end ThreeSum.LightSharedReportingCell
namespace ThreeSum.LightSharedReportingCounts
end ThreeSum.LightSharedReportingCounts
namespace ThreeSum.LightSharedReportingLevels
end ThreeSum.LightSharedReportingLevels
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
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
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalStored
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalStored
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

namespace ThreeSum1960614.Machine

/-!
# Executed wanted-mask packing, root query, and cumulative guard

The program packs the decoded original query rows, initializes the actual
root frontier using persistent catalogs, and updates the running mass
counter before any proportional traversal. Its Boolean result is exactly
the actual threshold comparison. The global guard-soundness theorem can
therefore certify this early branch on the original owner domain.
-/

namespace ThreeSum.LightReportingWantedInitialize
open _root_.ThreeSum.LightReportingWantedInitialize


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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

/-- Width, cut, J, L, source stages, catalog bank, raw/packed query rows,
retained cover, dense counter/header, root output, and query scratch. -/
def body (pPack pInit pGuard : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPack [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 13] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pInit [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pGuard [_root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 14] 0))))

def initialLibraries : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.program
def libraries : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.initialLibraries _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.program
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.libraries ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.body 0 39 40]
def time (h J t : ℕ) : ℕ :=
  _root_.ThreeSum.LightBlockMasks.time J (464*h)+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time h J t+_root_.ThreeSum.LightDenseGuard.time+600

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





end ThreeSum.LightReportingWantedInitialize

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compute a suffix capacity and every address before constructing a catalog

The local binomial counts and current prefix count/span are scalar state
maintained by the surrounding bank loops. The compact suffix capacity is
computed here by the actual Pascal/downset routine. All remaining addresses
are computed arithmetically, and the existing entry constructor is called
exactly once. The return value is the next free payload address.
-/

namespace ThreeSum.LightSharedReportingCell
open _root_.ThreeSum.LightSharedReportingCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout

set_option maxHeartbeats 2900000
set_option maxRecDepth 15000

/-- h,J,k,source pointer cells,t,boxCut,local choose/pair counts,current
prefix count/span,record destination,and first free payload cell. -/
def body (pSize pEntry : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 464) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSize [_root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 12] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 19) (_root_.ThreeSum1960614.Machine.Light.v 10))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 20) (_root_.ThreeSum1960614.Machine.Light.v 10))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 21) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 16))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 22) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 23)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 24) (_root_.ThreeSum1960614.Machine.Light.v 16)) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 25) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.k 1)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 1)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 1)))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 27 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEntry [_root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 15, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 13), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 11] 28) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 26))))))))))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.program _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.program ++
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.body 53 52]

def time (h J k boxCut : ℕ) : ℕ :=
  _root_.ThreeSum.LightDownsetSize.time ((J-k)*(464*h))+_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.time h J k boxCut+1500





end ThreeSum.LightSharedReportingCell

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Compute the two local combinatorial counts from an actual Pascal table -/

namespace ThreeSum.LightSharedReportingCounts
open _root_.ThreeSum.LightSharedReportingCounts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout

set_option maxHeartbeats 1700000
set_option maxRecDepth 9000

/-- h, two-cell count destination, Pascal scratch. -/
def body (pBuild : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 464) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBuild [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 8))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.body 1,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildBody 2 3,_root_.ThreeSum1960614.Machine.Light.fillBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.rowBody 4,_root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody]
def time (h : ℕ) : ℕ := _root_.ThreeSum.LightPascal.buildTime (464*h)+300





end ThreeSum.LightSharedReportingCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedOriginal


open _root_.Finset
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000



def owner {h J n g : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) : ℕ :=
  (_root_.ThreeSum.BandRawA.labelAt n g rs w.1.val).owner

def left {h J n g : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record) (fB : ℕ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) (j : ℕ) : ℤ :=
  fB (_root_.ThreeSum.BandPartition.start g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b+j)

def right {h J n g : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record) (fC : ℕ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) (j : ℕ) : ℤ :=
  fC (_root_.ThreeSum.BandPartition.start g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c+j)

def leftCount {h J n g : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record) (NB : ℕ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) : ℕ := _root_.ThreeSum.BandRawA.bandLength NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b

def rightCount {h J n g : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record) (NC : ℕ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) : ℕ := _root_.ThreeSum.BandRawA.bandLength NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c

def globalItems (h J n NB NC g p : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs)
    (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)

def localItems (h J n NB NC g p : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) :
    Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (_root_.ThreeSum.BandRawA.finiteOwnerProduct n NB NC g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w))
    (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)

def Terminal (h J n NB NC g p : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) (k : ℕ) : Prop :=
  ∃ pre∈_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w k,
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit (_root_.ThreeSum.BandRawA.valueAt n g rs fA w.1.val) p shift
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.leftCount rs NB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.rightCount rs NC w) w.2.2 k pre















section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J)
    (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
    (3*(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs)).length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)





end Actual

end ThreeSum.ReportingHostWantedOriginal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum.SharedReportingBankLevels


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData

set_option maxHeartbeats 1400000


def switch (h J k : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J k (_root_.ThreeSum.SharedReportingBankLevels.residual h J k)
def boxCut (h J k : ℕ) : ℕ := _root_.ThreeSum.SharedReportingBankLevels.residual h J k-_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J k
def offset (h J : ℕ) : ℕ → ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J)
def baseAt (base h J k : ℕ) : ℕ := base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.offset h J k
def catalogAt (base h J k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J k)

def Built (μ : ℕ → ℤ) (record base h J K : ℕ)
    (f g : Finset (Fin (J*(464*h))) → ℤ) : Prop :=
  ∀ k < K, ∃ hk : k ≤ J, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry μ (record+5*k) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k) hk f g



































end ThreeSum.SharedReportingBankLevels

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One retained selected-color payload, from original input to shared sources -/

namespace ThreeSum.EncodedColorPipelineData
open _root_.ThreeSum.EncodedColorPipelineData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

local instance instNeZeroNatRadix (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) := ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩

def coverBase (free n : ℕ) : ℕ :=
  _root_.ThreeSum.EncodedColorLayout.cover free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)

def wantedHeader (free n len : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) len

def controls (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) n
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)

def bankHeader (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader (_root_.ThreeSum.LightSourceControlsHost.sourceBase (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC))
    B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))

def finish (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)

def values (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List ℤ :=
  _root_.ThreeSum.LightEncodedColorResult.values (_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)

structure Stored (μ : ℕ → ℤ) (free n : ℕ) (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)) (x : Fin n → ℤ)
    (A B C : List ℤ) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop where
  heads : _root_.ThreeSum1960614.Machine.Light.Seg μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values free n A B C hsA hsB hsC)
  normalizedHeads : _root_.ThreeSum1960614.Machine.Light.Seg μ free (_root_.ThreeSum.EncodedColorLayout.normalizedHeads free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
  countCell : μ (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))=
    ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ)
  normalized : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized μ
    (_root_.ThreeSum.EncodedColorLayout.av free n) (_root_.ThreeSum.EncodedColorLayout.ae free n)
    (_root_.ThreeSum.EncodedColorLayout.bv free n) (_root_.ThreeSum.EncodedColorLayout.be free n)
    (_root_.ThreeSum.EncodedColorLayout.cv free n) (_root_.ThreeSum.EncodedColorLayout.ce free n)
    (_root_.ThreeSum.EncodedColorLayout.tables free n) (_root_.ThreeSum.EncodedColorLayout.rec free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (_root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
    (_root_.ThreeSum.ColorClassLists.classList color x 0 1) (_root_.ThreeSum.ColorClassLists.classList color x 1 1) (_root_.ThreeSum.ColorClassLists.classList color x 2 (-1))
    A B C hsA hsB hsC ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ)
  primes : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData.Stored μ (_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.moduli n A B C hsA hsB hsC)
  cover : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  wanted : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (_root_.ThreeSum.LightGuardedWanted.left (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
  sources : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Stored μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) B C
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) : ℤ)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC : ℤ)
  countBound : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n*(μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)).toNat ≤
    3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length*
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  lifts : _root_.ThreeSum1960614.Machine.Light.Seg μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (_root_.ThreeSum.RawAKeyLists.keys (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)) (x : Fin n → ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    r=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC : ℤ) ∧ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC



end ThreeSum.EncodedColorPipelineData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts
open _root_.ThreeSum.EncodedColorWantedCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

set_option maxHeartbeats 1800000

def time (P M h J U len : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.time h J+_root_.ThreeSum.LightRawAKeys.time len U+
    _root_.ThreeSum.LightOriginalOffset.time M (3*len) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J)+
    2000*(3*len+_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J+M+
      3*len*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J/M+1)*
      (Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J+1)+Nat.log 2 (M+M+1)+1)+400

def sourceBase (free M h J len : ℕ) : ℕ :=
  _root_.ThreeSum.LightWantedSetup.pairBase (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free h J len)
    (3*len) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M+
    2*(3*len*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J/M)

def space (free P M h J U len : ℕ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.space free h J)
    (max (_root_.ThreeSum.LightRawAKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J) len U)
      (max (_root_.ThreeSum.LightOriginalOffset.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free h J len)
        M (3*len+_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J))
        (max (_root_.ThreeSum.LightSourceResidues.space
          (_root_.ThreeSum.LightWantedSetup.pairBase (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free h J len)
            (3*len) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M)
          M (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J) M)
          (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J len))))



















end ThreeSum.EncodedColorWantedCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Terminal scanning from the actual frontier header

This adapter reads the capacity produced by root initialization and the
terminal level's retained count, query mask, and two prefix-array pointers.
It then executes the complete terminal scan in the unchanged frontier order.
-/

namespace ThreeSum.LightReportingTerminalStored
open _root_.ThreeSum.LightReportingTerminalStored


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
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

/-- The 20 original-source/encoding controls, depth and root pointer, then
the seven terminal scratch pointers. All frontier metadata is loaded. -/
def body (pScan : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 21) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 30 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 21) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 20) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.k 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 29)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 31 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 30))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 32 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 30) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 33 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 30) (_root_.ThreeSum1960614.Machine.Light.k 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 34 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 33) (_root_.ThreeSum1960614.Machine.Light.v 29))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScan [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 32, _root_.ThreeSum1960614.Machine.Light.v 33, _root_.ThreeSum1960614.Machine.Light.v 34, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 28, _root_.ThreeSum1960614.Machine.Light.v 31] 0)))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalStored.body 39]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (k : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 k
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length+600



end ThreeSum.LightReportingTerminalStored

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Construct every level once for one occurrence and independent source bands

The loop executes the cubic switch, maintains the exact prefix count and
prefix-array span, and appends one compact catalog per level. Its budget is
the sum of the actual level budgets. Five-cell metadata records are
contiguous; completed payloads remain immutable.
-/

namespace ThreeSum.LightSharedReportingLevels
open _root_.ThreeSum.LightSharedReportingLevels


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

/-- h,J,level count,source pointer cells,local choose/pair counts,record and
payload destinations. The surrounding initializer computes the level count. -/
def body (pSwitch pCell : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 12 (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 12)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSwitch [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 14))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCell [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 5) (_root_.ThreeSum1960614.Machine.Light.v 12)), _root_.ThreeSum1960614.Machine.Light.v 11] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 9))))))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 11))))))

def roundTime (h J i : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.time (_root_.ThreeSum.SharedReportingBankLevels.residual h J i)+_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.time h J i (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J i)+800
def time (h J K : ℕ) : ℕ := (∑ i ∈ Finset.range K, (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime h J i+8))+100

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.body 63 62]



structure Resources (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (base h J K B D d : ℕ) : Prop where
  state : ((J+K+464+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h K+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h K : ℕ) : ℤ) ≤ lim.word
  space : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J K ≤ lim.space
  powers : ((2^(464*h+1) : ℕ) : ℤ) ≤ lim.word
  keys : ∀ i < K, (_root_.ThreeSum.LightRadixKeys.word (2^(464*h)) (2^(464*h)) i : ℤ) ≤ lim.word
  width : (((J*(464*h)+1)*2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word
  index : ∀ i < K, (_root_.ThreeSum.LightReportingSortedCatalog.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h i) : ℤ) ≤ lim.word
  values : ∀ i < K, (((2^((J-i)*(464*h))*
    ((2^((J-i)*(464*h))*B)*(2^((J-i)*(464*h))*D))) : ℕ) : ℤ) ≤ lim.word
  switch : ∀ i < K, (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.word J (_root_.ThreeSum.SharedReportingBankLevels.residual h J i) : ℤ) ≤ lim.word
  pairDepth : d+464*h+K+8 ≤ lim.depth
  widthDepth : d+J*(464*h)+18 ≤ lim.depth
  sortDepth : ∀ i < K, d+Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h i)+6 ≤ lim.depth

def Inv (μ : ℕ → ℤ) (record base h J K cellL cellR i : ℕ)
    (f g : Finset (Fin (J*(464*h))) → ℤ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r t cut : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [h,J,K,cellL,cellR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h,record,base,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h i,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h i,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i,i,r,t,cut],ν⟩ ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built ν record base h J i f g ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν record ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν base record (5*K)



end ThreeSum.LightSharedReportingLevels

end ThreeSum1960614.Machine


