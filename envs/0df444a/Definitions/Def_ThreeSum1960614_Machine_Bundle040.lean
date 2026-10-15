-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle040
-- name    : ThreeSum1960614_Machine_Bundle040
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:19:45.531092+00:00
-- url     : https://prove2.me/theorems/22f14518-965a-4036-ae37-8d83f3aababc
-- title:
--   Original-input wanted host, persistent allocations, and hybrid runtime budgets
-- statement:
--   This bundle defines the concrete selected-color and wanted-record hosts together with their resource contracts. A color law specifies that, from the original integer input segment and the actual parameter and color records, a selected-color program returns a Boolean verdict equivalent to the corresponding color witness and preserves memory before the color row. The wanted host reads every scan control from the retained parameter, normalization, encoding, and reporting headers.
--
--   Persistent-end predicates bound each individual retained array, source-band header, histogram, occurrence row, coefficient table, and source-stage family before the mutable counter. They keep the two chosen bands independent. Uniform readiness at magnitude exponent $k\in\mathbb N$ requires positive input size and microblock half-size, radix at least $4$, the actual divisor-budget inequality, and separation of every nonzero integer of absolute value at most $3n^k$ by some generated auxiliary prime. The bundle includes an eventual cutoff satisfying these conditions before the input arrays are chosen.
--
--   The full fast driver initializes a nineteen-cell parameter record and a reusable six-cell color row, then scans the complete coloring family. Need records give relative word, cell, and depth reservations for dense setup, reporting setup, source preparation, the selected-color allocation, and the physical wanted scan. The guard-sensitive slot budget keeps the active-branch mass charge inside the cumulative threshold test.
--
--   For fixed exponent $k$, cutoff $N$, input size $n$, and supplied magnitude $U$, the hybrid cost selects the original triple-scan cost when $n<N$ or $n^k<U$, and otherwise selects the complete fast-driver cost, including integer exponentiation and caller overhead. The encoded-color reporting pipeline composes the actual source construction with reporting and dense initialization while retaining the original normalized witnesses.
--
--   These definitions provide the uniform readiness, exact physical loading, affine memory accounting, and finite-exception runtime interface needed by the complete deterministic integer 3SUM proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumColorDriverBounded.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumWantedHostDefs.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsDenseScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsWantedAccess.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumWantedHostConditions.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorWantedConsumerEnds.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumFastDriver.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsWantedScan.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedTraversalScanCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumReportingSetupResources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorReportingResources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorWantedConsumerRetention.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumFastResources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumHybridCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorReportingPipeline.lean

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
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
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorReportingResources
end ThreeSum.EncodedColorReportingResources
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightEncodedColorReportingPipeline
end ThreeSum.LightEncodedColorReportingPipeline
namespace ThreeSum.LightThreeSumColorDriver
end ThreeSum.LightThreeSumColorDriver
namespace ThreeSum.LightThreeSumFastDriver
end ThreeSum.LightThreeSumFastDriver
namespace ThreeSum.LightThreeSumWantedHost
end ThreeSum.LightThreeSumWantedHost
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.ThreeSumFastResources
end ThreeSum.ThreeSumFastResources
namespace ThreeSum.ThreeSumHybridCosts
end ThreeSum.ThreeSumHybridCosts
namespace ThreeSum.ThreeSumReportingSetupResources
end ThreeSum.ThreeSumReportingSetupResources
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts
end ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

namespace ThreeSum1960614.Machine

/-! # Run the closed color scan from actual input and parameter arrays -/

namespace ThreeSum.LightThreeSumColorDriver
open _root_.ThreeSum.LightThreeSumColorDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def ColorLaw (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ)
    (colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need) (src n params row U colorTime : ℕ) (x : Fin n→ℤ) : Prop :=
  ∀ (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.LightColorParametersCosts.width n)) (ν : ℕ→ℤ) (dd : ℕ),
    (colorNeed n U).Ok lim (row+6) dd →
    _root_.ThreeSum1960614.Machine.Light.Seg ν src (List.ofFn x) → _root_.ThreeSum1960614.Machine.Light.Seg ν params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n) →
    _root_.ThreeSum1960614.Machine.Light.Seg ν row (_root_.ThreeSum.ColorParameters.fields color) →
    _root_.ThreeSum1960614.Machine.Light.Meets lim colorProgram pColor dd [src,n,params,row,row+6] ν colorTime
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.ColorClassLists.witness color x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept ν ξ row)





end ThreeSum.LightThreeSumColorDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Load the retained color headers and execute the actual wanted scan

All controls passed to the fixed153 scan are read from the initialized
parameter, normalization, encoding and reporting headers. The raw-owner
array is located using the actual three band counts stored by normalization.
-/

namespace ThreeSum.LightThreeSumWantedHost
open _root_.ThreeSum.LightThreeSumWantedHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000



/-- n, parameter header, normalized header, encoded result header, counter. -/
def body (pScan : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 14))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 18))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 17))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.k 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.k 18)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 27 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 26) (_root_.ThreeSum1960614.Machine.Light.k 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 28 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 30 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 31 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 14)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 32 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 33 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 34 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 35 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 36 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 34) (_root_.ThreeSum1960614.Machine.Light.v 35)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 33) (_root_.ThreeSum1960614.Machine.Light.v 34))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 33) (_root_.ThreeSum1960614.Machine.Light.v 35)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 37 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 24) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 32) (_root_.ThreeSum1960614.Machine.Light.v 36)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScan [_root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 37, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 28, _root_.ThreeSum1960614.Machine.Light.v 29, _root_.ThreeSum1960614.Machine.Light.v 30, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 31] 0))))))))))))))))))))))))))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.body 152]



def word (n : ℕ) : ℕ := n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)+
  _root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+
  _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))+
  _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))+
  _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+50

end ThreeSum.LightThreeSumWantedHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial limits for the exact dense initialization resources -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1600000
set_option maxRecDepth 14000

def denseEnvelope (n : ℕ) : ℕ := 20000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^8

/-- Exact word, relative cell extent, and depth of the physical dense setup. -/
def denseNeed (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need := ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseWord n U,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseCells n U,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseDepth n⟩









noncomputable section





end





end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Every selected persistent row remains before the counter

The bounds keep the selected B and C bands independent. Each incidence and
occurrence is selected by its retained physical label, and every translated
pointer is bounded individually by the already occupied prefix.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored

set_option maxHeartbeats 2800000
set_option maxRecDepth 15000





structure WantedSourceEnds (X : _root_.ThreeSum.ReportingHostSourceSelection.Pointers) (pair bank cover srcB srcC i j code h J cut stop : ℕ) : Prop where
  pairHeader : pair+3≤ stop
  bankHeader : bank+5≤ stop
  coverHeader : cover+16≤ stop
  leftHead : _root_.ThreeSum.ReportingHostSourceSelection.leftHead X i+6≤ stop
  rightHead : _root_.ThreeSum.ReportingHostSourceSelection.rightHead X j+6≤ stop
  leftCell : _root_.ThreeSum.ReportingHostSourceSelection.leftStageCell X i code+1≤ stop
  rightCell : _root_.ThreeSum.ReportingHostSourceSelection.rightStageCell X j code+1≤ stop
  sourceL : srcB+X.startL+X.sizeL≤ stop
  sourceR : srcC+X.startR+X.sizeR≤ stop
  offsetsL : X.offsetsL+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+1≤ stop
  offsetsR : X.offsetsR+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+1≤ stop
  flatL : X.flatL+X.sizeL≤ stop
  flatR : X.flatR+X.sizeR≤ stop
  occurrence : _root_.ThreeSum.ReportingHostSourceSelection.occurrenceRow X code J+J≤ stop
  maps : X.maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤ stop
  candidates : X.candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤ stop
  histL : X.histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤ stop
  histR : X.histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤ stop
  stagesL : X.stagesL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut≤ stop
  stagesR : X.stagesR+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut≤ stop







end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Uniform size conditions and original-color semantics for the wanted consumer

The cutoff is chosen before any memory, color, or original array. The
auxiliary-prime separation premise is proved for the actual generated pool.
-/

namespace ThreeSum.ThreeSumWantedHostConditions
open _root_.ThreeSum.ThreeSumWantedHostConditions


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.Filter
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open scoped _root_.Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

structure Ready (k n : ℕ) : Prop where
  positive : 0<n
  half : 0<_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)
  radix : 4≤_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n
  divisor : _root_.ThreeSum.Scales.divisorBudget k n*_root_.ThreeSum.Scales.primeWindow n≤_root_.ThreeSum.Scales.candidateCount n*(4*(k+2)*(_root_.ThreeSum.Scales.inputBits n+1))
  separates : ∀ z : ℤ, z≠0 → z.natAbs≤3*n^k → ∃ l∈_root_.ThreeSum.DenseGuard.actualAux n, ¬l∣z

theorem ready_eventually (k : ℕ) : ∀ᶠ n : ℕ in atTop, _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (_root_.ThreeSum.Scales.microHalf_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).eventually (eventually_ge_atTop 1),
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_eventually_ge_four,_root_.ThreeSum.Scales.actual_divisor_budget k,_root_.ThreeSum.DenseGuard.actual_aux_separates k]
      with n hn hh hr hd hs
  simp only [Function.comp_apply] at hh
  exact ⟨by omega,by omega,hr,hd,hs⟩

theorem exists_cutoff (k : ℕ) : ∃ N : ℕ, ∀ n≥N, _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n :=
  eventually_atTop.mp (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.ready_eventually k)

noncomputable def cutoff (k : ℕ) : ℕ := Classical.choose (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.exists_cutoff k)



def OriginalZero (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop :=
  let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC
  ∃ t∈_root_.ThreeSum.BandRawA.finiteAllProducts A.length B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs,
    _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t=0





end ThreeSum.ThreeSumWantedHostConditions

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# All persistent wanted-consumer inputs precede the mutable counter

The bounds use the actual packed source and wanted extents. In particular,
the pair-array endpoint is the source-control base, and the occurrence rows
end exactly at the shared source-bank header.
-/

namespace ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum.EncodedColorWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

structure PersistentEnds (cfg : _root_.ThreeSum.LightReportingWantedDispatch.Config)
    (positions occ g cut rowCount wantedCount : ℕ) : Prop where
  values : cfg.vals+cfg.N≤cfg.counter
  owners : cfg.owners+cfg.N≤cfg.counter
  positions : positions+cfg.N≤cfg.counter
  records : cfg.records+4*rowCount≤cfg.counter
  srcB : cfg.srcB+cfg.NB≤cfg.counter
  srcC : cfg.srcC+cfg.NC≤cfg.counter
  pair : _root_.ThreeSum.SourceBandPairData.next cfg.pair cfg.NB cfg.NC g
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus cfg.h cfg.J)≤cfg.counter
  bank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish cfg.bank cfg.NB cfg.NC g cfg.h cfg.J cut≤cfg.report
  occurrence : occ+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count cfg.h cfg.J*cfg.J≤cfg.bank
  cover : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cfg.cover cfg.h cfg.J≤cfg.counter
  report : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish cfg.report cfg.h cfg.J cfg.NB cfg.NC g≤cfg.counter
  pairs : cfg.pairs+2*wantedCount≤cfg.counter
  masks : cfg.masks+cfg.layerCount≤cfg.counter
  reportBeforeCounter : cfg.report+9≤cfg.counter

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}













end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Initialize parameters once and execute the complete color family

The public arguments are [source,n,free]. The nineteen-cell parameter
record starts at free; the reusable six-cell color row starts at free+19;
the concrete selected-color program receives free+25 as its work boundary.
-/

namespace ThreeSum.LightThreeSumFastDriver
open _root_.ThreeSum.LightThreeSumFastDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 18000




def body (pScan : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 19))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call 0 [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScan [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3] 0)))

def libraries (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program colorProgram pColor)

def program (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries colorProgram pColor++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.body (colorProgram.length+25)]

def time (colorTime n : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time n+_root_.ThreeSum.LightColorScanHost.time colorTime n+500











end ThreeSum.LightThreeSumFastDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial call depth for scanning every physical wanted record

The scan retains the exact word and cell reservations of one wanted
dispatcher. Only its depth includes the number of physical records.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 1700000
set_option maxRecDepth 14000



def wantedScanNeed (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).word,(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).cells,(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).depth+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n+4⟩











noncomputable section



end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the actual fixed153 wanted scan and fixed154 header caller

The concrete dispatcher contributes4500 operations, and the ascending
recursion contributes300 per slot. The exact active-branch mass remains
inside the cumulative guard until the original reporting ledger is applied.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def slotEnvelope (n threshold : ℕ) (mass : ℕ→ℕ) (i : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead 4800 n+
    if threshold<_root_.ThreeSum.SharedTraversalCosts.prefixMass mass i+mass i then 0 else
      mass i*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n))

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





def colorBudget (k n : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.time n (n^k)+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatchBudget 4800 k n+5000



noncomputable section





end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Compose the two actual reporting allocations at an arbitrary free pointer -/

namespace ThreeSum.ThreeSumReportingSetupResources
open _root_.ThreeSum.ThreeSumReportingSetupResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def need (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).word+(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed n U).word,
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).cells+(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed n U).cells,
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).depth+(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed n U).depth+3⟩







noncomputable section



end
end ThreeSum.ThreeSumReportingSetupResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Affine resources for source construction followed by reporting setup -/

namespace ThreeSum.EncodedColorReportingResources
open _root_.ThreeSum.EncodedColorReportingResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def need (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).word+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need n U).word,
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).cells+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need n U).cells,
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).depth+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need n U).depth+2⟩







noncomputable section



end
end ThreeSum.EncodedColorReportingResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Retain the selected-color inputs while the wanted counter changes

Only the first dense-header cell is mutable during the scan. The encoded
payload, shared reporting catalog, threshold, cap and original false score
remain available with exactly the same normalized-list witnesses.
-/

namespace ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum.EncodedColorWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def DenseMetadata (μ : ℕ→ℤ) (counter cap score : ℕ) : Prop :=
  μ (counter+1)=((cap*score : ℕ) : ℤ) ∧
    μ (counter+2)=(cap : ℤ) ∧ μ (counter+3)=(score : ℤ)

variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}













end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Relative limits for the complete wanted-header loader and scan

All numeric controls come from the input size. The loader starts its reusable
scratch at `counter+4`; every retained absolute pointer is handled by its
individual allocation end rather than being included in a numeric envelope.
-/

namespace ThreeSum.ThreeSumFastResources
open _root_.ThreeSum.ThreeSumFastResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

set_option maxHeartbeats 2100000
set_option maxRecDepth 15000

def headerWord (n : ℕ) : ℕ :=
  n+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+_root_.ThreeSum.SharedReportingBankResourceBounds.half n+_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+
    _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+
    _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n+50

/-- Two outer call levels above the actual whole-wanted scan. -/
def need (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).word,(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).cells,(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).depth+2⟩























noncomputable section



end
end ThreeSum.ThreeSumFastResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The exact hybrid cost along every fixed input-magnitude exponent

The exceptional-size and excessive-magnitude branches use the original
triple scan. Once the size reaches the fixed cutoff, every bound at most
n^κ selects the same fast cost. The scalar exponentiation and fixed caller
cost fit within the proved gap between the certificate and target exponents.
-/

namespace ThreeSum.ThreeSumHybridCosts
open _root_.ThreeSum.ThreeSumHybridCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def time (κ cutoff n U : ℕ) : ℕ :=
  if n<cutoff ∨ n^κ<U then
    _root_.ThreeSum.LightBruteThreeSum.time n+_root_.ThreeSum.LightNatPower.time κ+1000
  else
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget κ n) n+
      _root_.ThreeSum.LightNatPower.time κ+1000

def fastTime (κ n : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget κ n) n+
    _root_.ThreeSum.LightNatPower.time κ+1000



noncomputable section





















end
end ThreeSum.ThreeSumHybridCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original selected color through the shared reporting and dense prefixProgram

The literal355-procedure program runs the existing source pipeline and then
the reporting setup. It returns the original source header; all normalized
lists and occurrence-shared catalogs are retained in the same payload.
-/

namespace ThreeSum.LightEncodedColorReportingPipeline
open _root_.ThreeSum.LightEncodedColorReportingPipeline


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 2600000
set_option maxRecDepth 17000

/-- Original array, length, parameter header, selected color row, free address. -/
def body (pSource pReporting : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSource [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pReporting [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 5))))

def joined : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program
  _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.program

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.joined++[_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.body 255 353]



def time (n U : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.time n U



end ThreeSum.LightEncodedColorReportingPipeline

end ThreeSum1960614.Machine


