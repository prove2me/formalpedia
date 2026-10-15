-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle039
-- name    : ThreeSum1960614_Machine_Bundle039
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:17:26.746494+00:00
-- url     : https://prove2.me/theorems/554abb64-d1d2-4566-8657-48627c2ebcc9
-- title:
--   Complete reporting setup, dispatch budgets, and outer-driver needs
-- statement:
--   For natural parameters $h,J,K,N,N_B,N_C$, the wanted-reporter resources separately define its layout work, scalar numeric envelope, terminal/query/decoder scratch, total extra cells and call depth. Buffer contracts translate these reservations from an arbitrary destination, while independently bounding every retained pointer and layout value. The per-input wanted need has word budget $E(n)(U+1)$ and cell/depth budgets $E(n)$, where $E$ is the schedule-derived envelope and $U$ bounds input values.
--
--   The dispatch budget includes the actual physical decoder and scratch-pointer constructor. It multiplies an explicit scalar overhead by the sum of initial, active and terminal reporting counts, using the uniform wanted- and false-mass budgets. Parameter initialization has a nineteen-cell persistent header and separately defined word, relative-cell, depth and time budgets; its actual square-root and quotient loops are charged in time rather than replaced by polynomial storage envelopes.
--
--   The reporting setup runs the shared-bank construction once, passes its returned free pointer to dense initialization, and returns the original source header. Its output retains the same normalized strictly increasing A/B/C lists, encoded sources, catalogs and dense state. A physical slot-hit predicate uses that slot's own original owner bands and terminal frontier; out-of-range slots have no hit. Wanted-consumer configuration is derived from actual retained headers, including incidence count, owner records, pair output, occurrence array, sources, modulus and shared report bank.
--
--   For any per-color need $R$, the color scan adds a six-cell color row, color-parameter arithmetic and call overhead. The full driver combines this with parameter initialization, taking the maximum of their scratch reservations while retaining nineteen persistent cells. Selected-color preprocessing and full reporting-prelude time expressions include normalization, prime choice, cover/key generation, balanced wanted rows, sources, shared catalogs and dense initialization.
--
--   These definitions assemble the exact costs and resource requirements used at the final composition stage of the deterministic integer 3SUM proof. Physical A incidences retain owner identity even when their numerical values agree, so whole-scan decisions and cumulative guards use the same original domain.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsWanted.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedTraversalDispatchCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumParameterResources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorPipelineTime.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorReportingData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumReportingSetup.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostWantedDecision.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsDense.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SharedReportingBankResourceBoundsWantedScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumColorDriverResources.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumParameterResourcesTime.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumWantedHostData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorReportingCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorWantedConsumerData.lean

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
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
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorReportingCosts
end ThreeSum.EncodedColorReportingCosts
namespace ThreeSum.EncodedColorReportingData
end ThreeSum.EncodedColorReportingData
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.EncodedColorTime
end ThreeSum.EncodedColorTime
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.LightThreeSumReportingSetup
end ThreeSum.LightThreeSumReportingSetup
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedDecision
end ThreeSum.ReportingHostWantedDecision
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.ThreeSumColorDriverResources
end ThreeSum.ThreeSumColorDriverResources
namespace ThreeSum.ThreeSumParameterResources
end ThreeSum.ThreeSumParameterResources
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
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
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorTime
end ThreeSum1960614.Machine.ThreeSum.EncodedColorTime
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

namespace ThreeSum1960614.Machine

/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

def wantedWork (h J K N NB NC : ℕ) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout 0 h J K N NB NC).work

def wantedNumeric (h J K N NB NC : ℕ) : ℕ :=
  N*NB+N*NB*NC+_root_.ThreeSum.ReportingHostWantedLayout.massBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J)+
    J+464*h+K+N+NB+NC+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J+_root_.ThreeSum.LocalCoverBounds.groupSize h+
    _root_.ThreeSum.LightBlockQuery.sourceCut h J+1024

def wantedScratch (h J V : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.space 0 h J+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWorkSpan h J+
    (Nat.log 2 (V+1)+2)+(464*h+1)+20

def wantedCells (h J K N NB NC V : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork h J K N NB NC+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNumeric h J K N NB NC+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScratch h J V

def wantedDepth (h J K N NB NC : ℕ) : ℕ :=
  K+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+_root_.ThreeSum.ReportingHostWantedLayout.massBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J)+
    2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+50









structure WantedBuffers (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (dst h J K N NB NC V : ℕ) : Prop where
  numeric : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work+
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNumeric h J K N NB NC≤lim.space
  terminal : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.space
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work h J≤lim.space
  query : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work+
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWorkSpan h J≤lim.space
  decoder : _root_.ThreeSum.LightWantedDecode.space
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work V≤lim.space
  pack : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work+(464*h+1)≤lim.space
  parameters : J+464*h+_root_.ThreeSum.LocalCoverBounds.groupSize h+_root_.ThreeSum.LightBlockQuery.sourceCut h J≤lim.space
  values : ∀ x∈_root_.ThreeSum.ReportingHostWantedLayout.values
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC), x≤lim.space







section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







end Raw
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def scalarOverhead (c n : ℕ) : ℕ :=
  800*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n+1)*(8192*(_root_.ThreeSum.Scales.inputBits n+1)+3)+8300+
    20*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)+2520+c



def totalOverhead (c n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead c n

def dispatchBudget (c k n : ℕ) : ℕ := 30+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c n*
  (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.initialCount _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n+
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.activeCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) n+
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) n)





open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open scoped _root_.Topology

noncomputable section









end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact polynomial resources for the executed parameter initializer

The nineteen-cell output starts at an arbitrary destination. Scratch begins
immediately after that header; its reservation is translated only once.
-/

namespace ThreeSum.ThreeSumParameterResources
open _root_.ThreeSum.ThreeSumParameterResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 14000


def cells (n : ℕ) : ℕ := 19+_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.space 0 n
def depth (n : ℕ) : ℕ := 464*_root_.ThreeSum.LightParameterInit.half n+6
def envelope (n : ℕ) : ℕ := 100000000000*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n
def need (n _U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need := ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.cells n,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.depth n⟩



















noncomputable section





end







end ThreeSum.ThreeSumParameterResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executed selected-color preprocessing fits the final time exponent

This charges the actual fixed256 program's complete time expression:
normalization and incidence construction, common-prime selection, local
cover and global keys, balanced wanted rows, shared source banks and the
retained result-header computation. Reporting and the outer color loop
remain separate composition obligations.
-/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def preprocessingTime (k n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.time n (n^k)

noncomputable section















end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The original source header after shared reporting and dense initialization

The prefixProgram returns the source header unchanged. The reporting header starts
eight cells later, and its field six contains the initialized dense counter.
All contracts retain the same normalized A, B and C witnesses.
-/

namespace ThreeSum.EncodedColorReportingData
open _root_.ThreeSum.EncodedColorReportingData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000



def Output (μ : ℕ → ℤ) (free n : ℕ) (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1))
    (x : Fin n → ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    r=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC : ℤ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC











end ThreeSum.EncodedColorReportingData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute both reporting preparations from the original encoded-color payload

The shared catalog bank is constructed once. Its returned free pointer is
passed directly to dense initialization, which reads the original arrays,
actual candidate records, selected modulus and prime pool from memory.
-/

namespace ThreeSum.LightThreeSumReportingSetup
open _root_.ThreeSum.LightThreeSumReportingSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

def body (pBank pDense : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBank [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDense [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 0))

def joined : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.program _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.program

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.joined++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.body 75 96]



def time (n U R : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time n+
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n U R+200



end ThreeSum.LightThreeSumReportingSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact whole-scan YES and NO for the original physical domain

Every emitted slot has its own original owner bands. Prefix threshold
crossings are sound by distinct physical labels; if no crossing occurs,
the terminal tests cover every original zero through an actual emitted slot.
-/

namespace ThreeSum.ReportingHostWantedDecision
open _root_.ThreeSum.ReportingHostWantedDecision


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
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
open _root_.ThreeSum.LightReportingWantedScan
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 2100000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J)
    (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
    (3*(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs)).length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)

def slotHit (fB fC : ℕ→ℤ) (NB NC K i : ℕ) : Prop :=
  if hi : i<(μ free).toNat then
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g P rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H ⟨i,hi⟩) K
  else False









end Actual

end ThreeSum.ReportingHostWantedDecision

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact finite resources for constructing the dense-stop counter

The power-loop bound includes its actual `(base+1)^(J+1)` intermediate.
The modular scoring workspace remains affine in an arbitrary destination.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000













/-- Exactly the word reservation of the physical twenty-one-procedure setup. -/
def denseWord (n U : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) U (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+
    n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+
    _root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)+20

def denseCells (n U : ℕ) : ℕ := 4+_root_.ThreeSum.LightWeightedScore.space 0 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) U
def denseDepth (n : ℕ) : ℕ := Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)+8









end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000



def wantedNeed (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n*(U+1),_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n,_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n⟩



















noncomputable section













end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Affine resources for a color scan and its single parameter initialization

Per-color storage is reused after one six-cell color row. The full driver
uses nineteen persistent parameter cells and reclaims the initializer's
scratch before the scan. Both allocations have coefficient one on free.
-/

namespace ThreeSum.ThreeSumColorDriverResources
open _root_.ThreeSum.ThreeSumColorDriverResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

def overhead (n _U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨_root_.ThreeSum.LightColorScanHost.word n,6,_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)+4⟩

def need (colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need) (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(colorNeed n U).word+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.overhead n U).word,
    (colorNeed n U).cells+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.overhead n U).cells,
    (colorNeed n U).depth+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.overhead n U).depth⟩

def fullNeed (colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need) (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.need n U).word+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need colorNeed n U).word,
    max (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.need n U).cells (19+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need colorNeed n U).cells),
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.need n U).depth+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need colorNeed n U).depth+2⟩















noncomputable section









end
end ThreeSum.ThreeSumColorDriverResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Charge the executed parameter initialization

The actual square-root and quotient loops are bounded by the band root and
divisor. Polynomial storage envelopes do not replace these time bounds.
-/

namespace ThreeSum.ThreeSumParameterResources
open _root_.ThreeSum.ThreeSumParameterResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1900000
set_option maxRecDepth 14000

def timeBudget (n : ℕ) : ℕ :=
  10000*(_root_.ThreeSum.Scales.inputBits n+1+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n+_root_.ThreeSum.EncodedColorResources.localEnvelope n)



noncomputable section









end
end ThreeSum.ThreeSumParameterResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The wanted consumer's configuration from the actual retained color payload -/

namespace ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.ThreeSumWantedHostData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData



def recordCount (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC).length

def count (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum.WantedResidueKeys.total (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (_root_.ThreeSum.LightGuardedWanted.left (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)

def config (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum.LightReportingWantedDispatch.Config where
  layoutHeader := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC+4
  J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)
  h := _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)
  K := _root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  N := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length
  NB := B.length
  NC := C.length
  cover := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n
  counter := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC
  pairs := _root_.ThreeSum.LightWantedSetup.pairBase
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)
    (3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
  layerCount := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
  scheduleSize := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
  masks := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
  vals := _root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  owners := _root_.ThreeSum.LightBandRawA.ownerBase (_root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  records := _root_.ThreeSum.EncodedColorLayout.rec free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  pair := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC+3
  bank := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  srcB := _root_.ThreeSum.EncodedColorLayout.bv free n
  srcC := _root_.ThreeSum.EncodedColorLayout.cv free n
  report := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC
  modulus := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n



theorem count_read {μ : ℕ→ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)=
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC : ℤ) := H.wanted.1



end ThreeSum.ThreeSumWantedHostData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual time of the source, shared reporting and dense prefixProgram -/

namespace ThreeSum.EncodedColorReportingCosts
open _root_.ThreeSum.EncodedColorReportingCosts


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def setupTime (n U : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time n+
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n U (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))+200

def time (n U : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.time n U+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setupTime n U+1000

def preprocessingTime (k n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.time n (n^k)





noncomputable section













end
end ThreeSum.EncodedColorReportingCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual retained inputs of the physical wanted consumer

These are projections and finite bounds for the same normalized witnesses
retained by the selected-color pipeline. Physical A incidences preserve
their owner labels even when their integer values are equal.
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

abbrev records (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :=
  _root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC

def positions (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum.LightBandRawA.positionBase (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).vals
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)

def occurrence (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pair
    B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

























end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine


