-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle041
-- name    : ThreeSum1960614_Machine_Bundle041
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:22:50.586239+00:00
-- url     : https://prove2.me/theorems/346abc2c-3e37-4f90-81e8-53d71a3e42fd
-- title:
--   Complete original-input 3SUM solver and its exact finite-cutoff hybrid
-- statement:
--   This bundle assembles the concrete deterministic integer 3SUM solver. The wanted-consumer interface labels each physical record by its original incidence and global output, defines its original fiber, root mass, terminal-hit predicate, and guard-sensitive execution time, and follows the frozen ascending order of the actual pair array. The threshold is the representation cap multiplied by the false score of the actually selected common modulus.
--
--   For one selected color, the program executes the complete encoding-and-reporting prelude, reads its retained counter pointer, and invokes the physical wanted scan. Its relative resource record combines persistent prelude storage with reused scratch. The complete fast solver then initializes parameters and scans every coloring; it has $537$ procedures and uses the resulting selected-color correctness law.
--
--   For fixed magnitude exponent $k\in\mathbb N$ and cutoff $N\in\mathbb N$, the hybrid caller first tests the actual size $n$. If $n<N$, it invokes the exact original-position triple scan. Otherwise it computes $n^k$; it again uses the triple scan when the supplied input bound $U$ exceeds that value, and uses the fast solver in the remaining case. Both branches reuse the same free address. The hybrid need record reserves the larger branch cell and depth requirements and includes the actual scalar controls and intermediate powers in its word requirement.
--
--   The final program chooses $N$ from the proved uniform readiness conditions for $k$. Its $543$ procedures comprise the fast library, relocated four-procedure triple solver, integer-power procedure, and hybrid caller. The associated need and time functions apply at every size and supplied magnitude, including zero. The intended decision concerns three distinct original positions and preserves all memory before the supplied free address.
--
--   These definitions are the final executable assembly used to connect the complete runtime analysis to the exact word-RAM end statement.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostWantedConsumerData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumFastResourcesColor.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostWantedConsumerScanData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumFastResourcesDriver.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumColor.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumFastResourcesHybrid.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumConcreteFast.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ThreeSumFastResourcesHybridPolynomial.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumHybridCore.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightThreeSumHybrid.lean

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.LightThreeSumColor
end ThreeSum.LightThreeSumColor
namespace ThreeSum.LightThreeSumConcreteFast
end ThreeSum.LightThreeSumConcreteFast
namespace ThreeSum.LightThreeSumHybrid
end ThreeSum.LightThreeSumHybrid
namespace ThreeSum.LightThreeSumHybridCore
end ThreeSum.LightThreeSumHybridCore
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
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
namespace ThreeSum.ThreeSumFastResourcesColor
end ThreeSum.ThreeSumFastResourcesColor
namespace ThreeSum.ThreeSumFastResourcesDriver
end ThreeSum.ThreeSumFastResourcesDriver
namespace ThreeSum.ThreeSumFastResourcesHybrid
end ThreeSum.ThreeSumFastResourcesHybrid
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
namespace ThreeSum1960614.Machine.ThreeSumApsp.Spec
end ThreeSum1960614.Machine.ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

namespace ThreeSum1960614.Machine

/-! # Physical labels and original-fiber semantics for the retained consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum.ReportingHostWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 16000





abbrev Label (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.ReportingHostWantedOriginal.AType A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))

def fiber (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) A.length B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w

def labelMass (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.fiber n A B C hsA hsB hsC w) w

def labelHit (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC) : Prop :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) A.length B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w (_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))

def recordTime (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC) (output old threshold : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) (fun j => B.getD j 0) w)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) (fun j => C.getD j 0) w)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.leftCount (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) B.length w)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.rightCount (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) C.length w) old threshold
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.fiber n A B C hsA hsB hsC w) w
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalogs A.length B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) w output) (_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))





variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

def slot (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    Fin (μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)).toNat :=
  ⟨s.val,by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count_read H,Int.toNat_natCast]; exact s.isLt⟩

def label (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H.wanted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s)











end ThreeSum.ReportingHostWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One affine allocation for a complete selected color

The prefixProgram retains its source and reporting catalogs, ending with the dense
counter. The wanted scan reuses scratch beginning four cells after that
counter. The two exact resource records are combined without bounding the
absolute starting address.
-/

namespace ThreeSum.ThreeSumFastResourcesColor
open _root_.ThreeSum.ThreeSumFastResourcesColor


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

def need (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).word+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).word,
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).cells+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).cells,
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).depth+(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).depth+3⟩















noncomputable section



end
end ThreeSum.ThreeSumFastResourcesColor

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Frozen physical order and the exact cost of the ascending consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum.ReportingHostWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 2200000
set_option maxRecDepth 17000

def threshold (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC

variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

def mass (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ→ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H.wanted (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length

def hit (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ→Prop :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit H.wanted (fun j => B.getD j 0) (fun j => C.getD j 0)
    B.length C.length (_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))

def stepTime (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (i : ℕ) : ℕ :=
  if hi : i<_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC then
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H ⟨i,hi⟩)
        (_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) i)
        (_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC))
  else 0

def scanTime (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ :=
  _root_.ThreeSum.LightReportingWantedScan.time (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime H) (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)













end ThreeSum.ReportingHostWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Concrete resources for the complete537-procedure fast driver

The nineteen parameter cells and six reusable color-row cells precede the
selected-color allocation. Parameter-initialization scratch is reclaimed.
The original free address has coefficient one in every memory premise.
-/

namespace ThreeSum.ThreeSumFastResourcesDriver
open _root_.ThreeSum.ThreeSumFastResourcesDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

set_option maxHeartbeats 1700000
set_option maxRecDepth 15000

def need : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need



















noncomputable section



end
end ThreeSum.ThreeSumFastResourcesDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute a complete selected color of the original input

The fixed355 prefixProgram prepares the actual encoding and shared source bank.
The fixed154 header caller then executes the physical wanted scan. Their
verified semantic and time connections yield the original color witness.
-/

namespace ThreeSum.LightThreeSumColor
open _root_.ThreeSum.LightThreeSumColor


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 2800000
set_option maxRecDepth 18000

def body (pPrelude pWanted : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrelude [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 14)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pWanted [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6] 0)))

def joined : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program
  _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.joined++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.body 354 508]





end ThreeSum.LightThreeSumColor

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Affine resources for the actual finite-cutoff hybrid

The fast branch uses the computed magnitude `n^κ`; the fallback retains
the supplied magnitude `U`. Both branches reuse the same free address.
The fixed cutoff and exponent are included among the actual scalar word
controls, together with every intermediate integer power.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid
open _root_.ThreeSum.ThreeSumFastResourcesHybrid


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 16000



def need (κ cutoff n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n (n^κ)).word+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.need n U).word+_root_.ThreeSum.ThreeSumFastResourcesHybrid.controls κ cutoff n,
    max (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n (n^κ)).cells (_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.need n U).cells,
    max (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n (n^κ)).depth (_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.need n U).depth+3⟩





















end ThreeSum.ThreeSumFastResourcesHybrid

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The concrete537-procedure fast solver

The actual selected-color executable supplies the color law of the closed
driver. The parameter header is built once, followed by one reusable color
row and the reusable selected-color allocation.
-/

namespace ThreeSum.LightThreeSumConcreteFast
open _root_.ThreeSum.LightThreeSumConcreteFast


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program 509

def need : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need

def time (k n : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget k n) n







noncomputable section









end
end ThreeSum.LightThreeSumConcreteFast

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial hybrid limits with the computed magnitude substituted

The exponent and cutoff are fixed program parameters. The polynomial
bound is valid for every input size and supplied magnitude, including
zero, and does not rely on eventual growth to justify substitution.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid
open _root_.ThreeSum.ThreeSumFastResourcesHybrid


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 300000
set_option maxRecDepth 16000



def poweredDriverNeed (κ n _U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n (n^κ)

noncomputable section







end
end ThreeSum.ThreeSumFastResourcesHybrid

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact assembly and execution of the final hybrid caller

The supplied first537 procedures are followed by the relocated four-procedure
original-triple solver, one integer-power procedure, and the hybrid caller.
The two runtime guards use the actual size and the supplied magnitude bound.
-/

namespace ThreeSum.LightThreeSumHybridCore
open _root_.ThreeSum.LightThreeSumHybridCore


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

def body (κ cutoff : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k cutoff)))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.call 540 [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 2,_root_.ThreeSum1960614.Machine.Light.v 3] 0)
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call 541 [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.k κ] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.call 540 [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.call 536 [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3] 0))))

def libraries (fastP : _root_.ThreeSum1960614.Machine.Light.Program) : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program fastP _root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.program

def program (fastP : _root_.ThreeSum1960614.Machine.Light.Program) (κ cutoff : ℕ) : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries fastP++[_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body κ cutoff]













end ThreeSum.LightThreeSumHybridCore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The complete543-procedure original-input solver

For each fixed magnitude exponent, the cutoff is chosen from the proved
uniform parameter conditions. The program tests that cutoff, computes the
integer power, and uses the exact original-triple fallback whenever needed.
Every branch returns the original distinct-position decision and preserves
all memory before the supplied free address.
-/

namespace ThreeSum.LightThreeSumHybrid
open _root_.ThreeSum.LightThreeSumHybrid


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

noncomputable section

def program (κ : ℕ) : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.program κ
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.cutoff κ)

def need (κ : ℕ) : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.cutoff κ)

def time (κ : ℕ) : ℕ→ℕ→ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.cutoff κ)











end
end ThreeSum.LightThreeSumHybrid

end ThreeSum1960614.Machine


