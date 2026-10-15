-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle023
-- name    : ThreeSum1960614_Machine_Bundle023
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:01:25.864347+00:00
-- url     : https://prove2.me/theorems/d5f7aa98-6ccb-4048-9bbe-528eb5ad2575
-- title:
--   Source-stage preparation, common modulus chains, and complete local-cover construction
-- statement:
--   This bundle defines source and query programs together with their retained-data interfaces. Source preparation constructs radix coefficient rows, both raw endpoint arrays, and independent trimming flags. A source-band record stores its original start and length, residue-code pointer, histogram pointer, bucket offsets, and flat original-index fibers; its predicates give the exact value read from every stored component.
--
--   The common-prime chain begins at modulus $1$ and, at each natural level, invokes aggregate score minimization and multiplies the running modulus by the selected prime. It retains every prefix modulus. The color-to-catalog program executes coloring, class extraction, normalization, endpoint construction, all three rectangular owner tables, and packed $A$ incidences. Its output retains strictly sorted class representatives, membership in the original color classes, physical owner identities, and sorted-array positions.
--
--   For each occurrence vector, the retained-source host constructs compact masks, coefficient rows, endpoint hashes, and flags, then gathers from shared band histograms and forms both suffix-stage families. The canonical-box and explicit-leaf query programs build their own missing-subset enumerations inside the query mask and sum the appropriate stored evaluations. Their procedure interfaces identify all enumeration, addressing, lookup, and signed-evaluation subroutines.
--
--   The complete local-cover builder enumerates local vertices, constructs their Boolean rows, builds all candidate data, executes the deterministic greedy schedule, and gathers the exact selected occurrence rows. Terminal preparation builds the two actual endpoint-mask and independent-flag arrays needed by physical leaf reporting. Explicit time, space, and word functions retain the costs and storage of these constructions.
--
--   These definitions connect original signed input arrays and executable cover construction to the stored source transforms and sparse queries used in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourcePreparation.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceBandData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandPrimeChain.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandRawAColor.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceRetainedHost.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCanonicalBoxSum.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightExplicitSum.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverBuild.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingTerminalPreparation.lean

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
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightBandPrimeChain
end ThreeSum.LightBandPrimeChain
namespace ThreeSum.LightBandRawAColor
end ThreeSum.LightBandRawAColor
namespace ThreeSum.LightBlockSourceRetainedHost
end ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum.LightCanonicalBoxSum
end ThreeSum.LightCanonicalBoxSum
namespace ThreeSum.LightExplicitSum
end ThreeSum.LightExplicitSum
namespace ThreeSum.LightLocalCoverBuild
end ThreeSum.LightLocalCoverBuild
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingTerminalPreparation
end ThreeSum.LightReportingTerminalPreparation
namespace ThreeSum.LightSourcePreparation
end ThreeSum.LightSourcePreparation
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SourceBandData
end ThreeSum.SourceBandData
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
end ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
end ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum
end ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum
namespace ThreeSum1960614.Machine.ThreeSum.LightExplicitSum
end ThreeSum1960614.Machine.ThreeSum.LightExplicitSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation
namespace ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandData
end ThreeSum1960614.Machine.ThreeSum.SourceBandData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Actual endpoint and independent-flag preparation from stored selected maps

The host constructs radix coefficient rows, both raw endpoint arrays, and
both independent trim-flag arrays. All four arrays are retained for the
original-input histogram/source-stage constructors.
-/

namespace ThreeSum.LightSourcePreparation
open _root_.ThreeSum.LightSourcePreparation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

/-- Arguments: J, L, required row size, local prime, cap; occurrence/maps/
candidate/table pointers; mask array/count; coefficient rows, raw arrays,
paired flag arrays, and reusable scratch. -/
def body (pHashes pFlags : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHashes [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 19] 20) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pFlags [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19] 20))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pHashes : ℕ
  pFlags : ℕ
  hashes : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs P pHashes
  flags : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs P pFlags
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.body pHashes pFlags)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.body 1 7,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.body 2 5,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.body 3 4,
    _root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightScaleArray.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.body 3 6,_root_.ThreeSum1960614.Machine.ThreeSum.LightOneHot.body 6,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.body 8,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.body 9 12,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.body 10 11,_root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body 11,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.body 13,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.body 14 15 16,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.body,
    _root_.ThreeSum1960614.Machine.Light.emodBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.body]

def programProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.program 0 :=
  ⟨1,7,⟨2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨8,⟨9,10,11,12,rfl,rfl,rfl,⟨13,14,15,16,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩



end ThreeSum.LightSourcePreparation

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained original-band headers, histograms, and physical position fibers -/

namespace ThreeSum.SourceBandData
open _root_.ThreeSum.SourceBandData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout

structure At (μ : ℕ → ℤ) (f : ℕ → ℤ) (base n g p m : ℕ) (shift : ℤ) (i : ℕ) : Prop where
  headStart : μ (base+6*i) = (_root_.ThreeSum.BandPartition.start g i : ℤ)
  headLength : μ (base+6*i+1) = (_root_.ThreeSum.SourceBandLayout.len n g i : ℤ)
  headCodes : μ (base+6*i+2) = (_root_.ThreeSum.SourceBandLayout.codes base n g m i : ℤ)
  headHist : μ (base+6*i+3) = (_root_.ThreeSum.SourceBandLayout.hist base n g m i : ℤ)
  headOffsets : μ (base+6*i+4) = (_root_.ThreeSum.SourceBandLayout.offsets base n g m i : ℤ)
  headFlat : μ (base+6*i+5) = (_root_.ThreeSum.SourceBandLayout.flat base n g m i : ℤ)
  codesRead : ∀ j < _root_.ThreeSum.SourceBandLayout.len n g i, μ (_root_.ThreeSum.SourceBandLayout.codes base n g m i+j) = (_root_.ThreeSum.SourceBandLayout.key f g p m shift i j : ℤ)
  histRead : ∀ r < m, μ (_root_.ThreeSum.SourceBandLayout.hist base n g m i+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.SourceBandLayout.key f g p m shift i) r (_root_.ThreeSum.SourceBandLayout.len n g i) : ℤ)
  buckets : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ (_root_.ThreeSum.SourceBandLayout.key f g p m shift i) (_root_.ThreeSum.SourceBandLayout.len n g i) m
    (_root_.ThreeSum.SourceBandLayout.offsets base n g m i) (_root_.ThreeSum.SourceBandLayout.flat base n g m i)















end ThreeSum.SourceBandData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute one common modulus chain for all candidate owners

The loop calls the verified aggregate minimum at every level. Its output is
the same common modulus whose contraction is proved in `BandPrimeChoice`.
All prefix moduli are retained; every score computation reuses the region
beyond the prefix array.
-/

namespace ThreeSum.LightBandPrimeChain
open _root_.ThreeSum.LightBandPrimeChain


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandPrimeChoice
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Arguments: the three original sorted arrays and lengths, band size,
candidate records and count, prime array and count, levels, free address. -/
def body (pMinimum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 13)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 14 (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pMinimum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 16] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 15))) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 13))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 13))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain.body 17]







def Inv (μ : ℕ → ℤ) (qs : ℕ → ℕ)
    (a b c nA nB nC g recs R aux s levels free i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (pval : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [a,b,c,nA,nB,nC,g,recs,R,aux,s,levels,free,
      qs i,i,pval,free+levels+1],ν⟩ ∧
    (∀ j ≤ i, ν (free+j)=(qs j : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs aux s levels free maxMod U Y : ℕ}



end ThreeSum.LightBandPrimeChain

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original input to the retained owner and A-incidence catalog

The selected index coloring, class extraction, normalization, endpoint
construction, three rectangular owner tables, four-cell owner records, and
packed A-incidence rows are all executed by this fixed program. The rows
retain physical owner identities and sorted-array coordinates. Membership
in the original color classes is retained separately by `Represents`.
-/

namespace ThreeSum.LightBandRawAColor
open _root_.ThreeSum.LightBandRawAColor


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000

/-- The existing color/band arguments, followed by records and incidence
value destinations. -/
def body (pColor pCatalog : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pColor [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20] 23) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCatalog [_root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 22] 0))











def Output (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g)
    (originalA originalB originalC : List ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC
    r = ((_root_.ThreeSum.BandRawA.items A.length g rs).length : ℤ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ tables
        (_root_.ThreeSum.BandPartition.family (fun i => A.getD i 0) A.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsA))
        (_root_.ThreeSum.BandPartition.family (fun i => B.getD i 0) B.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsB))
        (_root_.ThreeSum.BandPartition.family (fun i => C.getD i 0) C.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsC)) ∧
      _root_.ThreeSum1960614.Machine.Light.Seg μ rec (_root_.ThreeSum.BandCandidateRows.cells rs) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals (_root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g)
        (_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g)
        (fun i => A.getD i 0) (_root_.ThreeSum.BandRawA.items A.length g rs)



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pColor : ℕ
  pCatalog : ℕ
  color : _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs P pColor
  catalog : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs P pCatalog
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.body pColor pCatalog)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



/-- The verified color/band prefix retains its original procedure indices. -/
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.body 28 38,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.body 29 32 35,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.body 30,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow.body 31,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesCell.body _root_.ThreeSum.BandCandidateRows.Mode.bc,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.body 33,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow.body 34,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesCell.body _root_.ThreeSum.BandCandidateRows.Mode.ab,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.body 36,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow.body 37,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesCell.body _root_.ThreeSum.BandCandidateRows.Mode.ac,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA.body 39,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAStep.body 40,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.body 41 42,_root_.ThreeSum1960614.Machine.Light.copyBody,_root_.ThreeSum1960614.Machine.Light.fillBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.body 20 27]

def programProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.program 43 where
  pColor := 20
  pCatalog := 27
  color := {
    pClasses := 21
    pBands := 0
    classes := ⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
    bands := {
      pPrepare := 1
      pEnumerate := 12
      prepare := ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
      enumerate := ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
      main := rfl }
    main := rfl }
  catalog := {
    pCandidates := 28
    pRaw := 38
    candidates := ⟨29,32,35,30,33,36,31,34,37,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    raw := ⟨39,40,41,42,rfl,rfl,rfl,rfl,rfl⟩
    main := rfl }
  main := rfl







end ThreeSum.LightBandRawAColor

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Per-occurrence source construction with shared band histograms

For a fixed band pair, modulus, and common offset, this host constructs its
own compact masks, coefficient rows, endpoint arrays, and independent flags.
It then gathers from the retained band histograms and constructs both exact
original suffix-stage families. Histogram scans belong outside this loop.
-/

namespace ThreeSum.LightBlockSourceRetainedHost
open _root_.ThreeSum.LightBlockSourceRetainedHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild

set_option maxHeartbeats 4000000
set_option maxRecDepth 14000

def body (pEnum pPrepare pStages : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 25] 26) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrepare [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25] 27) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pStages [_root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 25, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 26] 27) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pStages [_root_.ThreeSum1960614.Machine.Light.v 18, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 19) (_root_.ThreeSum1960614.Machine.Light.v 26), _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 25, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 26] 27))))

def time (h J cut : ℕ) : ℕ :=
  _root_.ThreeSum.LightDownsetEnumerationSetup.time (J*(464*h)) cut+
  _root_.ThreeSum.LightSourcePreparation.time (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)+
  _root_.ThreeSum.LightSourceRetainedStages.time (J*(464*h)) cut (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+
  _root_.ThreeSum.LightSourceRetainedStages.time (J*(464*h)) cut (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+500

def space (work h J : ℕ) : ℕ :=
  max (work+(J*(464*h)+1))
    (max (_root_.ThreeSum.LightSourcePreparation.space work J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h))
      (_root_.ThreeSum.LightSourceRetainedStages.space work (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)))

def word (NL NR h J : ℕ) : ℕ :=
  2^(J*(464*h)+1)+
  _root_.ThreeSum.LightSourcePreparation.word J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    ((464*h).choose h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)+
  _root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) NL+
  _root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) NR

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pDownset : ℕ
  pLayer : ℕ
  pPrepare : ℕ
  pStages : ℕ
  enumMain : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumerationSetup.body pPowers pDownset)
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  downset : P[pDownset]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.body pLayer)
  layer : P[pLayer]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pLayer)
  prepare : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs P pPrepare
  stages : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs P pStages
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.body pEnum pPrepare pStages)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightBlockSourceRetainedHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete execution of the canonical box part of a sparse query

The query builds its own missing-subset array inside the actual query mask,
then evaluates every canonical box. Enumeration completeness and uniqueness
are discharged by the verified query-coordinate construction.
-/

namespace ThreeSum.LightCanonicalBoxSum
open _root_.ThreeSum.LightCanonicalBoxSum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

/-- Procedure layout shared by complete sparse queries. -/
structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pEnum pSum : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pCore : ℕ
  pBox : ℕ
  pMinimum : ℕ
  pLookup : ℕ
  pSize : ℕ
  pAddress : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pRank : ℕ
  pOffset : ℕ
  enumerate : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body pPowers pErase)
  erase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase)
  core : P[pCore]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBoxSum.body pBox)
  box : P[pBox]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryBox.body pMinimum pLookup)
  minimum : P[pMinimum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum.body pPowers pErase)
  lookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.body pSize pAddress)
  size : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.body pSetup pOffset)
  table : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body

/-- Width, cutoff, query cardinality and mask, missing cardinality,
box-table base, output-mask buffer, polynomial scratch. -/
def body (pEnum pSum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 7] 0))













end ThreeSum.LightCanonicalBoxSum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete execution of the explicit leaves of a sparse query

The loop visits only missing-set cardinalities below the threshold. Each
layer is enumerated inside the actual query mask and immediately evaluated.
One reusable mask buffer is sufficient; all source stages are preserved.
-/

namespace ThreeSum.LightExplicitSum
open _root_.ThreeSum.LightExplicitSum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pEnum pSum : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pCore : ℕ
  pLeaf : ℕ
  pLookup : ℕ
  pSign : ℕ
  pSize : ℕ
  pAddress : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pRank : ℕ
  pOffset : ℕ
  enumerate : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body pPowers pErase)
  erase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase)
  core : P[pCore]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightLeafSum.body pLeaf)
  leaf : P[pLeaf]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeaf.body pLookup pSign)
  lookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.body pSize pAddress)
  sign : P[pSign]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSign.body
  size : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.body pSetup pOffset)
  table : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body

def roundBody (pEnum pSum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 13] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 17)))))

/-- Width, source cutoff, suffix stage, two prefixes, query cardinality and
mask, missing threshold, two source bases, reusable mask buffer and scratch. -/
def body (pEnum pSum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 15 (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.ThreeSum.LightExplicitSum.roundBody pEnum pSum)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 14))))

















end ThreeSum.LightExplicitSum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete local-cover construction from the initialized parameters

The enumerated local vertices and their Boolean coordinate rows are built
inside this program. It then constructs all candidate tables, executes the
original greedy schedule, and gathers the exact occurrence coefficient
rows. There are no supplied mask, coefficient, histogram, or matrix tables.
-/

namespace ThreeSum.LightLocalCoverBuild
open _root_.ThreeSum.LightLocalCoverBuild


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables

set_option maxHeartbeats 1500000
set_option maxRecDepth 6000

def body (pEnum pBits pHost : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 14] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBits [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 14] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHost [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16] 0)))

def time (h : ℕ) : ℕ := _root_.ThreeSum.LightSubsetEnumerationSetup.time (464*h) h+
  _root_.ThreeSum.LightMaskBitTable.time (464*h) (_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h)+
  _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time h+200

def word (h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word h+2^(464*h+1)

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pEnumRec : ℕ
  pBits : ℕ
  pOneBits : ℕ
  pErase : ℕ
  pHost : ℕ
  enum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body pPowers pEnumRec)
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  enumRec : P[pEnumRec]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnumRec)
  bits : P[pBits]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable.body pOneBits)
  oneBits : P[pOneBits]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.body pPowers pErase)
  erase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase)
  host : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs P pHost
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.body pEnum pBits pHost)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightLocalCoverBuild

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal endpoint and independent flag arrays

The two complete endpoint-mask arrays are prepared using the actual selected
occurrence, coefficient, and local trimming tables. Their buffers are
allocated by the host. Only the left orientation of the first array and the
right orientation of the second array are needed by the physical leaf scan.
-/

namespace ThreeSum.LightReportingTerminalPreparation
open _root_.ThreeSum.LightReportingTerminalPreparation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 2600000
set_option maxRecDepth 12000









/-- J, L, h, local prime and cap; retained control pointers; two full-mask
arrays and their count; output base; bit, row, and arithmetic scratch. -/
def body (pPrepare : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 17)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 4) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.k 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 17))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 21 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 20) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 22 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 21) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 23 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 18))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.v 17))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 17)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 25) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 27 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 26) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrepare [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16] 28) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrepare [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 23, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16] 28) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.v 18))))))))))))))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.body 0]
def time (h J n : ℕ) : ℕ := 2*_root_.ThreeSum.LightSourcePreparation.time n J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)+800

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingTerminalPreparation

end ThreeSum1960614.Machine


