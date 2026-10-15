-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle024
-- name    : ThreeSum1960614_Machine_Bundle024
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:03:17.503926+00:00
-- url     : https://prove2.me/theorems/1086834b-b5b6-4ae1-8327-5d1fda4122a0
-- title:
--   Retained source banks, sparse queries, and executed prime metadata
-- statement:
--   This library defines the executable and stored-data interfaces for signed compact-table cells, source-band histograms, retained source banks, sparse subset queries, local-cover layouts, and the selected color's common-prime metadata. Procedure-placement structures identify the concrete leaf, address, subset-enumeration, histogram, transform, and arithmetic helpers in a finite light-language program. For initial memory $\mu$, source functions $f_L,f_R$, source lengths $N_L,N_R$, band size $g$, moduli $p,m$, and signed shift $d$, the paired-band predicate records every left and right band catalog plus a shared zero histogram; its stored form also records the packed header.
--
--   For local block size $h$, block count $J$, and compact cutoff $c$, a retained source-bank step builds both source-stage families from the previously constructed histograms and writes their two pointers. The closed retained-source program has 41 procedure bodies. Local-cover address definitions explicitly reserve the vertices, Boolean rows, coefficients, raw hashes, both histograms, cover matrix, schedule outputs, and reusable scratch. The sparse query constructs the mask layers it uses, evaluates explicit signed leaves and canonical boxes, and accumulates their contributions. Prime-scale and cost interfaces retain the actual modulus selected from physical owner records and their own source bands.
--
--   These definitions ensure that source preprocessing, common-modulus selection, and sparse reporting are charged for the programs that actually run in the deterministic integer 3SUM construction. They preserve physical input multiplicities and provide the finite resource quantities used by the dependent correctness and runtime theorems.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSignedLeafCell.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandStep.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceBandPairData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BandPrimeScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/EncodedColorPrimeData.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceBatchStep.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceRetainedProgram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSignedLeafBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBandHistSelect.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSparseQuery.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BandPrimeCosts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorPrimeCore.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverMagnitude.lean

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
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandPrimeCosts
end ThreeSum.BandPrimeCosts
namespace ThreeSum.BandPrimeScales
end ThreeSum.BandPrimeScales
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorPrimeData
end ThreeSum.EncodedColorPrimeData
namespace ThreeSum.LightBlockSourceBatchStep
end ThreeSum.LightBlockSourceBatchStep
namespace ThreeSum.LightBlockSourceRetainedProgram
end ThreeSum.LightBlockSourceRetainedProgram
namespace ThreeSum.LightEncodedColorLayout
end ThreeSum.LightEncodedColorLayout
namespace ThreeSum.LightEncodedColorPrimeCore
end ThreeSum.LightEncodedColorPrimeCore
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSignedLeafCell
end ThreeSum.LightSignedLeafCell
namespace ThreeSum.LightSourceBandBatch
end ThreeSum.LightSourceBandBatch
namespace ThreeSum.LightSourceBandHistSelect
end ThreeSum.LightSourceBandHistSelect
namespace ThreeSum.LightSourceBandStep
end ThreeSum.LightSourceBandStep
namespace ThreeSum.LightSparseQuery
end ThreeSum.LightSparseQuery
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
end ThreeSum.SourceBandPairSlices
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
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeScales
end ThreeSum1960614.Machine.ThreeSum.BandPrimeScales
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafCell
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafCell
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep
namespace ThreeSum1960614.Machine.ThreeSum.LightSparseQuery
end ThreeSum1960614.Machine.ThreeSum.LightSparseQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-! # Writing one initial signed-product cell at its compact address -/

namespace ThreeSum.LightSignedLeafCell
open _root_.ThreeSum.LightSignedLeafCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

/-- The actual leaf and address subprograms, with all of their dependencies. -/
structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pLeaf pAddress : ℕ) where
  (pUnion pLookup pSign pSize pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ)
  leaf : P[pLeaf]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.body pUnion pLookup pSign)
  union : P[pUnion]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskUnion.body pPowers pErase)
  lookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.body pSize pAddress)
  sign : P[pSign]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSign.body
  size : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.body pSetup pOffset)
  setup : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body
  erase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase)

/-- Width, source cutoff, suffix stage, both prefix cardinalities and masks,
leaf cardinality and mask, source bases, destination, polynomial scratch. -/
def body (pLeaf pAddress : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLeaf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 12] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pAddress [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 12] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.v 13))))











end ThreeSum.LightSignedLeafCell

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One actual original-band histogram, buckets, and six pointer headers -/

namespace ThreeSum.LightSourceBandStep
open _root_.ThreeSum.LightSourceBandStep


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

def tailBody (pOriginal : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 19) (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pOriginal [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 13), _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 11] 21) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.v 13)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 15)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 17)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 16)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 18)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 12))) (_root_.ThreeSum1960614.Machine.Light.k 5)) (_root_.ThreeSum1960614.Machine.Light.v 20))))))))))))))

def body (pOriginal : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.v 1)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.tailBody pOriginal))))








structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pOriginal : ℕ
  original : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOriginal.Procs P pOriginal
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.body pOriginal)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightSourceBandStep

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition












structure Data (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ) : Prop where
  left : ∀ i < _root_.ThreeSum.BandPartition.size NL g, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At μ fL (_root_.ThreeSum.SourceBandPairData.leftBase base) NL g p m 0 i
  right : ∀ i < _root_.ThreeSum.BandPartition.size NR g, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At μ fR (_root_.ThreeSum.SourceBandPairData.rightBase base NL g m) NR g p m shift i
  zero : ∀ r ≤ m, μ (_root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m+r)=0

structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ)
    extends _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Data μ fL fR base NL NR g p m shift : Prop where
  heads : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.ThreeSum.SourceBandPairData.header base NL NR g m)









end ThreeSum.SourceBandPairData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales
open _root_.ThreeSum.BandPrimeScales


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

def modulus (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) : ℕ :=
  _root_.ThreeSum.LightBandPrimeConstruction.modulus (_root_.ThreeSum.Scales.primeWindow n) nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    A B C rs (_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)

def score (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) : ℕ :=
  _root_.ThreeSum.BandWeightedScore.score (_root_.ThreeSum.LightPrimePool.prime (_root_.ThreeSum.Scales.primeWindow n))
    (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) q nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) A B C rs























end ThreeSum.BandPrimeScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained common-prime metadata for one actual color execution -/

namespace ThreeSum.EncodedColorPrimeData
open _root_.ThreeSum.EncodedColorPrimeData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light







structure Stored (μ : ℕ → ℤ) (free M y : ℕ) (qs : ℕ → ℕ) : Prop where
  header : _root_.ThreeSum1960614.Machine.Light.Seg μ free (_root_.ThreeSum.EncodedColorPrimeData.values free M y (qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y)))
  pool : _root_.ThreeSum1960614.Machine.Light.SegN μ (_root_.ThreeSum.EncodedColorPrimeData.poolBase free) (_root_.ThreeSum.LightPrimePool.values y)
  prefixes : ∀ i ≤ _root_.ThreeSum.LightBandPrimeDepth.depth M y, μ (_root_.ThreeSum.EncodedColorPrimeData.prefixBase free y+i)=(qs i : ℤ)





end ThreeSum.EncodedColorPrimeData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# One actual retained source bank and its two pointer headers

The program computes the bank's addresses, constructs both original source
stage families from the shared histograms, and writes their two pointers.
Every earlier bank and every input before the header array is retained.
-/

namespace ThreeSum.LightBlockSourceBatchStep
open _root_.ThreeSum.LightBlockSourceBatchStep


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
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

/-- The first fourteen arguments are the original retained-host controls and
inputs. The remaining arguments are header base, compact capacity, bank count,
bank base, bank stride, shared scratch addresses, and the current bank index. -/
def body (pSource : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 24 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 23) (_root_.ThreeSum1960614.Machine.Light.v 18)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 25 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 24) (_root_.ThreeSum1960614.Machine.Light.v 15))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 26 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 25) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 27 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 26) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 28 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 27) (_root_.ThreeSum1960614.Machine.Light.v 15))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 29 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 28) (_root_.ThreeSum1960614.Machine.Light.v 15))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 30 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 29) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 15))) (_root_.ThreeSum1960614.Machine.Light.k 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 31 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 30) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 15)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSource [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 24, _root_.ThreeSum1960614.Machine.Light.v 25, _root_.ThreeSum1960614.Machine.Light.v 26, _root_.ThreeSum1960614.Machine.Light.v 27, _root_.ThreeSum1960614.Machine.Light.v 28, _root_.ThreeSum1960614.Machine.Light.v 29, _root_.ThreeSum1960614.Machine.Light.v 30, _root_.ThreeSum1960614.Machine.Light.v 31, _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 21, _root_.ThreeSum1960614.Machine.Light.v 22] 32) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 23))) (_root_.ThreeSum1960614.Machine.Light.v 30)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 23))) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 31))))))))))))

def time (h J cut : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.time h J cut+500

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pSource : ℕ
  source : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs P pSource
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.body pSource)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightBlockSourceBatchStep

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Literal efficient program for original source-stage construction

The 41 procedures construct all occurrence-dependent data and reuse the
original band histograms. The cost has no factor proportional to the number
of original input incidences or the dense global modulus in this inner loop.
-/

namespace ThreeSum.LightBlockSourceRetainedProgram
open _root_.ThreeSum.LightBlockSourceRetainedProgram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.body 1 5 22,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumerationSetup.body 2 3,_root_.ThreeSum1960614.Machine.Light.powTableBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.body 4,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body 4,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.body 6 12,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.body 7 10,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.body 8 9,_root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightScaleArray.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.body 8 11,_root_.ThreeSum1960614.Machine.ThreeSum.LightOneHot.body 11,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.body 13,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.body 14 17,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.body 15 16,_root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body 16,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.body 18,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.body 19 20 21,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.body,_root_.ThreeSum1960614.Machine.Light.emodBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.body 23 25,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceGather.body 24,_root_.ThreeSum1960614.Machine.Light.emodBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.body 26 27,_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body 31 38,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass.body 28 29,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body 36 40,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaBatch.body 30,_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.body 31 38 39 37,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.body 32 36 37,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildBody 33 34,_root_.ThreeSum1960614.Machine.Light.fillBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.rowBody 35,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody,_root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rankBody 37,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body 39,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body 40]







def factor (h J : ℕ) : ℕ :=
  1200*(J*(464*h)+1)^2+300*(J+1)*(464*h+1)+600*(J*(464*h)+1)+
  (300*(J*(464*h)+1)^2+J*(150*(464*h)+464*(Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+1)+250)+400)+
  314*(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+1)+12000*(J*(464*h)+1)^4+1122



end ThreeSum.LightBlockSourceRetainedProgram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum.LightLocalCoverLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables

def vertices (h : ℕ) : ℕ := _root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h
def bitPtr (base h : ℕ) : ℕ := base+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h
def maps (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h*(464*h)
def raw0 (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*(2*(464*h))
def raw1 (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 base h+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h
def hist0 (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 base h+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h
def hist1 (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h
def matrixPtr (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h
def work (base h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h
def scheduleMaps (base h : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h+_root_.ThreeSum.LightCoverGreedy.total (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)
def candidates (base h : ℕ) : ℕ := _root_.ThreeSum.LightCoverGreedy.out (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)

def space (base h : ℕ) : ℕ :=
  max (_root_.ThreeSum.LightLocalCoverCandidate.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h) (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)))









end ThreeSum.LightLocalCoverLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Initial signed-product table writes on one actual mask layer -/

namespace ThreeSum.LightSignedLeafBatch
open _root_.ThreeSum.LightSignedLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



/-- Width, source cutoff, suffix stage, both prefix cardinalities and masks,
layer cardinality, number of masks, mask base, source bases, output, scratch. -/
def body (pCell : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 14 (_root_.ThreeSum1960614.Machine.Light.v 8)
    (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCell [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 2,_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4,_root_.ThreeSum1960614.Machine.Light.v 5,_root_.ThreeSum1960614.Machine.Light.v 6,_root_.ThreeSum1960614.Machine.Light.v 7,_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 14))),
      _root_.ThreeSum1960614.Machine.Light.v 10,_root_.ThreeSum1960614.Machine.Light.v 11,_root_.ThreeSum1960614.Machine.Light.v 12,_root_.ThreeSum1960614.Machine.Light.v 13] 15)













end ThreeSum.LightSignedLeafBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual once-per-original-band histogram and bucket loop -/

namespace ThreeSum.LightSourceBandBatch
open _root_.ThreeSum.LightSourceBandBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

def body (pStep : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 12 (_root_.ThreeSum1960614.Machine.Light.v 8) (
    _root_.ThreeSum1960614.Machine.Light.Stmt.call pStep [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 2,_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4,_root_.ThreeSum1960614.Machine.Light.v 5,_root_.ThreeSum1960614.Machine.Light.v 6,_root_.ThreeSum1960614.Machine.Light.v 7,_root_.ThreeSum1960614.Machine.Light.v 8,_root_.ThreeSum1960614.Machine.Light.v 9,_root_.ThreeSum1960614.Machine.Light.v 10,_root_.ThreeSum1960614.Machine.Light.v 11,_root_.ThreeSum1960614.Machine.Light.v 12] 13)



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pStep : ℕ
  step : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.Procs P pStep
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.body pStep)

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (src n g p m base : ℕ) (shift : ℤ) (i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [src,n,g,p,m,shift,base,_root_.ThreeSum.SourceBandLayout.cap n g,_root_.ThreeSum.BandPartition.size n g,_root_.ThreeSum.SourceBandLayout.data base n g,_root_.ThreeSum.SourceBandLayout.stride n g m,
      _root_.ThreeSum.SourceBandLayout.work base n g m,i,r],ν⟩ ∧
    (∀ j < i, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At ν f base n g p m shift j) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceBandBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual constant-time retained histogram selection with empty padding -/

namespace ThreeSum.LightSourceBandHistSelect
open _root_.ThreeSum.LightSourceBandHistSelect


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairSlices
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices

set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

def finishBody : _root_.ThreeSum1960614.Machine.Light.Stmt := (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 3)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 4)))

def rightBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 2))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.k 3)))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.finishBody)

/-- The pair-catalog header, common band index, and two temporary cells. -/
def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 4)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 0)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 6) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.k 3)))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.rightBody)))

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightSourceBandHistSelect

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete sparse Möbius query in the benchmark language

The fixed program constructs every missing-mask layer it uses, evaluates
explicit leaves through source-stage reads, evaluates canonical boxes
through their compact stored stages, adds both contributions, and applies
the outer sign. The exact partition identity proves the resulting Möbius
value. No enumeration, leaf-value, or query-value oracle is assumed.
-/

namespace ThreeSum.LightSparseQuery
open _root_.ThreeSum.LightSparseQuery


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open scoped _root_.BigOperators

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





/-- Width, source cutoff, suffix stage, two prefixes, query cardinality and
mask, missing threshold, two source bases, box cutoff and base, mask buffer,
and polynomial scratch. -/
def body (pExplicit pBoxes pSign : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pExplicit [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBoxes [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 17))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSign [_root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 7] 0))))





def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightSparseQuery.body 1 2 22,_root_.ThreeSum1960614.Machine.ThreeSum.LightExplicitSum.body 3 6,_root_.ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.body 3 7,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.body 4 5,_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body 17 20,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body 5,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLeafSum.body 8,_root_.ThreeSum1960614.Machine.ThreeSum.LightBoxSum.body 9,_root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeaf.body 10 22,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryBox.body 11 10,_root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.body 12 13,_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum.body 17 20,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body 14 19,_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.body 14 19,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.body 15 17 18,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildBody 16 21,_root_.ThreeSum1960614.Machine.Light.fillBody,_root_.ThreeSum1960614.Machine.Light.powTableBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rankBody 18,_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body 20,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.rowBody 23,_root_.ThreeSum1960614.Machine.ThreeSum.LightSign.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody]









end ThreeSum.LightSparseQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the executed common-prime setup

The bound includes the generated pool, every aggregate candidate minimum,
all original band-score calls, and the computed chain depth. The size-only
budget uses the same quadratic owner bound as the physical mass theorem.
-/

namespace ThreeSum.BandPrimeCosts
open _root_.ThreeSum.BandPrimeCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000























def timeBudget (k n : ℕ) : ℕ := _root_.ThreeSum.LightPrimePool.time (_root_.ThreeSum.Scales.primeWindow n)+
  15*(_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1)*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1)*
    (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)+1)^2*_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n



end ThreeSum.BandPrimeCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Compute and retain the selected-color array layout -/

namespace ThreeSum.LightEncodedColorLayout
open _root_.ThreeSum.LightEncodedColorLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 11000

def body (pDivide : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDivide [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 1] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.k 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.k 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 5))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 4) (_root_.ThreeSum1960614.Machine.Light.v 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.v 5)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 10)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 13)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 5)) (_root_.ThreeSum1960614.Machine.Light.v 15)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 6)) (_root_.ThreeSum1960614.Machine.Light.v 17)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 7)) (_root_.ThreeSum1960614.Machine.Light.v 18)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 19)))))))))))))))))))))))))))










variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightEncodedColorLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual common-prime construction with its reusable metadata retained

The verified depth, prime-pool and common-chain programs each run once.
Six header cells retain their controls before the pool and prefix arrays;
all temporary scoring memory follows the exact returned next-free pointer.
-/

namespace ThreeSum.LightEncodedColorPrimeCore
open _root_.ThreeSum.LightEncodedColorPrimeCore


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.EncodedColorPrimeData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData

set_option maxHeartbeats 2600000
set_option maxRecDepth 13000

def body (pDepth pPool pChain : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDepth [_root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPool [_root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 13] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pChain [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 15] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 16)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 12)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 17)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 13)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 14)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.k 5)) (_root_.ThreeSum1960614.Machine.Light.v 15)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 16))))))))))))))

def poolProgram : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.program _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.program
def joinedProgram : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.poolProgram _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain.program
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.joinedProgram ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.body 0 1 22]









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}



end ThreeSum.LightEncodedColorPrimeCore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One uniform exponential bound for all finite local-cover dimensions -/

namespace ThreeSum.LightLocalCoverMagnitude
open _root_.ThreeSum.LightLocalCoverMagnitude


open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout



structure Bounds (h B : ℕ) : Prop where
  positive : 1 ≤ B
  width : 464*h+1 ≤ B
  vertices : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h+1 ≤ B
  prime : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1 ≤ B
  cap : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h+1 ≤ B
  candidates : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h+1 ≤ B
  rounds : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1 ≤ B
  decodePower : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)^(2*(464*h)+1)+1 ≤ B
  maskPower : 2^(464*h+1)+1 ≤ B









end ThreeSum.LightLocalCoverMagnitude

end ThreeSum1960614.Machine


