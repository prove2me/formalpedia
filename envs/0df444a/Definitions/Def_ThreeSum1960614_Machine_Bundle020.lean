-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle020
-- name    : ThreeSum1960614_Machine_Bundle020
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:52:13.330138+00:00
-- url     : https://prove2.me/theorems/1cfe15c0-9c24-4f49-9727-e315bdcd8a37
-- title:
--   Stored zeta stages, local cover indices, and original-input catalogs
-- statement:
--   For a width-$L$ subset function $f$, a cutoff, and a compact-table base, the zeta-stage program computes the compact stride and applies one coordinate pass per bit, retaining stages $0,\ldots,L$. Its invariant records every completed stage and preservation outside the stage array. The local-cover matrix entry is a Boolean support indicator obtained from left/right mask hashes, their actual histograms, and bucket-cap flags. Its row candidates are the ordered radix enumeration of weights; its columns decode an ordered pair of residues modulo the selected local prime. Greedy choice indices and occurrence-to-candidate lookup preserve that ordering, including repeated choices.
--
--   For an original list of signed integers and modulus $P$, the guarded A-key interface retains all physical positions in each of the three lifts. A wanted incidence satisfies divisibility of its lifted residue plus the common offset minus the global output key. Three parallel catalog arrays store a value, its owner slot, and its sorted position. Programs construct flagged owner records, append only a flagged record's truncated A band, and compute its exact weighted modular score, returning zero for an unflagged record. A separate four-procedure original-input fallback scans triples with three distinct indices for the finite exceptional size regime.
--
--   The finite ledger defines six reporting counts: table construction, source encoding, prefix boxes, initial queries, active-prefix queries, and terminal work. For a natural-valued function $f$ and real exponent $a$, its power-bound interface means
--
--   $$\forall\varepsilon>0,\quad f(n)\le n^{a+\varepsilon}\quad\text{for all sufficiently large }n.$$
--
--   These finite counts remain separate from actual machine execution costs. Further programs normalize three supplied color classes, construct their bands and owner tables, decode a physical global-output index into forward-ordered occurrence and mask rows, construct every original A-key lift, and compute independent endpoint flags from a global mask.
--
--   The bundle supplies the exact array meanings and finite work quantities used to connect the combinatorial runtime ledger to the deterministic integer 3SUM machine. It preserves original-position multiplicities and avoids replacing physical record identity by equality of key values.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightZetaStages.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LocalCoverMatrix.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/RawAKeyLists.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/StageBounds.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BandRawAMemory.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandCandidatesTable.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandPreprocessing.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandRawAStep.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandWeightedScoreCell.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBruteThreeSum.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverSchedule.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOutputDecode.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightRawAKeys.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceMaskFlags.lean

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
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBandCandidatesTable
end ThreeSum.LightBandCandidatesTable
namespace ThreeSum.LightBandPreprocessing
end ThreeSum.LightBandPreprocessing
namespace ThreeSum.LightBandRawAStep
end ThreeSum.LightBandRawAStep
namespace ThreeSum.LightBandWeightedScoreCell
end ThreeSum.LightBandWeightedScoreCell
namespace ThreeSum.LightBruteThreeSum
end ThreeSum.LightBruteThreeSum
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightOutputDecode
end ThreeSum.LightOutputDecode
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightRawAKeys
end ThreeSum.LightRawAKeys
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceMaskFlags
end ThreeSum.LightSourceMaskFlags
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalCoverMatrix
end ThreeSum.LocalCoverMatrix
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StageBounds.PowerBound
end ThreeSum.StageBounds.PowerBound
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.SubsetStages
end ThreeSum.SubsetStages
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable
end ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing
end ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAStep
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAStep
namespace ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell
end ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell
namespace ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum
end ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecode
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecode
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightRawAKeys
end ThreeSum1960614.Machine.ThreeSum.LightRawAKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
end ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
end ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
end ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
end ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetStages
end ThreeSum1960614.Machine.ThreeSum.SubsetStages
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSumApsp.Spec
end ThreeSum1960614.Machine.ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

namespace ThreeSum1960614.Machine

/-!
# Building and retaining every compact suffix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for forced
prefix queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightZetaStages
open _root_.ThreeSum.LightZetaStages


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetStages
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





def roundBody (pPass : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.call pPass [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 6)),
    ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 5))),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 5))),_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4] 7

/-- Arguments: width, cutoff, base of all stage tables,
mask workspace, polynomial workspace. Stage zero initially holds `f`. -/
def body (pSize pPass : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSize [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 4] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.for 6 (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.roundBody pPass)))



def Inv {L : ℕ} (μ : ℕ → ℤ) (cut base maskBase work : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [L,cut,base,maskBase,work,_root_.ThreeSum.SubsetAddress.downsetCap L cut,j,r],μ'⟩ ∧
    _root_.ThreeSum.LightZetaStages.StoredThrough μ' base cut f j ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase base ((L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut)















end ThreeSum.LightZetaStages

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix
open _root_.ThreeSum.LocalCoverMatrix


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes

variable {h L k : ℕ}


def leftCount (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k) r (_root_.ThreeSum.LocalMaskGraph.vertexCount L k)
def rightCount (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k) r (_root_.ThreeSum.LocalMaskGraph.vertexCount L k)
def key (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k : ℕ) : ℕ → ℕ :=
  _root_.ThreeSum.LightPairFlags.pairKey (_root_.ThreeSum.LocalMaskGraph.vertexCount L k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k)
def valid (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k B : ℕ) : ℕ → ℕ :=
  _root_.ThreeSum.LightPairFlags.pairFlag L (_root_.ThreeSum.LocalMaskGraph.vertexCount L k) B (_root_.ThreeSum.LocalCoverMatrix.bits L k)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.leftCount w k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.rightCount w k)
def entry (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k B r : ℕ) : ℕ :=
  _root_.ThreeSum.LightSupportMark.bit (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.key w k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.valid w k B) r
    (_root_.ThreeSum.LocalMaskGraph.vertexCount L k*_root_.ThreeSum.LocalMaskGraph.vertexCount L k)















end ThreeSum.LocalCoverMatrix

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists
open _root_.ThreeSum.RawAKeyLists


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option maxHeartbeats 900000



































def selected (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset.selected M (_root_.ThreeSum.RawAKeyLists.keys P xs) h J





def wanted (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin xs.length)) :=
  Finset.univ.filter fun w =>
    (M : ℤ) ∣ xs.getD w.1.val 0%P+_root_.ThreeSum.RawIncidences.lift w.2.1*P+d-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2

theorem mem_wanted {M h J : ℕ} {P d : ℤ} {xs : List ℤ}
    {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin xs.length)} :
    w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted M P xs h J d ↔
      (M : ℤ) ∣ xs.getD w.1.val 0%P+_root_.ThreeSum.RawIncidences.lift w.2.1*P+d-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted,Finset.mem_filter,Finset.mem_univ,true_and]





end ThreeSum.RawAKeyLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds
open _root_.ThreeSum.StageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def tableCount (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n

def encoderCount (n : ℕ) : ℕ := 2 * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n

def boxCount (n : ℕ) : ℕ := 3 * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ^ 2 * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes n

def initialCount (W : ℕ → ℕ) (n : ℕ) : ℕ := W n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0

def activeCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  H n * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n * _root_.ThreeSum.CostLedger.microPartitions n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n

def terminalChoices (n : ℕ) : ℕ := 2 ^ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n)

def terminalCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * H n * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n * _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n







noncomputable section

/-- A proved power upper bound with arbitrarily small positive slack. -/
def PowerBound (f : ℕ → ℕ) (a : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d)

namespace PowerBound
open _root_.ThreeSum.StageBounds.PowerBound














end PowerBound

































end
end ThreeSum.StageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The three retained parallel arrays of A-value incidences -/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1400000

structure Stored (μ : ℕ → ℤ) (vals owners positions : ℕ)
    (f : ℕ → ℤ) (ls : List _root_.ThreeSum.BandRawA.Label) : Prop where
  valueRows : _root_.ThreeSum1960614.Machine.Light.Seg μ vals (_root_.ThreeSum.BandRawA.values f ls)
  ownerRows : _root_.ThreeSum1960614.Machine.Light.Seg μ owners (_root_.ThreeSum.BandRawA.ownerLabels ls)
  positionRows : _root_.ThreeSum1960614.Machine.Light.Seg μ positions (_root_.ThreeSum.BandRawA.positionLabels ls)













end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual rectangular owner records with two nested loops -/

namespace ThreeSum.LightBandCandidatesTable
open _root_.ThreeSum.LightBandCandidatesTable


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pRow : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 4 (_root_.ThreeSum1960614.Machine.Light.v 2) (
    _root_.ThreeSum1960614.Machine.Light.Stmt.call pRow [((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 3))),((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 3)))),_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4] 5)



def Inv (μ : ℕ → ℤ) (mode : _root_.ThreeSum.BandCandidateRows.Mode) (f : ℕ → ℕ → ℕ)
    (src dst m n i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [src,dst,m,n,i,r],ν⟩ ∧
    (∀ x < i, ∀ y < n, _root_.ThreeSum1960614.Machine.Light.Seg ν (dst+4*(x*n+y)) (_root_.ThreeSum.BandCandidateRows.make mode x y (f x y)).cells) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (4*(m*n))

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst m n U : ℕ} {f : ℕ → ℕ → ℕ}







end ThreeSum.LightBandCandidatesTable

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Closed normalization and band listing for three supplied color classes

The three class arrays are sorted and deduplicated separately. Their actual
length/count headers then drive the actual owner-table enumerator. The program
has twenty fixed procedures. No sorting function, lookup function, or band
enumerator is supplied by the caller.
-/

namespace ThreeSum.LightBandPreprocessing
open _root_.ThreeSum.LightBandPreprocessing


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def Represents (μ : ℕ → ℤ) (values endpoints g : ℕ) (hg : 0 < g)
    (original L : List ℤ) (hs : L.Pairwise (· < ·)) : Prop :=
  _root_.ThreeSum1960614.Machine.Light.Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ endpoints L.length
      (_root_.ThreeSum.BandPartition.family (fun i => L.getD i 0) L.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hs))

def Output (μ : ℕ → ℤ) (av ae bv be cv ce dst g : ℕ) (hg : 0 < g)
    (originalA originalB originalC : List ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
      r = (_root_.ThreeSum.LightBandEnumeration.count (_root_.ThreeSum.BandPartition.size A.length g) (_root_.ThreeSum.BandPartition.size B.length g) (_root_.ThreeSum.BandPartition.size C.length g) : ℤ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ dst
        (_root_.ThreeSum.BandPartition.family (fun i => A.getD i 0) A.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsA))
        (_root_.ThreeSum.BandPartition.family (fun i => B.getD i 0) B.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsB))
        (_root_.ThreeSum.BandPartition.family (fun i => C.getD i 0) C.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsC))



/-- Arguments: source/length pairs for A, B, C; band size; value/header
output pairs for A, B, C; common scratch and table output address. -/
def body (pPrepare pEnumerate : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrepare [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 13] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrepare [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 13] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPrepare [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnumerate [_root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13] 0))))









structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pPrepare : ℕ
  pEnumerate : ℕ
  prepare : _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs P pPrepare
  enumerate : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs P pEnumerate
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.body pPrepare pEnumerate)



def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.body 1 12,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.body 2 8,_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.body 3 7,
    _root_.ThreeSum1960614.Machine.Light.sortBody 3 4 5 6,_root_.ThreeSum1960614.Machine.Light.halfBody,_root_.ThreeSum1960614.Machine.Light.mergeBody,_root_.ThreeSum1960614.Machine.Light.copyBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedupBody 7,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.body 9 10 11,_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.lowerBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.upperBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.body 13,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.body 14 15 16,_root_.ThreeSum1960614.Machine.Light.clog2Body,_root_.ThreeSum1960614.Machine.Light.powTableBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.body 17,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.rowBody 18,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.body 19,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody 19]





end ThreeSum.LightBandPreprocessing

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Append the actual A band of one flagged owner record -/

namespace ThreeSum.LightBandRawAStep
open _root_.ThreeSum.LightBandRawAStep


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def tail (pRow : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRow [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 10), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 9), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 9), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 9), _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 10] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 11))))

/-- Sorted A base and length, g, flag, A band, owner, three output bases,
and the previous incidence count. -/
def body (pRow : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 10))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 11)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 (_root_.ThreeSum1960614.Machine.Light.v 2)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAStep.tail pRow)))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 9))



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src n g owner values owners positions previous capacity : ℕ} {r : _root_.ThreeSum.BandCandidateRows.Record}



end ThreeSum.LightBandRawAStep

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compute one flagged owner's weighted modular score

The actual record supplies its three band indices. This routine computes
their truncated lengths and invokes the existing exact counting program on
those slices. An unflagged record contributes zero without a counting call.
-/

namespace ThreeSum.LightBandWeightedScoreCell
open _root_.ThreeSum.LightBandWeightedScoreCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pLength pScore : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 13 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 2)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 3)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLength [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 13] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLength [_root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 14] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLength [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 15] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScore [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 6)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 6)), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 15) (_root_.ThreeSum1960614.Machine.Light.v 6)), _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11] 0))))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))))







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.body 14 0]



def programProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.program 0 where
  pCount := 2
  pJoint := 1
  count :=
    { pCapacity := 3, pHist := 4, pCyclic := 8, pResidues := 5, pEmod := 6,
      pHistogram := 7, pMultiply := 9, pHalf := 10, pLinear := 11, pFill := 12, pLookup := 13,
      main := rfl, capacity := rfl, hist := rfl, residues := rfl, emod := rfl,
      histogram := rfl, cyclic := rfl, multiply := ⟨rfl,rfl,rfl,rfl⟩, lookup := rfl }
  main := rfl
  joint := rfl

end ThreeSum.LightBandWeightedScoreCell

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete original-input solver for the finite exceptional sizes

This four-procedure program checks every original-position triple and all
three inequalities between its indices. Its time is polynomial but is not
the target subquadratic bound. It supplies the exact fallback needed before
the asymptotic parameter regime, with no hypothesis on the integer values
beyond the task's given magnitude bound.
-/

namespace ThreeSum.LightBruteThreeSum
open _root_.ThreeSum.LightBruteThreeSum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pScan : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScan [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 4] 0))



def need (n U : ℕ) : _root_.ThreeSum1960614.Machine.Light.Need :=
  ⟨_root_.ThreeSum.LightOriginalTripleRow.word n U,0,n^3+3⟩

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.body 2]



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







end ThreeSum.LightBruteThreeSum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum.LightLocalCoverSchedule


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

def rows (h : ℕ) : ℕ := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)^(2*(464*h))
def cols (h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h
def candidate (h i : ℕ) : _root_.ThreeSum.LocalHashMoments.Weight (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :=
  _root_.ThreeSum.WeightEnumeration.decodedWeight (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) i
def target (h r : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h × _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h :=
  (((r/_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h),((r%_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
def matrix (h i r : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h i) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) r
def indices (h : ℕ) : List ℕ :=
  _root_.ThreeSum.BooleanGreedy.choices (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.matrix h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)

















def candidateAt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) : ℕ := (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).getD s.val 0











end ThreeSum.LightLocalCoverSchedule

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete physical output-index decoding

The first pass writes the actual big-endian local-record digit array.
The second pass splits each digit, reads its retained layer mask, and
accumulates the occurrence-only source-bank code. Both output rows are
in forward original block order, including repeated record values.
-/

namespace ThreeSum.LightOutputDecode
open _root_.ThreeSum.LightOutputDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

def body (pDigits pStep : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDigits [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 11 (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 11)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pStep [_root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 11), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 11), _root_.ThreeSum1960614.Machine.Light.v 6] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 2)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 9)))))))







def Inv (μ : ℕ → ℤ) (k J T M masks dst work : ℕ) (q : ℤ)
    (f : ℕ → ℕ) (i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (x : ℤ) (ν : ℕ → ℤ),
    σ=⟨_root_.Light.frame [k,J,T,M,masks,dst,work,T*M,q,
      _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M i k,T^i,i,x],ν⟩ ∧
    (∀ j, i ≤ j → j < J →
      ν (dst+J-1-j)=(((k/(T*M)^j)%(T*M) : ℕ) : ℤ)) ∧
    (∀ j < i,
      ν (dst+J-1-j)=(((k/(T*M)^j)%(T*M)/M : ℕ) : ℤ) ∧
      ν (dst+J+J-1-j)=(f ((k/(T*M)^j)%(T*M)%M) : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pDigits : ℕ
  pStep : ℕ
  pDivide : ℕ
  digits : P[pDigits]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.body pDivide)
  step : P[pStep]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep.body pDivide)
  divide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body
  main : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.body pDigits pStep)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J T M masks dst work V U : ℕ} {f : ℕ → ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.body 1 2,_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.body 3,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep.body 3,_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body]







end ThreeSum.LightOutputDecode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of the three lifted original A-key arrays

The middle row is computed by the checked signed remainder routine. Two
affine scans append the minus and plus lifts. Every original position is
retained in each row, and the resulting segment is the exact guarded-key
list whose balancing bound is proved in `RawAKeyLists`.
-/

namespace ThreeSum.LightRawAKeys
open _root_.ThreeSum.LightRawAKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.RawAKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists

set_option maxHeartbeats 1000000
set_option maxRecDepth 6000

/-- Original array, length, modulus, and first free address. -/
def body (pResidues pAffine : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pResidues [_root_.ThreeSum1960614.Machine.Light.v 0, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.k 1] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pAffine [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 1, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 2), _root_.ThreeSum1960614.Machine.Light.k 1] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pAffine [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 1), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 1)), _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.k 1] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 3))))))





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightRawAKeys.body 1 2,_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody 3,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body,_root_.ThreeSum1960614.Machine.Light.emodBody]





end ThreeSum.LightRawAKeys

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing independent endpoint flags directly from a global mask

The fixed program creates its own powers and Boolean coordinate row, then
performs the actual selected-block trimming scan. There is no Boolean-bit or
trim-flag oracle in the contract.
-/

namespace ThreeSum.LightSourceMaskFlags
open _root_.ThreeSum.LightSourceMaskFlags


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- Arguments: block count, width, row size, local modulus, cap, occurrence
indices, schedule coefficients, occurrence-to-candidate indices, both
candidate histograms, global mask, output, bit scratch, row scratch,
and reusable arithmetic scratch. -/
def body (pBits pTrim : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBits [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1), _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 14] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTrim [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 11] 15))







structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pBits : ℕ
  pPowers : ℕ
  pErase : ℕ
  pTrim : ℕ
  bits : P[pBits]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.body pPowers pErase)
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  erase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase)
  trim : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Procs P pTrim
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.body pBits pTrim)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightSourceMaskFlags

end ThreeSum1960614.Machine


