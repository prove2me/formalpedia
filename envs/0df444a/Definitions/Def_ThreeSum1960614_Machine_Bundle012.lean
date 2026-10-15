-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle012
-- name    : ThreeSum1960614_Machine_Bundle012
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:28:12.639717+00:00
-- url     : https://prove2.me/theorems/cabd98fd-5e2b-41d5-aa3c-5fce956c6d1f
-- title:
--   Executable residue, subset-address, and quartic-switch interfaces
-- statement:
--   The library defines concrete light-language routines for Cartesian positional-key rows, Pascal-table binomial lookup, exact original-value bucket testing, positive-query filtering, padded residue histograms, integer scale initialization, shifted residue keys, and compact subset ranks. A subset rank is evaluated recursively in the remaining width using stored powers of two and Pascal coefficients. The finite bucket representation retains original physical indices and their multiplicities. Valid stored reporting prefixes have exactly the prescribed length and row cardinality; their signed subset query is explicitly zero when validity or the fixed original-index key check fails.
--
--   For natural parameters $J,j,r,q$, the quartic switch tests the exact integer comparison
--   $$100000000(159243801J+500000000j)r^4\le500000000(J-j)q\bigl(785174904r^3+q(72447023r^2+q(24044466r+12022459q))\bigr).$$
--   Its candidate set restricts $q$ to $0\le q\le\lfloor r/2\rfloor$, and its index is the least accepted candidate when one exists, with default zero otherwise. The source includes the stated adaptation of the pinned Apache-2.0 switch construction. The library also specifies the wrapper from the 3SUM task's array layout to the benchmark end statement, and reindexes block subset queries into row-major machine coordinates.
--
--   These definitions expose the actual programs and finite data behind the reporting and parameter-selection stages of the deterministic integer 3SUM proof. Their placement records specify helper procedure locations; later theorems establish execution, resource bounds, and agreement with the semantic counts.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightRadixRows.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingBinomial.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingBucketRow.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingFilter.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightResidueHistogram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceControlsMax.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceResidues.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSubsetAddress.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/QuarticSwitch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/SourceBuckets.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/StoredReporting.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/RunningTimes/Sec3/Theorem22/ThreeSumLayout.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BlockIndexedQuery.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Field.Basic
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
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
import Mathlib.Order.Filter.AtTopBot.Basic
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

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Sec3
end Light.Sec3
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightRadixRows
end ThreeSum.LightRadixRows
namespace ThreeSum.LightReportingBinomial
end ThreeSum.LightReportingBinomial
namespace ThreeSum.LightReportingBucketRow
end ThreeSum.LightReportingBucketRow
namespace ThreeSum.LightReportingFilter
end ThreeSum.LightReportingFilter
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LightSourceControlsMax
end ThreeSum.LightSourceControlsMax
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.LightQuarticSwitch
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Sec3
end ThreeSum1960614.Machine.Light.Sec3
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixRows
end ThreeSum1960614.Machine.ThreeSum.LightRadixRows
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial
end ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingFilter
end ThreeSum1960614.Machine.ThreeSum.LightReportingFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax
end ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Spec
end ThreeSum1960614.Machine.ThreeSumApsp.Spec
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

/-!
# Costed Cartesian rows for positional keys

For every local key, an actual affine scan writes one entire row of extended
keys. The arrays contain the complete product list, including equal integer
keys attached to different original records. No division or decoding loop is
used to locate Cartesian coordinates at runtime.
-/

namespace ThreeSum.LightRadixRows
open _root_.ThreeSum.LightRadixRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

def body (pAffine : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 6 (_root_.ThreeSum1960614.Machine.Light.v 3)
    (_root_.ThreeSum1960614.Machine.Light.Stmt.call pAffine [_root_.ThreeSum1960614.Machine.Light.v 1,((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 4))),_root_.ThreeSum1960614.Machine.Light.v 4,_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 6))),_root_.ThreeSum1960614.Machine.Light.v 5] 7)




def Inv (μ : ℕ → ℤ) (srcBase srcPrev dst p : ℕ) (base prev : List ℤ)
    (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [srcBase,srcPrev,dst,base.length,prev.length,p,j,r],ν⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum.RadixKeyLists.step (p : ℤ) (base.take j) prev) ∧
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (base.length*prev.length)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightRadixRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual Pascal lookup for reporting child and terminal candidate counts -/

namespace ThreeSum.LightReportingBinomial
open _root_.ThreeSum.LightReportingBinomial


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-- Arguments are n, k, and a polynomial Pascal scratch region. -/
def body (pPascal : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPascal [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 0] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 4)))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.Light.fillBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.rowBody 1,_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildBody 0 2,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial.body 3]


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}





end ThreeSum.LightReportingBinomial

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-value testing of one retained physical bucket

The procedure visits the bucket's physical index array and reads the original
value at each index. It counts exact integer equalities with the supplied
target and preserves every memory cell. Equal values at distinct original
indices remain separate tests.
-/

namespace ThreeSum.LightReportingBucketRow
open _root_.ThreeSum.LightReportingBucketRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000











def roundBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 6))))) (_root_.ThreeSum1960614.Machine.Light.v 0)))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip

/-- Target value, original value array, retained physical indices, bucket
length, original value-array length. -/
def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 6 (_root_.ThreeSum1960614.Machine.Light.v 3) _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.roundBody) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 5))))




variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightReportingBucketRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual positive-query filtering for a reporting frontier

The scan writes exactly the indices of positive stored query counts, in input
order. Its cost is linear in the candidate count, and original input arrays
are preserved. It does not recompute or assume the query implementation.
-/

namespace ThreeSum.LightReportingFilter
open _root_.ThreeSum.LightReportingFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















def roundBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 4)))))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 3)) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))))
    _root_.ThreeSum1960614.Machine.Light.Stmt.skip

/-- Number of candidates, stored query counts, selected-index output. -/
def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 4 (_root_.ThreeSum1960614.Machine.Light.v 0) _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.roundBody) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 3))))



def Inv (μ : ℕ → ℤ) (count : ℕ → ℕ) (n src dst j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨_root_.Light.frame [n,src,dst,(_root_.ThreeSum.LightReportingFilter.selected count j).length,j],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.LightReportingFilter.selected count j) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n







end ThreeSum.LightReportingFilter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram
open _root_.ThreeSum.LightResidueHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





















/-- Arguments: source, histogram, item count, modulus, histogram capacity,
first scratch cell, remainder scratch cell, sign. -/
def body (pResidues pHistogram : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pResidues [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHistogram [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4] 8))











end ThreeSum.LightResidueHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales
open _root_.ThreeSum.LightScales


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















def values (n : ℕ) : List ℤ :=
  [_root_.ThreeSum.Scales.inputBits n,_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n),_root_.ThreeSum.Scales.muZero n,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n),_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n]

/-- Arguments: original input length and destination of the five parameters.
The result is `mu`; the destination stores bits, micro-half, micro-size,
block count, and total size in that order. -/
def body (pLog pCube pHalf pDiv : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLog [_root_.ThreeSum1960614.Machine.Light.v 0] 2) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCube [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1)] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHalf [_root_.ThreeSum1960614.Machine.Light.v 3] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 5))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pDiv [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 203889696) (_root_.ThreeSum1960614.Machine.Light.v 2), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 20000000000) (_root_.ThreeSum1960614.Machine.Light.v 6)] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 20) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 6))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 6)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 8)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 4)) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 9)))))))))))))))

def time (n : ℕ) : ℕ := _root_.Light.log2Time n + _root_.Light.cbrtCeilTime (_root_.ThreeSum.Scales.inputBits n+1) +
  _root_.Light.halfTime (_root_.Light.cbrtLeast (_root_.ThreeSum.Scales.inputBits n+1)) +
  _root_.ThreeSum.LightSmallDivide.time (203889696*_root_.ThreeSum.Scales.inputBits n) (20000000000*_root_.ThreeSum.Scales.muZero n)+300









/-- A syntax-only placement interface for embedding the initializer into a
larger fixed program. -/
structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pLog : ℕ
  pCube : ℕ
  pHalf : ℕ
  pDiv : ℕ
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.body pLog pCube pHalf pDiv)
  log : P[pLog]? = some _root_.ThreeSum1960614.Machine.Light.log2Body
  cube : P[pCube]? = some _root_.ThreeSum1960614.Machine.Light.cbrtCeilBody
  half : P[pHalf]? = some _root_.ThreeSum1960614.Machine.Light.halfBody
  divide : P[pDiv]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body



end ThreeSum.LightScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Scalar maximum for exact shared-bank dimensions -/

namespace ThreeSum.LightSourceControlsMax
open _root_.ThreeSum.LightSourceControlsMax


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def body : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 0))

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceControlsMax

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000







/-- Arguments: source, destination, count, first modulus, second modulus,
scratch, and signed carry offset. The two remainder calls share scratch. -/
def body (pEmod : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 7 (_root_.ThreeSum1960614.Machine.Light.v 2) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 7)), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 5] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 6), _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.v 9)))))







def Inv (μ : ℕ → ℤ) (src dst n p m work : ℕ) (shift : ℤ) (i : ℕ)
    (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [src,dst,n,p,m,work,shift,i,r0,r1],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+j)) : ℤ)) ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν work dst n

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.body 1,_root_.ThreeSum1960614.Machine.Light.emodBody]





end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







/-- Arguments: remaining width, cardinality, mask, original width,
Pascal table, and power table. The seventh local stores the next bit index.
The return value replaces the first argument. -/
def rankBody (pSelf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v 0)))
    ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSelf [_root_.ThreeSum1960614.Machine.Light.v 6, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1), (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 6))), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 0) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.v 1)))))))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.k 0))









end ThreeSum.LightSubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
The actual quartic integer test and its Light-language execution contract.
The finite scan and proof structure adapt the pinned Apache-2.0 source
Submission/ThreeSum/LightSwitch{,Bounds}.lean, commit
2b639655e07421b9ac743de9090459bab473a7c0.
The coefficients, powers and resource allowances below are changed to
the exact expansion-232 degree-four comparison in PROOF.md, Section 4.2.
-/

namespace ThreeSum1960614.LightQuarticSwitch
open _root_.ThreeSum1960614.LightQuarticSwitch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

def polynomial (r q : ℕ) : ℕ :=
  q * (785174904*r*r*r + q*(72447023*r*r + q*(24044466*r + 12022459*q)))

def left (J j r : ℕ) : ℕ :=
  100000000*(159243801*J+500000000*j)*r*r*r*r

def factor (J j : ℕ) : ℕ := 500000000*(J-j)

def accepts (J j r q : ℕ) : Prop := _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left J j r ≤ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor J j * _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial r q

instance instDecidableAccepts (J j r q : ℕ) : Decidable (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts J j r q) :=
  inferInstanceAs (Decidable (_ ≤ _))

def candidates (J j r : ℕ) : Finset ℕ :=
  (Finset.range (r/2+1)).filter (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts J j r)

def index (J j r : ℕ) : ℕ :=
  if h : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty then (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).min' h else 0

def word (J r : ℕ) : ℕ := (J+r+1000000001)^96















def test : _root_.ThreeSum1960614.Machine.Light.Cond :=
  (_root_.ThreeSum1960614.Machine.Light.Cond.lt ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 500000000) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 785174904) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 72447023) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 24044466) (_root_.ThreeSum1960614.Machine.Light.v 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 12022459) (_root_.ThreeSum1960614.Machine.Light.v 3))))))))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 100000000) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 159243801) (_root_.ThreeSum1960614.Machine.Light.v 0)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 500000000) (_root_.ThreeSum1960614.Machine.Light.v 1)))) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.v 2)))

def body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.while _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 3))))

def time (r : ℕ) : ℕ := 200*(r+1)+100

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J j r q d : ℕ}













end ThreeSum1960614.LightQuarticSwitch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets
open _root_.ThreeSum.SourceBuckets


open _root_.Finset
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000



































/-- Concrete array contract produced by prefix offsets and cursor scatter. -/
structure Stored (μ : ℕ → ℤ) (key : ℕ → ℕ) (N M offsets flat : ℕ) : Prop where
  offsets : ∀ r ≤ M, μ (offsets+r) = (_root_.ThreeSum.SourceBuckets.offset key N r : ℤ)
  indices : ∀ i < N, μ (flat+_root_.ThreeSum.SourceBuckets.position key N i) = (i : ℤ)













end ThreeSum.SourceBuckets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting
open _root_.ThreeSum.StoredReporting


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced











def ValidPrefix {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (464 * h)))) : Prop :=
  pre.length = k ∧ ∀ i : Fin J, i.val < k →
    _root_.ThreeSum.StoredReporting.prefixRows pre i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i ∧ (_root_.ThreeSum.StoredReporting.prefixRows pre i).card = h

instance instDecidableValidPrefix {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (464 * h)))) : Decidable (_root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix
  infer_instance

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



/-- A signed subset query, with the inexpensive validity and fixed A-key
checks displayed explicitly. Its natural value is established below. -/
def storedQueryValue {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (464 * h)))) : ℤ :=
  if _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre then
    if w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
        (a w.1 % P + _root_.ThreeSum.RawIncidences.lift w.2.1 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2 then
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue P d B C b c w.2.2 (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre)
    else 0
  else 0



















end Indices

end ThreeSum.StoredReporting

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# 3SUM: from a solver of the task to a program for the layout of the end statement

3SUM (Theorem 22).  `realized_threeSum`: if the task `s3Task` is solved in time T, then
`EndStatement.ThreeSum` is solved on the word RAM within a constant times T.

The input is n in cell 0 and the n numbers in the cells 1, …, n; the free pointer is n + 1
(`threeSumInst`).  The task speaks of the vector that is read from the list of the numbers, which is
the vector of the instance (`vecOf_ofFn`).  So the input meets the task's precondition
(`pre_threeSum`), and the result of a solver is the right verdict (`post_threeSum`).
-/

@[expose] public section

namespace Light.Sec3
open _root_.Light.Sec3


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec

/-- The numbers of a list made from a function are the values of the function. -/
theorem vecOf_ofFn {n : ℕ} (x : Fin n → ℤ) : _root_.ThreeSumApsp.Spec.vecOf n (List.ofFn x) = x := by
  funext i
  simp [_root_.ThreeSumApsp.Spec.vecOf, List.getD_eq_getElem?_getD]

/-- The instance of the task: the numbers stand from cell 1 on. -/
def threeSumInst (x : _root_.ThreeSumApsp.WordRam.Bounded _root_.EndStatement.ThreeSum) : _root_.ThreeSum1960614.Machine.Light.s3Task.Inst := ⟨x.n, x.U, 1, List.ofFn x.x⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_threeSum (x : _root_.ThreeSumApsp.WordRam.Bounded _root_.EndStatement.ThreeSum) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    _root_.ThreeSum1960614.Machine.Light.s3Task.Pre (_root_.ThreeSum1960614.Machine.Light.Sec3.threeSumInst x) (_root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd _root_.EndStatement.ThreeSum).input x)) (x.n + 1) where
  N_pos := hn
  U_pos := hU
  len := List.length_ofFn (f := x.x)
  seg := by
    simpa [_root_.EndStatement.ThreeSum, _root_.ThreeSum1960614.Machine.Light.Sec3.threeSumInst] using _root_.ThreeSum1960614.Machine.Light.seg_memOf [(x.n : ℤ)] (List.ofFn x.x) []
  le := fun _ ha => _root_.ThreeSumApsp.WordRam.Bounded.abs_le ha
  below := (Nat.add_comm 1 x.n).le

/-- The result of a solver of the task is the right verdict of the end statement's 3SUM. -/
theorem post_threeSum (x : _root_.ThreeSumApsp.WordRam.Bounded _root_.EndStatement.ThreeSum) (r : ℤ) (μ' : ℕ → ℤ)
    (h : _root_.ThreeSum1960614.Machine.Light.s3Task.Post (_root_.ThreeSum1960614.Machine.Light.Sec3.threeSumInst x) (_root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd _root_.EndStatement.ThreeSum).input x)) (x.n + 1) r
      μ') :
    (_root_.ThreeSumApsp.WordRam.ofEnd _root_.EndStatement.ThreeSum).IsAnswer x (_root_.Light.verdictOf true r) fun i =>
      μ' (((_root_.ThreeSumApsp.WordRam.ofEnd _root_.EndStatement.ThreeSum).input x).length + i) := by
  obtain ⟨rfl, -⟩ := h
  exact ⟨(_root_.Light.verdictOf_flag _).trans (iff_of_eq (congrArg _root_.ThreeSumApsp.ThreeSum (_root_.ThreeSum1960614.Machine.Light.Sec3.vecOf_ofFn x.x))), trivial⟩

/-- What connects 3SUM in the layout of the end statement with the task. -/
noncomputable def wrap3Sum : _root_.ThreeSum1960614.Machine.Light.Wrap _root_.EndStatement.ThreeSum _root_.ThreeSum1960614.Machine.Light.s3Task true where
  args := [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.k 1, ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1))]
  inst := _root_.ThreeSum1960614.Machine.Light.Sec3.threeSumInst
  fr x := x.n + 1
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by
    have := Nat.le_mul_self x.n
    omega
  vals x σ hn hU _ := by simp [_root_.ThreeSum1960614.Machine.Light.s3Task, _root_.ThreeSum1960614.Machine.Light.Sec3.threeSumInst, hn, hU]
  safe x lim σ hn _ _ hw := by
    have hnn : (x.n : ℤ) ≤ (x.n : ℤ) * x.n := by exact_mod_cast Nat.le_mul_self x.n
    push_cast at hw
    simp [hn, abs_le]
    omega
  zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨i, _⟩ => absurd i.isLt (by omega)⟩, trivial⟩
  pre := _root_.ThreeSum1960614.Machine.Light.Sec3.pre_threeSum
  post x r μ' _ h := _root_.ThreeSum1960614.Machine.Light.Sec3.post_threeSum x r μ' h



end Light.Sec3

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockIndexedQuery


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftSource {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) :
    Finset (Fin (J*(464*h))) → ℤ :=
  _root_.ThreeSum.SubsetTransport.reindex (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h))
    (fun S => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b S : ℤ))

def rightSource {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) :
    Finset (Fin (J*(464*h))) → ℤ :=
  _root_.ThreeSum.SubsetTransport.reindex (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h))
    (fun S => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c S : ℤ))









def queryValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (u : Fin J → Finset (Fin (464*h))) : ℤ :=
  _root_.ThreeSum.Subset.mobius (fun S =>
    _root_.ThreeSum.SubsetStages.stageValue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u ∪ S) *
    _root_.ThreeSum.SubsetStages.stageValue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d C c q) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
      (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ S)) (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q))





end Histograms

end ThreeSum.BlockIndexedQuery

end ThreeSum1960614.Machine


