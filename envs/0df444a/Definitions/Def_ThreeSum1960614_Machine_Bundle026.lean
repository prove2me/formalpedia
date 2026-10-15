-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle026
-- name    : ThreeSum1960614_Machine_Bundle026
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:09:33.888311+00:00
-- url     : https://prove2.me/theorems/0596e46e-0640-4b77-a162-b62a90e29335
-- title:
--   Suffix-local sparse queries, guarded wanted records, and dense thresholds
-- statement:
--   Let the global ground-set width be $W$, the residual suffix width be $V$, and its offset be $a$, with $a+V\le W$. Suffix preprocessing enumerates only local masks of width $V$, lifts them by the factor $2^a$, evaluates signed leaves through the global source transforms, and stores compact local tables. The explicit-query program enumerates the required local layers and sums their actual global source reads. The complementary canonical-box query uses local compact addresses; their signed combination has the same intended subset-Moebius value. A separate mask-lowering program converts a lifted global subset back to its local mask by coordinate tests.
--
--   The reporting frontier uses the actual recursive child enumeration order. For a wanted record and depth $k$, its positive frontier is the one obtained from the raw-prefix query on those children, preserving raw incidence multiplicities.
--
--   The guarded-wanted constructor initializes the local cover, creates the global keys and all three original A-key lifts, chooses a balanced common offset, and emits matching physical position pairs. It retains the cover and key tables for later source-bank and output-decoding operations. For schedule length $s(h)$, bucket cap $b(h)$ and block count $J$, the dense-stop representation cap is computed by an actual scalar power routine as
--
--   $$\operatorname{cap}(h,J)=(s(h)b(h)^2)^J.$$
--
--   The dense setup reads the retained cover data, recomputes the exact aggregate weighted modular score $H$, and writes a four-cell record consisting of initial counter zero, threshold $\operatorname{cap}(h,J)H$, the cap, and $H$. All component time, space, word and procedure-closure interfaces remain explicit.
--
--   These executable objects provide the local-width sparse-query path and the actual stopping threshold used in the complete deterministic integer 3SUM reporting proof. Exponential suffix storage depends on $V$; the larger global width contributes to the specified overhead rather than replacing the residual domain.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixBatch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixLower.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixSum.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostFrontier.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightDenseCap.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightGuardedWanted.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixExplicit.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixTable.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightDenseSetup.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixQuery.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixSetup.lean

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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightDenseCap
end ThreeSum.LightDenseCap
namespace ThreeSum.LightDenseSetup
end ThreeSum.LightDenseSetup
namespace ThreeSum.LightGuardedWanted
end ThreeSum.LightGuardedWanted
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixBatch
end ThreeSum.LightReportingSuffixBatch
namespace ThreeSum.LightReportingSuffixExplicit
end ThreeSum.LightReportingSuffixExplicit
namespace ThreeSum.LightReportingSuffixLower
end ThreeSum.LightReportingSuffixLower
namespace ThreeSum.LightReportingSuffixQuery
end ThreeSum.LightReportingSuffixQuery
namespace ThreeSum.LightReportingSuffixSetup
end ThreeSum.LightReportingSuffixSetup
namespace ThreeSum.LightReportingSuffixSum
end ThreeSum.LightReportingSuffixSum
namespace ThreeSum.LightReportingSuffixTable
end ThreeSum.LightReportingSuffixTable
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseCap
end ThreeSum1960614.Machine.ThreeSum.LightDenseCap
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
end ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted
end ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-! # Evaluating one locally enumerated suffix layer against global source tables -/

namespace ThreeSum.LightReportingSuffixBatch
open _root_.ThreeSum.LightReportingSuffixBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def body (pCell : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 16 (_root_.ThreeSum1960614.Machine.Light.v 10)
    (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCell [_root_.ThreeSum1960614.Machine.Light.v 0,_root_.ThreeSum1960614.Machine.Light.v 1,_root_.ThreeSum1960614.Machine.Light.v 2,_root_.ThreeSum1960614.Machine.Light.v 3,_root_.ThreeSum1960614.Machine.Light.v 4,_root_.ThreeSum1960614.Machine.Light.v 5,_root_.ThreeSum1960614.Machine.Light.v 6,_root_.ThreeSum1960614.Machine.Light.v 7,_root_.ThreeSum1960614.Machine.Light.v 9,_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 16))),
      _root_.ThreeSum1960614.Machine.Light.v 8,_root_.ThreeSum1960614.Machine.Light.v 12,_root_.ThreeSum1960614.Machine.Light.v 13,_root_.ThreeSum1960614.Machine.Light.v 14,_root_.ThreeSum1960614.Machine.Light.v 15] 17)



def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage cardinal maskBase baseL baseR dst work : ℕ)
    (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [W,sourceCut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
      V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work,j,r],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst (_root_.ThreeSum.SubsetAddress.downsetCap V boxCut) ∧
    _root_.ThreeSum.LightZetaCell.TableAt μ' dst boxCut
      (_root_.ThreeSum.LightSignedLeafBatch.values μ dst (masks.take j) (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR))





end ThreeSum.LightReportingSuffixBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual global-to-local suffix-mask conversion

The program constructs powers once, tests each suffix coordinate using the
verified mask-bit procedure, and accumulates its local power. Runtime is
quadratic in the width, independent of the numeric mask value.
-/

namespace ThreeSum.LightReportingSuffixLower
open _root_.ThreeSum.LightReportingSuffixLower


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}









def roundBody (pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pErase [_root_.ThreeSum1960614.Machine.Light.v 0, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 7), _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 4] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 3)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 7)))))))

def body (pPowers pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 4, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 6 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 7 (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower.roundBody pErase)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 6)))))



def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V))
    (μ : ℕ → ℤ) (powers : ℕ) (ret : ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ r : ℤ, σ = ⟨_root_.Light.frame [W,V,offset,_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S),powers,ret,_root_.ThreeSum.LightReportingSuffixLower.scanMask S j,j,r],μ⟩







end ThreeSum.LightReportingSuffixLower

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Explicit local suffix leaves evaluated by actual global source reads -/

namespace ThreeSum.LightReportingSuffixSum
open _root_.ThreeSum.LightReportingSuffixSum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}









def roundBody (pLeaf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 19 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 13) (_root_.ThreeSum1960614.Machine.Light.v 18)))) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLeaf [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 11), _root_.ThreeSum1960614.Machine.Light.v 19, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16] 20) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 17) (_root_.ThreeSum1960614.Machine.Light.v 20)))))

def body (pLeaf : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 17 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 18 (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.roundBody pLeaf)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 17))))



def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (Q : Finset (Fin V)) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V)))
    (cut t maskBase baseL baseR work j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (mask r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [W,cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
      V,2^offset,Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,
      _root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing j,j,mask,r],μ'⟩ ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work





end ThreeSum.LightReportingSuffixSum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier
open _root_.ThreeSum.ReportingHostFrontier


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open scoped _root_.BigOperators

def children {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) : List (Finset (Fin (464*h))) :=
  if hk : k < J then _root_.ThreeSum.ReportingHostMasks.localChildren ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩) h else []







section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def frontier {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (k : ℕ) :=
  _root_.ThreeSum.Reporting.frontier (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w) k

























end Indices

end ThreeSum.ReportingHostFrontier

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compute the representation cap from the actual retained cover

The two factors are read from the verified cover header. An actual scalar
power loop computes the J-fold cap; no cap value is supplied as an input.
-/

namespace ThreeSum.LightDenseCap
open _root_.ThreeSum.LightDenseCap


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

def base (h : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h^2

def word (h J : ℕ) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base h+1)^(J+1)+_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base h+J+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h^2+_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h+20

def body (pPower : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 2 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 10)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 2))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPower [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 1] 0)))))









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ → ℤ} {free h J d : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.body 1,_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body]



end ThreeSum.LightDenseCap

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted
open _root_.ThreeSum.LightGuardedWanted


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000


def right (h J : ℕ) : ℕ → ℤ := fun j => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J).getD j 0
def totalKeys (h J : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h^J
def keyBound (P h J : ℕ) : ℕ := 2*P+(464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)^J
def wantedFree (free h J n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J+3*n

/-- h, block count, A-incidence array and length, arithmetic modulus,
guarded modulus, and first free address. -/
def body (pCover pLifts pWanted : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCover [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 6] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 11))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pLifts [_root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 10] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pWanted [_root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 12] 0))))))))

def liftProgram : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.program _root_.ThreeSum1960614.Machine.ThreeSum.LightRawAKeys.program
def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.liftProgram _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.body 67 68 97]



def time (P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.time h J+_root_.ThreeSum.LightRawAKeys.time xs.length U+
    _root_.ThreeSum.LightBalancedWanted.time M (_root_.ThreeSum.LightGuardedWanted.left P xs) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J)+300

def space (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.space free h J)
    (max (_root_.ThreeSum.LightRawAKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J) xs.length U)
      (_root_.ThreeSum.LightBalancedWanted.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free h J xs.length) M (_root_.ThreeSum.LightGuardedWanted.left P xs) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
        (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J)))

def word (P M h J U n : ℕ) : ℕ :=
  max (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.word h J) (max (_root_.ThreeSum.LightRawAKeys.word P U)
    (_root_.ThreeSum.LightBalancedWanted.word M (3*n) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J)))







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightGuardedWanted

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual output-sensitive enumeration and evaluation of explicit local suffix leaves -/

namespace ThreeSum.LightReportingSuffixExplicit
open _root_.ThreeSum.LightReportingSuffixExplicit


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
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pEnum pSum : ℕ) where
  (pWeights pCore pLeaf pAddress : ℕ)
  leafProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafCell.Procs P pLeaf pAddress
  enumerate : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body leafProcs.pPowers leafProcs.pErase)
  core : P[pCore]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.body pLeaf)

def roundBody (pEnum pSum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [_root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 15] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 17, _root_.ThreeSum1960614.Machine.Light.v 18, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 15] 19) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 19)))))

def body (pEnum pSum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 17 (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.roundBody pEnum pSum)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 16))))




def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage cut t baseL baseR maskBase work j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (count r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [W,cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,V,2^offset,
      Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,baseL,baseR,maskBase,work,
      _root_.ThreeSum.ExplicitLayers.valueSum Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) j,j,count,r],μ'⟩ ∧
      _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work maskBase (_root_.ThreeSum.SubsetAddress.layerOffset Q.card t)





end ThreeSum.LightReportingSuffixExplicit

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete box-leaf preprocessing over the shrinking suffix ground set

Each local cardinality layer is actually enumerated at width V and evaluated
against the width-W source transforms. The exponentially sized storage and
enumeration are downsetCap V boxCut; W occurs only in polynomial overhead.
-/

namespace ThreeSum.LightReportingSuffixTable
open _root_.ThreeSum.LightReportingSuffixTable


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





def roundBody (pEnumSetup pBatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnumSetup [_root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBatch [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 14] 17))

def body (pEnumSetup pBatch : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 15 (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.roundBody pEnumSetup pBatch)



def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage baseL baseR dst maskBase work : ℕ)
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [W,sourceCut,boxCut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
      V,2^offset,baseL,baseR,dst,maskBase,work,j,n,r],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase dst (_root_.ThreeSum.SubsetAddress.downsetCap V boxCut) ∧
    _root_.ThreeSum.LightZetaCell.TableAt μ' dst boxCut (_root_.ThreeSum.LightSignedLeafTable.stageValues μ dst j (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR))



def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedBoxSetup.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.body 6 10,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch.body 25,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.body 3 26]





end ThreeSum.LightReportingSuffixTable

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup
open _root_.ThreeSum.LightDenseSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def body (pCap pScore : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 15 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 4))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCap [_root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13] 16) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScore [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 15] 17) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 18 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 16) (_root_.ThreeSum1960614.Machine.Light.v 17))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.v 18)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.v 16)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.k 3)) (_root_.ThreeSum1960614.Machine.Light.v 17)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 14))))))))))

def joinedProgram : _root_.ThreeSum1960614.Machine.Light.Program :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.program _root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScore.program

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.joinedProgram++[_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.body 0 18]





def word (maxMod nA nB nC g R s U h J : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word h J+_root_.ThreeSum.LightBandWeightedScore.word maxMod nA nB nC g R s U+
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J*(R*(s*g^3))+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J+20







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}



end ThreeSum.LightDenseSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The complete sparse query consumes suffix-local box tables

Explicit leaves use local output-sensitive enumeration and global source
reads; canonical boxes use only local-width compact addresses. The exact
finite partition yields the same global source Möbius value.
-/

namespace ThreeSum.LightReportingSuffixQuery
open _root_.ThreeSum.LightReportingSuffixQuery


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open scoped _root_.BigOperators

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def body (pExplicit pBoxes pSign : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pExplicit [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17] 18) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pBoxes [_root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 15, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 17] 19) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 20 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 18) (_root_.ThreeSum1960614.Machine.Light.v 19))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSign [_root_.ThreeSum1960614.Machine.Light.v 20, _root_.ThreeSum1960614.Machine.Light.v 9] 0))))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightSparseQuery.program ++
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskUnion.body 17 20,_root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.body 24 10 22,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.body 25,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.body 3 26,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.body 27 2 22]

def leafProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafCell.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program 25 13 where
  pUnion := 24
  pLookup := 10
  pSign := 22
  pSize := 12
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pPowers := 17
  pRank := 18
  pOffset := 19
  pErase := 20
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl

def explicitProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program 3 26 :=
  ⟨4,5,25,13,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.leafProcs,rfl,rfl,rfl,rfl⟩

def boxProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program 3 7 where
  pWeights := 4
  pPowers := 17
  pErase := 20
  pCore := 5
  pBox := 9
  pMinimum := 11
  pLookup := 10
  pSize := 12
  pAddress := 13
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pRank := 18
  pOffset := 19
  enumerate := rfl
  weights := rfl
  erase := rfl
  core := rfl
  sum := rfl
  box := rfl
  minimum := rfl
  lookup := rfl
  size := rfl
  address := rfl
  table := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl







end ThreeSum.LightReportingSuffixQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete suffix-local box preprocessing, including its own shift factor

The program constructs the mask-lifting power, fills every local compact leaf
through the original global source reads, and builds every local prefix-zeta
stage. Its exponentially sized domain is the residual width V.
-/

namespace ThreeSum.LightReportingSuffixSetup
open _root_.ThreeSum.LightReportingSuffixSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def coreBody (pTable pStages : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pTable [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pStages [_root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14] 0))

def body (pPowers pCore : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 14, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 16 (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 14) (_root_.ThreeSum1960614.Machine.Light.v 9)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCore [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 16, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 13, _root_.ThreeSum1960614.Machine.Light.v 14] 0)))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.coreBody 27 2,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.body 14 28]

def procs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafCell.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.program 6 10 where
  pUnion := 7
  pLookup := 8
  pSign := 19
  pSize := 9
  pSetup := 11
  pBuild := 12
  pFill := 13
  pRow := 15
  pLinear := 24
  pPowers := 14
  pRank := 16
  pOffset := 17
  pErase := 18
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl












end ThreeSum.LightReportingSuffixSetup

end ThreeSum1960614.Machine


