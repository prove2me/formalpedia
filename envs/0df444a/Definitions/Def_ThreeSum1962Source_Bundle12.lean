-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle12
-- name    : ThreeSum1962Source_Bundle12
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:19:48.681988+00:00
-- url     : https://prove2.me/theorems/d584083c-aea4-4b56-be7a-09cefe0d2af2
-- title:
--   Parameter initialization, source hosts, and assembled search drivers
-- statement:
--   This bundle defines composed Light programs for parameter initialization, local-cover construction, balanced wanted-pair joins, source-band catalogs, color normalization, common-prime minimization, and sparse queries. Dense setup stores
--   $$
--   [0,CS,C,S],
--   $$
--   where $C$ is the representation cap and $S$ the aggregate weighted score. The fast-driver layout places nineteen parameter cells at free address $f$, a reusable six-cell color row at $f+19$, and color workspace at $f+25$. Further definitions specify retained B/C catalog headers, source-cover interfaces, reporting-prefix keys, suffix embeddings, terminal choices, positive frontier order, and frontier slots whose capacity depends on root raw mass. Program-interface predicates and resource functions support subsequent execution theorems.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockSourceCoverInput.lean#L17-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorWantedData.lean#L9-L10
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBalancedWanted.lean#L19-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPrimeChain.lean#L19-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPrimeMinimum.lean#L18-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawAColor.lean#L22-L214
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawAResources.lean#L18-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockChildrenIndexed.lean#L14-L83
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockMasks.lean#L19-L163
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceRetainedHost.lean#L24-L62
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDenseSetup.lean#L21-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorLayout.lean#L12-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorNormalize.lean#L14-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverHost.lean#L20-L45
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverMagnitude.lean#L10-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverTables.lean#L17-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightParameterInit.lean#L21-L202
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingPositiveMasks.lean#L26-L28
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandPair.lean#L22-L60
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandSetup.lean#L19-L49
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSparseQuery.lean#L21-L157
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumColorDriverBounded.lean#L12-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumFastDriver.lean#L18-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumReportingSetupDense.lean#L17-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostFrontier.lean#L17-L48
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostFrontierLayout.lean#L16-L114
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPositive.lean#L50-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L20-L95
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostSuffix.lean#L18-L120
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostTerminalChoices.lean#L24-L95

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorWantedData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys


/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData

open Light WantedResidueKeys

def nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : ℕ :=
  LightWantedSetup.pairBase out NL NR M+2*total M left right NL NR shift























end ThreeSum.EncodedColorWantedData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBalancedWanted


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys


/-!
# Executable balancing followed by the complete wanted-pair join

The host chooses the common shift from the two original signed arrays and
then builds every matching original-position pair. The returned count obeys
the exact incidence mean bound. The offset and the residue/bucket inputs are
computed by the closed program, with the same duplicate multiplicities.
-/

namespace ThreeSum.LightBalancedWanted

open Light WantedResidueKeys

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- Two original signed arrays, their lengths, modulus, and free address. -/
def body (pOffset pWanted : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 2) (v 3)))
    (Light.Stmt.seq (.call pOffset [v 0, v 1, v 2, v 3, v 4, v 6, v 5] 7)
      (.call pWanted [v 0, v 1, v 2, v 3, v 4, v 7, v 5] 0)))

def program : Program := ReportingHostRelocation.program
  LightOriginalOffset.program LightWantedSetup.program ++ [body 0 24]



def time (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) : ℕ :=
  LightOriginalOffset.time M NL NR U+
    LightWantedSetup.time M left right NL NR U M
      (LightOriginalOffset.selected M left right NL NR)+100

def space (free M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) : ℕ :=
  max (LightOriginalOffset.space free M (NL+NR) U)
    (LightWantedSetup.space free M left right NL NR U M
      (LightOriginalOffset.selected M left right NL NR))

def word (M NL NR U : ℕ) : ℕ :=
  max (LightOriginalOffset.word M (NL+NR) U) (LightSourceResidues.word M M U M)

variable {lim : Limits}












































































end ThreeSum.LightBalancedWanted

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout


/-!
# Original source array to a complete packed band catalog

The band count, truncated capacity, all pointer-table addresses, and shared
remainder scratch are computed by actual RAM expressions. Each original
slice is visited once by the existing code/histogram/prefix/scatter program.
-/

namespace ThreeSum.LightSourceBandSetup

open Light BandPartition SourceBandLayout

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

def addressBody (pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 9
      ((Light.Expr.op Light.Op.add) (v 6)
        ((Light.Expr.op Light.Op.mul) (k 6) (v 8))))
    (Light.Stmt.seq
      (.set 10
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (k 3) (v 4))
            (k 1))
          ((Light.Expr.op Light.Op.mul) (k 2) (v 7))))
      (Light.Stmt.seq
        (.set 11
          ((Light.Expr.op Light.Op.add) (v 9)
            ((Light.Expr.op Light.Op.mul) (v 8) (v 10))))
        (Light.Stmt.seq
          (.call pBatch
            [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11] 12)
          (.set 0 (v 11))))))

def countBody (pDivide pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 8 (k 0))
    (Light.Stmt.seq
      (.ite (Light.Cond.lt (k 0) (v 1))
        (Light.Stmt.seq
          (.call pDivide [(Light.Expr.op Light.Op.sub) (v 1) (k 1), v 2] 8)
          (.set 8 ((Light.Expr.op Light.Op.add) (v 8) (k 1))))
        .skip)
      (addressBody pBatch)))

def body (pDivide pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 7 (v 2))
    (Light.Stmt.seq (.ite (Light.Cond.lt (v 1) (v 2)) (.set 7 (v 1)) .skip)
      (countBody pDivide pBatch)))

def addressTime (n g p m U D : ℕ) : ℕ := LightSourceBandBatch.time n g p m U D+250
def countTime (n g p m U D : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+LightSourceBandBatch.time n g p m U D+350
def time (n g p m U D : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+LightSourceBandBatch.time n g p m U D+500

structure Procs (P : Program) (pMain : ℕ) where
  pDivide : ℕ
  pBatch : ℕ
  divide : P[pDivide]? = some LightSmallDivide.body
  batch : LightSourceBandBatch.Procs P pBatch
  main : P[pMain]? = some (body pDivide pBatch)

variable {lim : Limits} {P : Program} {d : ℕ}



























































































































end ThreeSum.LightSourceBandSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandRawAColor


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists


/-!
# Original input to the retained owner and A-incidence catalog

The selected index coloring, class extraction, normalization, endpoint
construction, three rectangular owner tables, four-cell owner records, and
packed A-incidence rows are all executed by this fixed program. The rows
retain physical owner identities and sorted-array coordinates. Membership
in the original color classes is retained separately by `Represents`.
-/

namespace ThreeSum.LightBandRawAColor

open Light BandPartition BandCandidateRows BandRawA ColorClassLists

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000

/-- The existing color/band arguments, followed by records and incidence
value destinations. -/
def body (pColor pCatalog : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pColor
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
        v 14, v 15, v 16, v 17, v 18, v 19, v 20]
      23)
    (.call pCatalog [v 20, v 21, v 14, v 15, v 17, v 19, v 13, v 22] 0))

def catalogTime (n g : ℕ) : ℕ :=
  3000*(ColorBandBounds.count n g+3*size n g+1)*(g+1)

def time (W n g : ℕ) : ℕ := LightColorBands.time W n g+catalogTime n g+300

def space (work vals W n g : ℕ) : ℕ :=
  max (LightColorBands.space work W n g)
    (LightBandRawA.space vals (ColorBandBounds.count n g) g)

def word (W n g U : ℕ) : ℕ :=
  LightColorBands.word W n g U+
    LightBandRawACatalog.word n (size n g) (size n g) (size n g) g

def depth (W n g : ℕ) : ℕ := LightColorBands.depth W n g+5

def Output (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g)
    (originalA originalB originalC : List ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    let rs := sortedRecords A B C g hg hsA hsB hsC
    r = ((items A.length g rs).length : ℤ) ∧
      LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
      LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
      LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
      LightBandEnumeration.Tables μ tables
        (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
        (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
        (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)) ∧
      Seg μ rec (cells rs) ∧
      Stored μ vals (LightBandRawA.ownerBase vals rs.length g)
        (LightBandRawA.positionBase vals rs.length g)
        (fun i => A.getD i 0) (items A.length g rs)




















structure Procs (P : Program) (pMain : ℕ) where
  pColor : ℕ
  pCatalog : ℕ
  color : LightColorBands.Procs P pColor
  catalog : LightBandRawACatalog.Procs P pCatalog
  main : P[pMain]? = some (body pColor pCatalog)

variable {lim : Limits} {P : Program} {d : ℕ}






























































































/-- The verified color/band prefix retains its original procedure indices. -/
def program : Program := LightColorBands.program ++
  [LightBandRawACatalog.body 28 38,
    LightBandCandidates.body 29 32 35,
    LightBandCandidatesTable.body 30,LightBandCandidatesRow.body 31,LightBandCandidatesCell.body .bc,
    LightBandCandidatesTable.body 33,LightBandCandidatesRow.body 34,LightBandCandidatesCell.body .ab,
    LightBandCandidatesTable.body 36,LightBandCandidatesRow.body 37,LightBandCandidatesCell.body .ac,
    LightBandRawA.body 39,LightBandRawAStep.body 40,LightBandRawARow.body 41 42,copyBody,fillBody,
    body 20 27]

def programProcs : Procs program 43 where
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

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout


/-! # Compute and retain the selected-color array layout -/

namespace ThreeSum.LightEncodedColorLayout

open Light BandPartition EncodedColorLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 11000

def body (pDivide : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDivide [(Light.Expr.op Light.Op.sub) (v 0) (k 1), v 1] 3)
    (Light.Stmt.seq (.set 4 ((Light.Expr.op Light.Op.add) (v 3) (k 1)))
      (Light.Stmt.seq
        (.set 5
          ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (k 3) (v 4))
            (v 4)))
        (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 2) (k 8)))
          (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.add) (v 6) (v 0)))
            (Light.Stmt.seq
              (.set 8
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) (v 7) (v 0)) (k 1)))
              (Light.Stmt.seq
                (.set 9
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v 8) (v 0)) (k 1)))
                (Light.Stmt.seq
                  (.set 10
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add) (v 9) (v 0)) (k 1)))
                  (Light.Stmt.seq
                    (.set 11 ((Light.Expr.op Light.Op.add) (v 10) (v 0)))
                    (Light.Stmt.seq
                      (.set 12
                        ((Light.Expr.op Light.Op.add)
                          ((Light.Expr.op Light.Op.add) (v 11) (k 2))
                          ((Light.Expr.op Light.Op.mul) (k 2) (v 0))))
                      (Light.Stmt.seq
                        (.set 13 ((Light.Expr.op Light.Op.add) (v 12) (v 0)))
                        (Light.Stmt.seq
                          (.set 14
                            ((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add) (v 13) (k 2))
                              ((Light.Expr.op Light.Op.mul) (k 2) (v 0))))
                          (Light.Stmt.seq
                            (.set 15 ((Light.Expr.op Light.Op.add) (v 14) (v 0)))
                            (Light.Stmt.seq
                              (.set 16
                                ((Light.Expr.op Light.Op.add)
                                  ((Light.Expr.op Light.Op.add) (v 15) (k 2))
                                  ((Light.Expr.op Light.Op.mul) (k 2) (v 0))))
                              (Light.Stmt.seq
                                (.set 17
                                  ((Light.Expr.op Light.Op.add) (v 16) (v 5)))
                                (Light.Stmt.seq
                                  (.set 18
                                    ((Light.Expr.op Light.Op.add) (v 17)
                                      ((Light.Expr.op Light.Op.mul) (k 4) (v 5))))
                                  (Light.Stmt.seq
                                    (.set 19
                                      ((Light.Expr.op Light.Op.add) (v 18)
                                        ((Light.Expr.op Light.Op.mul)
                                          ((Light.Expr.op Light.Op.mul) (k 3)
                                            (v 1))
                                          (v 5))))
                                    (Light.Stmt.seq (.store (v 2) (v 10))
                                      (Light.Stmt.seq
                                        (.store
                                          ((Light.Expr.op Light.Op.add) (v 2)
                                            (k 1))
                                          (v 11))
                                        (Light.Stmt.seq
                                          (.store
                                            ((Light.Expr.op Light.Op.add) (v 2)
                                              (k 2))
                                            (v 12))
                                          (Light.Stmt.seq
                                            (.store
                                              ((Light.Expr.op Light.Op.add) (v 2)
                                                (k 3))
                                              (v 13))
                                            (Light.Stmt.seq
                                              (.store
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 2) (k 4))
                                                (v 14))
                                              (Light.Stmt.seq
                                                (.store
                                                  ((Light.Expr.op Light.Op.add)
                                                    (v 2) (k 5))
                                                  (v 15))
                                                (Light.Stmt.seq
                                                  (.store
                                                    ((Light.Expr.op Light.Op.add)
                                                      (v 2) (k 6))
                                                    (v 17))
                                                  (Light.Stmt.seq
                                                    (.store
                                                      ((Light.Expr.op
                                                          Light.Op.add)
                                                        (v 2) (k 7))
                                                      (v 18))
                                                    (.set 0
                                                      (v
                                                        19)))))))))))))))))))))))))))

def time (n g : ℕ) : ℕ := LightSmallDivide.time (n-1) g+1000
def word (n g : ℕ) : ℕ := n+g+ColorBandBounds.count n g+100

def headMemory (μ : ℕ → ℤ) (free n g : ℕ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update μ free (av free n))
      (free+1) (ae free n)) (free+2) (bv free n)) (free+3) (be free n))
      (free+4) (cv free n)) (free+5) (ce free n)) (free+6) (rec free n g)) (free+7) (vals free n g)












variable {lim : Limits} {P : Program} {d : ℕ}


























































































end ThreeSum.LightEncodedColorLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightParameterInit


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# One fixed integer-parameter initializer from the input length

The program starts with only `n`, an output pointer, and a scratch pointer.
It constructs the exact block schedule, local graph counts, selected local
prime, cap, typed global output count, radix, rounded band size, and prime
window. Every helper in the fixed program has an operational contract.
-/

namespace ThreeSum.LightParameterInit

open Light LocalCoverBounds Scales

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000

def half (n : ℕ) : ℕ := microHalf (inputBits n)

def values (n : ℕ) : List ℤ :=
  ((LightScales.values n ++ LightLocalParameters.values (half n)) ++
    LightGlobalSizes.values (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n)) ++ [(primeWindow n : ℤ)]

def body (pCore pLocal pGlobal pSqrt pPower : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCore [v 0, v 1] 3)
    (Light.Stmt.seq (.set 4 (M ((Light.Expr.op Light.Op.add) (v 1) (k 1))))
      (Light.Stmt.seq
        (.call pLocal [v 4, (Light.Expr.op Light.Op.add) (v 1) (k 5), v 2] 5)
        (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 1) (k 3))))
          (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 1) (k 5))))
            (Light.Stmt.seq
              (.call pGlobal
                [v 7, v 5, v 6, v 3, (Light.Expr.op Light.Op.add) (v 1) (k 13)] 8)
              (Light.Stmt.seq (.set 9 (M (v 1)))
                (Light.Stmt.seq (.call pSqrt [v 9] 10)
                  (Light.Stmt.seq
                    (.set 11 ((Light.Expr.op Light.Op.add) (v 10) (k 1)))
                    (Light.Stmt.seq (.call pPower [k 2, v 11] 12)
                      (Light.Stmt.seq
                        (.store ((Light.Expr.op Light.Op.add) (v 1) (k 18))
                          (v 12))
                        (.set 0 (v 8)))))))))))))

def time (n : ℕ) : ℕ := LightScales.time n+LightLocalParameters.time (half n)+
  LightGlobalSizes.time (LightGlobalSizes.localCount n) (blockCount (inputBits n)) (mu n)+
  sqrtTime (inputBits n)+LightNatPower.time (windowExponent (inputBits n))+400

def space (work n : ℕ) : ℕ := LightLocalParameters.space work (half n)

def word (n : ℕ) : ℕ := 1000*(n+1)+LightLocalParameters.word (half n)+
  LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
    (blockCount (inputBits n)) (mu n)+100*(primeWindow n+inputBits n+1)

structure Procs (P : Program) (pMain : ℕ) where
  pCore : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pSqrt : ℕ
  pPower : ℕ
  core : LightScales.Procs P pCore
  localParams : LightLocalParameters.Procs P pLocal
  globalSizes : LightGlobalSizes.Procs P pGlobal
  sqrt : P[pSqrt]? = some sqrtBody
  power : P[pPower]? = some LightNatPower.body
  main : P[pMain]? = some (body pCore pLocal pGlobal pSqrt pPower)

variable {lim : Limits} {P : Program} {d : ℕ}


























































































































def program : Program :=
  [body 1 6 20 16 21,
    LightScales.body 2 3 4 5,log2Body,cbrtCeilBody,halfBody,LightSmallDivide.body,
    LightLocalParameters.body 7 15 5,LightLocalCounts.body 8,LightSubsetSetup.body 9 13 14,
    LightPascal.buildBody 10 11,fillBody,LightPascal.rowBody 12,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 14,
    LightSelectedPrime.body 16 17,sqrtBody,LightPrimePool.body 18,LightPrimality.body 19,emodBody,
    LightGlobalSizes.body 21 5 16,LightNatPower.body]

def procs : Procs program 0 :=
  ⟨1,6,20,16,21,
    ⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨7,15,5,⟨8,9,10,11,12,13,14,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
      ⟨16,17,rfl,⟨18,⟨19,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨21,5,16,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩









end ThreeSum.LightParameterInit

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandPrimeMinimum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore


/-!
# Execute common-prime minimization over all owner candidates

Every candidate prime is scored by the actual aggregate band loop. The
first minimum is returned, with no supplied score array or counting oracle.
-/

namespace ThreeSum.LightBandPrimeMinimum

open Light BandCandidateRows BandWeightedScore BandPrimeChoice

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def body (pScore : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pScore
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8,
        (Light.Expr.op Light.Op.mul) (v 9) (M (v 10)), v 10, v 11, v 12]
      13)
    (Light.Stmt.seq (.set 14 (k 0))
      (Light.Stmt.seq
        (.for 15 (v 11)
          (Light.Stmt.seq
            (.call pScore
              [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8,
                (Light.Expr.op Light.Op.mul) (v 9)
                  (M ((Light.Expr.op Light.Op.add) (v 10) (v 15))),
                v 10, v 11, v 12]
              16)
            (.ite (Light.Cond.lt (v 16) (v 13))
              (Light.Stmt.seq (.set 13 (v 16)) (.set 14 (v 15))) .skip)))
        (.set 0 (M ((Light.Expr.op Light.Op.add) (v 10) (v 14)))))))

def program : Program := LightBandWeightedScore.program ++ [body 16]



def time (maxMod g R s U : ℕ) : ℕ :=
  LightBandWeightedScore.time maxMod g R s U+
    s*(LightBandWeightedScore.time maxMod g R s U+140)+140

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (a b c nA nB nC g recs R q aux s free i : ℕ) (σ : State) : Prop :=
  ∃ (value : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,q,aux,s,free,
      f (LightMinimum.least f i),LightMinimum.least f i,i,value],ν⟩ ∧ Kept μ ν free






variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}






























































































































end ThreeSum.LightBandPrimeMinimum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDenseSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding


/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup

open Light GlobalEncoding BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def body (pCap pScore : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 15 ((Light.Expr.op Light.Op.add) (v 14) (k 4)))
    (Light.Stmt.seq (.call pCap [v 12, v 13] 16)
      (Light.Stmt.seq
        (.call pScore
          [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 15] 17)
        (Light.Stmt.seq (.set 18 ((Light.Expr.op Light.Op.mul) (v 16) (v 17)))
          (Light.Stmt.seq (.store (v 14) (k 0))
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 14) (k 1)) (v 18))
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 14) (k 2)) (v 16))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 14) (k 3)) (v 17))
                  (.set 0 (v 14))))))))))

def joinedProgram : Program :=
  ReportingHostRelocation.program LightDenseCap.program LightBandWeightedScore.program

def program : Program := joinedProgram++[body 0 18]



def time (maxMod g R s U J : ℕ) : ℕ :=
  LightDenseCap.time J+LightBandWeightedScore.time maxMod g R s U+400

def word (maxMod nA nB nC g R s U h J : ℕ) : ℕ :=
  LightDenseCap.word h J+LightBandWeightedScore.word maxMod nA nB nC g R s U+
    representationCap h J*(R*(s*g^3))+representationCap h J+20

def Stored (μ : ℕ → ℤ) (free cap H : ℕ) : Prop :=
  μ free=0 ∧ μ (free+1)=((cap*H : ℕ) : ℤ) ∧
    μ (free+2)=(cap : ℤ) ∧ μ (free+3)=(H : ℤ)

def falseScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  Arithmetic.weightedFalseCount (BandRawA.finiteAllProducts nA nB nC g rs)
    (fun t => C t.2.2.val-B t.2.1.val-BandRawA.valueAt nA g rs A t.1.val)
    (Auxiliary.moduli (WeightedScore.auxiliarySet primes s)) q







variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}




























































































end ThreeSum.LightDenseSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockMasks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Packing physical block masks into global row-major coordinates

The fixed program builds a power table, scales every input row mask by its
block position, writes the global row masks, and returns their union mask.
Only linear scans and polynomial scratch are used.
-/

namespace ThreeSum.LightBlockMasks

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout

variable {lim : Limits} {P : Program}

def roundBody : Stmt :=
  (Light.Stmt.seq
    (.set 10
      ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v 2) (v 9)))
        (v 7)))
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 3) (v 9)) (v 10))
      (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 8) (v 10)))
        (.set 7 ((Light.Expr.op Light.Op.mul) (v 7) (v 6))))))

def nonemptyBody (pPowers : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 4, (Light.Expr.op Light.Op.add) (v 1) (k 1), k 2] 5)
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 4) (v 1))))
      (Light.Stmt.seq (.set 7 (k 1))
        (Light.Stmt.seq (.set 8 (k 0))
          (Light.Stmt.seq (.for 9 (v 0) roundBody) (.set 0 (v 8)))))))

/-- Block count, row width, physical input masks, packed-mask output, scratch. -/
def body (pPowers : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 0))) (nonemptyBody pPowers) (.set 0 (k 0))

def time (J L : ℕ) : ℕ := powTableTime (L+1)+J*150+200

def Inv {J L : ℕ} (μ : ℕ → ℤ) (rows : Fin J → Finset (Fin L))
    (src dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [J,L,src,dst,work,powRet,2^L,2^(j*L),prefixMask rows j,j,r],μ'⟩ ∧
    SegN μ' dst ((packedMasks rows).take j) ∧ Powers μ' work L ∧
    KeptBut μ μ' work dst J






















































































































def program : Program := [body 1,powTableBody]
















end ThreeSum.LightBlockMasks

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockSourceCoverInput


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Constructed local-cover output as source-encoding input

This adapter connects the actual cover builder's retained candidate tables
and gathered occurrence rows to the exact reads used by source preparation.
Occurrence order, repeated candidates, and both independent bucket tables
are preserved without further searching or histogram construction.
-/

namespace ThreeSum.BlockSourceCoverInput

open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags

structure Input (μ : ℕ → ℤ) (h maps candidates histL histR : ℕ) : Prop where
  candidates : ∀ s : Occurrence h,
    μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ)
  leftRows : ∀ s < scheduleSize h, ∀ t < 512*h,
    μ (maps+2*(512*h)*s+t) = (mapRow h false s t : ℤ)
  rightRows : ∀ s < scheduleSize h, ∀ t < 512*h,
    μ (maps+2*(512*h)*s+512*h+t) = (mapRow h true s t : ℤ)
  leftCounts : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
    μ (histL+k*localPrime h+r) = (leftCount h k r : ℤ)
  rightCounts : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
    μ (histR+k*localPrime h+r) = (rightCount h k r : ℤ)

















































end ThreeSum.BlockSourceCoverInput

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockChildrenIndexed


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
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
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds

variable {lim : Limits}

def childPrefixes {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) :=
  (localChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h).map fun S => pre ++ [S]
































































def childAt {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) (i : ℕ) :=
  (childPrefixes q pre hk)[i]?.getD []
































































end ThreeSum.LightBlockChildrenIndexed

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostFrontier


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks


/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier

open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators

def children {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Fin (512*h))) :=
  if hk : k < J then localChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h else []























section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def frontier {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :=
  Reporting.frontier (children w.2.2) (prefixQuery I w) k

























































































end Indices

end ThreeSum.ReportingHostFrontier

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostSuffix


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Local suffix coordinates with exact global source semantics

The remaining ambient ground set has width V, whereas source transforms use
the original width W. A contiguous shift embeds local box masks into global
source masks. Enumeration and box-table addresses can therefore use V without
changing the original raw-incidence query.
-/

namespace ThreeSum.ReportingHostSuffix

open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

def shiftEmbedding {W V : ℕ} (offset : ℕ) (hfit : offset+V ≤ W) : Fin V ↪ Fin W where
  toFun i := ⟨offset+i.val,(Nat.add_lt_add_left i.isLt offset).trans_le hfit⟩
  inj' := by intro i j he; apply Fin.ext; have := congrArg Fin.val he; simp only at this; omega




def liftSet {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) : Finset (Fin W) :=
  S.map (shiftEmbedding offset hfit)
























def lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W)) : Finset (Fin V) :=
  univ.filter fun i => shiftEmbedding offset hfit i ∈ Q

































def leafWeight {W V offset : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (preL preR : Finset (Fin W))
    (S : Finset (Fin V)) : ℤ := SignedLeaf.value f g stage preL preR (liftSet hfit S)


















theorem block_fit {J L k : ℕ} (hk : k ≤ J) : k*L+(J-k)*L ≤ J*L := by
  rw [← Nat.add_mul,Nat.add_sub_of_le hk]










def localQuery {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    Finset (Fin ((J-k)*L)) := lowerSet (block_fit hk) (querySet k Q)









section Original

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
open RawIncidences RawReporting RawPrefixCounts
















end Original
end ThreeSum.ReportingHostSuffix

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPrefixCatalog


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Exact prefix catalog keys and sharing for fixed source occurrences

A catalog key consists only of the first k ordered disjoint balanced row
pairs. Its exact cardinality is (microOutputs*microPartitions)^k. Neither the
remaining output rows nor the wanted A-index enter a local box table once
the global occurrence vector is fixed.
-/

namespace ThreeSum.ReportingHostPrefixCatalog

open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix

set_option linter.unusedSectionVars false

abbrev Prefix (h k : ℕ) := Fin k → Edge (512*h) h





def leftRows {h J k : ℕ} (p : Prefix h k) : Fin J → Finset (Fin (512*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.1 else ∅

def rightRows {h J k : ℕ} (p : Prefix h k) : Fin J → Finset (Fin (512*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.2 else ∅

def leftSet {h J k : ℕ} (p : Prefix h k) : Finset (Fin (J*(512*h))) :=
  leftPrefix k (leftRows p)

def rightSet {h J k : ℕ} (p : Prefix h k) : Finset (Fin (J*(512*h))) :=
  leftPrefix k (rightRows p)















def ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) : Prefix h k :=
  fun i =>
    let j : Fin J := ⟨i.val,i.isLt.trans_le hk⟩
    ⟨(prefixRows pre j,outputRows q j \ prefixRows pre j),by
      have hu := hp.2 j i.isLt
      have hQ : (outputRows q j).card = 2*h := LayerCounts.mem_vertices.mp (q j).2.property
      apply LayerCounts.mem_edgeSet.mpr
      refine ⟨hu.2,?_,disjoint_sdiff_self_right⟩
      rw [Finset.card_sdiff_of_subset hu.1,hQ,hu.2]
      omega⟩






















section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftSourceOf {h J : ℕ} (o : Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h)) (fun S => (leftWeights o P B b S : ℤ))

def rightSourceOf {h J : ℕ} (o : Occurrences h J) (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h)) (fun S => (rightWeights o P shift C c S : ℤ))









































end Sources

end ThreeSum.ReportingHostPrefixCatalog

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostTerminalChoices


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Finite terminal completions in the actual mask enumerator's order

At any valid reporting prefix, a full balanced endpoint needs exactly
`(J-k)*h` of the remaining query coordinates. Enumerating that one layer
contains every retained completion and costs no more than the terminal
Boolean-cube allowance. The selected bucket pair masses sum to at most the
unchanged original raw prefix count.
-/

namespace ThreeSum.ReportingHostTerminalChoices

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open QueryCoordinates
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def choices {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Coord J (512*h))) :=
  (missingSets (querySet k (outputRows q)) ((J-k)*h)).map unindexSet




























































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def pairMass {h J : ℕ} (P shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512*h)))) (S : Finset (Coord J (512*h))) : ℕ :=
  leftWeights (outputOccurrences q) P B b (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S)*
    rightWeights (outputOccurrences q) P shift C c
      (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S))
















end ThreeSum.ReportingHostTerminalChoices

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverMagnitude


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-! # One uniform exponential bound for all finite local-cover dimensions -/

namespace ThreeSum.LightLocalCoverMagnitude

open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout

def magnitude (h : ℕ) : ℕ := 2^(600000*(h+1)^2)

structure Bounds (h B : ℕ) : Prop where
  positive : 1 ≤ B
  width : 512*h+1 ≤ B
  vertices : LightLocalCoverLayout.vertices h+1 ≤ B
  prime : localPrime h+1 ≤ B
  cap : localBucketCap h+1 ≤ B
  candidates : rows h+1 ≤ B
  rounds : scheduleSize h+1 ≤ B
  decodePower : (localPrime h)^(2*(512*h)+1)+1 ≤ B
  maskPower : 2^(512*h+1)+1 ≤ B









































































end ThreeSum.LightLocalCoverMagnitude

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverHost


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Constructing the exact local schedule and its retained tables

This fixed program constructs every candidate table, executes the unchanged
first-maximum greedy routine, and gathers the selected coefficient rows.
Its output contains the original schedule maps in exact occurrence order,
including ties and repetitions, and retains both candidate count tables.
-/

namespace ThreeSum.LightLocalCoverHost

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

def body (pMatrix pGreedy pGather : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pMatrix
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13]
      16)
    (Light.Stmt.seq (.set 17 ((Light.Expr.op Light.Op.mul) (v 1) (v 1)))
      (Light.Stmt.seq (.call pGreedy [v 12, v 13, v 2, v 17, v 14] 16)
        (Light.Stmt.seq (.set 18 ((Light.Expr.op Light.Op.mul) (k 2) (v 0)))
          (Light.Stmt.seq (.call pGather [v 16, v 7, v 15, v 14, v 18] 16)
            (.set 0 (v 15)))))))

def time (h : ℕ) : ℕ :=
  LightLocalCoverMatrix.time (512*h) (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) (rows h)+
  LightCoverGreedy.time (rows h) (cols h) (scheduleSize h)+
  LightWeightGather.time (scheduleSize h) (2*(512*h))+200

def word (h : ℕ) : ℕ :=
  LightLocalCoverCandidate.word (512*h) (LocalMaskGraph.vertexCount (512*h) h)
    (localPrime h) (localBucketCap h) (rows h)+
  LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h))

structure Procs (P : Program) (pMain : ℕ) where
  pMatrix : ℕ
  pGreedy : ℕ
  pGather : ℕ
  matrix : LightLocalCoverMatrix.Procs P pMatrix
  greedy : LightCoverGreedy.Procs P pGreedy
  gather : LightWeightGather.Procs P pGather
  main : P[pMain]? = some (body pMatrix pGreedy pGather)

variable {lim : Limits} {P : Program} {d : ℕ}











































































































































end ThreeSum.LightLocalCoverHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverTables


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments


/-!
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables

open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

def Data (μ : ℕ → ℤ) (h maps hist0 hist1 matrixPtr : ℕ) : Prop :=
  LightLocalCoverMatrix.Tables μ (512*h) (LocalMaskGraph.vertexCount (512*h) h)
    (localPrime h) (localBucketCap h) maps hist0 hist1 matrixPtr
    (LocalMaskGraph.maskAt (512*h) h) (LocalCoverMatrix.bits (512*h) h)
    (fun j => LocalMaskHashes.coeff false (candidate h j))
    (fun j => LocalMaskHashes.coeff true (candidate h j)) (rows h)

def ScheduleRows (μ : ℕ → ℤ) (h dst : ℕ) : Prop :=
  ∀ s < scheduleSize h, ∀ i < 512*h,
    μ (dst+s*(2*(512*h))+i) = (BlockCoefficientRows.mapRow h false s i : ℤ) ∧
    μ (dst+s*(2*(512*h))+512*h+i) = (BlockCoefficientRows.mapRow h true s i : ℤ)
















































































end ThreeSum.LightLocalCoverTables

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSparseQuery


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A complete sparse Möbius query in the benchmark language

The fixed program constructs every missing-mask layer it uses, evaluates
explicit leaves through source-stage reads, evaluates canonical boxes
through their compact stored stages, adds both contributions, and applies
the outer sign. The exact partition identity proves the resulting Möbius
value. No enumeration, leaf-value, or query-value oracle is assumed.
-/

namespace ThreeSum.LightSparseQuery

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open scoped BigOperators

variable {lim : Limits} {P : Program}

def queryItems (c t : ℕ) : ℕ := layerOffset c t+c.choose t

def magnitudeBound (W stage c t B D : ℕ) : ℕ :=
  (queryItems c t+1)*(2^W*((2^stage*B)*(2^stage*D)))

/-- Width, source cutoff, suffix stage, two prefixes, query cardinality and
mask, missing threshold, two source bases, box cutoff and base, mask buffer,
and polynomial scratch. -/
def body (pExplicit pBoxes pSign : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pExplicit
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 14, v 15]
      16)
    (Light.Stmt.seq (.call pBoxes [v 0, v 12, v 7, v 8, v 9, v 13, v 14, v 15] 17)
      (Light.Stmt.seq (.set 18 ((Light.Expr.op Light.Op.add) (v 16) (v 17)))
        (.call pSign [v 18, v 7] 0))))




















































































































def program : Program :=
  [body 1 2 22,LightExplicitSum.body 3 6,LightCanonicalBoxSum.body 3 7,
    LightQueryEnumeration.body 4 5,LightQueryWeights.body 17 20,LightSubsetEnumeration.body 5,
    LightLeafSum.body 8,LightBoxSum.body 9,LightSignedLeaf.body 10 22,
    LightQueryBox.body 11 10,LightStageLookup.body 12 13,LightMaskMinimum.body 17 20,
    LightDownsetSize.body 14 19,LightDownsetAddress.body 14 19,LightSubsetSetup.body 15 17 18,
    buildBody 16 21,fillBody,powTableBody,rankBody 18,LightSubsetOffset.body,
    LightMaskErase.body 20,rowBody 23,LightSign.body,LightArray.linearBody]









































































































end ThreeSum.LightSparseQuery

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceRetainedHost


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Per-occurrence source construction with shared band histograms

For a fixed band pair, modulus, and common offset, this host constructs its
own compact masks, coefficient rows, endpoint arrays, and independent flags.
It then gathers from the retained band histograms and constructs both exact
original suffix-stage families. Histogram scans belong outside this loop.
-/

namespace ThreeSum.LightBlockSourceRetainedHost

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LightSubsetAddress LightPascal LocalCoverBounds BlockSourceFlags
open BlockSourceEncoding LightBlockSourceBuild

set_option maxHeartbeats 4000000
set_option maxRecDepth 14000

def body (pEnum pPrepare pStages : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pEnum [(Light.Expr.op Light.Op.mul) (v 0) (v 1), v 5, v 14, v 25] 26)
    (Light.Stmt.seq
      (.call pPrepare
        [v 0, v 1, v 2, v 3, v 4, v 7, v 8, v 9, v 10, v 11, v 14, v 26, v 15,
          v 16, v 17, v 18, v 19, v 23, v 24, v 25]
        27)
      (Light.Stmt.seq
        (.call pStages
          [v 17, v 19, v 12, v 20, v 6, v 25,
            (Light.Expr.op Light.Op.mul) (v 0) (v 1), v 5, v 22, v 26]
          27)
        (.call pStages
          [v 18, (Light.Expr.op Light.Op.add) (v 19) (v 26), v 13, v 21, v 6,
            v 25, (Light.Expr.op Light.Op.mul) (v 0) (v 1), v 5, v 22, v 26]
          27))))

def time (h J cut : ℕ) : ℕ :=
  LightDownsetEnumerationSetup.time (J*(512*h)) cut+
  LightSourcePreparation.time (downsetCap (J*(512*h)) cut) J (512*h) (localPrime h)+
  LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J)+
  LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J)+500

def space (work h J : ℕ) : ℕ :=
  max (work+(J*(512*h)+1))
    (max (LightSourcePreparation.space work J (512*h) (localPrime h))
      (LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J)))

def word (NL NR h J : ℕ) : ℕ :=
  2^(J*(512*h)+1)+
  LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
    ((512*h).choose h) (localBucketCap h)+
  LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NL+
  LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NR

structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pDownset : ℕ
  pLayer : ℕ
  pPrepare : ℕ
  pStages : ℕ
  enumMain : P[pEnum]? = some (LightDownsetEnumerationSetup.body pPowers pDownset)
  powers : P[pPowers]? = some powTableBody
  downset : P[pDownset]? = some (LightDownsetEnumeration.body pLayer)
  layer : P[pLayer]? = some (LightSubsetEnumeration.body pLayer)
  prepare : LightSourcePreparation.Procs P pPrepare
  stages : LightSourceRetainedStages.Procs P pStages
  main : P[pMain]? = some (body pEnum pPrepare pStages)

variable {lim : Limits} {P : Program} {d : ℕ}


























































































































































end ThreeSum.LightBlockSourceRetainedHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandPair


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData


/-!
# Actual B/C source catalogs from retained normalized headers

The program reads both physical lengths and band counts, and reads the C
shift from its supplied result cell. It constructs the B catalog with shift
zero, then the C catalog, then one shared empty histogram/offset row. The
eight-cell result header retains both catalog pointers and counts, the
empty-row pointer, the next free address, and both original lengths.
-/

namespace ThreeSum.LightSourceBandPair

open Light BandPartition SourceBandPairData

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

/-- Values B, endpoint header B, values C, endpoint header C, band size,
prime, residue count, selected-shift cell, and result header. -/
def body (pSetup pFill : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 9 (M (v 1)))
    (Light.Stmt.seq (.set 10 (M (v 3)))
      (Light.Stmt.seq (.set 11 (M (v 7)))
        (Light.Stmt.seq (.set 12 (M ((Light.Expr.op Light.Op.add) (v 1) (k 1))))
          (Light.Stmt.seq (.set 13 (M ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
            (Light.Stmt.seq (.set 14 ((Light.Expr.op Light.Op.add) (v 8) (k 8)))
              (Light.Stmt.seq
                (.call pSetup [v 0, v 9, v 4, v 5, v 6, k 0, v 14] 15)
                (Light.Stmt.seq
                  (.call pSetup [v 2, v 10, v 4, v 5, v 6, v 11, v 15] 16)
                  (Light.Stmt.seq
                    (.call pFill
                      [v 16, (Light.Expr.op Light.Op.add) (v 6) (k 1), k 0] 17)
                    (Light.Stmt.seq
                      (.set 18
                        ((Light.Expr.op Light.Op.add)
                          ((Light.Expr.op Light.Op.add) (v 16) (v 6)) (k 1)))
                      (Light.Stmt.seq (.store (v 8) (v 14))
                        (Light.Stmt.seq
                          (.store ((Light.Expr.op Light.Op.add) (v 8) (k 1))
                            (v 12))
                          (Light.Stmt.seq
                            (.store ((Light.Expr.op Light.Op.add) (v 8) (k 2))
                              (v 15))
                            (Light.Stmt.seq
                              (.store ((Light.Expr.op Light.Op.add) (v 8) (k 3))
                                (v 13))
                              (Light.Stmt.seq
                                (.store ((Light.Expr.op Light.Op.add) (v 8) (k 4))
                                  (v 16))
                                (Light.Stmt.seq
                                  (.store
                                    ((Light.Expr.op Light.Op.add) (v 8) (k 5))
                                    (v 18))
                                  (Light.Stmt.seq
                                    (.store
                                      ((Light.Expr.op Light.Op.add) (v 8) (k 6))
                                      (v 9))
                                    (Light.Stmt.seq
                                      (.store
                                        ((Light.Expr.op Light.Op.add) (v 8) (k 7))
                                        (v 10))
                                      (.set 0 (v 18))))))))))))))))))))

def time (NL NR g p m U D : ℕ) : ℕ :=
  LightSourceBandSetup.time NL g p m U D+LightSourceBandSetup.time NR g p m U D+
    fillTime (m+1)+2000

def space (base NL NR g p m U D : ℕ) : ℕ :=
  LightSourceResidues.space (next base NL NR g m) p U D

def word (NL NR g p m U D : ℕ) : ℕ :=
  max (LightSourceBandStep.word NL g p m U D) (LightSourceBandStep.word NR g p m U D)+16

structure Procs (P : Program) (pMain : ℕ) where
  pSetup : ℕ
  pFill : ℕ
  setup : LightSourceBandSetup.Procs P pSetup
  fill : P[pFill]?=some fillBody
  main : P[pMain]?=some (body pSetup pFill)

variable {lim : Limits} {P : Program} {d : ℕ}





























































































































end ThreeSum.LightSourceBandPair

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandRawAResources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout


/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources

open Light EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def cells (W n g : ℕ) : ℕ :=
  LightBandRawAColor.space (tables 0 n) (vals 0 n g) W n g











































end ThreeSum.LightBandRawAResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorNormalize


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # Selected-color normalization from actual parameter and color rows -/

namespace ThreeSum.LightEncodedColorNormalize

open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

/-- src,n,parameter header,color row,first free address. -/
def body (pLayout pColor : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.add) (M (v 2)) (k 1)))
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 2) (k 17))))
      (Light.Stmt.seq (.call pLayout [v 1, v 6, v 4] 7)
        (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 4) (k 8)))
          (Light.Stmt.seq (.set 9 ((Light.Expr.op Light.Op.add) (v 8) (v 1)))
            (Light.Stmt.seq
              (.set 10
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) (v 9) (v 1)) (k 1)))
              (Light.Stmt.seq
                (.set 11
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v 10) (v 1)) (k 1)))
                (Light.Stmt.seq (.set 12 (M (v 4)))
                  (Light.Stmt.seq
                    (.set 13 (M ((Light.Expr.op Light.Op.add) (v 4) (k 1))))
                    (Light.Stmt.seq
                      (.set 14 (M ((Light.Expr.op Light.Op.add) (v 4) (k 2))))
                      (Light.Stmt.seq
                        (.set 15 (M ((Light.Expr.op Light.Op.add) (v 4) (k 3))))
                        (Light.Stmt.seq
                          (.set 16 (M ((Light.Expr.op Light.Op.add) (v 4) (k 4))))
                          (Light.Stmt.seq
                            (.set 17
                              (M ((Light.Expr.op Light.Op.add) (v 4) (k 5))))
                            (Light.Stmt.seq
                              (.set 18
                                (M ((Light.Expr.op Light.Op.add) (v 4) (k 6))))
                              (Light.Stmt.seq
                                (.set 19
                                  (M ((Light.Expr.op Light.Op.add) (v 4) (k 7))))
                                (Light.Stmt.seq
                                  (.set 20
                                    ((Light.Expr.op Light.Op.add)
                                      ((Light.Expr.op Light.Op.add) (v 17) (k 2))
                                      ((Light.Expr.op Light.Op.mul) (k 2) (v 1))))
                                  (Light.Stmt.seq (.set 21 (M (v 3)))
                                    (Light.Stmt.seq
                                      (.set 22
                                        (M
                                          ((Light.Expr.op Light.Op.add) (v 3)
                                            (k 1))))
                                      (Light.Stmt.seq
                                        (.set 23
                                          (M
                                            ((Light.Expr.op Light.Op.add) (v 3)
                                              (k 2))))
                                        (Light.Stmt.seq
                                          (.set 24
                                            (M
                                              ((Light.Expr.op Light.Op.add) (v 3)
                                                (k 3))))
                                          (Light.Stmt.seq
                                            (.set 25
                                              (M
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 3) (k 4))))
                                            (Light.Stmt.seq
                                              (.set 26
                                                (M
                                                  ((Light.Expr.op Light.Op.add)
                                                    (v 3) (k 5))))
                                              (Light.Stmt.seq
                                                (.call pColor
                                                  [v 0, v 1, v 5, v 21, v 22,
                                                    v 23, v 24, v 25, v 26, v 8,
                                                    v 9, v 10, v 11, v 6, v 12,
                                                    v 13, v 14, v 15, v 16, v 17,
                                                    v 20, v 18, v 19]
                                                  27)
                                                (Light.Stmt.seq
                                                  (.store (v 7) (v 27))
                                                  (.set 0
                                                    (v 7))))))))))))))))))))))))))

def program : Program := LightBandRawAColor.program ++ [LightEncodedColorLayout.body 9,body 44 43]



def time (n : ℕ) : ℕ := LightEncodedColorLayout.time n (bandSize n)+
  LightBandRawAColor.time (inputBits n+1) n (bandSize n)+1200

def space (free n : ℕ) : ℕ :=
  LightBandRawAColor.space (tables free n) (vals free n (bandSize n)) (inputBits n+1) n (bandSize n)+1

def word (n U : ℕ) : ℕ :=
  LightBandRawAColor.word (inputBits n+1) n (bandSize n) U+
    LightEncodedColorLayout.word n (bandSize n)+(inputBits n+1)+100

variable {lim : Limits} {d : ℕ}


































































































































end ThreeSum.LightEncodedColorNormalize

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumColorDriverBounded


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts


/-! # Run the closed color scan from actual input and parameter arrays -/

namespace ThreeSum.LightThreeSumColorDriver

open Light ColorParameters LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def ColorLaw (lim : Limits) (colorProgram : Program) (pColor : ℕ)
    (colorNeed : ℕ→ℕ→Need) (src n params row U colorTime : ℕ) (x : Fin n→ℤ) : Prop :=
  ∀ (color : Coloring.Parameter (width n)) (ν : ℕ→ℤ) (dd : ℕ),
    (colorNeed n U).Ok lim (row+6) dd →
    Seg ν src (List.ofFn x) → Seg ν params (LightParameterInit.values n) →
    Seg ν row (fields color) →
    Meets lim colorProgram pColor dd [src,n,params,row,row+6] ν colorTime
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ ColorClassLists.witness color x) ∧ Kept ν ξ row)





















end ThreeSum.LightThreeSumColorDriver

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumFastDriver


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Initialize parameters once and execute the complete color family

The public arguments are [source,n,free]. The nineteen-cell parameter
record starts at free; the reusable six-cell color row starts at free+19;
the concrete selected-color program receives free+25 as its work boundary.
-/

namespace ThreeSum.LightThreeSumFastDriver

open Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

def row (free : ℕ) : ℕ := free+19


def body (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.add) (v 2) (k 19)))
    (Light.Stmt.seq (.call 0 [v 1, v 2, v 3] 4)
      (.call pScan [v 0, v 1, v 2, v 3] 0)))

def libraries (colorProgram : Program) (pColor : ℕ) : Program :=
  ReportingHostRelocation.program LightParameterInit.program
    (LightThreeSumColorDriver.program colorProgram pColor)

def program (colorProgram : Program) (pColor : ℕ) : Program :=
  libraries colorProgram pColor++[body (colorProgram.length+25)]

def time (colorTime n : ℕ) : ℕ :=
  LightParameterInit.time n+LightColorScanHost.time colorTime n+500




























































end ThreeSum.LightThreeSumFastDriver

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandPrimeChain


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice


/-!
# Execute one common modulus chain for all candidate owners

The loop calls the verified aggregate minimum at every level. Its output is
the same common modulus whose contraction is proved in `BandPrimeChoice`.
All prefix moduli are retained; every score computation reuses the region
beyond the prefix array.
-/

namespace ThreeSum.LightBandPrimeChain

open Light BandCandidateRows BandPrimeChoice

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Arguments: the three original sorted arrays and lengths, band size,
candidate records and count, prime array and count, levels, free address. -/
def body (pMinimum : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 13 (k 1))
    (Light.Stmt.seq
      (.set 16
        ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 12) (v 11))
          (k 1)))
      (Light.Stmt.seq (.store (v 12) (v 13))
        (Light.Stmt.seq
          (.for 14 (v 11)
            (Light.Stmt.seq
              (.call pMinimum
                [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 13, v 9, v 10,
                  v 16]
                15)
              (Light.Stmt.seq
                (.set 13 ((Light.Expr.op Light.Op.mul) (v 13) (v 15)))
                (.store
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v 12) (v 14)) (k 1))
                  (v 13)))))
          (.set 0 (v 13))))))

def program : Program := LightBandPrimeMinimum.program ++ [body 17]



def time (maxMod g R s U levels : ℕ) : ℕ :=
  levels*(LightBandPrimeMinimum.time maxMod g R s U+140)+140

def space (free maxMod g U levels : ℕ) : ℕ :=
  LightWeightedScore.space (free+levels+1) maxMod g U

def Inv (μ : ℕ → ℤ) (qs : ℕ → ℕ)
    (a b c nA nB nC g recs R aux s levels free i : ℕ) (σ : State) : Prop :=
  ∃ (pval : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,aux,s,levels,free,
      qs i,i,pval,free+levels+1],ν⟩ ∧
    (∀ j ≤ i, ν (free+j)=(qs j : ℤ)) ∧ Kept μ ν free

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs aux s levels free maxMod U Y : ℕ}



































































































































end ThreeSum.LightBandPrimeChain

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumReportingSetupDense


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData


/-! # Initialize the actual dense counter using the retained original arrays -/

namespace ThreeSum.LightThreeSumReportingSetupDense

open Light Scales BandScales CostLedger ArithmeticStageBounds ThreeSumReportingSetupData
open BandPartition BandCandidateRows BandRawA

set_option maxHeartbeats 2600000
set_option maxRecDepth 16000



/-- n, parameter header, normalized header, encoded result header, counter. -/
def body (pDense : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 (M (v 3)))
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
      (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 3) (k 7))))
        (Light.Stmt.seq (.set 8 (M (v 2)))
          (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 2) (k 1))))
            (Light.Stmt.seq
              (.set 10 (M ((Light.Expr.op Light.Op.add) (v 2) (k 2))))
              (Light.Stmt.seq
                (.set 11 (M ((Light.Expr.op Light.Op.add) (v 2) (k 3))))
                (Light.Stmt.seq
                  (.set 12 (M ((Light.Expr.op Light.Op.add) (v 2) (k 4))))
                  (Light.Stmt.seq
                    (.set 13 (M ((Light.Expr.op Light.Op.add) (v 2) (k 5))))
                    (Light.Stmt.seq
                      (.set 14 (M ((Light.Expr.op Light.Op.add) (v 2) (k 6))))
                      (Light.Stmt.seq (.set 15 (M (v 9)))
                        (Light.Stmt.seq (.set 16 (M (v 11)))
                          (Light.Stmt.seq (.set 17 (M (v 13)))
                            (Light.Stmt.seq
                              (.set 18
                                (M ((Light.Expr.op Light.Op.add) (v 9) (k 1))))
                              (Light.Stmt.seq
                                (.set 19
                                  (M ((Light.Expr.op Light.Op.add) (v 11) (k 1))))
                                (Light.Stmt.seq
                                  (.set 20
                                    (M
                                      ((Light.Expr.op Light.Op.add) (v 13)
                                        (k 1))))
                                  (Light.Stmt.seq
                                    (.set 21
                                      ((Light.Expr.op Light.Op.add)
                                        ((Light.Expr.op Light.Op.add)
                                          ((Light.Expr.op Light.Op.mul) (v 19)
                                            (v 20))
                                          ((Light.Expr.op Light.Op.mul) (v 18)
                                            (v 19)))
                                        ((Light.Expr.op Light.Op.mul) (v 18)
                                          (v 20))))
                                    (Light.Stmt.seq
                                      (.set 22
                                        (M
                                          ((Light.Expr.op Light.Op.add) (v 1)
                                            (k 17))))
                                      (Light.Stmt.seq
                                        (.set 23
                                          (M
                                            ((Light.Expr.op Light.Op.add) (v 1)
                                              (k 3))))
                                        (Light.Stmt.seq
                                          (.set 24
                                            (M
                                              ((Light.Expr.op Light.Op.add) (v 5)
                                                (k 3))))
                                          (Light.Stmt.seq
                                            (.set 25
                                              (M
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 5) (k 4))))
                                            (.call pDense
                                              [v 8, v 10, v 12, v 15, v 16, v 17,
                                                v 22, v 14, v 21, v 7, v 24, v 25,
                                                v 6, v 23, v 4]
                                              0))))))))))))))))))))))

def program : Program := LightDenseSetup.program++[body 19]



def time (n U R : ℕ) : ℕ :=
  LightDenseSetup.time (maxMod n) (bandSize n) R (LightPrimePool.size (primeWindow n))
    U (blockCount (inputBits n))+1600

def word (n U : ℕ) : ℕ :=
  LightDenseSetup.word (maxMod n) n n n (bandSize n) (ColorBandBounds.count n (bandSize n))
    (LightPrimePool.size (primeWindow n)) U (microHalf (inputBits n)) (blockCount (inputBits n))+
    n+bandSize n+blockCount (inputBits n)+ColorBandBounds.count n (bandSize n)+maxMod n+
    LightPrimePool.size (primeWindow n)+20















































































































































































































end ThreeSum.LightThreeSumReportingSetupDense

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingPositiveMasks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Actual gathered positive mask arrays are the exact original next-prefix list -/

namespace ThreeSum.LightReportingPositiveMasks

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostPositive

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false








variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def selectedIndices {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) : List ℕ :=
  LightReportingFilter.selected (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i)) (groupSize h)











































































end ThreeSum.LightReportingPositiveMasks

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPositive


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive

open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators

set_option linter.unusedSectionVars false




























variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def positiveChildren {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    List (List (Finset (Fin (512*h)))) :=
  (LightReportingFilter.selected (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i))
    (groupSize h)).map (childAt w.2.2 pre hk)











































end ThreeSum.ReportingHostPositive

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostFrontierLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting LightBlockQuery ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

def slot (base cap k : ℕ) : ℕ := base+k*(4+2*cap)
def left (base cap k : ℕ) : ℕ := slot base cap k+4
def right (base cap k : ℕ) : ℕ := left base cap k+cap





























variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

abbrev rootMass {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) : ℕ :=
  prefixQuery I w 0 []





def capacity {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) : ℕ :=
  (rootMass I w+1)*groupSize h

























def leftMasks {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) : List ℕ :=
  (ReportingHostFrontier.frontier I w k).map fun pre => subsetMask (leftPrefix k (prefixRows (J := J) pre))

def rightMasks {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) : List ℕ :=
  (ReportingHostFrontier.frontier I w k).map fun pre =>
    subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))


















structure At {h J : ℕ} (μ : ℕ→ℤ) (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (base cap k : ℕ) : Prop where
  count : μ (slot base cap k)=((ReportingHostFrontier.frontier I w k).length : ℤ)
  query : μ (slot base cap k+1)=(subsetMask (querySet k (outputRows w.2.2)) : ℤ)
  left : SegN μ (ReportingHostFrontierLayout.left base cap k) (leftMasks I w k)
  right : SegN μ (ReportingHostFrontierLayout.right base cap k) (rightMasks I w k)


















end ThreeSum.ReportingHostFrontierLayout

end


