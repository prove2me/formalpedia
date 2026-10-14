-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle06
-- name    : ThreeSum1962Source_Bundle06
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:09:06.352858+00:00
-- url     : https://prove2.me/theorems/6d5e9322-6ff2-458a-8d4d-a3175ba1d3ce
-- title:
--   Source preprocessing, bucket scatter, and output-record decoding
-- statement:
--   This bundle defines the composed preprocessing routines for colors, source hashes and histograms, local cover rows, trimming flags, and sorted reporting catalogs. Bucket-offset and scatter bodies use histogram prefix sums
--   $$
--   O_r=\sum_{q<r}H_q,
--   $$
--   where \(H_q\) is the number of original indices in bucket \(q\); their invariants track offset cells, insertion cursors and stored index segments. Further definitions specify header-based bucket views, original-value pair tests, radix digit arrays, occurrence-and-mask decoding, Pascal and subset-rank setup, cyclic folding, normalization, and band-candidate tables. Program-interface records and explicit time, word and scratch expressions support the separate compositional execution proofs.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ColorClassLists.lean#L16-L73
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandCandidatesCell.lean#L12-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandEnumeration.lean#L24-L93
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawAStep.lean#L12-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceHashes.lean#L20-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L20-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorArray.lean#L18-L33
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorScan.lean#L21-L42
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverSelect.lean#L10-L61
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCyclic.lean#L78-L84
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightHashHistogram.lean#L17-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverRow.lean#L17-L37
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalKeyRow.lean#L20-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMaskBitTable.lean#L11-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightNormalize.lean#L20-L141
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOriginalTripleScan.lean#L12-L73
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOutputDecodeDigits.lean#L20-L37
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOutputDecodeStep.lean#L21-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingBinomial.lean#L12-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingBucketTest.lean#L18-L32
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSortedCatalog.lean#L18-L29
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingCounts.lean#L12-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketOffsets.lean#L18-L32
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketScatter.lean#L18-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceHistogram.lean#L20-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceTrim.lean#L20-L72
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetSetup.lean#L18-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostBucketTest.lean#L20-L63
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBucketView.lean#L9-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceTableLayout.lean#L107-L109

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
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceTableLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# The actual compact enumeration uses the actual compact table addresses

This bridges a sequentially constructed source array to `TableAt`: the mask
stored at `subsetRank S` by the existing enumerator is exactly `subsetMask S`.
No additional scatter, rank oracle, or arbitrary enumeration is required.
-/

namespace ThreeSum.SourceTableLayout

open SubsetAddress

set_option maxHeartbeats 800000

























































































def maskAt (L cut i : ℕ) : ℕ := (enumerateDownset L cut).getD i 0

def setAt (L cut i : ℕ) : Finset (Fin L) := MaskDecode.decode L (maskAt L cut i)











































end ThreeSum.SourceTableLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorScan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.ColorScan
end ThreeSum.ColorScan


/-!
# Execute the finite coloring search

The recursive driver reuses one six-cell parameter row and all subsequent
per-color scratch. Once a color accepts, later color calls are skipped.
This is a compositional execution theorem: the concrete selected-color
decision procedure must supply the explicit per-color call contract below.
It does not assert existence of that still-being-integrated solver.
-/

namespace ThreeSum.LightColorScan

open Light ColorParameters ColorScan

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Source, length, persistent parameter header, reusable row, width, prefix length. -/
def body (pSelf pParameters pColor : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 5)))
    ((Light.Stmt.seq
       (.call pSelf
         [v 0, v 1, v 2, v 3, v 4, (Light.Expr.op Light.Op.sub) (v 5) (k 1)] 6)
       (.ite (Light.Cond.lt (k 0) (v 6)) (.set 0 (k 1))
         (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.sub) (v 5) (k 1)))
           (Light.Stmt.seq (.call pParameters [v 4, v 7, v 3] 8)
             (Light.Stmt.seq
               (.call pColor
                 [v 0, v 1, v 2, v 3, (Light.Expr.op Light.Op.add) (v 3) (k 6)] 9)
               (.set 0 (v 9))))))))
    (.set 0 (k 0))

def time (colorTime W t : ℕ) : ℕ :=
  t*(100*count W+colorTime+3000)+100

structure Procs (P : Program) (pMain : ℕ) where
  pParameters : ℕ
  pDivide : ℕ
  pColor : ℕ
  main : P[pMain]?=some (body pMain pParameters pColor)
  parameters : P[pParameters]?=some (LightColorParameters.body pDivide)
  divide : P[pDivide]?=some LightSmallDivide.body

variable {lim : Limits} {P : Program}































































end ThreeSum.LightColorScan

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingBinomial


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal


/-! # Actual Pascal lookup for reporting child and terminal candidate counts -/

namespace ThreeSum.LightReportingBinomial

open Light LightPascal

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-- Arguments are n, k, and a polynomial Pascal scratch region. -/
def body (pPascal : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pPascal [v 2, v 0] 3)
    (Light.Stmt.seq
      (.set 4
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v 2)
            ((Light.Expr.op Light.Op.mul) (v 0)
              ((Light.Expr.op Light.Op.add) (v 0) (k 1))))
          (v 1)))
      (.set 0 (M (v 4)))))

def program : Program := [fillBody,LightArray.linearBody,rowBody 1,buildBody 0 2,body 3]
def time (n : ℕ) : ℕ := buildTime n+100

variable {lim : Limits}


































end ThreeSum.LightReportingBinomial

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingCounts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Compute the two local combinatorial counts from an actual Pascal table -/

namespace ThreeSum.LightSharedReportingCounts

open Light LightPascal LightSubsetAddress SubsetAddress SharedReportingBankLayout

set_option maxHeartbeats 1700000
set_option maxRecDepth 9000

/-- h, two-cell count destination, Pascal scratch. -/
def body (pBuild : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.mul) (k 512) (v 0)))
    (Light.Stmt.seq (.call pBuild [v 2, v 3] 4)
      (Light.Stmt.seq
        (.set 5
          (M
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v 2)
                ((Light.Expr.op Light.Op.mul) (v 3)
                  ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
              (v 0))))
        (Light.Stmt.seq
          (.set 6
            (M
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 2)
                  ((Light.Expr.op Light.Op.mul) (v 3)
                    ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                ((Light.Expr.op Light.Op.mul) (k 2) (v 0)))))
          (Light.Stmt.seq
            (.set 7
              (M
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) (v 2)
                    ((Light.Expr.op Light.Op.mul)
                      ((Light.Expr.op Light.Op.mul) (k 2) (v 0))
                      ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                  (v 0))))
            (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.mul) (v 6) (v 7)))
              (Light.Stmt.seq (.store (v 1) (v 5))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 1) (k 1)) (v 8))
                  (.set 0 (v 8))))))))))

def program : Program := [body 1,buildBody 2 3,fillBody,rowBody 4,LightArray.linearBody]
def time (h : ℕ) : ℕ := buildTime (512*h)+300
















































































end ThreeSum.LightSharedReportingCounts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSubsetSetup


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
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: bit width, cardinality, mask, scratch base. -/
def body (pBuild pPowers pRank : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 4
      ((Light.Expr.op Light.Op.add) (v 3)
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 0) (k 1))
          ((Light.Expr.op Light.Op.add) (v 0) (k 1)))))
    (Light.Stmt.seq (.call pBuild [v 3, v 0] 5)
      (Light.Stmt.seq
        (.call pPowers [v 4, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 5)
        (.call pRank [v 0, v 1, v 2, v 0, v 3, v 4] 0))))

def time (L : ℕ) : ℕ := buildTime L + powTableTime (L+1) + rankTime L + 60

structure Procs (P : Program) (pMain pBuild pFill pRow pLinear pPowers pRank : ℕ) : Prop where
  main : P[pMain]? = some (body pBuild pPowers pRank)
  build : P[pBuild]? = some (buildBody pFill pRow)
  fill : P[pFill]? = some fillBody
  row : P[pRow]? = some (rowBody pLinear)
  linear : P[pLinear]? = some LightArray.linearBody
  powers : P[pPowers]? = some powTableBody
  rank : P[pRank]? = some (rankBody pRank)



































































end ThreeSum.LightSubsetSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCoverSelect


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Actual first-maximum candidate selection from a Boolean cover matrix -/

namespace ThreeSum.LightCoverSelect

open Light

def body (pScores pMinimum : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pScores [v 0, v 1, v 2, v 4, v 3] 5)
    (.call pMinimum [v 2, v 3] 0))

def time (rows cols : ℕ) : ℕ :=
  LightCoverScores.time rows cols+LightMinimum.time rows+60

variable {lim : Limits} {P : Program} {d : ℕ}




































structure Procs (P : Program) (pMain : ℕ) where
  pScores : ℕ
  pDot : ℕ
  pMinimum : ℕ
  main : P[pMain]? = some (body pScores pMinimum)
  scores : P[pScores]? = some (LightCoverScores.body pDot)
  dot : P[pDot]? = some LightBooleanDot.body
  minimum : P[pMinimum]? = some LightMinimum.body










































end ThreeSum.LightCoverSelect

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBucketOffsets


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Actual prefix offsets and initial scatter cursors

One linear scan of the retained count histogram writes all M+1 bucket
offsets and the M initial cursors. Original arrays before the output remain
untouched; no bucket is found by searching its original indices.
-/

namespace ThreeSum.LightSourceBucketOffsets

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def body : Stmt :=
  (Light.Stmt.seq (.set 6 (k 0))
    (Light.Stmt.seq
      (.for 5 (v 3)
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 1) (v 5)) (v 6))
          (Light.Stmt.seq
            (.store ((Light.Expr.op Light.Op.add) (v 2) (v 5)) (v 6))
            (.set 6
              ((Light.Expr.op Light.Op.add) (v 6)
                (M ((Light.Expr.op Light.Op.add) (v 0) (v 5))))))))
      (.store ((Light.Expr.op Light.Op.add) (v 1) (v 3)) (v 6))))

def time (M : ℕ) : ℕ := 120*M+120

def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (hist offsets cursor M N j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ = ⟨frame [hist,offsets,cursor,M,N,j,offset key N j],ν⟩ ∧
    (∀ r < j, ν (offsets+r) = (offset key N r : ℤ) ∧
      ν (cursor+r) = (offset key N r : ℤ)) ∧
    SameOutside μ ν offsets (cursor+M-offsets)

variable {lim : Limits} {P : Program} {d : ℕ}


















































































end ThreeSum.LightSourceBucketOffsets

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBucketScatter


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Actual linear scatter of original indices into residue buckets

Each original physical index is stored exactly once at its current bucket
cursor; that cursor is incremented. The position proof supplies complete,
duplicate-free fibers and charges one constant-time iteration per input.
-/

namespace ThreeSum.LightSourceBucketScatter

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body : Stmt :=
  .for 5 (v 3) (
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 0) (v 5))))
      (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 1) (v 6))))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 2) (v 7)) (v 5))
          (.store ((Light.Expr.op Light.Op.add) (v 1) (v 6))
            ((Light.Expr.op Light.Op.add) (v 7) (k 1)))))))

def time (N : ℕ) : ℕ := 120*N+20

def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (keys cursor flat N M i : ℕ) (σ : State) : Prop :=
  ∃ (k q : ℤ) (ν : ℕ → ℤ), σ = ⟨frame [keys,cursor,flat,N,M,i,k,q],ν⟩ ∧
    (∀ r < M, ν (cursor+r) = ((offset key N r+count key r i : ℕ) : ℤ)) ∧
    (∀ j < i, ν (flat+position key N j) = (j : ℤ)) ∧
    SameOutside μ ν cursor (flat+N-cursor)

variable {lim : Limits} {P : Program} {d : ℕ}













































































end ThreeSum.LightSourceBucketScatter

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBucketView


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-! # Header-driven exact views of the retained original-index buckets -/

namespace ThreeSum.SourceBucketView

open SourceBuckets LightHistogram

def start (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := (μ (offsets+r)).toNat
def stop (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := (μ (offsets+r+1)).toNat
def length (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := stop μ offsets r-start μ offsets r
def indices (μ : ℕ → ℤ) (offsets flat r : ℕ) : List ℕ :=
  bucketList μ flat (start μ offsets r) (length μ offsets r)























































end ThreeSum.SourceBucketView

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ColorClassLists


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter

def value {n : ℕ} (x : Fin n → ℤ) (i : ℕ) : ℤ := if hi : i < n then x ⟨i,hi⟩ else 0




def indexColor {n W : ℕ} (p : Coloring.Parameter W) (i : Fin n) : Fin 3 :=
  p.2 (i.val.testBit p.1.1.val,i.val.testBit p.1.2.val)

def classList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : List ℤ :=
  items (value x) (LightColorIndex.color p) c scale n












































def witness {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) : Prop :=
  ∃ a ∈ classList p x 0 1, ∃ b ∈ classList p x 1 1,
    ∃ c ∈ classList p x 2 (-1), a+b=c















































end ThreeSum.ColorClassLists

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorArray


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress


/-!
# Building the color of every original array position

The program constructs its own binary-power table and evaluates one selected
two-coordinate coloring on every index. No index-bit or coloring oracle is
part of the input. Memory outside the output colors and scratch is preserved.
-/

namespace ThreeSum.LightColorArray

open Light LightSubsetAddress

set_option maxHeartbeats 1200000

def body (pPowers pColor : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 9, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 10)
    (.for 11 (v 1)
      (Light.Stmt.seq
        (.call pColor [v 0, v 11, v 2, v 3, v 4, v 5, v 6, v 7, v 9] 12)
        (.store ((Light.Expr.op Light.Op.add) (v 8) (v 11)) (v 12)))))

def time (W n : ℕ) : ℕ := powTableTime (W+1)+n*(LightColorIndex.time W+100)+100

def Inv {W : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (n dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      dst,work,powRet,j,r],ν⟩ ∧
    (∀ i < j, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
    Powers ν work W ∧ KeptBut μ ν work dst n

variable {lim : Limits} {P : Program} {d : ℕ}



















































































end ThreeSum.LightColorArray

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingBucketTest


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Actual independent bucket selection followed by original tuple testing

The host reads the two retained offset headers, applies each endpoint's
independent flag, and runs the exact original-value Cartesian scanner. Its
time is linear in the actual selected physical pair mass plus a constant.
-/

namespace ThreeSum.LightReportingBucketTest

open Light SourceBuckets LightHistogram LightSourceBucketSelect ReportingHostBucketTest

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pSelect pPairs : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSelect [v 3, v 4, v 5, v 6, v 14, v 13, v 11] 15)
    (Light.Stmt.seq
      (.call pSelect
        [v 7, v 8, v 9, v 10, (Light.Expr.op Light.Op.add) (v 14) (k 2), v 13,
          v 12]
        15)
      (Light.Stmt.seq (.set 16 (M (v 14)))
        (Light.Stmt.seq (.set 17 (M ((Light.Expr.op Light.Op.add) (v 14) (k 1))))
          (Light.Stmt.seq
            (.set 18 (M ((Light.Expr.op Light.Op.add) (v 14) (k 2))))
            (Light.Stmt.seq
              (.set 19 (M ((Light.Expr.op Light.Op.add) (v 14) (k 3))))
              (.call pPairs [v 0, v 1, v 2, v 16, v 18, v 17, v 19, v 11, v 12]
                0)))))))

def program : Program :=
  [LightSourceBucketSelect.body,LightReportingBucketRow.body,
    LightReportingBucketPairs.body 1,body 0 2]

def time (keyL keyR : ℕ → ℕ) (NL NR rL rR flagL flagR : ℕ) : ℕ :=
  LightReportingBucketPairs.time (countSelected keyL NL rL flagL) (countSelected keyR NR rR flagR)+600

variable {lim : Limits} {P : Program} {d : ℕ}



















































































































end ThreeSum.LightReportingBucketTest

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostBucketTest


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Physical bucket-test semantics and original-index completeness

The selected offset segment contains exactly the original physical indices
in one residue fiber, with an independent endpoint flag. The literal pair
tester therefore recognizes exactly the compatible original value pairs.
-/

namespace ThreeSum.ReportingHostBucketTest

open Light SourceBuckets LightHistogram LightSourceBucketSelect

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

def index (μ : ℕ → ℤ) (flat : ℕ) (key : ℕ → ℕ) (N r j : ℕ) : ℕ :=
  (μ (flat+offset key N r+j)).toNat





































def testCount (μ : ℕ → ℤ) (a : ℤ) (left right : ℕ → ℤ)
    (keyL keyR : ℕ → ℕ) (NL NR flatL flatR rL rR flagL flagR : ℕ) : ℕ :=
  LightReportingBucketPairs.count a left right
    (index μ flatL keyL NL rL) (index μ flatR keyR NR rR)
    (countSelected keyR NR rR flagR) (countSelected keyL NL rL flagL)


























end ThreeSum.ReportingHostBucketTest

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOriginalTripleScan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BruteTripleIndex
end ThreeSum.BruteTripleIndex


/-! # Execute the exact finite fallback scan over original triples -/

namespace ThreeSum.LightOriginalTripleScan

open Light BruteTripleIndex

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def body (pSelf pRow : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 2)))
    ((Light.Stmt.seq
       (.call pSelf [v 0, v 1, (Light.Expr.op Light.Op.sub) (v 2) (k 1)] 3)
       (Light.Stmt.seq
         (.call pRow [v 0, v 1, (Light.Expr.op Light.Op.sub) (v 2) (k 1)] 4)
         (.ite (Light.Cond.lt (k 0) ((Light.Expr.op Light.Op.add) (v 3) (v 4)))
           (.set 0 (k 1)) (.set 0 (k 0))))))
    (.set 0 (k 0))

def time (n t : ℕ) : ℕ := t*(LightOriginalTripleRow.time n+150)+50

variable {lim : Limits} {P : Program}



















































def program : Program := LightOriginalTripleRow.program ++ [body 2 0]

end ThreeSum.LightOriginalTripleScan

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceTrim


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct


/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim

open Light SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def rowFlag (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  LightSourceRowFlag.flag L h p cap (fun a => bits (j*L+a))
    (w0 (sel j)) (w1 (sel j)) (counts (candidate (sel j)))






def roundBody (pRowFlag : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pRowFlag
      [(Light.Expr.op Light.Op.add) (v 10)
          ((Light.Expr.op Light.Op.mul) (v 16) (v 1)),
        (Light.Expr.op Light.Op.add) (v 6)
          ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (k 2) (v 1))
            (M ((Light.Expr.op Light.Op.add) (v 5) (v 16)))),
        (Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v 6)
            ((Light.Expr.op Light.Op.mul)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 1))
              (M ((Light.Expr.op Light.Op.add) (v 5) (v 16)))))
          (v 1),
        v 1, v 2,
        (Light.Expr.op Light.Op.add) (v 8)
          ((Light.Expr.op Light.Op.mul)
            (M
              ((Light.Expr.op Light.Op.add) (v 7)
                (M ((Light.Expr.op Light.Op.add) (v 5) (v 16)))))
            (v 3)),
        (Light.Expr.op Light.Op.add) (v 9)
          ((Light.Expr.op Light.Op.mul)
            (M
              ((Light.Expr.op Light.Op.add) (v 7)
                (M ((Light.Expr.op Light.Op.add) (v 5) (v 16)))))
            (v 3)),
        v 3, v 4, v 11, v 12]
      17)
    (Light.Stmt.seq (.set 14 ((Light.Expr.op Light.Op.mul) (v 14) (M (v 11))))
      (.set 15
        ((Light.Expr.op Light.Op.mul) (v 15)
          (M ((Light.Expr.op Light.Op.add) (v 11) (k 1)))))))

/-- Arguments: block count, width, required row size, modulus, cap,
occurrence indices, selected-map coefficient rows, occurrence-to-candidate
indices, both candidate bucket tables, Boolean rows, two-cell row scratch,
remainder scratch, and two-cell final output. -/
def body (pRowFlag : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 14 (k 1))
    (Light.Stmt.seq (.set 15 (k 1))
      (Light.Stmt.seq (.for 16 (v 0) (roundBody pRowFlag))
        (Light.Stmt.seq (.store (v 13) (v 14))
          (.store ((Light.Expr.op Light.Op.add) (v 13) (k 1)) (v 15))))))

def time (J L U : ℕ) : ℕ := J*(LightSourceRowFlag.time L U+250)+100

structure Procs (P : Program) (pMain : ℕ) where
  pRowFlag : ℕ
  pRow : ℕ
  pEmod : ℕ
  pFlag : ℕ
  rowFlagDef : P[pRowFlag]? = some (LightSourceRowFlag.body pRow pEmod pFlag)
  row : P[pRow]? = some LightSourceRowScan.body
  emod : P[pEmod]? = some emodBody
  flag : P[pFlag]? = some LightSourceFlagTest.body
  main : P[pMain]? = some (body pRowFlag)

def Inv (μ : ℕ → ℤ) (J L h p cap occ maps candidates histL histR bitBase rowOut work dst : ℕ)
    (sel candidate bits : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,h,p,cap,occ,maps,candidates,histL,histR,bitBase,rowOut,work,dst,
      product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) j,
      product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) j,j,r],ν⟩ ∧
    Kept μ ν rowOut

variable {lim : Limits} {P : Program} {d : ℕ}











































































































































































end ThreeSum.LightSourceTrim

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightMaskBitTable


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Constructing all Boolean coordinate rows for an enumerated mask list -/

namespace ThreeSum.LightMaskBitTable

open Light

set_option maxHeartbeats 1000000

def body (pBits : ℕ) : Stmt :=
  .for 5 (v 3) (.call pBits [v 0,M (((Light.Expr.op Light.Op.add) (v 1) (v 5))),((Light.Expr.op Light.Op.add) (v 2) ((Light.Expr.op Light.Op.mul) (v 5) (v 0))),v 4] 6)

def time (L n : ℕ) : ℕ := n*(LightMaskBits.time L+70)+6

def Inv (μ : ℕ → ℤ) (mask : ℕ → ℕ)
    (L masks dst n work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L,masks,dst,n,work,i,r],μ'⟩ ∧
    (∀ j < i, ∀ a < L, μ' (dst+j*L+a) = (LightMaskBits.bit L (mask j) a : ℤ)) ∧
    KeptBut μ μ' work dst (n*L)

variable {lim : Limits} {P : Program} {d : ℕ}



























































end ThreeSum.LightMaskBitTable

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceHashes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows


/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes

open Light BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: J, L, radix, occurrences, maps, coefficient-zero,
coefficient-one, masks, left output, right output, mask count, scratch. -/
def body (pCoefficients pHashes : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pCoefficients [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 11] 12)
    (Light.Stmt.seq
      (.call pHashes
        [(Light.Expr.op Light.Op.mul) (v 0) (v 1), v 7, v 8, v 10, v 5, v 6, v 11]
        12)
      (.call pHashes
        [(Light.Expr.op Light.Op.mul) (v 0) (v 1), v 7, v 9, v 10, v 6, v 5, v 11]
        12)))

def time (J L n : ℕ) : ℕ :=
  LightBlockCoefficients.time J L + 2*LightMaskHashes.time (J*L) n + 200

def word (J L p U : ℕ) : ℕ :=
  LightBlockCoefficients.word J p U + LightOneHot.word (J*L) (p^J*U)

def space (work J L : ℕ) : ℕ := work + max (J+1) (J*L+1)

structure Procs (P : Program) (pMain : ℕ) where
  pCoefficients : ℕ
  pPowers : ℕ
  pScale : ℕ
  pHashes : ℕ
  pOneHot : ℕ
  coefficients : P[pCoefficients]? = some (LightBlockCoefficients.body pPowers pScale)
  powers : P[pPowers]? = some powTableBody
  scale : P[pScale]? = some LightScaleArray.body
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pOneHot)
  onehot : P[pOneHot]? = some (LightOneHot.body pOneHot)
  main : P[pMain]? = some (body pCoefficients pHashes)

variable {lim : Limits} {P : Program} {d : ℕ}


























































































































































end ThreeSum.LightBlockSourceHashes

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightHashHistogram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# One-hot mask hashes through actual residues and bucket counts

The complete wrapper constructs raw hashes, canonical residue codes, and
the histogram. Both code and histogram arrays are retained for the later
pair-trimming pass; every earlier input cell is preserved.
-/

namespace ThreeSum.LightHashHistogram

open Light

def code (L p : ℕ) (mask w0 w1 : ℕ → ℕ) (i : ℕ) : ℕ :=
  LightResidues.residue p 1 (OneHotMask.eval w0 w1 L (mask i) : ℤ)

def body (pHashes pResidues pHist : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pHashes [v 0, v 1, v 2, v 5, v 6, v 7, v 9] 10)
    (Light.Stmt.seq (.call pResidues [v 2, v 3, v 5, v 8, v 9, k 1] 10)
      (.call pHist [v 3, v 4, v 5, v 8] 10)))

def time (L n p U : ℕ) : ℕ := LightMaskHashes.time L n+
  LightResidues.residuesTime n (L*U)+LightHistogram.histogramTime n p+100

def word (L p U : ℕ) : ℕ := LightOneHot.word L U+4*(L*U)+4*p+16

def space (work L U : ℕ) : ℕ := work+max (L+1) (Nat.log 2 (L*U+1)+2)

structure Procs (P : Program) (pMain : ℕ) where
  pHashes : ℕ
  pPowers : ℕ
  pOneHot : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHist : ℕ
  pFill : ℕ
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pOneHot)
  powers : P[pPowers]? = some powTableBody
  onehot : P[pOneHot]? = some (LightOneHot.body pOneHot)
  residues : P[pResidues]? = some (LightResidues.residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  hist : P[pHist]? = some (LightHistogram.histogramBody pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pHashes pResidues pHist)

variable {lim : Limits} {P : Program} {d : ℕ}
















































































end ThreeSum.LightHashHistogram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalKeyRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress


/-!
# Computing one complete row of signed local output keys

For every stored output mask, this fixed program sums the true and false
coefficients outside that mask and subtracts the two sums. It constructs
its own zero row and powers table. Both input coefficient rows and the
literal output-mask enumeration remain intact.
-/

namespace ThreeSum.LightLocalKeyRow

open Light LightSubsetAddress

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

/-- Width, masks, mask count, false coefficients, true coefficients, free. -/
def body (pFill pHashes pLinear : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 5) (v 0)))
    (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.add) (v 6) (v 2)))
      (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 7) (v 2)))
        (Light.Stmt.seq (.call pFill [v 5, v 0, k 0] 9)
          (Light.Stmt.seq (.call pHashes [v 0, v 1, v 6, v 2, v 4, v 5, v 8] 9)
            (Light.Stmt.seq (.call pHashes [v 0, v 1, v 7, v 2, v 3, v 5, v 8] 9)
              (Light.Stmt.seq
                (.call pLinear
                  [v 6, v 7, v 6, v 2, (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
                  9)
                (.set 0 (v 6)))))))))

def time (L n : ℕ) : ℕ := fillTime L+2*LightMaskHashes.time L n+LightArray.linearTime n+300
def space (free L n : ℕ) : ℕ := free+L+2*n+(L+1)
def word (L U : ℕ) : ℕ := 2*LightOneHot.word L U+2

structure Procs (P : Program) (pMain : ℕ) where
  pFill : ℕ
  pHashes : ℕ
  pPowers : ℕ
  pHash : ℕ
  pLinear : ℕ
  main : P[pMain]? = some (body pFill pHashes pLinear)
  fill : P[pFill]? = some fillBody
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pHash)
  powers : P[pPowers]? = some powTableBody
  hash : P[pHash]? = some (LightOneHot.body pHash)
  linear : P[pLinear]? = some LightArray.linearBody

variable {lim : Limits} {P : Program} {d : ℕ}






































































































end ThreeSum.LightLocalKeyRow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Actual construction of one retained local-cover row

The program constructs all pair keys and trimming flags, clears the output
row, and marks exactly the keys with retained representations. Repeated
representations are handled by the support operation. Earlier matrix rows
and inputs below the scratch boundary are preserved.
-/

namespace ThreeSum.LightLocalCoverRow

open Light

def body (pPair pSupport : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPair [v 0, v 1, v 2, v 3, v 4, v 10, v 6, v 7, v 8, v 9] 11)
    (.call pSupport
      [v 10,
        (Light.Expr.op Light.Op.add) (v 10)
          ((Light.Expr.op Light.Op.mul) (v 6) (v 6)),
        v 5, (Light.Expr.op Light.Op.mul) (v 6) (v 6),
        (Light.Expr.op Light.Op.mul) (v 8) (v 8)]
      11))

def time (L n p : ℕ) : ℕ :=
  LightPairFlags.time L n+LightSupportMark.time (n*n) (p*p)+100

structure Procs (P : Program) (pMain : ℕ) where
  pPair : ℕ
  pDivide : ℕ
  pDot : ℕ
  pTrim : ℕ
  pSupport : ℕ
  pFill : ℕ
  pair : P[pPair]? = some (LightPairFlags.body pDivide pDot pTrim)
  divide : P[pDivide]? = some LightSmallDivide.body
  dot : P[pDot]? = some LightBooleanDot.body
  trim : P[pTrim]? = some LightTrimTest.body
  support : P[pSupport]? = some (LightSupportMark.body pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pPair pSupport)

variable {lim : Limits} {P : Program} {d : ℕ}















































































end ThreeSum.LightLocalCoverRow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOutputDecodeDigits


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Actual big-endian radix digit arrays

The running quotient is divided by the radix once per coordinate, using
the checked binary quotient routine. Digits are written backwards into a
forward-order array. This works for an arbitrary positive radix, including
the occurrence-only radix used by the shared source catalog.
-/

namespace ThreeSum.LightOutputDecodeDigits

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pDivide : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 (v 0))
    (Light.Stmt.seq
      (.for 6 (v 1)
        (Light.Stmt.seq (.call pDivide [v 5, v 2, v 4] 7)
          (Light.Stmt.seq
            (.set 8
              ((Light.Expr.op Light.Op.sub) (v 5)
                ((Light.Expr.op Light.Op.mul) (v 7) (v 2))))
            (Light.Stmt.seq
              (.store
                ((Light.Expr.op Light.Op.sub)
                  ((Light.Expr.op Light.Op.sub)
                    ((Light.Expr.op Light.Op.add) (v 3) (v 1)) (k 1))
                  (v 6))
                (v 8))
              (.set 5 (v 7))))))
      (.set 0 (v 5))))

def time (J V : ℕ) : ℕ := J*(LightOutputDecodeDivide.budget V+100)+30
def word (V m J : ℕ) : ℕ := 4*V+4*m+4*J+32
def space (work V : ℕ) : ℕ := work+(Nat.log 2 (V+1)+2)

def Inv (μ : ℕ → ℤ) (k J m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (q r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [k,J,m,dst,work,(k/m^i : ℕ),i,q,r],ν⟩ ∧
    (∀ j < i, ν (dst+J-1-j)=(((k/m^j)%m : ℕ) : ℤ)) ∧
    Kept μ ν dst

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}



















































































































end ThreeSum.LightOutputDecodeDigits

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOutputDecodeStep


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# One actual output-record decoding step

A local record digit is split into its occurrence and layer indices by
the checked logarithmic quotient routine. The layer mask is read from the
existing table, both output cells are written, and the occurrence-only
source-bank code is updated. Every other cell below the scratch pointer
is preserved, so separate output rows can be filled in any order.
-/

namespace ThreeSum.LightOutputDecodeStep

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pDivide : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDivide [v 0, v 2, v 8] 9)
    (Light.Stmt.seq
      (.set 10
        ((Light.Expr.op Light.Op.sub) (v 0)
          ((Light.Expr.op Light.Op.mul) (v 9) (v 2))))
      (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 3) (v 10))))
        (Light.Stmt.seq (.store (v 6) (v 9))
          (Light.Stmt.seq (.store (v 7) (v 11))
            (.set 0
              ((Light.Expr.op Light.Op.add) (v 4)
                ((Light.Expr.op Light.Op.mul) (v 5) (v 9)))))))))

def time (V : ℕ) : ℕ := LightOutputDecodeDivide.budget V+100
def word (V T M acc power U : ℕ) : ℕ := 4*(V+T+M+acc+power*T+U+10)
def space (work V : ℕ) : ℕ := work+(Nat.log 2 (V+1)+2)

def KeptOthers (μ ν : ℕ → ℤ) (work outOcc outMask : ℕ) : Prop :=
  SameOn (fun a => a < work ∧ a ≠ outOcc ∧ a ≠ outMask) μ ν






variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {x T M masks acc power outOcc outMask work V U : ℕ} {f : ℕ → ℕ}












































































































end ThreeSum.LightOutputDecodeStep

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceRetainedStages


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Exact block source stages using the shared original-input histograms

The histogram read condition is the ordinary output of the already costed
`LightSourceHistogram` program. The physical array-index equivalence supplies
its semantic connection to the finite original input set. Once retained, this
same histogram supports every occurrence vector of the corresponding band.
-/

namespace ThreeSum.LightBlockSourceRetainedStages

open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild

set_option maxHeartbeats 1800000

def histogram (p m : ℕ) (shift : ℤ) (v : ℕ → ℤ) (N r : ℕ) : ℕ :=
  LightHistogram.count (fun j => LightSourceResidues.key p m shift (v j)) r N





























variable {lim : Limits} {P : Program} {d : ℕ}











































































end ThreeSum.LightBlockSourceRetainedStages

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceHistogram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Exact source histogram from original signed inputs

This complete wrapper computes the two-modulus key of every original input,
clears the histogram, and increments it once per input incidence. The carry
offset is supplied as a signed integer. No residue-array or histogram oracle
appears in the input contract.
-/

namespace ThreeSum.LightSourceHistogram

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-- Arguments: original source, histogram destination, item count, first
modulus, histogram modulus, key scratch, remainder scratch, carry offset. -/
def body (pKeys pHistogram : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pKeys [v 0, v 5, v 2, v 3, v 4, v 6, v 7] 8)
    (.call pHistogram [v 5, v 1, v 2, v 4] 8))

def time (n p m U D : ℕ) : ℕ :=
  LightSourceResidues.time n p U D + LightHistogram.histogramTime n m + 40

structure Procs (P : Program) (pMain : ℕ) where
  pKeys : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pFill : ℕ
  keys : P[pKeys]? = some (LightSourceResidues.body pEmod)
  emod : P[pEmod]? = some emodBody
  histogram : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pKeys pHistogram)

variable {lim : Limits} {P : Program} {d : ℕ}









































































end ThreeSum.LightSourceHistogram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCyclic


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba


/-!
# Costed folding of the verified polynomial product

The ordinary linear array procedure adds coefficients `r` and `r+p` for
each output residue. Its specification is the exact natural cyclic
correlation, including histogram multiplicities.
-/

namespace ThreeSum.LightCyclic

open Light Karatsuba CyclicFold LightKaratsuba

variable {lim : Limits} {P : Program} {d : ℕ}





























































/-- Arguments: capacity, left array, right array, product array, output
array, Karatsuba scratch, and cyclic modulus. -/
def body (pMultiply pLinear : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pMultiply [v 0, v 1, v 2, v 3, v 5] 7)
    (.call pLinear [v 3, (Light.Expr.op Light.Op.add) (v 3) (v 6), v 4, v 6, k 1]
      7))

def combinedTime (k p : ℕ) : ℕ := LightKaratsuba.time k + LightArray.linearTime p + 100






















































































end ThreeSum.LightCyclic

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightNormalize


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Sorting and deduplicating a single already separated color class

The merge-sort implementation and proof are reused unchanged from the
attached upstream `ThreeSumApsp/Lang/Lib/Merge{,Sort}.lean` sources. The new
linear procedure removes adjacent repeats from the sorted output. The
original membership equivalence is retained, which is the witness needed
by the three-color reduction. Duplicates are removed only inside a class.
-/

namespace ThreeSum.LightNormalize

open Light

variable {lim : Limits} {P : Program}

def emitBody (pSelf : ℕ) : Stmt :=
  (Light.Stmt.seq (.store (v 2) (M (v 0)))
    (Light.Stmt.seq
      (.call pSelf
        [(Light.Expr.op Light.Op.add) (v 0) (k 1),
          (Light.Expr.op Light.Op.sub) (v 1) (k 1),
          (Light.Expr.op Light.Op.add) (v 2) (k 1)]
        3)
      (.set 0 ((Light.Expr.op Light.Op.add) (v 3) (k 1)))))

/-- Arguments: sorted source, length, output. The last occurrence of each
value is retained, matching `List.dedup`. -/
def dedupBody (pSelf : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 1)))
    (.ite ((Light.Cond.lt (k 1) (v 1)))
      (.ite ((Light.Cond.eq (M (v 0)) (M ((Light.Expr.op Light.Op.add) (v 0) (k 1)))))
        (.call pSelf [((Light.Expr.op Light.Op.add) (v 0) (k 1)),((Light.Expr.op Light.Op.sub) (v 1) (k 1)),v 2] 0)
        (emitBody pSelf))
      (emitBody pSelf))
    (.set 0 (k 0))

def dedupTime (n : ℕ) : ℕ := 200*n+30
























































































/-- Arguments: class source, class length, normalized output, merge scratch. -/
def body (pSort pDedup : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSort [v 1, v 0, v 3] 4) (.call pDedup [v 0, v 1, v 2] 0))

def time (n : ℕ) : ℕ := sortTime n+dedupTime n+80
def space (work n : ℕ) : ℕ := work+n

structure Procs (P : Program) (pMain : ℕ) where
  pSort : ℕ
  pHalf : ℕ
  pMerge : ℕ
  pCopy : ℕ
  pDedup : ℕ
  sort : MergeSort.Procs P pSort pHalf pMerge pCopy
  dedup : P[pDedup]? = some (dedupBody pDedup)
  main : P[pMain]? = some (body pSort pDedup)





















































end ThreeSum.LightNormalize

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSortedCatalog


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog


/-!
# Actual packed-key construction and sorted catalog index

The powers table supplies the physical mask radix. A linear pass retains the
original catalog index as a low digit, and the benchmark's verified merge
sort orders these records without changing their multiplicity or payload.
-/

namespace ThreeSum.LightReportingSortedCatalog

open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog

variable {lim : Limits}

def body (pPowers pPack pSort : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 5, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 6)
    (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 5) (v 0))))
      (Light.Stmt.seq (.call pPack [v 1, v 2, v 3, v 7, v 4] 8)
        (.call pSort [v 3, v 4, v 5] 0))))

def program : Program :=
  [powTableBody,LightReportingPackKeys.body,sortBody 2 3 4 5,halfBody,mergeBody,copyBody,body 0 1 2]

def time (W n : ℕ) : ℕ := powTableTime (W+1)+LightReportingPackKeys.time n+sortTime n+120

def word (W n : ℕ) : ℕ := LightReportingPackKeys.word (2^W) n+2^(W+1)
































































end ThreeSum.LightReportingSortedCatalog

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress


/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def At (μ : ℕ → ℤ) (lo hi : ℕ) (A : Family) : Prop :=
  (∀ i < A.size, μ (lo+i) = A.lower i) ∧
  (∀ i < A.size, μ (hi+i) = A.upper i)

def Bounded (A : Family) (U : ℕ) : Prop :=
  ∀ i < A.size, |A.lower i| ≤ (U : ℤ) ∧ |A.upper i| ≤ (U : ℤ)












def count (nA nB nC : ℕ) : ℕ := nB*nC+nA*nB+nA*nC
def width (nA nB nC : ℕ) : ℕ := Nat.clog 2 (nA+nB+nC+1)
def space (dst nA nB nC : ℕ) : ℕ := dst+count nA nB nC+width nA nB nC+1
def word (nA nB nC U : ℕ) : ℕ := 8*(nA+nB+nC+U+1)+32

def Tables (μ : ℕ → ℤ) (dst : ℕ) (A B C : Family) : Prop :=
  (∀ j < B.size, ∀ k < C.size,
    μ (dst+j*C.size+k) =
      (LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j) : ℤ)) ∧
  (∀ i < A.size, ∀ j < B.size,
    μ (dst+B.size*C.size+i*B.size+j) =
      (LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) : ℤ)) ∧
  (∀ i < A.size, ∀ k < C.size,
    μ (dst+B.size*C.size+A.size*B.size+i*C.size+k) =
      (LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) : ℤ))

/-- Arguments: six endpoint pointers, three band counts, output base. -/
def body (pClog pPowers pTable : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 10
      ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 6) (v 7))
        (v 8)))
    (Light.Stmt.seq (.set 11 ((Light.Expr.op Light.Op.mul) (v 7) (v 8)))
      (Light.Stmt.seq (.set 12 ((Light.Expr.op Light.Op.mul) (v 6) (v 7)))
        (Light.Stmt.seq (.set 13 ((Light.Expr.op Light.Op.mul) (v 6) (v 8)))
          (Light.Stmt.seq (.set 14 ((Light.Expr.op Light.Op.add) (v 9) (v 11)))
            (Light.Stmt.seq (.set 15 ((Light.Expr.op Light.Op.add) (v 14) (v 12)))
              (Light.Stmt.seq
                (.set 16 ((Light.Expr.op Light.Op.add) (v 15) (v 13)))
                (Light.Stmt.seq
                  (.call pClog [(Light.Expr.op Light.Op.add) (v 10) (k 1)] 17)
                  (Light.Stmt.seq
                    (.call pPowers
                      [v 16, (Light.Expr.op Light.Op.add) (v 17) (k 1), k 2] 18)
                    (Light.Stmt.seq
                      (.call pTable
                        [v 3, v 4, v 0, v 1, v 7, v 8, v 6, v 9, v 16, v 17,
                          (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
                        18)
                      (Light.Stmt.seq
                        (.call pTable
                          [v 0, v 2, v 4, v 5, v 6, v 7, v 8, v 14, v 16, v 17,
                            k 1]
                          18)
                        (Light.Stmt.seq
                          (.call pTable
                            [v 0, v 4, v 2, v 3, v 6, v 8, v 7, v 15, v 16, v 17,
                              (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
                            18)
                          (.set 0
                            ((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add) (v 11) (v 12))
                              (v 13)))))))))))))))

def time (nA nB nC : ℕ) : ℕ :=
  clog2Time (nA+nB+nC+1)+powTableTime (width nA nB nC+1)+
    LightBandTable.time nB nC (width nA nB nC)+
    LightBandTable.time nA nB (width nA nB nC)+
    LightBandTable.time nA nC (width nA nB nC)+500

structure Procs (P : Program) (pMain : ℕ) where
  pClog : ℕ
  pPowers : ℕ
  pTable : ℕ
  pRow : ℕ
  pLookup : ℕ
  pSearch : ℕ
  main : P[pMain]? = some (body pClog pPowers pTable)
  clog : P[pClog]? = some clog2Body
  powers : P[pPowers]? = some powTableBody
  table : P[pTable]? = some (LightBandTable.body pRow)
  row : P[pRow]? = some (LightBandTable.rowBody pLookup)
  lookup : P[pLookup]? = some (LightBandLookup.body pSearch)
  search : P[pSearch]? = some (LightBandLookup.searchBody pSearch)



































































































































































































































































































end ThreeSum.LightBandEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandCandidatesCell


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-! # Actual four-cell flagged owner records -/

namespace ThreeSum.LightBandCandidatesCell

open Light BandCandidateRows

set_option maxHeartbeats 1400000
set_option maxRecDepth 6000

def tail (mode : Mode) : Stmt :=
  (Light.Stmt.seq (.store (v 3) (v 4))
    (Light.Stmt.seq
      (.store ((Light.Expr.op Light.Op.add) (v 3) (k 1))
        (match mode with
        | .bc => v 5
        | _ => v 1))
      (Light.Stmt.seq
        (.store ((Light.Expr.op Light.Op.add) (v 3) (k 2))
          (match mode with
          | .bc => v 1
          | .ab => v 2
          | .ac => v 5))
        (.store ((Light.Expr.op Light.Op.add) (v 3) (k 3))
          (match mode with
          | .ab => v 5
          | _ => v 2)))))

/-- Lookup result, outer coordinate, inner coordinate, output pointer. -/
def body (mode : Mode) : Stmt :=
  (Light.Stmt.seq (.set 4 (k 0))
    (Light.Stmt.seq (.set 5 (k 0))
      (Light.Stmt.seq
        (.ite (Light.Cond.lt (k 0) (v 0))
          (Light.Stmt.seq (.set 4 (k 1))
            (.set 5 ((Light.Expr.op Light.Op.sub) (v 0) (k 1))))
          .skip)
        (tail mode))))

def time : ℕ := 220

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {r i j dst U : ℕ}


















































end ThreeSum.LightBandCandidatesCell

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandRawAStep


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA


/-! # Append the actual A band of one flagged owner record -/

namespace ThreeSum.LightBandRawAStep

open Light BandCandidateRows BandRawA

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def tail (pRow : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pRow
      [(Light.Expr.op Light.Op.add) (v 0) (v 10),
        (Light.Expr.op Light.Op.add) (v 6) (v 9),
        (Light.Expr.op Light.Op.add) (v 7) (v 9),
        (Light.Expr.op Light.Op.add) (v 8) (v 9), v 11, v 5, v 10]
      12)
    (.set 0 ((Light.Expr.op Light.Op.add) (v 9) (v 11))))

/-- Sorted A base and length, g, flag, A band, owner, three output bases,
and the previous incidence count. -/
def body (pRow : ℕ) : Stmt :=
  .ite ((Light.Cond.eq (v 3) (k 1)))
    ((Light.Stmt.seq (.set 10 ((Light.Expr.op Light.Op.mul) (v 4) (v 2)))
       (Light.Stmt.seq (.set 11 ((Light.Expr.op Light.Op.sub) (v 1) (v 10)))
         (Light.Stmt.seq (.ite (Light.Cond.lt (v 2) (v 11)) (.set 11 (v 2)) .skip)
           (tail pRow)))))
    (.set 0 (v 9))

def time (g : ℕ) : ℕ := LightBandRawARow.time g+250

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src n g owner values owners positions previous capacity : ℕ} {r : Record}






























































































end ThreeSum.LightBandRawAStep

end


