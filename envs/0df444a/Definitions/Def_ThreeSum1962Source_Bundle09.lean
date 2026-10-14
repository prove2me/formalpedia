-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle09
-- name    : ThreeSum1962Source_Bundle09
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:14:37.249024+00:00
-- url     : https://prove2.me/theorems/f03275b6-2031-4eae-85ed-3a6159029ab4
-- title:
--   Weighted owner catalogs, residue buckets, and reporting components
-- statement:
--   This bundle defines the aggregate score of a physical band-owner catalog $R$:
--   $$
--   \operatorname{score}(R)=\sum_{r\in R}\operatorname{block}(r),
--   $$
--   where an unflagged record contributes zero and a flagged record uses its three truncated bands. Catalog occurrences remain separate even when their values agree. The bundle specifies packed A-value, owner, and position arrays; finite owner-product domains; prime-pool generation; residue-bucket construction; common-offset selection; and weighted-score program bodies. It also defines local cover-matrix support bits, blockwise endpoint conditions, original-output decoding indices, raw reporting prefixes, child construction, sparse-box reads, arithmetic budgets, and the guarded hybrid caller assembly.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ArithmeticStageBounds.lean#L21-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAFinite.lean#L19-L51
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAOriginal.lean#L21-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandWeightedScore.lean#L21-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockEncoding.lean#L20-L204
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/CostLedger.lean#L21-L40
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HierarchyScales.lean#L19-L257
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandCandidatesTable.lean#L13-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPreprocessing.lean#L21-L230
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawA.lean#L19-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockChildren.lean#L21-L154
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorScanHost.lean#L13-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightGlobalKeys.lean#L21-L86
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOriginalOffset.lean#L22-L192
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightPrimePool.lean#L22-L265
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightQueryBox.lean#L22-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingLeafBatch.lean#L20-L65
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingOwnerSelect.lean#L19-L35
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingPairRows.lean#L23-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketBuild.lean#L18-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketOriginal.lean#L19-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceFlagArray.lean#L19-L52
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumHybridCore.lean#L19-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightDecode.lean#L16-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightedScore.lean#L26-L307
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalCoverMatrix.lean#L18-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/OutputDecodeRecords.lean#L14-L122
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RawReporting.lean#L23-L98
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandPairData.lean#L9-L35
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WantedResidueKeys.lean#L17-L34

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBucketBuild


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Actual contiguous buckets from a generic residue-code array

This fixed program constructs its own count histogram, then exact prefix
offsets and an index scatter. No caller-supplied bucket lengths or lists are
assumed. It is shared by source extraction and output-sensitive residue joins.
-/

namespace ThreeSum.LightSourceBucketBuild

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def body (pHistogram pBuckets : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pHistogram [v 0, v 1, v 5, v 6] 7)
    (.call pBuckets [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 7))

def time (N M : ℕ) : ℕ := histogramTime N M+LightSourceBucketFromHistogram.time N M+50

structure Procs (P : Program) (pMain : ℕ) where
  pHistogram : ℕ
  pFill : ℕ
  pBuckets : ℕ
  histogram : P[pHistogram]? = some (histogramBody pFill)
  fill : P[pFill]? = some fillBody
  buckets : LightSourceBucketFromHistogram.Procs P pBuckets
  main : P[pMain]? = some (body pHistogram pBuckets)

variable {lim : Limits} {P : Program} {d : ℕ}


















































end ThreeSum.LightSourceBucketBuild

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBucketOriginal


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Original signed inputs to retained histograms and exact index buckets

The actual code/histogram constructor runs once, followed by linear prefix
and scatter passes. Both source transforms and terminal Cartesian reporting
reuse these same counts and original-index fibers.
-/

namespace ThreeSum.LightSourceBucketOriginal

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pSource pBuckets : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSource [v 0, v 5, v 1, v 2, v 3, v 6, v 10, v 4] 11)
    (.call pBuckets [v 6, v 5, v 7, v 8, v 9, v 1, v 3] 11))

def time (N p m U D : ℕ) : ℕ :=
  LightSourceHistogram.time N p m U D+LightSourceBucketFromHistogram.time N m+50

structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  pBuckets : ℕ
  sourceProcs : LightSourceHistogram.Procs P pSource
  buckets : LightSourceBucketFromHistogram.Procs P pBuckets
  main : P[pMain]? = some (body pSource pBuckets)

variable {lim : Limits} {P : Program} {d : ℕ}
































































end ThreeSum.LightSourceBucketOriginal

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_WantedResidueKeys


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# The actual residue scans and the selected wanted mass

The two-remainder source scanner specializes to an ordinary shifted residue
when its moduli agree. Its actual fiber count is exactly the incidence mass
minimized by the original signed-array offset program.
-/

namespace ThreeSum.WantedResidueKeys

open Light
open scoped BigOperators

def code (M : ℕ) (shift x : ℤ) : ℕ := LightSourceResidues.key M M shift x















def total (M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : ℕ :=
  WantedPairs.count (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL


































end ThreeSum.WantedResidueKeys

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingLeafBatch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Actual terminal-candidate batch with a sum of physical pair charges

All endpoint and independent flag arrays are read from retained memory.
The recursion evaluates each candidate and retains a Boolean disjunction.
Its cost sums the actual leaf costs instead of multiplying a worst fiber
size by the number of candidates.
-/

namespace ThreeSum.LightReportingLeafBatch

open Light Finset SourceBuckets LightResidues
open scoped BigOperators

set_option maxHeartbeats 2600000
set_option maxRecDepth 10000

def Hit (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (NL NR Mo n : ℕ) : Prop :=
  ∃ i<n, LightReportingLeaf.Hit a (xL i) (xR i) left right keyL keyR NL NR Mo (flagL i) (flagR i)
















def time (keyL keyR flagL flagR : ℕ→ℕ) (NL NR Mo U : ℕ) (xL xR : ℕ→ℤ) : ℕ→ℕ
  | 0 => 30
  | n+1 => time keyL keyR flagL flagR NL NR Mo U xL xR n+
      LightReportingLeaf.time keyL keyR NL NR Mo (flagL n) (flagR n) U (xL n) (xR n)+300








/-- a, source and bucket pointers, source lengths, modulus, four retained
endpoint/flag arrays, candidate count, and scratch. -/
def body (pSelf pLeaf : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 14)))
    ((Light.Stmt.seq
       (.call pSelf
         [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
           (Light.Expr.op Light.Op.sub) (v 14) (k 1), v 15]
         16)
       (Light.Stmt.seq (.set 17 ((Light.Expr.op Light.Op.sub) (v 14) (k 1)))
         (Light.Stmt.seq (.set 18 (M ((Light.Expr.op Light.Op.add) (v 10) (v 17))))
           (Light.Stmt.seq (.set 19 (M ((Light.Expr.op Light.Op.add) (v 11) (v 17))))
             (Light.Stmt.seq
               (.set 20 (M ((Light.Expr.op Light.Op.add) (v 12) (v 17))))
               (Light.Stmt.seq
                 (.set 21 (M ((Light.Expr.op Light.Op.add) (v 13) (v 17))))
                 (Light.Stmt.seq
                   (.call pLeaf
                     [v 0, v 1, v 2, v 3, v 4, v 18, v 20, v 5, v 6, v 19, v 21, v 7,
                       v 8, v 9, v 15]
                     22)
                   (.ite
                     (Light.Cond.lt (k 0)
                       ((Light.Expr.op Light.Op.add) (v 16) (v 22)))
                     (.set 0 (k 1)) (.set 0 (k 0)))))))))))
    (.set 0 (k 0))

def program : Program := LightReportingLeaf.program ++ [body 6 5]

variable {lim : Limits}


























































































end ThreeSum.LightReportingLeafBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumHybridCore


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Exact assembly and execution of the final hybrid caller

The supplied first537 procedures are followed by the relocated four-procedure
original-triple solver, one integer-power procedure, and the hybrid caller.
The two runtime guards use the actual size and the supplied magnitude bound.
-/

namespace ThreeSum.LightThreeSumHybridCore

open Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

def body (κ cutoff : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (v 0) (k cutoff)))
    (.call 540 [v 0,v 1,v 2,v 3] 0)
    ((Light.Stmt.seq (.call 541 [v 0, k κ] 4)
       (.ite (Light.Cond.lt (v 4) (v 1)) (.call 540 [v 0, v 1, v 2, v 3] 0)
         (.call 536 [v 2, v 0, v 3] 0))))

def libraries (fastP : Program) : Program :=
  ReportingHostRelocation.program fastP LightBruteThreeSum.program

def program (fastP : Program) (κ cutoff : ℕ) : Program :=
  libraries fastP++[LightNatPower.body,body κ cutoff]















































































































end ThreeSum.LightThreeSumHybridCore

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceFlagArray


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct


/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray

open Light SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

def flag (J L h p cap : ℕ) (sel candidate : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (mask : ℕ) : ℕ :=
  product (LightSourceTrim.rowFlag L h p cap sel candidate
    (LightMaskBits.bit (J*L) mask) w0 w1 counts) J






/-- Arguments: the same map/table inputs as the single-mask program, followed
by mask array, mask count, paired-array output, and three scratch pointers. -/
def body (pFlag : ℕ) : Stmt :=
  .for 16 (v 11) (
    (Light.Stmt.seq
      (.call pFlag
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9,
          M ((Light.Expr.op Light.Op.add) (v 10) (v 16)),
          (Light.Expr.op Light.Op.add) (v 12)
            ((Light.Expr.op Light.Op.mul) (k 2) (v 11)),
          v 13, v 14, v 15]
        17)
      (Light.Stmt.seq
        (.store ((Light.Expr.op Light.Op.add) (v 12) (v 16))
          (M
            ((Light.Expr.op Light.Op.add) (v 12)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 11)))))
        (.store
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 12) (v 11))
            (v 16))
          (M
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v 12)
                ((Light.Expr.op Light.Op.mul) (k 2) (v 11)))
              (k 1)))))))

def time (n J L U : ℕ) : ℕ := n*(LightSourceMaskFlags.time J L U+200)+10

structure Procs (P : Program) (pMain : ℕ) where
  pFlag : ℕ
  flagProcs : LightSourceMaskFlags.Procs P pFlag
  main : P[pMain]? = some (body pFlag)

def Inv (μ : ℕ → ℤ) (J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work : ℕ)
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,dst,bitBase,rowOut,work,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (flag J L h p cap sel candidate w0 w1 leftCount (mask j) : ℤ)) ∧
    (∀ j < i, ν (dst+n+j) = (flag J L h p cap sel candidate w1 w0 rightCount (mask j) : ℤ)) ∧
    KeptBut μ ν bitBase dst (2*n+2)

variable {lim : Limits} {P : Program} {d : ℕ}





















































































































































end ThreeSum.LightSourceFlagArray

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LocalCoverMatrix


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes


/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix

open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes

variable {h L k : ℕ}

def bits (L k i : ℕ) : ℕ → ℕ := LightMaskBits.bit L (maskAt L k i)
def leftCount (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k)
def rightCount (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k)
def key (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  LightPairFlags.pairKey (LocalMaskGraph.vertexCount L k) (localPrime h)
    (leftCode w k) (rightCode w k)
def valid (w : Weight L (LocalField h)) (k B : ℕ) : ℕ → ℕ :=
  LightPairFlags.pairFlag L (LocalMaskGraph.vertexCount L k) B (bits L k)
    (leftCode w k) (rightCode w k) (leftCount w k) (rightCount w k)
def entry (w : Weight L (LocalField h)) (k B r : ℕ) : ℕ :=
  LightSupportMark.bit (key w k) (valid w k B) r
    (LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k)








































































































end ThreeSum.LocalCoverMatrix

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightGlobalKeys


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# From selected coefficient rows to every original global output key

The fixed program constructs the output-mask layer, all signed local keys,
and the full positional product. Its output is the literal occurrence-aware
`GlobalKeyEnumeration.globalKeys` array. No input key or mask table is assumed.
-/

namespace ThreeSum.LightGlobalKeys

open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress

set_option maxHeartbeats 600000
set_option maxRecDepth 10000

/-- L, layer cardinality, schedule length, radix, block count, coefficient rows,
layer size, and first free address. Sizes are read from the parameter initializer. -/
def body (pEnum pLocal pGlobal : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.mul) (v 2) (v 6)))
    (Light.Stmt.seq (.set 9 ((Light.Expr.op Light.Op.add) (v 7) (v 6)))
      (Light.Stmt.seq (.set 10 ((Light.Expr.op Light.Op.add) (v 9) (v 8)))
        (Light.Stmt.seq (.call pEnum [v 0, v 1, v 7, v 10] 11)
          (Light.Stmt.seq (.call pLocal [v 0, v 7, v 11, v 5, v 2, v 9, v 10] 12)
            (.call pGlobal [v 9, v 8, v 4, v 3, v 10] 0))))))

def localCount (h : ℕ) : ℕ := scheduleSize h*outputCount (512*h) h
def scratch (free h : ℕ) : ℕ := free+outputCount (512*h) h+localCount h

def space (free h J : ℕ) : ℕ :=
  max (LightLocalKeyRow.space (scratch free h) (512*h) (outputCount (512*h) h))
    (LightRadixKeys.space (scratch free h) (localCount h) J)

def word (h J : ℕ) : ℕ := 2^(512*h+1)+
  LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h)+
  LightRadixKeys.word (localPrime h) (512*h*localPrime h) J+J+512

def time (h J : ℕ) : ℕ := LightSubsetEnumerationSetup.time (512*h) (2*h)+
  LightLocalKeys.time (512*h) (outputCount (512*h) h) (scheduleSize h)+
  LightRadixKeys.time (localCount h) J+200


























structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pLayer : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pRows : ℕ
  pAffine : ℕ
  main : P[pMain]? = some (body pEnum pLocal pGlobal)
  enum : P[pEnum]? = some (LightSubsetEnumerationSetup.body pPowers pLayer)
  powers : P[pPowers]? = some powTableBody
  layer : P[pLayer]? = some (LightSubsetEnumeration.body pLayer)
  locals : LightLocalKeys.Procs P pLocal
  globalProc : P[pGlobal]? = some (LightRadixKeys.body pGlobal pRows)
  rows : P[pRows]? = some (LightRadixRows.body pAffine)
  affine : P[pAffine]? = some LightReportingAffine.body

variable {lim : Limits} {P : Program} {d : ℕ}











































































































































end ThreeSum.LightGlobalKeys

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOriginalOffset


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues


/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset

open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def selected (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) : ℕ :=
  LightBalancedOffset.offset (signedHistogram p 1 right nRight)
    (signedHistogram p 1 left nLeft)




















/-- Left and right signed key arrays, their lengths, modulus, maximum
length, and first free address. -/
def body (pCapacity pHist pOffset : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCapacity [v 4] 7)
    (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 6) (v 7)))
      (Light.Stmt.seq
        (.set 9
          ((Light.Expr.op Light.Op.add) (v 6)
            ((Light.Expr.op Light.Op.mul) (k 2) (v 7))))
        (Light.Stmt.seq
          (.set 10
            ((Light.Expr.op Light.Op.add) (v 6)
              ((Light.Expr.op Light.Op.mul) (k 3) (v 7))))
          (Light.Stmt.seq
            (.set 11
              ((Light.Expr.op Light.Op.add) (v 6)
                ((Light.Expr.op Light.Op.mul) (k 5) (v 7))))
            (Light.Stmt.seq (.set 12 ((Light.Expr.op Light.Op.add) (v 11) (v 5)))
              (Light.Stmt.seq
                (.call pHist
                  [v 0, v 9, v 2, v 4, v 7, v 11, v 12,
                    (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
                  13)
                (Light.Stmt.seq
                  (.call pHist [v 1, v 8, v 3, v 4, v 7, v 11, v 12, k 1] 13)
                  (.call pOffset [v 7, v 8, v 9, v 10, v 6, v 12, v 4] 0)))))))))

def time (p nLeft nRight U : ℕ) : ℕ := LightCapacity.time p+
  LightResidueHistogram.time nLeft (capacity p) U+
  LightResidueHistogram.time nRight (capacity p) U+
  LightBalancedOffset.time (Nat.clog 2 p) p+300
def space (free p N U : ℕ) : ℕ := free+13*capacity p+N+Nat.log 2 (U+1)+2
def word (p N U : ℕ) : ℕ := LightKaratsuba.wordBound (capacity p) N+4*U+4*p+16

structure Procs (P : Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pFill : ℕ
  pOffset : ℕ
  pCyclic : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pMinimum : ℕ
  capacityProc : P[pCapacity]? = some LightCapacity.body
  histogram : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  count : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  offset : P[pOffset]? = some (LightBalancedOffset.body pCyclic pMinimum)
  cyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear)
  karatsuba : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  minimum : P[pMinimum]? = some LightMinimum.body
  main : P[pMain]? = some (body pCapacity pHist pOffset)

variable {lim : Limits} {P : Program} {d : ℕ}






























































































def program : Program :=
  [body 1 2 7,LightCapacity.body,LightResidueHistogram.body 3 5,residuesBody 4,
    emodBody,LightHistogram.histogramBody 6,fillBody,LightBalancedOffset.body 8 12,
    LightCyclic.body 9 11,LightKaratsuba.body 9 10 11 6,halfBody,
    LightArray.linearBody,LightMinimum.body]

def programProcs : Procs program 0 :=
  ⟨1,2,3,4,5,6,7,8,9,10,11,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩

































end ThreeSum.LightOriginalOffset

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandCandidatesTable


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-! # Actual rectangular owner records with two nested loops -/

namespace ThreeSum.LightBandCandidatesTable

open Light BandCandidateRows

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pRow : ℕ) : Stmt :=
  .for 4 (v 2) (
    .call pRow [((Light.Expr.op Light.Op.add) (v 0) ((Light.Expr.op Light.Op.mul) (v 4) (v 3))),((Light.Expr.op Light.Op.add) (v 1)
                                                                                                  ((Light.Expr.op Light.Op.mul) (k 4)
                                                                                                    ((Light.Expr.op Light.Op.mul) (v 4) (v 3)))),v 3,v 4] 5)

def time (m n : ℕ) : ℕ := m*(LightBandCandidatesRow.time n+100)+6

def Inv (μ : ℕ → ℤ) (mode : Mode) (f : ℕ → ℕ → ℕ)
    (src dst m n i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [src,dst,m,n,i,r],ν⟩ ∧
    (∀ x < i, ∀ y < n, Seg ν (dst+4*(x*n+y)) (make mode x y (f x y)).cells) ∧
    SameOutside μ ν dst (4*(m*n))

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst m n U : ℕ} {f : ℕ → ℕ → ℕ}

















































































end ThreeSum.LightBandCandidatesTable

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingOwnerSelect


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA


/-!
# Actual owner and original A-value selection by physical incidence index

Four retained cells give the exact original A value, physical owner slot,
and its independent B/C bands. Equal values and repeated owner-domain
incidences retain their separate physical indices.
-/

namespace ThreeSum.LightReportingOwnerSelect

open Light BandRawA BandCandidateRows

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-- Packed A values, owner labels, owner records, decoded incidence, output. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 5 (M ((Light.Expr.op Light.Op.add) (v 0) (v 3))))
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 1) (v 3))))
      (Light.Stmt.seq
        (.set 7
          (M
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v 2)
                ((Light.Expr.op Light.Op.mul) (k 4) (v 6)))
              (k 2))))
        (Light.Stmt.seq
          (.set 8
            (M
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 2)
                  ((Light.Expr.op Light.Op.mul) (k 4) (v 6)))
                (k 3))))
          (Light.Stmt.seq (.store (v 4) (v 5))
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 4) (k 1)) (v 6))
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 4) (k 2)) (v 7))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 4) (k 3)) (v 8))
                  (.set 0 (v 4))))))))))

def program : Program := [body]

def row (f : ℕ→ℤ) (n g : ℕ) (rs : List Record) (i : ℕ) : List ℤ :=
  [f (labelAt n g rs i).position,(labelAt n g rs i).owner,
    (ownerRecord n g rs i).b,(ownerRecord n g rs i).c]










































end ThreeSum.LightReportingOwnerSelect

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandRawA


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA


/-!
# The actual flattened A-incidence catalog

The loop reads each four-cell owner record once. Successful records append
only their actual truncated A band. Parallel value, owner-slot, and sorted
position arrays are packed using capacity g times the owner count.
-/

namespace ThreeSum.LightBandRawA

open Light BandCandidateRows BandRawA

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

def capacity (N g : ℕ) : ℕ := g*N
def ownerBase (vals N g : ℕ) : ℕ := vals+capacity N g
def positionBase (vals N g : ℕ) : ℕ := ownerBase vals N g+capacity N g
def space (vals N g : ℕ) : ℕ := positionBase vals N g+capacity N g
def word (n g N : ℕ) : ℕ := n+g+N+20
def time (N g : ℕ) : ℕ := N*(LightBandRawAStep.time g+200)+100

/-- Record base/count, sorted A base/length, g, first output address. -/
def body (pStep : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.mul) (v 4) (v 1)))
    (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.add) (v 5) (v 6)))
      (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 7) (v 6)))
        (Light.Stmt.seq (.set 9 (k 0))
          (Light.Stmt.seq
            (.for 10 (v 1)
              (Light.Stmt.seq
                (.set 11
                  (M
                    ((Light.Expr.op Light.Op.add) (v 0)
                      ((Light.Expr.op Light.Op.mul) (k 4) (v 10)))))
                (Light.Stmt.seq
                  (.set 12
                    (M
                      ((Light.Expr.op Light.Op.add)
                        ((Light.Expr.op Light.Op.add) (v 0)
                          ((Light.Expr.op Light.Op.mul) (k 4) (v 10)))
                        (k 1))))
                  (.call pStep
                    [v 2, v 3, v 4, v 11, v 12, v 10, v 5, v 7, v 8, v 9] 9))))
            (.set 0 (v 9)))))))

def Inv (μ : ℕ → ℤ) (rs : List Record) (f : ℕ → ℤ)
    (records src n g vals i : ℕ) (σ : State) : Prop :=
  ∃ (flag a : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [records,rs.length,src,n,g,vals,capacity rs.length g,
      ownerBase vals rs.length g,positionBase vals rs.length g,count n g rs i,i,flag,a],ν⟩ ∧
    Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g)
      f (firstRows n g rs i) ∧ Kept μ ν vals

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  pRow : ℕ
  pCopy : ℕ
  pFill : ℕ
  step : P[pStep]?=some (LightBandRawAStep.body pRow)
  row : P[pRow]?=some (LightBandRawARow.body pCopy pFill)
  copy : P[pCopy]?=some copyBody
  fill : P[pFill]?=some fillBody
  main : P[pMain]?=some (body pStep)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}
























































































































































end ThreeSum.LightBandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAFinite


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

def coordinates {a b c : ℕ} (t : Fin a × Fin b × Fin c) : ℕ × ℕ × ℕ :=
  (t.1.val,t.2.1.val,t.2.2.val)

def finiteAIndices (n g : ℕ) (rs : List Record) (s : ℕ) :
    Finset (Fin (items n g rs).length) :=
  univ.filter fun i => i.val ∈ aIndices n g rs s

def finiteBandPositions (n g a : ℕ) : Finset (Fin n) :=
  univ.filter fun i => i.val ∈ bandPositions n g a

def finiteOwnerProduct (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    Finset (Fin (items nA g rs).length × Fin nB × Fin nC) :=
  finiteAIndices nA g rs s ×ˢ (finiteBandPositions nB g (rs.getD s default).b ×ˢ
    finiteBandPositions nC g (rs.getD s default).c)

def finiteAllProducts (nA nB nC g : ℕ) (rs : List Record) :
    Finset (Fin (items nA g rs).length × Fin nB × Fin nC) :=
  univ.filter fun t => coordinates t ∈ allProducts nA nB nC g rs












@[simp] theorem mem_finiteBandPositions {n g a : ℕ} {i : Fin n} :
    i ∈ finiteBandPositions n g a ↔ i.val ∈ bandPositions n g a := by
  simp only [finiteBandPositions,mem_filter,mem_univ,true_and]




















































































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAOriginal


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition


/-!
# Exact original-value membership and equation coverage of the owner catalog

Normalized sorted coordinates remain distinct from original input
positions. The normalization membership equivalence transfers values back
to their original color classes; the color-class bridge can then recover
the required distinct original positions.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def sortedRecords (A B C : List ℤ) (g : ℕ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List Record :=
  records (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
    (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
    (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC))


























































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandPreprocessing


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition


/-!
# Closed normalization and band listing for three supplied color classes

The three class arrays are sorted and deduplicated separately. Their actual
length/count headers then drive the actual owner-table enumerator. The program
has twenty fixed procedures. No sorting function, lookup function, or band
enumerator is supplied by the caller.
-/

namespace ThreeSum.LightBandPreprocessing

open Light ThreeSum.BandPartition

set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

variable {lim : Limits} {P : Program}

def Represents (μ : ℕ → ℤ) (values endpoints g : ℕ) (hg : 0 < g)
    (original L : List ℤ) (hs : L.Pairwise (· < ·)) : Prop :=
  Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
    LightHeaderBands.At μ endpoints L.length
      (family (fun i => L.getD i 0) L.length g hg (LightSortedBands.getD_strict hs))

def Output (μ : ℕ → ℤ) (av ae bv be cv ce dst g : ℕ) (hg : 0 < g)
    (originalA originalB originalC : List ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
      r = (LightBandEnumeration.count (size A.length g) (size B.length g) (size C.length g) : ℤ) ∧
      Represents μ av ae g hg originalA A hsA ∧
      Represents μ bv be g hg originalB B hsB ∧
      Represents μ cv ce g hg originalC C hsC ∧
      LightBandEnumeration.Tables μ dst
        (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
        (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
        (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC))



















/-- Arguments: source/length pairs for A, B, C; band size; value/header
output pairs for A, B, C; common scratch and table output address. -/
def body (pPrepare pEnumerate : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pPrepare [v 0, v 1, v 6, v 7, v 8, v 13] 14)
    (Light.Stmt.seq (.call pPrepare [v 2, v 3, v 6, v 9, v 10, v 13] 14)
      (Light.Stmt.seq (.call pPrepare [v 4, v 5, v 6, v 11, v 12, v 13] 14)
        (.call pEnumerate [v 8, v 10, v 12, v 13] 0))))

def time (a b c g : ℕ) : ℕ :=
  LightSortedBands.time a+LightSortedBands.time b+LightSortedBands.time c+
    LightHeaderBands.time (size a g) (size b g) (size c g)+300

def space (work a b c g : ℕ) : ℕ :=
  work+(a+b+c)+LightBandEnumeration.count (size a g) (size b g) (size c g)+
    LightBandEnumeration.width (size a g) (size b g) (size c g)+1

def word (a b c g U : ℕ) : ℕ :=
  a+b+c+g+2+LightBandEnumeration.word (size a g) (size b g) (size c g) U

def depth (a b c g : ℕ) : ℕ :=
  a+b+c+Nat.clog 2 (a+b+c)+
    LightBandEnumeration.width (size a g) (size b g) (size c g)+10

structure Procs (P : Program) (pMain : ℕ) where
  pPrepare : ℕ
  pEnumerate : ℕ
  prepare : LightSortedBands.Procs P pPrepare
  enumerate : LightHeaderBands.Procs P pEnumerate
  main : P[pMain]? = some (body pPrepare pEnumerate)







































































































































def program : Program :=
  [body 1 12,
    LightSortedBands.body 2 8,LightNormalize.body 3 7,
    sortBody 3 4 5 6,halfBody,mergeBody,copyBody,LightNormalize.dedupBody 7,
    LightBandPartition.body 9 10 11,LightSmallDivide.body,
    LightBandPartition.lowerBody,LightBandPartition.upperBody,
    LightHeaderBands.body 13,LightBandEnumeration.body 14 15 16,clog2Body,powTableBody,
    LightBandTable.body 17,LightBandTable.rowBody 18,LightBandLookup.body 19,LightBandLookup.searchBody 19]






























end ThreeSum.LightBandPreprocessing

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandPairData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition


/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition

def leftBase (base : ℕ) : ℕ := base+8
def rightBase (base NL g m : ℕ) : ℕ := SourceBandLayout.work (leftBase base) NL g m
def zeroBase (base NL NR g m : ℕ) : ℕ := SourceBandLayout.work (rightBase base NL g m) NR g m
def next (base NL NR g m : ℕ) : ℕ := zeroBase base NL NR g m+m+1











def header (base NL NR g m : ℕ) : List ℤ :=
  [leftBase base,size NL g,rightBase base NL g m,size NR g,
    zeroBase base NL NR g m,next base NL NR g m,NL,NR]

structure Data (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ) : Prop where
  left : ∀ i < size NL g, SourceBandData.At μ fL (leftBase base) NL g p m 0 i
  right : ∀ i < size NR g, SourceBandData.At μ fR (rightBase base NL g m) NR g p m shift i
  zero : ∀ r ≤ m, μ (zeroBase base NL NR g m+r)=0

structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ)
    extends Data μ fL fR base NL NR g p m shift : Prop where
  heads : Seg μ base (header base NL NR g m)





























































end ThreeSum.SourceBandPairData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandWeightedScore


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

def length (n g a : ℕ) : ℕ := min g (n-a*g)



















def block (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (r : Record) : ℕ :=
  if r.flag=1 then
    WeightedScore.score primes s q (length nA g r.a) (length nB g r.b) (length nC g r.c)
      (fun i => A (r.a*g+i)) (fun i => B (r.b*g+i)) (fun i => C (r.c*g+i))
  else 0

def partialScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ) : ℕ :=
  ∑ i ∈ range k, block primes s q nA nB nC g A B C (rs.getD i default)

def score (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  partialScore primes s q nA nB nC g A B C rs rs.length






























































































end ThreeSum.BandWeightedScore

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightPrimePool


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool

open Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def scanned (y : ℕ) : ℕ → List ℕ
  | 0 => []
  | i+1 =>
    if Nat.Prime (y+i+1) then scanned y i ++ [y+i+1] else scanned y i











theorem mem_prefix {y i p : ℕ} :
    p ∈ scanned y i ↔ Nat.Prime p ∧ y < p ∧ p ≤ y+i := by
  induction i with
  | zero => simp only [scanned,List.not_mem_nil,false_iff]; omega
  | succ i ih =>
      by_cases hp : Nat.Prime (y+i+1)
      · simp only [scanned,if_pos hp,List.mem_append,List.mem_singleton,ih]
        constructor
        · rintro (⟨hpr,hlo,hhi⟩ | rfl)
          · exact ⟨hpr,hlo,by omega⟩
          · exact ⟨hp,by omega,by omega⟩
        · rintro ⟨hpr,hlo,hhi⟩
          by_cases heq : p = y+i+1
          · exact Or.inr heq
          · exact Or.inl ⟨hpr,hlo,by omega⟩
      · simp only [scanned,if_neg hp,ih]
        constructor
        · rintro ⟨hpr,hlo,hhi⟩
          exact ⟨hpr,hlo,by omega⟩
        · rintro ⟨hpr,hlo,hhi⟩
          have hne : p ≠ y+i+1 := fun heq => hp (heq ▸ hpr)
          exact ⟨hpr,hlo,by omega⟩


















def values (y : ℕ) : List ℕ := scanned y (3*y)
def size (y : ℕ) : ℕ := (values y).length
def prime (y i : ℕ) : ℕ := (values y).getD i 0





theorem mem_values {y p : ℕ} :
    p ∈ values y ↔ Nat.Prime p ∧ y < p ∧ p ≤ 4*y := by
  rw [values,mem_prefix]
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨hp,hlo,by omega⟩
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨hp,hlo,by omega⟩

theorem values_toFinset (y : ℕ) : (values y).toFinset = PrimeDensity.candidates y := by
  ext p
  simp only [List.mem_toFinset,mem_values,PrimeDensity.mem_candidates]





theorem prime_mem {y i : ℕ} (hi : i < size y) : prime y i ∈ values y := by
  unfold prime
  rw [List.getD_eq_getElem _ _ hi]
  exact List.mem_of_getElem rfl









































theorem auxiliarySet_eq_candidates (y : ℕ) :
    WeightedScore.auxiliarySet (prime y) (size y) = PrimeDensity.candidates y := by
  rw [← values_toFinset]
  ext p
  simp only [WeightedScore.auxiliarySet,Finset.mem_image,Finset.mem_range,List.mem_toFinset]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact prime_mem hi
  · intro hp
    obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp hp
    refine ⟨i,hi,?_⟩
    simpa only [prime,List.getD_eq_getElem _ _ hi] using heq

/-- Arguments: lower endpoint and first free address. The output occupies
at most `3*y` cells; the primality helper reuses the scratch beyond them. -/
def body (pTest : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 2 (k 0))
    (Light.Stmt.seq
      (.set 6
        ((Light.Expr.op Light.Op.add) (v 1)
          ((Light.Expr.op Light.Op.mul) (k 3) (v 0))))
      (Light.Stmt.seq
        (.for 3 ((Light.Expr.op Light.Op.mul) (k 3) (v 0))
          (Light.Stmt.seq
            (.set 4
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 0) (v 3)) (k 1)))
            (Light.Stmt.seq (.call pTest [v 4, v 6] 5)
              (.ite (Light.Cond.eq (v 5) (k 1))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 1) (v 2)) (v 4))
                  (.set 2 ((Light.Expr.op Light.Op.add) (v 2) (k 1))))
                .skip))))
        (.set 0 (v 2)))))

def time (y : ℕ) : ℕ := 3*y*(LightPrimality.time (4*y) (4*y)+100)+100
def space (free y : ℕ) : ℕ := free+3*y+(Nat.log 2 (4*y+1)+2)
def word (y : ℕ) : ℕ := 32*y+16

def Inv (μ : ℕ → ℤ) (y free i : ℕ) (σ : State) : Prop :=
  ∃ (cval rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(y : ℤ),free,(scanned y i).length,i,cval,rval,free+3*y],ν⟩ ∧
      SegN ν free (scanned y i) ∧ Kept μ ν free

structure Procs (P : Program) (pMain : ℕ) where
  pTest : ℕ
  test : LightPrimality.Procs P pTest
  main : P[pMain]? = some (body pTest)

variable {lim : Limits} {P : Program} {d : ℕ}








































































def program : Program := [body 1,LightPrimality.body 2,emodBody]

def program_procs : Procs program 0 where
  pTest := 1
  test := ⟨2,rfl,rfl⟩
  main := rfl










end ThreeSum.LightPrimePool

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWeightedScore


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore


/-!
# Executing the weighted modular score

The joint-modulus helper uses the verified division-free remainder routine.
The score loop computes a base count, then visits the auxiliary-prime array
once.  All calls reuse the same scratch region and preserve the original
arrays.  Its intermediate scores are proved nonnegative.

The generic loop theorem exposes the modular-counting execution contract.
The concrete wrapper instantiates that contract with the checked fixed
modular-counting program; no counting operation is added to the machine.
-/

namespace ThreeSum.LightWeightedScore

open Light WeightedModuli WeightedScore LightResidues

variable {lim : Limits} {P : Program} {d : ℕ}

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Arguments: positive base modulus, positive auxiliary modulus, scratch. -/
def jointBody (pEmod : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEmod [v 0, v 1, v 2] 3)
    (.ite (Light.Cond.eq (v 3) (k 0)) .skip
      (.set 0 ((Light.Expr.op Light.Op.mul) (v 0) (v 1)))))

def jointTime (maxMod : ℕ) : ℕ := residueBudget maxMod + 40
















































/-- Arguments: A, B, C, their lengths, base modulus, maximum array length,
auxiliary-prime array, number of primes, and scratch.
Locals 11 and 12 hold the base count and remaining score; 13 is the loop
counter, and 14 and 15 hold the joint modulus and its count. -/
def body (pCount pJoint : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCount [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 10] 11)
    (Light.Stmt.seq (.set 12 ((Light.Expr.op Light.Op.mul) (v 9) (v 11)))
      (Light.Stmt.seq
        (.for 13 (v 9)
          (Light.Stmt.seq
            (.call pJoint
              [v 6, M ((Light.Expr.op Light.Op.add) (v 8) (v 13)), v 10] 14)
            (Light.Stmt.seq
              (.call pCount [v 0, v 1, v 2, v 3, v 4, v 5, v 14, v 7, v 10] 15)
              (.set 12 ((Light.Expr.op Light.Op.sub) (v 12) (v 15))))))
        (.set 0 (v 12)))))

def time (countTime s maxMod : ℕ) : ℕ :=
  countTime + s*(countTime+jointTime maxMod+100)+100

def Inv (μ : ℕ → ℤ) (primes : ℕ → ℕ)
    (a b c nA nB nC q N aux s free : ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (jval cval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(a : ℤ),b,c,nA,nB,nC,q,N,aux,s,free,
      ModuloCounts.count q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)),
      remaining primes s q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j))
        (fun j => μ (c+j)) i,i,jval,cval],ν⟩ ∧ Kept μ ν free












































































































/-- Time for the score with the actual modular-counting implementation. -/
def runtimeTime (maxMod nA nB nC s U : ℕ) : ℕ :=
  time (LightModuloCounts.time maxMod nA nB nC U) s maxMod

/-- Both helpers reuse the same scratch region, so their reservations take a
maximum. No scratch allocation is multiplied by the number of primes. -/
def space (free maxMod N U : ℕ) : ℕ :=
  max (LightModuloCounts.space free maxMod N U)
    (free + (Nat.log 2 (maxMod+1)+2))

def word (maxMod N s U : ℕ) : ℕ :=
  LightModuloCounts.word maxMod N U + (s+1)*N^3 + 8*maxMod + 16

/-- Syntax-only closure for a weighted-score procedure and its concrete
modular-counting, joint-modulus, and arithmetic procedures. -/
structure Procs (P : Program) (pMain : ℕ) where
  pCount : ℕ
  pJoint : ℕ
  count : LightModuloCounts.Procs P pCount
  main : P[pMain]? = some (body pCount pJoint)
  joint : P[pJoint]? = some (jointBody count.pEmod)




































































/-- A fixed fourteen-procedure program. All recursive and nonrecursive calls
refer to members of this list; no modular-counting oracle is assumed. -/
def program : Program :=
  [body 2 1, jointBody 6, LightModuloCounts.body 3 4 8 5 13,
    LightCapacity.body, LightResidueHistogram.body 5 7, residuesBody 6,
    emodBody, LightHistogram.histogramBody 12, LightCyclic.body 9 11,
    LightKaratsuba.body 9 10 11 12, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]
























































end ThreeSum.LightWeightedScore

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ArithmeticStageBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds


/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds

open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology

set_option maxHeartbeats 1000000

def maxMod (n : ℕ) : ℕ := radix n * (4*primeWindow n)^2

def bitBudget (k n : ℕ) : ℕ := 2*(k+2)*primeWindow n^2+1

def perTripleBudget (k n : ℕ) : ℕ :=
  10000*(roundedPower (maxMod n) + bandSize n * bitBudget k n + 1)













































noncomputable section


































































































































end
end ThreeSum.ArithmeticStageBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_HierarchyScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch


/-!
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def initialCap (r : ℕ) : ℕ := r ⌈/⌉ 25







































noncomputable section

def hierarchyEnvelope (C B : ℝ) (n : ℕ) : ℝ :=
  (mu n + 1 : ℝ) * Real.exp ((mu n : ℝ) * Real.log 2 * C + B)


































































































































































































def unroundedBandCount (n : ℕ) : ℝ := (n : ℝ) / BandScales.bandSize n










































































end
end ThreeSum.HierarchyScales

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorScanHost


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts


/-! # Load the actual index width and run the entire coloring family -/

namespace ThreeSum.LightColorScanHost

open Light ColorParameters LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 4 ((Light.Expr.op Light.Op.add) (M (v 2)) (k 1)))
    (Light.Stmt.seq
      (.set 5
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (k 81) (v 4))
          (v 4)))
      (.call pScan [v 0, v 1, v 2, v 3, v 4, v 5] 0)))

def time (colorTime n : ℕ) : ℕ :=
  LightColorScan.time colorTime (width n) (count (width n))+100

def word (n : ℕ) : ℕ := n+count (width n)+width n+100






structure Procs (P : Program) (pMain : ℕ) where
  pScan : ℕ
  scan : LightColorScan.Procs P pScan
  main : P[pMain]?=some (body pScan)

variable {lim : Limits} {P : Program}







































end ThreeSum.LightColorScanHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_CostLedger


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch


/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000

def bandCount (n : ℕ) : ℕ := n ⌈/⌉ BandScales.bandSize n

def microOutputs (n : ℕ) : ℕ := (256 * muZero n).choose (muZero n)

def microPartitions (n : ℕ) : ℕ := (muZero n).choose (muZero n / 2)

def prefixChoices (n j : ℕ) : ℕ := (microOutputs n * microPartitions n) ^ j

def suffixBoxes (n j : ℕ) : ℕ :=
  (256 * residualSize n j).choose (residualSize n j - actualSwitch n j)

def prefixBoxes (n j : ℕ) : ℕ := prefixChoices n j * suffixBoxes n j

def queryTerms (n j : ℕ) : ℕ := (residualSize n j).choose (actualSwitch n j)

def allPrefixBoxes (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (terminalDepth n + 1), prefixBoxes n j

def allQueryTerms (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (terminalDepth n + 1), queryTerms n j




























noncomputable section

















































































































































end
end ThreeSum.CostLedger

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_OutputDecodeRecords


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists


/-! # A physical global-record index decodes to the original occurrence and mask rows -/

namespace ThreeSum.OutputDecodeRecords

open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def layerCount (h : ℕ) : ℕ := outputCount (512*h) h
def localCount (h : ℕ) : ℕ := scheduleSize h*layerCount h

theorem layerCount_pos (h : ℕ) : 0 < layerCount h := Nat.choose_pos (by omega)
theorem schedule_pos (h : ℕ) : 0 < scheduleSize h := by
  unfold scheduleSize scheduleLength
  positivity



def blockDefault (h : ℕ) : OutputBlock h :=
  (⟨0,schedule_pos h⟩,layerRecord h ⟨0,layerCount_pos h⟩)

def outputDefault (h J : ℕ) : GlobalOutput h J := fun _ => blockDefault h
























def localIndex (h J k j : ℕ) : ℕ := (indices (localCount h) J k).getD j 0
def occurrenceIndex (h J k j : ℕ) : ℕ := localIndex h J k j/layerCount h
def maskIndex (h J k j : ℕ) : ℕ := localIndex h J k j%layerCount h















theorem globalRecords_length' (h J : ℕ) : (globalRecords h J).length=localCount h^J := by
  rw [globalRecords_length]
  simp only [localCount,layerCount,mul_pow]













































theorem original_global_key {h J k : ℕ} (hk : k < localCount h^J) :
    (globalKeys h J).getD k 0 =
      globalKey ((globalRecords h J).getD k (outputDefault h J)) := by
  rw [globalKeys_eq_map]
  exact List.getD_map_of_lt _ (by rwa [globalRecords_length']) (outputDefault h J) 0

end ThreeSum.OutputDecodeRecords

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockEncoding


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences


/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

abbrev Occurrences (h J : ℕ) := Fin J → Occurrence h

def outputOccurrences {h J : ℕ} (q : GlobalOutput h J) : Occurrences h J := fun i => (q i).1

def leftSubset {h J : ℕ} (t : ChoiceTuple h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (edge (t i)).val.1

def rightSubset {h J : ℕ} (t : ChoiceTuple h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (edge (t i)).val.2

def outputSubset {h J : ℕ} (q : GlobalOutput h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (q i).2.val
























































def LeftAllowed {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : Prop :=
  ∀ i, (row S i).card = h ∧
    HashFamily.bucketSize (leftVertices (512 * h) h) (mapAt h (o i))
      (HashFamily.hashValue (mapAt h (o i)) (leftWord (row S i))) ≤ localBucketCap h

def RightAllowed {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : Prop :=
  ∀ i, (row S i).card = h ∧
    HashFamily.bucketSize (rightVertices (512 * h) h) (mapAt h (o i))
      (HashFamily.hashValue (mapAt h (o i)) (rightWord (row S i))) ≤ localBucketCap h

instance {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) :
    Decidable (LeftAllowed o S) := by unfold LeftAllowed; infer_instance

instance {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) :
    Decidable (RightAllowed o S) := by unfold RightAllowed; infer_instance

def endpointLeft {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : ℤ :=
  Radix.positionalHash (localPrime h) id
    (List.ofFn fun i => rawHash (mapAt h (o i)) (leftWord (row S i)))

def endpointRight {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : ℤ :=
  Radix.positionalHash (localPrime h) id
    (List.ofFn fun i => rawHash (mapAt h (o i)) (rightWord (row S i)))
















































/-- Actual retained pairs can be reconstructed from independently trimmed
opposite block subsets. No shared-edge trimming premise is required. -/
def fromSubsets {h J : ℕ} (o : Occurrences h J) (S V : Finset (Coord J (512 * h)))
    (hS : LeftAllowed o S) (hV : RightAllowed o V) (hd : Disjoint S V) : ChoiceTuple h J :=
  fun i => ⟨(o i, ⟨(row S i, row V i), LayerCounts.mem_edgeSet.mpr
    ⟨(hS i).1, (hV i).1, Finset.disjoint_left.mpr (fun _ hx hy =>
      Finset.disjoint_left.mp hd (mem_row.mp hx) (mem_row.mp hy))⟩⟩),
    ⟨(hS i).2, (hV i).2⟩⟩























section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftWeights {h J : ℕ} (o : Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ)
    (S : Finset (Coord J (512 * h))) : ℕ :=
  if LeftAllowed o S then
    ∑ j ∈ B, if globalModulus h J ∣ b j % P - endpointLeft o S then 1 else 0
  else 0

def rightWeights {h J : ℕ} (o : Occurrences h J) (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (V : Finset (Coord J (512 * h))) : ℕ :=
  if RightAllowed o V then
    ∑ j ∈ C, if globalModulus h J ∣ c j % P + d - endpointRight o V then 1 else 0
  else 0





























end Histograms

end ThreeSum.BlockEncoding

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_RawReporting


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences


/-!
# Positive-prefix reporting for concrete guarded incidences

The band triple is fixed by the input index sets and offset passed to this
module. Its wanted queries retain the original A index, signed lift and
full output tuple, including every chosen-map occurrence. Children are
the balanced subsets of the next output block, in deterministic colex order.
-/

namespace ThreeSum.RawReporting

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences

 def colexEmbedding (L : ℕ) : Finset (Fin L) ↪ Colex (Finset (Fin L)) :=
  ⟨toColex, fun _ _ h => h⟩

/-- A deterministic ordering of exactly the balanced child subsets. -/
def childList {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) : List (Finset (Fin L)) :=
  (((Q.powersetCard h).map (colexEmbedding L)).sort (· ≤ ·)).map ofColex























def children {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Fin (512 * h))) :=
  if hk : k < J then childList (q ⟨k, hk⟩).2.val h else []














def partitionWord {h J : ℕ} (t : ChoiceTuple h J) : List (Finset (Fin (512 * h))) :=
  List.ofFn fun i => (edge (t i)).val.1




instance outputBlockDecidableEq (h : ℕ) : DecidableEq (OutputBlock h) := inferInstance
instance globalOutputDecidableEq (h J : ℕ) : DecidableEq (GlobalOutput h J) :=
  Fintype.decidablePiFintype

abbrev Wanted (h J : ℕ) (α : Type*) := α × (Fin 3 × GlobalOutput h J)

instance wantedDecidableEq (h J : ℕ) (α : Type*) [DecidableEq α] :
    DecidableEq (Wanted h J α) := inferInstance

def wantedOf {h J : ℕ} {α β γ : Type*} (r : RawItem h J α β γ) : Wanted h J α :=
  (r.1.1, (r.2.2, tupleOutput r.2.1))

def word {h J : ℕ} {α β γ : Type*} (r : RawItem h J α β γ) := partitionWord r.2.1

section FixedBand

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def domain {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :=
  I.filter fun r => wantedOf r = w

def prefixQuery {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  Reporting.mass (domain I w) word (fun _ => 1) k pre















































































end FixedBand

end ThreeSum.RawReporting

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWeightDecode


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Actual decoding of the unchanged ordered hash-weight enumeration

The five-procedure program constructs its own power table, then decodes
the even and odd coordinates into two contiguous coefficient rows. The
digits are exactly those of `WeightEnumeration.decodedWeight`, which is
already proved equal to the original `allWeights` enumeration in order.
-/

namespace ThreeSum.LightWeightDecode

open Light

def body (pPowers pRow : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.mul) (k 2) (v 0)))
    (Light.Stmt.seq
      (.call pPowers [v 4, (Light.Expr.op Light.Op.add) (v 5) (k 1), v 1] 6)
      (Light.Stmt.seq (.call pRow [v 5, v 1, v 2, v 4, k 0, k 2, v 3, v 0] 6)
        (.call pRow
          [v 5, v 1, v 2, v 4, k 1, k 2, (Light.Expr.op Light.Op.add) (v 3) (v 0),
            v 0]
          6))))

def time (L k : ℕ) : ℕ := powTableTime (2*L+1)+2*LightWeightRow.time L k+120
def word (L p k : ℕ) : ℕ := LightWeightRow.word (2*L) p k 1 2

def Rows (μ : ℕ → ℤ) (dst L p k : ℕ) : Prop :=
  ∀ i < L,
    μ (dst+i) = (WeightEnumeration.digit p (2*L) k (2*i) : ℤ) ∧
    μ (dst+L+i) = (WeightEnumeration.digit p (2*L) k (2*i+1) : ℤ)

structure Procs (P : Program) (pMain : ℕ) where
  pPowers : ℕ
  pRow : ℕ
  pDigit : ℕ
  pDivide : ℕ
  powers : P[pPowers]? = some powTableBody
  row : P[pRow]? = some (LightWeightRow.body pDigit)
  digit : P[pDigit]? = some (LightRadixDigit.body pDivide)
  divide : P[pDivide]? = some LightSmallDivide.body
  main : P[pMain]? = some (body pPowers pRow)

variable {lim : Limits} {P : Program} {d : ℕ}































































































end ThreeSum.LightWeightDecode

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockChildren


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks

variable {lim : Limits} {P : Program}

/-- Width, child cardinality, next-row mask, left/right prefixes, remaining
query mask, child-mask destination, left/right destinations, scratch. -/
def body (pEnum pAffine : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnum [v 0, v 2, v 1, v 6, v 9] 10)
    (Light.Stmt.seq (.set 11 ((Light.Expr.op Light.Op.add) (v 4) (v 2)))
      (Light.Stmt.seq (.call pAffine [v 6, v 7, v 10, v 3, k 1] 12)
        (Light.Stmt.seq
          (.call pAffine
            [v 6, v 8, v 10, v 11, (Light.Expr.op Light.Op.sub) (k 0) (k 1)] 12)
          (.set 0 ((Light.Expr.op Light.Op.sub) (v 5) (v 2)))))))

def time (W c h : ℕ) : ℕ :=
  LightQueryEnumeration.time W c h+2*LightReportingAffine.time (c.choose h)+100

def leftMasks {W : ℕ} (A Q : Finset (Fin W)) (h : ℕ) : List ℕ :=
  (missingSets Q h).map fun S => subsetMask (A ∪ S)

def rightMasks {W : ℕ} (B Q : Finset (Fin W)) (h : ℕ) : List ℕ :=
  (missingSets Q h).map fun S => subsetMask (B ∪ (Q \ S))

structure Procs (P : Program) (pEnum pAffine : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pRec : ℕ
  enumBody : P[pEnum]? = some (LightQueryEnumeration.body pWeights pRec)
  weightsBody : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  powersBody : P[pPowers]? = some powTableBody
  eraseBody : P[pErase]? = some (LightMaskErase.body pErase)
  recBody : P[pRec]? = some (LightSubsetEnumeration.body pRec)
  affineBody : P[pAffine]? = some LightReportingAffine.body




































































































def program : Program :=
  [body 1 6,LightQueryEnumeration.body 2 5,LightQueryWeights.body 3 4,powTableBody,
    LightMaskErase.body 4,LightSubsetEnumeration.body 5,LightReportingAffine.body]

def procs : Procs program 1 6 := ⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩





























end ThreeSum.LightBlockChildren

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingPairRows


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual direct construction of all local balanced row pairs

An own-power layer enumerator constructs the left subsets. For each left
subset, an actual output-sensitive query enumerator constructs its disjoint
right subsets, and an affine pass writes the matching repeated left mask.
-/

namespace ThreeSum.LightReportingPairRows

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration

set_option maxHeartbeats 1800000

variable {lim : Limits}

def roundBody (pQuery pAffine : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 10 (M ((Light.Expr.op Light.Op.add) (v 2) (v 9))))
    (Light.Stmt.seq (.set 11 ((Light.Expr.op Light.Op.sub) (v 7) (v 10)))
      (Light.Stmt.seq
        (.call pQuery
          [v 0, v 11, v 1, (Light.Expr.op Light.Op.add) (v 4) (v 8), v 5] 12)
        (Light.Stmt.seq
          (.call pAffine
            [(Light.Expr.op Light.Op.add) (v 4) (v 8),
              (Light.Expr.op Light.Op.add) (v 3) (v 8), v 12, v 10, k 0]
            13)
          (.set 8 ((Light.Expr.op Light.Op.add) (v 8) (v 12)))))))

def body (pLayer pQuery pAffine : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pLayer [v 0, v 1, v 2, v 5] 6)
    (Light.Stmt.seq
      (.set 7
        ((Light.Expr.op Light.Op.sub)
          (M ((Light.Expr.op Light.Op.add) (v 5) (v 0))) (k 1)))
      (Light.Stmt.seq (.set 8 (k 0))
        (Light.Stmt.seq (.for 9 (v 6) (roundBody pQuery pAffine))
          (.set 0 (v 8))))))

def program : Program := LightQueryEnumeration.program ++
  [LightSubsetEnumerationSetup.body 2 4,LightReportingAffine.body,body 5 0 6]

def roundTime (L h : ℕ) : ℕ :=
  LightQueryEnumeration.time L (L-h) h+LightReportingAffine.time ((L-h).choose h)+220

def time (L h : ℕ) : ℕ :=
  LightSubsetEnumerationSetup.time L h+L.choose h*(roundTime L h+20)+130

def Inv (μ : ℕ → ℤ) (L h srcS dstL dstR work j : ℕ) (σ : State) : Prop :=
  ∃ (a b nr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,h,srcS,dstL,dstR,work,L.choose h,subsetMask (Finset.univ : Finset (Fin L)),
      j*(L-h).choose h,j,a,b,nr,r],μ'⟩ ∧
    SegN μ' srcS (enumerateLayer L h) ∧
    (∀ i < j, ∀ l < (L-h).choose h,
      μ' (dstL+i*(L-h).choose h+l) = (subsetMask (leftAt L h i) : ℤ) ∧
      μ' (dstR+i*(L-h).choose h+l) = (subsetMask (rightAt L h i l) : ℤ)) ∧
    Kept μ μ' srcS














































































































































end ThreeSum.LightReportingPairRows

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightQueryBox


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Executing a canonical sparse-query box

Given valid masks `U ⊆ Q`, the program subtracts their masks and
cardinalities, computes the least missing coordinate itself, computes
the compact stage address, and reads the signed box sum. The empty
missing set uses the final prefix stage. No address or minimum is
provided as advice.
-/

namespace ThreeSum.LightQueryBox

open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: width, cutoff, Q cardinality and mask, U cardinality and
mask, box-table base, polynomial scratch base. -/
def body (pMinimum pLookup : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.sub) (v 2) (v 4)))
    (Light.Stmt.seq (.set 9 ((Light.Expr.op Light.Op.sub) (v 3) (v 5)))
      (Light.Stmt.seq
        (.ite (Light.Cond.eq (v 5) (k 0)) (.set 10 (v 0))
          (.call pMinimum [v 0, v 5, v 7] 10))
        (.call pLookup [v 0, v 1, v 8, v 9, v 10, v 6, v 7] 0))))

def time (L : ℕ) : ℕ := LightMaskMinimum.time L+LightStageLookup.time L+120































































































































end ThreeSum.LightQueryBox

end


