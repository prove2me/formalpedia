-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle05
-- name    : ThreeSum1962Source_Bundle05
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:08:08.34475+00:00
-- url     : https://prove2.me/theorems/b5dfb795-319a-4dfe-bd0d-b601f76b099a
-- title:
--   Local hash schedules, positional keys, and arithmetic program bodies
-- statement:
--   This bundle defines the finite local hash-weight space and its greedy schedule. For half-size \(h\) and positive modulus \(p\), the prescribed schedule length is
--   $$
--   L(h,p)=320(2h+1)\bigl(\lfloor\log_2(p^2)\rfloor+1\bigr).
--   $$
--   It also introduces physical band-owner records, consecutive band partitions, prime-window candidates, indexed subset masks and weighted query-coordinate enumeration. The Light bodies cover positional coefficient construction, mask hashes, independent pair flags, signed histograms, lifted input keys, source residues, matching-key joins and output-index division. Karatsuba and merge-sort bodies, their procedure interfaces, result predicates and resource expressions provide arithmetic and sorting components for later composition.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandCandidateRows.lean#L19-L67
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandPartition.lean#L13-L108
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandTable.lean#L19-L114
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockCoefficients.lean#L24-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDownsetEnumerationSetup.lean#L17-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightKaratsuba.lean#L19-L137
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMaskBits.lean#L10-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMaskHashes.lean#L18-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOriginalTripleRow.lean#L13-L128
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOutputDecodeDivide.lean#L18-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightPairFlags.lean#L21-L53
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightPrimality.lean#L19-L161
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightRadixRows.lean#L20-L32
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightRawAKeys.lean#L21-L114
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingCatalogLookup.lean#L23-L48
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightResidueHistogram.lean#L22-L119
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceGather.lean#L19-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceResidues.lean#L18-L147
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceRowFlag.lean#L21-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetEnumerationSetup.lean#L17-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSwitchDepth.lean#L10-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWantedJoin.lean#L20-L138
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightedEnumeration.lean#L20-L64
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalHashMoments.lean#L29-L289
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalMaskGraph.lean#L19-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/MaskUnion.lean#L10-L12
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/PrimeDensity.lean#L22-L122
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/QueryCoordinates.lean#L19-L216
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostQueryBounds.lean#L10-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L34-L103

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightResidueHistogram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues


/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram

open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba

variable {lim : Limits} {P : Program} {d : ℕ}

def signedHistogram (p : ℕ) (c : ℤ) (values : ℕ → ℤ) (n : ℕ) (z : ZMod p) : ℕ :=
  Histograms.histogram (Finset.range n) (fun i => ((c * values i : ℤ) : ZMod p))
    (fun _ => 1) z
























































































/-- Arguments: source, histogram, item count, modulus, histogram capacity,
first scratch cell, remainder scratch cell, sign. -/
def body (pResidues pHistogram : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pResidues [v 0, v 5, v 2, v 3, v 6, v 7] 8)
    (.call pHistogram [v 5, v 1, v 2, v 4] 8))

def time (n cap U : ℕ) : ℕ := residuesTime n U + histogramTime n cap + 30






























































end ThreeSum.LightResidueHistogram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceGather


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Residue-indexed source lookup and independent trimming

Each endpoint is reduced by the global modulus and its original-input
histogram count is gathered. The already constructed independent endpoint
flag selects that count or zero. No search through the original inputs is
performed for individual subset masks.
-/

namespace ThreeSum.LightSourceGather

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def value (m : ℕ) (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ) (i : ℕ) : ℕ :=
  if flag i = 1 then hist (LightResidues.residue m 1 (endpoint i)) else 0








/-- Arguments: raw endpoints, independent flags, source histogram, output,
number of masks, global modulus, and reusable remainder scratch. -/
def body (pEmod : ℕ) : Stmt :=
  .for 7 (v 4) (
    (Light.Stmt.seq
      (.call pEmod [M ((Light.Expr.op Light.Op.add) (v 0) (v 7)), v 5, v 6] 8)
      (.ite (Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v 1) (v 7))) (k 1))
        (.store ((Light.Expr.op Light.Op.add) (v 3) (v 7))
          (M ((Light.Expr.op Light.Op.add) (v 2) (v 8))))
        (.store ((Light.Expr.op Light.Op.add) (v 3) (v 7)) (k 0)))))

def time (n U : ℕ) : ℕ := n*(LightResidues.residueBudget U+80)+6

def Inv (μ : ℕ → ℤ) (raw flags table dst n m work : ℕ)
    (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ), σ = ⟨frame [raw,flags,table,dst,n,m,work,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (value m endpoint flag hist j : ℤ)) ∧
    KeptBut μ ν work dst n

variable {lim : Limits} {P : Program} {d : ℕ}

















































































































end ThreeSum.LightSourceGather

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockCoefficients


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}

def Powers (μ : ℕ → ℤ) (work J p : ℕ) : Prop :=
  ∀ i ≤ J, μ (work+i) = ((p^i : ℕ) : ℤ)

def Rows (μ : ℕ → ℤ) (dst0 dst1 L p : ℕ) (sel : ℕ → ℕ)
    (w0 w1 : ℕ → ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ a < j, ∀ i < L,
    μ (dst0+a*L+i) = ((p^a*w0 (sel a) i : ℕ) : ℤ) ∧
    μ (dst1+a*L+i) = ((p^a*w1 (sel a) i : ℕ) : ℤ)

def roundBody (pScale : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 9
      ((Light.Expr.op Light.Op.add) (v 4)
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (k 2) (v 1))
          (M ((Light.Expr.op Light.Op.add) (v 3) (v 8))))))
    (Light.Stmt.seq
      (.set 10
        ((Light.Expr.op Light.Op.add) (v 5)
          ((Light.Expr.op Light.Op.mul) (v 8) (v 1))))
      (Light.Stmt.seq
        (.set 11
          ((Light.Expr.op Light.Op.add) (v 6)
            ((Light.Expr.op Light.Op.mul) (v 8) (v 1))))
        (Light.Stmt.seq
          (.call pScale
            [v 9, v 10, v 1, M ((Light.Expr.op Light.Op.add) (v 7) (v 8))] 12)
          (.call pScale
            [(Light.Expr.op Light.Op.add) (v 9) (v 1), v 11, v 1,
              M ((Light.Expr.op Light.Op.add) (v 7) (v 8))]
            13)))))

/-- Arguments: number of blocks, block width, radix, occurrence array,
map-coefficient array, output-zero row, output-one row, scratch. -/
def body (pPowers pScale : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 7, (Light.Expr.op Light.Op.add) (v 0) (k 1), v 2] 8)
    (.for 8 (v 0) (roundBody pScale)))

def roundTime (L : ℕ) : ℕ := 2*LightScaleArray.time L+100
def time (J L : ℕ) : ℕ := powTableTime (J+1)+J*(roundTime L+20)+100
def word (J p U : ℕ) : ℕ := p^(J+1)*(U+1)

def Inv (μ : ℕ → ℤ) (J L p occ maps dst0 dst1 work : ℕ)
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (s a b r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,p,occ,maps,dst0,dst1,work,j,s,a,b,r0,r1],ν⟩ ∧
    Rows ν dst0 dst1 L p sel w0 w1 j ∧ Kept μ ν dst0 ∧ Powers ν work J p




















































































































































































end ThreeSum.LightBlockCoefficients

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOriginalTripleRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BruteTripleIndex
end ThreeSum.BruteTripleIndex


/-! # Execute one exact original-position triple test -/

namespace ThreeSum.LightOriginalTripleRow

open Light BruteTripleIndex

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pDivide : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDivide [v 2, v 1] 3)
    (Light.Stmt.seq (.call pDivide [v 3, v 1] 4)
      (Light.Stmt.seq
        (.set 5
          ((Light.Expr.op Light.Op.sub) (v 3)
            ((Light.Expr.op Light.Op.mul) (v 4) (v 1))))
        (Light.Stmt.seq
          (.set 6
            ((Light.Expr.op Light.Op.sub) (v 2)
              ((Light.Expr.op Light.Op.mul) (v 3) (v 1))))
          (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 0) (v 4))))
            (Light.Stmt.seq
              (.set 8 (M ((Light.Expr.op Light.Op.add) (v 0) (v 5))))
              (Light.Stmt.seq
                (.set 9 (M ((Light.Expr.op Light.Op.add) (v 0) (v 6))))
                (Light.Stmt.seq
                  (.set 10
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add) (v 7) (v 8)) (v 9)))
                  (.ite (Light.Cond.eq (v 4) (v 5)) (.set 0 (k 0))
                    (.ite (Light.Cond.eq (v 4) (v 6)) (.set 0 (k 0))
                      (.ite (Light.Cond.eq (v 5) (v 6)) (.set 0 (k 0))
                        (.ite (Light.Cond.eq (v 10) (k 0)) (.set 0 (k 1))
                          (.set 0 (k 0))))))))))))))

def time (n : ℕ) : ℕ := 20*(n*n+n)+500
def word (n U : ℕ) : ℕ := n^3+3*U+n+20

variable {lim : Limits} {P : Program}

































































































def program : Program := [body 1,LightSmallDivide.body]

end ThreeSum.LightOriginalTripleRow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSwitchDepth


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Actual computation of the terminal reporting depth -/

namespace ThreeSum.LightSwitchDepth

open Light

def depth (J : ℕ) : ℕ := 13*J/20

def body (pDiv : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDiv [(Light.Expr.op Light.Op.mul) (k 13) (v 0), k 20] 1)
    (.set 0 (v 1)))

def time (J : ℕ) : ℕ := LightSmallDivide.time (13*J) 20+50
def word (J : ℕ) : ℕ := 13*J+22

variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}














def program : Program := [body 1,LightSmallDivide.body]













end ThreeSum.LightSwitchDepth

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceRowFlag


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def flag (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) : ℕ :=
  LightSourceFlagTest.flag (LightSourceRowScan.count bits L) h
    (hist (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ))) cap




/-- Arguments: Boolean row, coefficient-zero, coefficient-one, width,
required cardinality, left and right bucket tables, local modulus, cap,
two-cell flag output, and reusable scratch. -/
def body (pRow pEmod pFlag : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pRow [v 0, v 1, v 2, v 3, v 10] 11)
    (Light.Stmt.seq
      (.call pEmod
        [M ((Light.Expr.op Light.Op.add) (v 10) (k 1)), v 7,
          (Light.Expr.op Light.Op.add) (v 10) (k 3)]
        12)
      (Light.Stmt.seq
        (.call pEmod
          [M ((Light.Expr.op Light.Op.add) (v 10) (k 2)), v 7,
            (Light.Expr.op Light.Op.add) (v 10) (k 3)]
          13)
        (Light.Stmt.seq
          (.call pFlag
            [M (v 10), v 4, M ((Light.Expr.op Light.Op.add) (v 5) (v 12)), v 8]
            14)
          (Light.Stmt.seq
            (.call pFlag
              [M (v 10), v 4, M ((Light.Expr.op Light.Op.add) (v 6) (v 13)), v 8]
              15)
            (Light.Stmt.seq (.store (v 9) (v 14))
              (.store ((Light.Expr.op Light.Op.add) (v 9) (k 1)) (v 15))))))))

def time (L U : ℕ) : ℕ := LightSourceRowScan.time L+
  2*LightResidues.residueBudget (L*U)+2*LightSourceFlagTest.time+160

def word (L p U V cap : ℕ) : ℕ := LightSourceRowScan.word L U+
  4*(L*U)+4*p+16+2*L+V+cap+2

def space (work L U : ℕ) : ℕ := work+3+(Nat.log 2 (L*U+1)+2)

variable {lim : Limits} {P : Program} {d : ℕ}



























































































































end ThreeSum.LightSourceRowFlag

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightMaskBits


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase


/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase

def bit (L m j : ℕ) : ℕ := if eraseMask L j m = m then 0 else 1













def loopBody (pErase : ℕ) : Stmt :=
  .for 4 (v 0) (
    (Light.Stmt.seq (.call pErase [v 0, v 4, v 1, v 0, v 3] 5)
      (.ite (Light.Cond.eq (v 5) (v 1))
        (.store ((Light.Expr.op Light.Op.add) (v 2) (v 4)) (k 0))
        (.store ((Light.Expr.op Light.Op.add) (v 2) (v 4)) (k 1)))))

def body (pPowers pErase : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 3, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 5)
    (loopBody pErase))

def time (L : ℕ) : ℕ := powTableTime (L+1)+L*(LightMaskErase.time L+80)+50

def Inv (μ : ℕ → ℤ) (L m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L,m,dst,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (bit L m j : ℤ)) ∧ Powers μ' work L ∧
    KeptBut μ μ' work dst L

variable {lim : Limits} {P : Program} {d : ℕ}


























































































end ThreeSum.LightMaskBits

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightMaskHashes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress


/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes

open Light LightSubsetAddress

set_option maxHeartbeats 1000000

def loopBody (pHash : ℕ) : Stmt :=
  .for 7 (v 3) (
    (Light.Stmt.seq
      (.call pHash
        [v 0, M ((Light.Expr.op Light.Op.add) (v 1) (v 7)), v 0, v 6, v 4, v 5] 8)
      (.store ((Light.Expr.op Light.Op.add) (v 2) (v 7)) (v 8))))

def body (pPowers pHash : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 6, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 8)
    (loopBody pHash))

def time (L n : ℕ) : ℕ := powTableTime (L+1)+n*(LightOneHot.time L+70)+50

def Inv (μ : ℕ → ℤ) (mask w0 w1 : ℕ → ℕ)
    (L masks dst n src0 src1 work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,masks,dst,n,src0,src1,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (OneHotMask.eval w0 w1 L (mask j) : ℤ)) ∧
    Powers μ' work L ∧ KeptBut μ μ' work dst n

variable {lim : Limits} {P : Program} {d : ℕ}













































































































end ThreeSum.LightMaskHashes

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightPairFlags


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Constructing every candidate pair's key and trimming flag

All pairs of enumerated local vertices are visited. A zero coordinate-row
inner product tests disjointness; the two actual bucket counts determine
whether the pair survives. The local exhaustive scan is intentionally
unoptimized and its entire arithmetic and lookup cost is charged.
-/

namespace ThreeSum.LightPairFlags

open Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000

def pairKey (n p : ℕ) (left right : ℕ → ℕ) (i : ℕ) : ℕ :=
  left (i/n)*p+right (i%n)

def pairFlag (L n cap : ℕ) (bits : ℕ → ℕ → ℕ)
    (left right leftCount rightCount : ℕ → ℕ) (i : ℕ) : ℕ :=
  LightTrimTest.flag (LightBooleanDot.dot (bits (i/n)) (bits (i%n)) L)
    (leftCount (left (i/n))) (rightCount (right (i%n))) cap

def roundBody (pDivide pDot pTrim : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDivide [v 11, v 6] 12)
    (Light.Stmt.seq
      (.set 13
        ((Light.Expr.op Light.Op.sub) (v 11)
          ((Light.Expr.op Light.Op.mul) (v 12) (v 6))))
      (Light.Stmt.seq
        (.call pDot
          [(Light.Expr.op Light.Op.add) (v 0)
              ((Light.Expr.op Light.Op.mul) (v 12) (v 7)),
            (Light.Expr.op Light.Op.add) (v 0)
              ((Light.Expr.op Light.Op.mul) (v 13) (v 7)),
            v 7]
          14)
        (Light.Stmt.seq (.set 15 (M ((Light.Expr.op Light.Op.add) (v 1) (v 12))))
          (Light.Stmt.seq
            (.set 16 (M ((Light.Expr.op Light.Op.add) (v 2) (v 13))))
            (Light.Stmt.seq
              (.call pTrim
                [v 14, M ((Light.Expr.op Light.Op.add) (v 3) (v 15)),
                  M ((Light.Expr.op Light.Op.add) (v 4) (v 16)), v 9]
                17)
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 5) (v 11))
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.mul) (v 15) (v 8)) (v 16)))
                (.store ((Light.Expr.op Light.Op.add) (v 10) (v 11)) (v 17)))))))))

def body (pDivide pDot pTrim : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 10
      ((Light.Expr.op Light.Op.add) (v 5)
        ((Light.Expr.op Light.Op.mul) (v 6) (v 6))))
    (.for 11 ((Light.Expr.op Light.Op.mul) (v 6) (v 6))
      (roundBody pDivide pDot pTrim)))

def roundTime (L n : ℕ) : ℕ := 20*n+LightBooleanDot.time L+LightTrimTest.time+350
def time (L n : ℕ) : ℕ := n*n*(roundTime L n+12)+30
def word (L n p cap : ℕ) : ℕ := 100*(n*n+p*p+cap+L+n+p+1)

def Inv (μ : ℕ → ℤ) (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap i : ℕ) (σ : State) : Prop :=
  ∃ (a b c e f g : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap,dst+n*n,i,a,b,c,e,f,g],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (pairKey n p left right j : ℤ)) ∧
    (∀ j < i, μ' (dst+n*n+j) = (pairFlag L n cap bits left right leftCount rightCount j : ℤ)) ∧
    SameOutside μ μ' dst (2*(n*n))

variable {lim : Limits} {P : Program} {d : ℕ}






























































































































































































































end ThreeSum.LightPairFlags

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWantedJoin


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.WantedPairs
end ThreeSum.WantedPairs


/-!
# A literal output-sensitive join of original-position residue arrays

The host reads each left code and visits only its matching retained right
fiber. Recursion gives a sum of actual row costs; it never charges or scans
the full left/right Cartesian product. The output contains every matching
original-position pair exactly once.
-/

namespace ThreeSum.LightWantedJoin

open Light SourceBuckets WantedPairs

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- Left codes, right offsets, right indices, left/right lengths, modulus,
and first output address. -/
def body (pSelf pRow : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 3)))
    ((Light.Stmt.seq
       (.call pSelf
         [v 0, v 1, v 2, (Light.Expr.op Light.Op.sub) (v 3) (k 1), v 4, v 5, v 6] 7)
       (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.sub) (v 3) (k 1)))
         (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 0) (v 8))))
           (Light.Stmt.seq (.set 10 (M ((Light.Expr.op Light.Op.add) (v 1) (v 9))))
             (Light.Stmt.seq
               (.set 11
                 ((Light.Expr.op Light.Op.sub)
                   (M
                     ((Light.Expr.op Light.Op.add)
                       ((Light.Expr.op Light.Op.add) (v 1) (v 9)) (k 1)))
                   (v 10)))
               (Light.Stmt.seq (.call pRow [v 8, v 2, v 10, v 11, v 6, v 7] 12)
                 (.set 0 ((Light.Expr.op Light.Op.add) (v 7) (v 11))))))))))
    (.set 0 (k 0))

def time (left right : ℕ → ℕ) (NR : ℕ) : ℕ → ℕ
  | 0 => 50
  | n+1 => time left right NR n+LightWantedRow.time (LightHistogram.count right (left n) NR)+250







variable {lim : Limits} {P : Program}






























































































def program : Program := [body 0 1,LightWantedRow.body]













end ThreeSum.LightWantedJoin

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOutputDecodeDivide


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace Light.Emod
end Light.Emod


/-!
# Binary quotient for physical output indices

The existing checked doubling table is reused. During descending
subtraction this routine also accumulates the quotient bits, so its time
is logarithmic in the numerator rather than linear in the quotient.
-/

namespace ThreeSum.LightOutputDecodeDivide

open Light Light.Emod

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

abbrev Quotient : ℕ := 6

def reduceRound : Stmt :=
  (Light.Stmt.seq (.set Count ((Light.Expr.op Light.Op.sub) (v Count) (k 1)))
    (Light.Stmt.seq
      (.set Quotient ((Light.Expr.op Light.Op.mul) (k 2) (v Quotient)))
      (.ite
        (Light.Cond.le (M ((Light.Expr.op Light.Op.add) (v Free) (v Count)))
          (v Rest))
        (Light.Stmt.seq
          (.set Rest
            ((Light.Expr.op Light.Op.sub) (v Rest)
              (M ((Light.Expr.op Light.Op.add) (v Free) (v Count)))))
          (.set Quotient ((Light.Expr.op Light.Op.add) (v Quotient) (k 1))))
        .skip)))

def reduce : Stmt := .while ((Light.Cond.lt (k 0) (v Count))) reduceRound

def body : Stmt :=
  (Light.Stmt.seq (.set Rest (v Arg))
    (Light.Stmt.seq (.set Count (k 0))
      (Light.Stmt.seq (.set Mult (v Modulus))
        (Light.Stmt.seq emodTable
          (Light.Stmt.seq (.set Quotient (k 0))
            (Light.Stmt.seq reduce (.set Arg (v Quotient))))))))

def time (a Mo : ℕ) : ℕ := 80*emodRounds a Mo+100
def budget (V : ℕ) : ℕ := 100*(Nat.log 2 (V+1)+2)

variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}





























































































end ThreeSum.LightOutputDecodeDivide

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightPrimality


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues


/-!
# A costed elementary primality test

For `2 ≤ n`, this fixed program tests the integers from 2 through `n-1`
using the verified division-free remainder procedure. The deliberately
elementary running time is suitable for a subpolynomial prime window.
-/

namespace ThreeSum.LightPrimality

open Light LightResidues

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def flag (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => if i+2 ∣ n then 0 else flag n i











































def answer (n : ℕ) : ℕ := if Nat.Prime n then 1 else 0









/-- Arguments: the integer to test and a scratch pointer. -/
def body (pEmod : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 2 (k 1))
    (Light.Stmt.seq
      (.for 3 ((Light.Expr.op Light.Op.sub) (v 0) (k 2))
        (Light.Stmt.seq
          (.call pEmod [v 0, (Light.Expr.op Light.Op.add) (v 3) (k 2), v 1] 4)
          (.ite (Light.Cond.eq (v 4) (k 0)) (.set 2 (k 0)) .skip)))
      (.set 0 (v 2))))

def time (n maxValue : ℕ) : ℕ := (n-2)*(residueBudget maxValue+70)+70







def Inv (μ : ℕ → ℤ) (n free i : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(n : ℤ),free,flag n i,i,rval],ν⟩ ∧ Kept μ ν free

variable {lim : Limits} {P : Program} {d : ℕ}






























































structure Procs (P : Program) (pMain : ℕ) where
  pEmod : ℕ
  main : P[pMain]? = some (body pEmod)
  emod : P[pEmod]? = some emodBody





























end ThreeSum.LightPrimality

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightRawAKeys


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences


/-!
# Actual construction of the three lifted original A-key arrays

The middle row is computed by the checked signed remainder routine. Two
affine scans append the minus and plus lifts. Every original position is
retained in each row, and the resulting segment is the exact guarded-key
list whose balancing bound is proved in `RawAKeyLists`.
-/

namespace ThreeSum.LightRawAKeys

open Light LightResidues RawIncidences RawAKeyLists

set_option maxHeartbeats 1000000
set_option maxRecDepth 6000

/-- Original array, length, modulus, and first free address. -/
def body (pResidues pAffine : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 4
      ((Light.Expr.op Light.Op.add) (v 3)
        ((Light.Expr.op Light.Op.mul) (k 3) (v 1))))
    (Light.Stmt.seq
      (.call pResidues
        [v 0, (Light.Expr.op Light.Op.add) (v 3) (v 1), v 1, v 2, v 4, k 1] 5)
      (Light.Stmt.seq
        (.call pAffine
          [(Light.Expr.op Light.Op.add) (v 3) (v 1), v 3, v 1,
            (Light.Expr.op Light.Op.sub) (k 0) (v 2), k 1]
          5)
        (Light.Stmt.seq
          (.call pAffine
            [(Light.Expr.op Light.Op.add) (v 3) (v 1),
              (Light.Expr.op Light.Op.add) (v 3)
                ((Light.Expr.op Light.Op.mul) (k 2) (v 1)),
              v 1, v 2, k 1]
            5)
          (.set 0 (v 3))))))

def time (n U : ℕ) : ℕ := residuesTime n U+2*LightReportingAffine.time n+150
def space (free n U : ℕ) : ℕ := free+3*n+Nat.log 2 (U+1)+2
def word (p U : ℕ) : ℕ := 4*U+4*p+16

variable {lim : Limits} {P : Program} {d : ℕ}
















































































def program : Program := [body 1 2,residuesBody 3,LightReportingAffine.body,emodBody]















end ThreeSum.LightRawAKeys

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceResidues


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def key (p m : ℕ) (shift x : ℤ) : ℕ := ((x % (p : ℤ) + shift) % (m : ℤ)).toNat











/-- Arguments: source, destination, count, first modulus, second modulus,
scratch, and signed carry offset. The two remainder calls share scratch. -/
def body (pEmod : ℕ) : Stmt :=
  .for 7 (v 2) (
    (Light.Stmt.seq
      (.call pEmod [M ((Light.Expr.op Light.Op.add) (v 0) (v 7)), v 3, v 5] 8)
      (Light.Stmt.seq
        (.call pEmod [(Light.Expr.op Light.Op.add) (v 8) (v 6), v 4, v 5] 9)
        (.store ((Light.Expr.op Light.Op.add) (v 1) (v 7)) (v 9)))))

def time (n p U D : ℕ) : ℕ :=
  n * (LightResidues.residueBudget U + LightResidues.residueBudget (p+D) + 100) + 6

def word (p m U D : ℕ) : ℕ := 4*U+8*p+4*D+4*m+32

def space (work p U D : ℕ) : ℕ :=
  work + max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)

def Inv (μ : ℕ → ℤ) (src dst n p m work : ℕ) (shift : ℤ) (i : ℕ)
    (σ : State) : Prop :=
  ∃ (r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,dst,n,p,m,work,shift,i,r0,r1],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (key p m shift (μ (src+j)) : ℤ)) ∧
    KeptBut μ ν work dst n

variable {lim : Limits} {P : Program} {d : ℕ}





























































































def program : Program := [body 1,emodBody]



















end ThreeSum.LightSourceResidues

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightKaratsuba


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba


/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba

open Light
open ThreeSum.Karatsuba
open Polynomial

abbrev Len : ℕ := 0
abbrev Left : ℕ := 1
abbrev Right : ℕ := 2
abbrev Out : ℕ := 3
abbrev Work : ℕ := 4
abbrev Half : ℕ := 5
abbrev Unused : ℕ := 6

def joinBody (pLinear pFill : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pLinear
      [(Light.Expr.op Light.Op.add) (v Work)
          ((Light.Expr.op Light.Op.mul) (k 2) (v Len)),
        v Work,
        (Light.Expr.op Light.Op.add) (v Work)
          ((Light.Expr.op Light.Op.mul) (k 2) (v Len)),
        v Len, (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
      Unused)
    (Light.Stmt.seq
      (.call pLinear
        [(Light.Expr.op Light.Op.add) (v Work)
            ((Light.Expr.op Light.Op.mul) (k 2) (v Len)),
          (Light.Expr.op Light.Op.add) (v Work) (v Len),
          (Light.Expr.op Light.Op.add) (v Work)
            ((Light.Expr.op Light.Op.mul) (k 2) (v Len)),
          v Len, (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
        Unused)
      (Light.Stmt.seq
        (.call pFill [v Out, (Light.Expr.op Light.Op.mul) (k 2) (v Len), k 0]
          Unused)
        (Light.Stmt.seq (.call pLinear [v Out, v Work, v Out, v Len, k 1] Unused)
          (Light.Stmt.seq
            (.call pLinear
              [(Light.Expr.op Light.Op.add) (v Out) (v Half),
                (Light.Expr.op Light.Op.add) (v Work)
                  ((Light.Expr.op Light.Op.mul) (k 2) (v Len)),
                (Light.Expr.op Light.Op.add) (v Out) (v Half), v Len, k 1]
              Unused)
            (.call pLinear
              [(Light.Expr.op Light.Op.add) (v Out) (v Len),
                (Light.Expr.op Light.Op.add) (v Work) (v Len),
                (Light.Expr.op Light.Op.add) (v Out) (v Len), v Len, k 1]
              Unused))))))

def recurseBody (pSelf pHalf pLinear pFill : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pHalf [v Len] Half)
    (Light.Stmt.seq
      (.call pLinear
        [v Left, (Light.Expr.op Light.Op.add) (v Left) (v Half),
          (Light.Expr.op Light.Op.add) (v Work)
            ((Light.Expr.op Light.Op.mul) (k 3) (v Len)),
          v Half, k 1]
        Unused)
      (Light.Stmt.seq
        (.call pLinear
          [v Right, (Light.Expr.op Light.Op.add) (v Right) (v Half),
            (Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v Work)
                ((Light.Expr.op Light.Op.mul) (k 3) (v Len)))
              (v Half),
            v Half, k 1]
          Unused)
        (Light.Stmt.seq
          (.call pSelf
            [v Half, v Left, v Right, v Work,
              (Light.Expr.op Light.Op.add) (v Work)
                ((Light.Expr.op Light.Op.mul) (k 4) (v Len))]
            Unused)
          (Light.Stmt.seq
            (.call pSelf
              [v Half, (Light.Expr.op Light.Op.add) (v Left) (v Half),
                (Light.Expr.op Light.Op.add) (v Right) (v Half),
                (Light.Expr.op Light.Op.add) (v Work) (v Len),
                (Light.Expr.op Light.Op.add) (v Work)
                  ((Light.Expr.op Light.Op.mul) (k 4) (v Len))]
              Unused)
            (Light.Stmt.seq
              (.call pSelf
                [v Half,
                  (Light.Expr.op Light.Op.add) (v Work)
                    ((Light.Expr.op Light.Op.mul) (k 3) (v Len)),
                  (Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v Work)
                      ((Light.Expr.op Light.Op.mul) (k 3) (v Len)))
                    (v Half),
                  (Light.Expr.op Light.Op.add) (v Work)
                    ((Light.Expr.op Light.Op.mul) (k 2) (v Len)),
                  (Light.Expr.op Light.Op.add) (v Work)
                    ((Light.Expr.op Light.Op.mul) (k 4) (v Len))]
                Unused)
              (joinBody pLinear pFill)))))))

def baseBody : Stmt :=
  (Light.Stmt.seq
    (.store (v Out) ((Light.Expr.op Light.Op.mul) (M (v Left)) (M (v Right))))
    (.store ((Light.Expr.op Light.Op.add) (v Out) (k 1)) (k 0)))

def body (pSelf pHalf pLinear pFill : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 1) (v Len))) (recurseBody pSelf pHalf pLinear pFill) baseBody

structure Procs (P : Program) (pSelf pHalf pLinear pFill : ℕ) : Prop where
  self : P[pSelf]? = some (body pSelf pHalf pLinear pFill)
  half : P[pHalf]? = some halfBody
  linear : P[pLinear]? = some LightArray.linearBody
  fill : P[pFill]? = some fillBody

/-- The conservative recurrence has ample space for all expression and call
costs; a proof of a procedure must discharge this bound through `Ends`. -/
def time : ℕ → ℕ
  | 0 => 30
  | k + 1 => 3 * time k + 2500 * 2 ^ k






















def ProductAt (μ : ℕ → ℤ) (out n : ℕ) (as bs : List ℤ) : Prop :=
  ∀ j < 2 * n, μ (out + j) = (asPolynomial as * asPolynomial bs).coeff j

/-- Only the output cells below the scratch pointer may change. -/
def Result (μ : ℕ → ℤ) (out n work : ℕ) (as bs : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  ProductAt μ' out n as bs ∧ KeptBut μ μ' work out (2 * n)

def wordBound (n U : ℕ) : ℕ := 128 * n ^ 3 * (U + 1) ^ 2

def window (f : ℕ → ℤ) (offset n j : ℕ) : ℤ :=
  if offset ≤ j ∧ j < offset + n then f (j - offset) else 0



























def joined (μ : ℕ → ℤ) (work n half j : ℕ) : ℤ :=
  window (fun i => μ (work + i)) 0 n j +
  window (fun i => μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i)) half n j +
  window (fun i => μ (work + n + i)) n n j

def joinTime (n : ℕ) : ℕ := 200 * n + 300

section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}




































































































































end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}






































end BaseCase

















































































































section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}











































































































































end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}




















































































end CompleteProcedure

end ThreeSum.LightKaratsuba

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSumApsp_Lang_Lib_MergeSort
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Merge sort

sort(n, a, fr) sorts the n cells from a in place, in ascending order (`sort_meets`).  It is the
recursive merge sort: sort the first ⌈n/2⌉ cells, sort the rest, merge the two halves into the n
cells from the free pointer fr, and copy them back.  It calls half, merge and copy.

The proof is an induction on n.  `body_ends` treats the body of the procedure, given that the
procedure sorts the lists of half the length, and `join_ends` its last two calls; `sorted_merge`
says that what the four calls leave is a sorted permutation of the list.  The number of steps,
`sortTime n`, is of the order n log n (`clog_split`, `time_split`), and the calls are nested
⌈log₂ n⌉ + 1 deep.  Numbers are only compared and copied, so their size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program}

namespace MergeSort

/-- The local variables of sort: the arguments n, a and fr; h = ⌈n/2⌉; and a local that takes the
results of the calls, which are not used. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Start : ℕ := 1
@[inherit_doc Len] abbrev Free : ℕ := 2
@[inherit_doc Len] abbrev Half : ℕ := 3
@[inherit_doc Len] abbrev Unused : ℕ := 4

end MergeSort

open MergeSort in
/-- The two sorted halves are merged into the cells from fr and copied back. -/
def sortJoin (pMerge pCopy : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pMerge
      [v Start, v Half, (Light.Expr.op Light.Op.add) (v Start) (v Half),
        (Light.Expr.op Light.Op.sub) (v Len) (v Half), v Free]
      Unused)
    (.call pCopy [v Free, v Start, v Len] Unused))

open MergeSort in
/-- sort(n, a, fr).  The parameters are the procedure numbers of sort itself, half, merge and
copy. -/
def sortBody (pSort pHalf pMerge pCopy : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 1) (v Len))) (
    (Light.Stmt.seq (.call pHalf [v Len] Half)
      (Light.Stmt.seq (.call pSort [v Half, v Start, v Free] Unused)
        (Light.Stmt.seq
          (.call pSort
            [(Light.Expr.op Light.Op.sub) (v Len) (v Half),
              (Light.Expr.op Light.Op.add) (v Start) (v Half), v Free]
            Unused)
          (sortJoin pMerge pCopy))))) .skip

/-- The time of sort. -/
def sortTime (n : ℕ) : ℕ := 61 * (n * Nat.clog 2 n) + 74 * (n - 1) + 4

namespace MergeSort





















/-- The program holds the four procedures. -/
structure Procs (P : Program) (pSort pHalf pMerge pCopy : ℕ) : Prop where
  sort : P[pSort]? = some (sortBody pSort pHalf pMerge pCopy)
  half : P[pHalf]? = some halfBody
  merge : P[pMerge]? = some mergeBody
  copy : P[pCopy]? = some copyBody








/-- What sort leaves: a sorted permutation of the list L at a; of the cells below fr only those of
the list may have changed. -/
def Sorted (μ : ℕ → ℤ) (a fr : ℕ) (L : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧
    KeptBut μ μ' fr a L.length


























variable {pSort pHalf pMerge pCopy : ℕ}
























































































end MergeSort

end Light

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandTable


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress


/-!
# Actual rectangular tables of band-owner lookups

Each output cell is a real call to the division-free interval lookup.
The two fixed outer counters identify the owner coordinates; the cell stores
zero for a miss or the third coordinate plus one. Keeping harmless candidate
duplicates is sufficient for the quadratic work bound and avoids any cubic
triple filtering operation.
-/

namespace ThreeSum.LightBandTable

open Light ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def rowValue (lo hi : ℕ → ℤ) (n : ℕ) (x s : ℤ) (f : ℕ → ℤ) (j : ℕ) : ℕ :=
  LightBandLookup.result lo hi n (s*x+f j)

/-- Arguments: left value, right base, target endpoints, right length,
target length, output, powers, width, left sign. -/
def rowBody (pLookup : ℕ) : Stmt :=
  .for 10 (v 4) (
    (Light.Stmt.seq
      (.call pLookup
        [v 2, v 3, v 5,
          (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v 9) (v 0))
            (M ((Light.Expr.op Light.Op.add) (v 1) (v 10))),
          v 7, v 8]
        11)
      (.store ((Light.Expr.op Light.Op.add) (v 6) (v 10)) (v 11))))

def rowTime (n W : ℕ) : ℕ := n*(LightBandLookup.time W+60)+6













































































/-- Arguments: the two query-endpoint bases, target endpoint bases, both
owner dimensions, target size, output, powers, width, left sign. -/
def body (pRow : ℕ) : Stmt :=
  .for 11 (v 4) (
    .call pRow [M (((Light.Expr.op Light.Op.add) (v 0) (v 11))),v 1,v 2,v 3,v 5,v 6,
      ((Light.Expr.op Light.Op.add) (v 7) ((Light.Expr.op Light.Op.mul) (v 11) (v 5))),v 8,v 9,v 10] 12)

def time (nX nY W : ℕ) : ℕ := nX*(rowTime nY W+70)+6
































































































end ThreeSum.LightBandTable

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingCatalogLookup


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
# Actual logarithmic lookup of an original prefix-catalog index

The program constructs its own powers, forms the physical query pair key,
performs division-free binary search over the sorted packed records, and
uses the benchmark's binary remainder algorithm to recover the original
catalog position. No full-catalog scan or index oracle occurs.
-/

namespace ThreeSum.LightReportingCatalogLookup

open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : Limits}

def valueBound (W n : ℕ) : ℕ := 2^(2*W)*(n+1)

def word (W n : ℕ) : ℕ :=
  4*valueBound W n+4*(n+1)+n+2^(2*W+2)+2^(W+1)+16










def body (pPowers pSearch pEmod : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers
      [v 5,
        (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (k 2) (v 0))
          (k 2),
        k 2]
      6)
    (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 5) (v 0))))
      (Light.Stmt.seq
        (.set 8
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.mul)
              ((Light.Expr.op Light.Op.add) (v 3)
                ((Light.Expr.op Light.Op.mul) (v 7) (v 4)))
              ((Light.Expr.op Light.Op.add) (v 1) (k 1)))
            (v 1)))
        (Light.Stmt.seq
          (.call pSearch
            [v 2, v 1, v 8, v 5,
              (Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.mul) (k 2) (v 0)) (k 1),
              k 0]
            9)
          (Light.Stmt.seq
            (.set 10
              (M
                ((Light.Expr.op Light.Op.sub)
                  ((Light.Expr.op Light.Op.add) (v 2) (v 9)) (k 1))))
            (.call pEmod [v 10, (Light.Expr.op Light.Op.add) (v 1) (k 1), v 5]
              0))))))

def program : Program := [powTableBody,LightBandLookup.searchBody 1,emodBody,body 0 1 2]

def time (W n : ℕ) : ℕ := powTableTime (2*W+2)+LightBandLookup.searchTime (2*W+1)+
  100*(Nat.log 2 (valueBound W n+1)+2)+200













































































































end ThreeSum.LightReportingCatalogLookup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandCandidateRows


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

inductive Mode where
  | bc | ab | ac
  deriving DecidableEq

structure Record where
  flag : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  deriving DecidableEq, Inhabited

def make (mode : Mode) (i j r : ℕ) : Record :=
  match mode with
  | .bc => ⟨if 0 < r then 1 else 0,r-1,i,j⟩
  | .ab => ⟨if 0 < r then 1 else 0,i,j,r-1⟩
  | .ac => ⟨if 0 < r then 1 else 0,i,r-1,j⟩

def Record.cells (r : Record) : List ℤ := [r.flag,r.a,r.b,r.c]

def bc (A B C : Family) (j k : ℕ) : Record :=
  make .bc j k (LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j))

def ab (A B C : Family) (i j : ℕ) : Record :=
  make .ab i j (LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j))

def ac (A B C : Family) (i k : ℕ) : Record :=
  make .ac i k (LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i))

def rect (m n : ℕ) (F : ℕ → ℕ → Record) : List Record :=
  (List.range m).flatMap fun i => (List.range n).map (F i)

def records (A B C : Family) : List Record :=
  rect B.size C.size (bc A B C) ++
    (rect A.size B.size (ab A B C) ++ rect A.size C.size (ac A B C))

def cells (rs : List Record) : List ℤ := rs.flatMap Record.cells

def slot (A B C : Family) : Owner A B C → ℕ
  | .inl (j,k) => j.val*C.size+k.val
  | .inr (i,.inl j) => B.size*C.size+i.val*B.size+j.val
  | .inr (i,.inr k) => B.size*C.size+A.size*B.size+i.val*C.size+k.val

def fromOwner (A B C : Family) : Owner A B C → Record
  | .inl (j,k) => bc A B C j.val k.val
  | .inr (i,.inl j) => ab A B C i.val j.val
  | .inr (i,.inr k) => ac A B C i.val k.val

def fromTriple {A B C : Family} (t : Triple A B C) : Record :=
  ⟨1,t.1.val,t.2.1.val,t.2.2.val⟩


























































































































































end ThreeSum.BandCandidateRows

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandPartition


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition

def size (n g : ℕ) : ℕ := if n = 0 then 0 else (n-1)/g+1
def start (g i : ℕ) : ℕ := i*g
def stop (n g i : ℕ) : ℕ := min n ((i+1)*g)
























theorem start_lt {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) : start g i < n := by
  unfold size at hi
  split_ifs at hi with hn
  · omega
  · have hid : i ≤ (n-1)/g := by omega
    have hm := (Nat.le_div_iff_mul_le hg).mp hid
    unfold start
    omega

theorem start_lt_stop {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    start g i < stop n g i := by
  have hn := start_lt hg hi
  unfold start stop at *
  have hprod : i*g < (i+1)*g := Nat.mul_lt_mul_of_pos_right (by omega) hg
  omega

theorem stop_le (n g i : ℕ) : stop n g i ≤ n := min_le_left _ _

theorem stop_sub_one_lt {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    stop n g i-1 < n := by
  have hp := start_lt_stop hg hi
  have hs := stop_le n g i
  omega
























theorem monotone_of_strict {f : ℕ → ℤ} {n i j : ℕ}
    (hs : ∀ i j, i < j → j < n → f i < f j) (hij : i ≤ j) (hj : j < n) :
    f i ≤ f j := by
  rcases lt_or_eq_of_le hij with h | rfl
  · exact (hs i j h hj).le
  · rfl

def family (f : ℕ → ℤ) (n g : ℕ) (hg : 0 < g)
    (hs : ∀ i j, i < j → j < n → f i < f j) : BandEnumeration.Family where
  size := size n g
  lower i := f (start g i)
  upper i := f (stop n g i-1)
  nonempty i hi := monotone_of_strict hs (by have := start_lt_stop hg hi; omega)
    (stop_sub_one_lt hg hi)
  sorted i j hij hj := monotone_of_strict hs (Nat.mul_le_mul_right g hij) (start_lt hg hj)
  separated i j hij hj := by
    have hstop : stop n g i ≤ (i+1)*g := min_le_right _ _
    have hprod : (i+1)*g ≤ j*g := Nat.mul_le_mul_right g (by omega)
    have hpositive : 0 < j*g := by
      have hjpos : 0 < j := by omega
      exact Nat.mul_pos hjpos hg
    apply hs _ _ (by unfold start; omega) (start_lt hg hj)










end ThreeSum.BandPartition

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_PrimeDensity


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# A proved supply of candidates for the deterministic modulus chain

The candidate interval is `(y, 4*y]`, a subset of `[y, 4*y]`. This is an explicit
revision from the preliminary `[y,2*y]` interval: Mathlib's elementary Chebyshev
constants give a positive difference on the fourfold interval. Multiplying the
window width by this fixed constant changes none of the target exponents.

The final theorem proves a concrete lower bound `y / (4 log y)` on the cardinality,
for every sufficiently large integer `y`. The set is an explicitly computable finset.
-/

namespace ThreeSum.PrimeDensity

open Real Filter Finset
open scoped Topology

def candidates (y : ℕ) : Finset ℕ := Nat.primesLE (4 * y) \ Nat.primesLE y

noncomputable section

theorem mem_candidates {p y : ℕ} :
    p ∈ candidates y ↔ Nat.Prime p ∧ y < p ∧ p ≤ 4 * y := by
  unfold candidates
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp4, hp⟩, hn⟩
    refine ⟨hp, ?_, hp4⟩
    by_contra h
    exact hn ⟨by omega, hp⟩
  · rintro ⟨hp, hyp, hp4⟩
    exact ⟨⟨hp4, hp⟩, fun h => (not_le_of_gt hyp) h.1⟩

theorem candidate_card_add (y : ℕ) :
    (candidates y).card + Nat.primeCounting y = Nat.primeCounting (4 * y) := by
  have hsub : Nat.primesLE y ⊆ Nat.primesLE (4 * y) := Nat.primesLE_mono (by omega)
  simpa only [candidates, Nat.primesLE_card_eq_primeCounting] using card_sdiff_add_card_eq_card hsub

def lowerScaled (y : ℕ) : ℝ :=
  (4 * Real.log 2 - Real.log (4 * y + 1 : ℝ) / y) /
    (1 + Real.log 4 / Real.log y)

theorem lowerScaled_tendsto : Tendsto lowerScaled atTop (𝓝 (4 * Real.log 2)) := by
  have herr := ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero (c := 4) (by norm_num)
  have hinv := ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop
  have hnum := (tendsto_const_nhds (x := 4 * Real.log 2)).sub herr
  have hsmall := hinv.const_mul (Real.log 4)
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  have h := hnum.div hden (by norm_num : (1 + Real.log 4 * 0 : ℝ) ≠ 0)
  unfold lowerScaled
  simpa [Pi.div_def, Pi.mul_def, div_eq_mul_inv, Pi.inv_apply] using h

theorem lowerScaled_identity {y : ℕ} (hy : 1 < y) :
    lowerScaled y * ((y : ℝ) / Real.log y) =
      ((4 * y : ℝ) * Real.log 2 - Real.log (4 * y + 1 : ℝ)) / Real.log (4 * y : ℝ) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (lt_trans Nat.zero_lt_one hy)
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by exact_mod_cast hy)
  have hlog4y : Real.log (4 * y : ℝ) = Real.log 4 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hsum : Real.log 4 + Real.log y ≠ 0 := by
    have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  unfold lowerScaled
  rw [hlog4y]
  field_simp
  ring

theorem eventually_lower_count :
    ∀ᶠ y : ℕ in atTop, (2 : ℝ) * ((y : ℝ) / Real.log y) ≤ Nat.primeCounting (4 * y) := by
  have htwo : (2 : ℝ) < 4 * Real.log 2 := by linarith [ThreeSum.Parameters.log_two_lower]
  have hs := lowerScaled_tendsto.eventually (lt_mem_nhds htwo)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with y hs hy
  have hy1 : 1 < y := by omega
  have hratio : 0 ≤ (y : ℝ) / Real.log y := by
    apply div_nonneg (Nat.cast_nonneg y)
    exact (Real.log_pos (by exact_mod_cast hy1)).le
  have hmul := mul_le_mul_of_nonneg_right hs.le hratio
  rw [lowerScaled_identity hy1] at hmul
  have hpi := Chebyshev.pi_ge (4 * y)
  push_cast at hpi
  exact hmul.trans hpi

theorem eventually_upper_count :
    ∀ᶠ y : ℕ in atTop, (Nat.primeCounting y : ℝ) ≤ (7 / 4 : ℝ) * ((y : ℝ) / Real.log y) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := (1 / 4 : ℝ)) (by norm_num))
  have hcoef : Real.log 4 + (1 / 4 : ℝ) < 7 / 4 := by
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [ThreeSum.Parameters.log_two_upper]
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with y hy hge
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hratio : 0 ≤ (y : ℝ) / Real.log y :=
    div_nonneg (Nat.cast_nonneg y) (Real.log_pos hy1).le
  have hbound : (Nat.primeCounting y : ℝ) ≤
      (Real.log 4 + 1 / 4) * ((y : ℝ) / Real.log y) := by simpa only [Nat.floor_natCast, mul_div_assoc] using hy
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef.le hratio)

/-- A concrete elementary density theorem for the executable candidate finset. -/
theorem eventually_candidate_density :
    ∀ᶠ y : ℕ in atTop, (y : ℝ) / (4 * Real.log y) ≤ ((candidates y).card : ℝ) := by
  filter_upwards [eventually_lower_count, eventually_upper_count] with y hlo hhi
  have hcard : ((candidates y).card : ℝ) + (Nat.primeCounting y : ℝ) =
      (Nat.primeCounting (4 * y) : ℝ) := by exact_mod_cast candidate_card_add y
  have hid : (y : ℝ) / (4 * Real.log y) = (1 / 4 : ℝ) * ((y : ℝ) / Real.log y) := by ring
  rw [hid]
  linarith

theorem eventually_candidates_nonempty :
    ∀ᶠ y : ℕ in atTop, (candidates y).Nonempty := by
  filter_upwards [eventually_candidate_density, eventually_ge_atTop (2 : ℕ)] with y hy hge
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hpos : (0 : ℝ) < (y : ℝ) / (4 * Real.log y) := by
    apply div_pos (by linarith)
    exact mul_pos (by norm_num) (Real.log_pos hy1)
  apply card_pos.mp
  exact_mod_cast lt_of_lt_of_le hpos hy

end

end ThreeSum.PrimeDensity

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LocalHashMoments


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph


/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments

open Finset
open scoped BigOperators

open LocalGraph LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}

abbrev Weight (L : ℕ) (K : Type*) := Fin L × Bool → K

/-- Exact light-bucket threshold, with integer rounding built in. -/
def bucketBound (L h p : ℕ) : ℕ := bucketCap (vertexCount L h) p





/-- The number of represented edges after retaining both endpoint buckets. -/
def hitCount (L h : ℕ) (B : ℕ) (w : Weight L K) (target : K × K) : ℕ :=
  HashFamily.incidenceCount (fun e : Edge L h =>
    HashFamily.trimmedPairEvent (left e) (right e) target.1 target.2
      (leftVertices L h) (rightVertices L h) B) w

def Covers (L h : ℕ) (B : ℕ) (w : Weight L K) (target : K × K) : Prop :=
  hitCount L h B w target ≠ 0

instance instDecidableCovers (L h B : ℕ) :
    DecidableRel (Covers (K := K) L h B) := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ (0 : ℕ)))





















































































































































instance weightInhabited : Inhabited (Weight L K) := ⟨fun _ => 0⟩

def coordinates (L : ℕ) : List (Fin L × Bool) :=
  (List.finRange L).flatMap (fun i => [(i, false), (i, true)])

theorem mem_coordinates (i : Fin L × Bool) : i ∈ coordinates L := by
  obtain ⟨i, b⟩ := i
  cases b <;> simp [coordinates]

/-- Explicit list enumeration; it does not use the noncomputable choice of
an ordering of a `Finset`. -/
def allWeights (L : ℕ) (values : List K) : List (Weight L K) :=
  (List.pi (coordinates L) (fun _ => values)).map
    (fun f i => f i (mem_coordinates i))







def scheduleLength (h p : ℕ) : ℕ :=
  320 * (2 * h + 1) * (Nat.log2 (p ^ 2) + 1)

/-- Exhaustive argmax selection with a fully specified finite stopping time. -/
def schedule (L h : ℕ) (values : List K) :
    List (Weight L K) :=
  Cover.greedyChoices (allWeights L values)
    (Covers L h (bucketBound L h (Fintype.card K)))
    (univ : Finset (K × K)) (scheduleLength h (Fintype.card K))

theorem schedule_length (values : List K) :
    (schedule L h values).length = scheduleLength h (Fintype.card K) :=
  Cover.greedyChoices_length ..

































/-! ## The selected local prime and its actual finite schedule -/

instance localPrimeFact (h : ℕ) : Fact (Nat.Prime (localPrime h)) :=
  ⟨localPrime_prime h⟩

abbrev LocalField (h : ℕ) := ZMod (localPrime h)

def localValues (h : ℕ) : List (LocalField h) :=
  (List.range (localPrime h)).map (fun x : ℕ => (x : LocalField h))







def localSchedule (h : ℕ) : List (Weight (512 * h) (LocalField h)) :=
  schedule (512 * h) h (localValues h)

theorem localSchedule_length (h : ℕ) :
    (localSchedule h).length =
      320 * (2 * h + 1) * (Nat.log2 (localPrime h ^ 2) + 1) := by
  simpa only [localSchedule, scheduleLength, ZMod.card] using
    schedule_length (L := 512 * h) (h := h) (localValues h)













































end ThreeSum.LocalHashMoments

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightRadixRows


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists


/-!
# Costed Cartesian rows for positional keys

For every local key, an actual affine scan writes one entire row of extended
keys. The arrays contain the complete product list, including equal integer
keys attached to different original records. No division or decoding loop is
used to locate Cartesian coordinates at runtime.
-/

namespace ThreeSum.LightRadixRows

open Light RadixKeyLists

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

def body (pAffine : ℕ) : Stmt :=
  .for 6 (v 3)
    (.call pAffine [v 1,((Light.Expr.op Light.Op.add) (v 2) ((Light.Expr.op Light.Op.mul) (v 6) (v 4))),v 4,M (((Light.Expr.op Light.Op.add) (v 0) (v 6))),v 5] 7)

def time (m n : ℕ) : ℕ := m*(LightReportingAffine.time n+100)+20
def word (p U V : ℕ) : ℕ := U+p*V+p+1

def Inv (μ : ℕ → ℤ) (srcBase srcPrev dst p : ℕ) (base prev : List ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [srcBase,srcPrev,dst,base.length,prev.length,p,j,r],ν⟩ ∧
    Seg ν dst (step (p : ℤ) (base.take j) prev) ∧
    SameOutside μ ν dst (base.length*prev.length)

variable {lim : Limits} {P : Program} {d : ℕ}
















































































































end ThreeSum.LightRadixRows

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_MaskUnion


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Exact width-scan invariants for general mask union -/

namespace ThreeSum.MaskUnion

open Finset ThreeSum.SubsetAddress

/-- Bits of `B` below the scan position have been added to `A`. -/
def scanSet {W : ℕ} (A B : Finset (Fin W)) (j : ℕ) : Finset (Fin W) :=
  A ∪ (B ∩ BoxStages.initialCoords W j)














































end ThreeSum.MaskUnion

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostQueryBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Output bounds and stored-table preservation for actual query batching -/

namespace ThreeSum.ReportingHostQueryBounds

open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators

def value {W : ℕ} (f g : Finset (Fin W) → ℤ) (stage : ℕ)
    (preL preR Q : Finset (Fin W)) : ℤ :=
  Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
    SubsetStages.stageValue g stage (preR ∪ S)) Q



















































end ThreeSum.ReportingHostQueryBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDownsetEnumerationSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A complete fixed program for compact downset enumeration

The main routine builds one power table and enumerates every layer through
the given cutoff into adjacent output cells. Its specification names the
exact compact list and bounds actual benchmark-language execution time.
-/

namespace ThreeSum.LightDownsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def body (pPowers pDownset : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 3, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 4)
    (.call pDownset [v 0, v 1, v 2, v 3] 0))

def time (L cut : ℕ) : ℕ := powTableTime (L+1)+LightDownsetEnumeration.time L cut+40











































































end ThreeSum.LightDownsetEnumerationSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSubsetEnumerationSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def body (pPowers pEnum : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 3, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 4)
    (.call pEnum [v 0, v 1, k 0, v 2, v 3] 0))

def time (L k : ℕ) : ℕ := powTableTime (L+1)+LightSubsetEnumeration.time L k+40

































































end ThreeSum.LightSubsetEnumerationSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWeightedEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Output-sensitive enumeration with arbitrary nonnegative coordinate weights

The existing recursive machine body is checked under a second contract.
Each output is the sum of the selected coordinate weights and the initial
prefix. The time and number of outputs remain binomial in the number of
available coordinates, independent of the size of the ambient mask.
-/

namespace ThreeSum.LightWeightedEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

open scoped BigOperators

variable {lim : Limits} {P : Program}

def total (weights : ℕ → ℕ) (L : ℕ) : ℕ := ∑ i ∈ Finset.range L, weights i








def output (weights : ℕ → ℕ) : ℕ → ℕ → ℕ → List ℤ
  | _,0,pref => [pref]
  | 0,_+1,_ => []
  | L+1,k+1,pref =>
      if k+1 ≤ L+1 then
        output weights L (k+1) pref ++ output weights L k (pref+weights L)
      else []



























def Weights (μ : ℕ → ℤ) (base W : ℕ) (weights : ℕ → ℕ) : Prop :=
  ∀ i, i < W → μ (base+i) = (weights i : ℤ)























































































































































end ThreeSum.LightWeightedEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LocalMaskGraph


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators

def maskAt (L h i : ℕ) : ℕ := (enumerateLayer L h).getD i 0
def setAt (L h i : ℕ) : Finset (Fin L) := decode L (maskAt L h i)
def vertexCount (L h : ℕ) : ℕ := L.choose h

theorem maskAt_mem {L h i : ℕ} (hi : i < vertexCount L h) :
    maskAt L h i ∈ enumerateLayer L h := by
  have hi' : i < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hi
  unfold maskAt
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'




theorem setAt_card {L h i : ℕ} (hi : i < vertexCount L h) : (setAt L h i).card = h :=
  decode_card_layer (maskAt_mem hi)



























































end ThreeSum.LocalMaskGraph

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_QueryCoordinates


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates

open Finset ThreeSum.SubsetAddress
open scoped BigOperators

/-- The selected coordinates among the first `j` scanned positions. -/
def positions {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) : List ℕ :=
  (List.range j).filter fun i => i ∈ natPositions Q








@[simp] theorem mem_positions {W : ℕ} (Q : Finset (Fin W)) (j i : ℕ) :
    i ∈ positions Q j ↔ i < j ∧ i ∈ natPositions Q := by
  simp [positions]

theorem positions_nodup {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (positions Q j).Nodup := List.nodup_range.filter _





@[simp] theorem positions_toFinset {W : ℕ} (Q : Finset (Fin W)) :
    (positions Q W).toFinset = natPositions Q := by
  ext i
  simp only [List.mem_toFinset,mem_positions,and_iff_right_iff_imp]
  exact fun hi => Finset.mem_range.mp (natPositions_subset Q hi)





def selectedPowers {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) : List ℕ :=
  (positions Q j).map fun i => 2^i


















def weights {W : ℕ} (Q : Finset (Fin W)) (i : ℕ) : ℕ :=
  (selectedPowers Q W)[i]?.getD 0












/-- Fixed-size sublists, interpreted as finite subsets. -/
def setLayer (xs : List ℕ) (k : ℕ) : List (Finset ℕ) :=
  (xs.sublistsLen k).map List.toFinset














theorem mem_setLayer (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) (s : Finset ℕ) :
    s ∈ setLayer xs k ↔ s ⊆ xs.toFinset ∧ s.card = k := by
  constructor
  · rintro hs
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hs
    obtain ⟨hys,hyk⟩ := List.mem_sublistsLen.mp hy
    refine ⟨?_,?_⟩
    · intro a ha
      exact List.mem_toFinset.mpr (hys.subset (List.mem_toFinset.mp ha))
    · rw [List.toFinset_card_of_nodup (hn.sublist hys),hyk]
  · rintro ⟨hs,hk⟩
    let ys := xs.filter fun i => i ∈ s
    have he : ys.toFinset = s := by
      ext i
      simp only [ys,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
      exact ⟨fun h => h.2,fun hi => ⟨List.mem_toFinset.mp (hs hi),hi⟩⟩
    apply List.mem_map.mpr
    refine ⟨ys,List.mem_sublistsLen.mpr ⟨List.filter_sublist,?_⟩,he⟩
    rw [← List.toFinset_card_of_nodup (hn.filter _),he,hk]
































































def missingSets {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) : List (Finset (Fin W)) :=
  (setLayer (positions Q W).reverse k).map fun s => MaskDecode.decode W (maskOf s)

theorem decode_maskOf {W : ℕ} {s : Finset ℕ} (hs : s ⊆ range W) :
    natPositions (MaskDecode.decode W (maskOf s)) = s := by
  apply maskOf_injective
  exact MaskDecode.subsetMask_decode (maskOf_isMask hs).1

theorem missingSets_mem {W : ℕ} (Q U : Finset (Fin W)) (k : ℕ) :
    U ∈ missingSets Q k ↔ U ⊆ Q ∧ U.card = k := by
  have hn := (List.nodup_reverse.mpr (positions_nodup Q W))
  constructor
  · intro hu
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hu
    have hset := (mem_setLayer _ hn _ _).mp hs
    rw [List.toFinset_reverse,positions_toFinset] at hset
    have hr : s ⊆ range W := hset.1.trans (natPositions_subset Q)
    have he := decode_maskOf hr
    refine ⟨?_,?_⟩
    · intro a ha
      have hp : a.val ∈ s := by
        rw [← he]
        exact Finset.mem_map.mpr ⟨a,ha,rfl⟩
      obtain ⟨b,hb,hba⟩ := Finset.mem_map.mp (hset.1 hp)
      exact (Fin.ext hba : b = a) ▸ hb
    · rw [← natPositions_card,he,hset.2]
  · rintro ⟨hU,hk⟩
    apply List.mem_map.mpr
    refine ⟨natPositions U,?_,MaskDecode.decode_subsetMask U⟩
    apply (mem_setLayer _ hn _ _).mpr
    rw [List.toFinset_reverse,positions_toFinset,natPositions_card]
    exact ⟨Finset.map_subset_map.mpr hU,hk⟩









































end ThreeSum.QueryCoordinates

end


