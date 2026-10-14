-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle07
-- name    : ThreeSum1962Source_Bundle07
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:10:55.937282+00:00
-- url     : https://prove2.me/theorems/17acefa7-6b6a-4cfd-a25f-16b79a36b46d
-- title:
--   Integer block scales, occurrence encoding, and compact source routines
-- statement:
--   This bundle defines the integer block schedule from input length $n$. With $m=\lfloor\log_2 n\rfloor$ (zero at $n=0$) and natural division, including $a/0=0$, its micro-size $u$, block count $J$, and total size $\mu$ are
--   $$
--   u=2\bigl(\lfloor\sqrt[3]m\rfloor/2\bigr),\qquad J=20\bigl(m/(100u)\bigr),\qquad \mu=Ju.
--   $$
--   It also defines physical A-incidence labels, packed band histograms and index buckets, occurrence-preserving global encodings, and ordered coefficient decoders. Light program bodies cover compact subset addresses, mask unions, greedy cover selection, local key arrays, coloring, modular triple counts, balanced offsets, and original-value leaf tests. Matching-key pair lists and the exhaustive original-triple fallback supply further specifications for later program composition.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Auxiliary.lean#L19-L83
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawA.lean#L19-L94
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ColorScan.lean#L9-L10
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/GlobalEncoding.lean#L23-L247
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBalancedOffset.lean#L17-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPartition.lean#L20-L128
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBruteThreeSum.lean#L21-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorClasses.lean#L19-L51
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverGreedy.lean#L21-L58
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDownsetAddress.lean#L19-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDownsetSize.lean#L18-L86
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCounts.lean#L20-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalKeys.lean#L18-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMaskUnion.lean#L19-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightModuloCounts.lean#L23-L224
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOutputDecode.lean#L20-L201
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightQueryWeights.lean#L19-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightRadixKeys.lean#L19-L93
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingLeaf.lean#L20-L35
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketFromHistogram.lean#L19-L33
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceMaskFlags.lean#L18-L42
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L19-L29
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightZetaCell.lean#L23-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalMaskHashes.lean#L19-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L18-L111
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Scales.lean#L25-L903
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SignedLeaf.lean#L22-L63
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandLayout.lean#L11-L120
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WantedPairs.lean#L21-L107
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WeightEnumeration.lean#L29-L151

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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawA


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

structure Label where
  owner : ℕ
  position : ℕ
  deriving DecidableEq, Inhabited

def bandLength (n g a : ℕ) : ℕ := stop n g a-start g a






def row (n g owner : ℕ) (r : Record) : List Label :=
  if r.flag=1 then
    (List.range (bandLength n g r.a)).map (fun j => ⟨owner,start g r.a+j⟩)
  else []

def firstRows (n g : ℕ) (rs : List Record) (i : ℕ) : List Label :=
  (List.range i).flatMap fun owner => row n g owner (rs.getD owner default)

def items (n g : ℕ) (rs : List Record) : List Label := firstRows n g rs rs.length

def count (n g : ℕ) (rs : List Record) (i : ℕ) : ℕ := (firstRows n g rs i).length

def values (f : ℕ → ℤ) (ls : List Label) : List ℤ := ls.map (fun l => f l.position)
def ownerLabels (ls : List Label) : List ℤ := ls.map (fun l => (l.owner : ℤ))
def positionLabels (ls : List Label) : List ℤ := ls.map (fun l => (l.position : ℤ))
















































theorem values_length (f : ℕ → ℤ) (ls : List Label) : (values f ls).length=ls.length := List.length_map ..























































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandPartition


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition


/-!
# Constructing consecutive band endpoints in actual memory

The program computes the number of bands itself. Its quotient loop is charged
linearly in that number, and both endpoint passes issue bounded-address
loads from the sorted source. Output arrays reserve `n` cells each; only the
computed band count is populated.
-/

namespace ThreeSum.LightBandPartition

open Light ThreeSum.BandPartition

variable {lim : Limits} {P : Program}

def lowerBody : Stmt :=
  pass 4 (v 2) (v 1) (M (((Light.Expr.op Light.Op.add) (v 0) ((Light.Expr.op Light.Op.mul) (v 4) (v 3)))))

def lowerTime (m : ℕ) : ℕ := 25*m+6
























def upperBody : Stmt :=
  .for 5 (v 4) (
    (Light.Stmt.seq
      (.set 6
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 5) (k 1))
          (v 2)))
      (Light.Stmt.seq (.ite (Light.Cond.lt (v 1) (v 6)) (.set 6 (v 1)) .skip)
        (.store ((Light.Expr.op Light.Op.add) (v 3) (v 5))
          (M
            ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v 0) (v 6))
              (k 1)))))))

def upperTime (m : ℕ) : ℕ := 100*m+6






























































def body (pDivide pLower pUpper : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 1)))
    ((Light.Stmt.seq (.call pDivide [(Light.Expr.op Light.Op.sub) (v 1) (k 1), v 2] 4)
       (Light.Stmt.seq (.set 4 ((Light.Expr.op Light.Op.add) (v 4) (k 1)))
         (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.add) (v 3) (v 1)))
           (Light.Stmt.seq (.call pLower [v 0, v 3, v 4, v 2] 6)
             (Light.Stmt.seq (.call pUpper [v 0, v 1, v 2, v 5, v 4] 6)
               (.set 0 (v 4))))))))
    (.set 0 (k 0))

def time (n g : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+lowerTime (size n g)+upperTime (size n g)+100







































































end ThreeSum.LightBandPartition

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets

def cap (n g : ℕ) : ℕ := min n g
def len (n g i : ℕ) : ℕ := stop n g i-start g i
def stride (n g m : ℕ) : ℕ := 3*m+1+2*cap n g
def data (base n g : ℕ) : ℕ := base+6*size n g
def hist (base n g m i : ℕ) : ℕ := data base n g+i*stride n g m
def codes (base n g m i : ℕ) : ℕ := hist base n g m i+m
def offsets (base n g m i : ℕ) : ℕ := codes base n g m i+cap n g
def cursor (base n g m i : ℕ) : ℕ := offsets base n g m i+m+1
def flat (base n g m i : ℕ) : ℕ := cursor base n g m i+m
def work (base n g m : ℕ) : ℕ := hist base n g m (size n g)


































































































def key (f : ℕ → ℤ) (g p m : ℕ) (shift : ℤ) (i j : ℕ) : ℕ :=
  LightSourceResidues.key p m shift (f (start g i+j))




end ThreeSum.SourceBandLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Auxiliary


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Exact auxiliary tests from the same finite prime pool

The prime pool used for deterministic contraction supplies enough distinct
primes to separate bounded nonzero differences. To use this same pool in
the weighted counting identity, the joint modulus must account for a prime
that already divides the current modulus; see `WeightedModuli.lean`.
-/

namespace ThreeSum.Auxiliary

open Finset
open scoped BigOperators

def moduli (C : Finset ℕ) : Finset ℤ := C.image (fun p : ℕ => (p : ℤ))




theorem prime_product_lower (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    2 ^ C.card ≤ ∏ p ∈ C, p := by
  calc
    2 ^ C.card = ∏ _p ∈ C, 2 := by simp
    _ ≤ ∏ p ∈ C, p := prod_le_prod' (fun p hp => (hC p hp).two_le)

theorem product_gt_of_card (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (M : ℕ) (hcard : Nat.log 2 M < C.card) : M < ∏ p ∈ C, p := by
  exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) M).trans_le
    ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) hcard).trans (prime_product_lower C hC))

theorem moduli_product (C : Finset ℕ) :
    (∏ p ∈ moduli C, p) = (∏ p ∈ C, p : ℕ) := by
  rw [moduli, Finset.prod_image]
  · simp
  · intro p hp q hq hpq
    exact Nat.cast_injective hpq

theorem moduli_pairwise_coprime (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    (moduli C : Set ℤ).Pairwise (fun a b => IsCoprime a b) := by
  intro a ha b hb hne
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
  have hpq : p ≠ q := by intro h; subst q; exact hne rfl
  have hc : p.Coprime q := (Nat.coprime_primes (hC p hp) (hC q hq)).mpr hpq
  exact hc.isCoprime

theorem separates_nonzero (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    {M : ℕ} (hprod : M < ∏ p ∈ C, p)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    ∃ p ∈ moduli C, ¬p ∣ z := by
  apply Arithmetic.exists_aux_not_dvd_of_prod_bound (moduli C) z
    (moduli_pairwise_coprime C hC) hz
  rw [moduli_product, Int.natAbs_natCast]
  exact hbound.trans_lt hprod


















theorem candidate_pool_separates (y M : ℕ)
    (hcard : Nat.log 2 M < (PrimeDensity.candidates y).card)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    ∃ p ∈ moduli (PrimeDensity.candidates y), ¬p ∣ z := by
  have hprime : ∀ p ∈ PrimeDensity.candidates y, Nat.Prime p :=
    fun p hp => (PrimeDensity.mem_candidates.mp hp).1
  exact separates_nonzero _ hprime (product_gt_of_card _ hprime M hcard) hz hbound

end ThreeSum.Auxiliary

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Scales


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology

def inputBits (n : ℕ) : ℕ := Nat.log2 n

def microSize (m : ℕ) : ℕ := 2 * (Nat.nthRoot 3 m / 2)

def blockCount (m : ℕ) : ℕ := 20 * (m / (100 * microSize m))

def totalSize (m : ℕ) : ℕ := blockCount m * microSize m

def muZero (n : ℕ) : ℕ := microSize (inputBits n)

def mu (n : ℕ) : ℕ := totalSize (inputBits n)

def typedOutputs (n : ℕ) : ℕ :=
  ((256 * muZero n).choose (muZero n)) ^ blockCount (inputBits n)

def localSearch (C n : ℕ) : ℕ := 2 ^ (C * muZero n ^ 2)




/-- For integral `m`, `sqrt m + 1` is exactly `ceil(sqrt(m+1))`. -/
def windowExponent (m : ℕ) : ℕ := Nat.sqrt m + 1

def primeWindow (n : ℕ) : ℕ := 2 ^ windowExponent (inputBits n)

def primeDepth (R : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.log (4 * primeWindow n) (R n / 4)

def primeLoss (R : ℕ → ℕ) (n : ℕ) : ℕ :=
  32 * primeWindow n * 4 ^ primeDepth R n

def microHalf (m : ℕ) : ℕ := Nat.nthRoot 3 m / 2

def localRadix (n : ℕ) : ℕ := LocalCoverBounds.localPrime (microHalf (inputBits n))

def radix (n : ℕ) : ℕ := localRadix n ^ blockCount (inputBits n)

def divisorBudget (k n : ℕ) : ℕ := Nat.log (primeWindow n) (3 * n ^ k)

def scoreLoss (k n : ℕ) : ℕ :=
  (16 * (k + 2) * (inputBits n + 1)) ^ primeDepth radix n

def candidateCount (n : ℕ) : ℕ := (PrimeDensity.candidates (primeWindow n)).card







theorem microSize_rounding (m : ℕ) :
    microSize m ≤ Nat.nthRoot 3 m ∧ Nat.nthRoot 3 m < microSize m + 2 := by
  have h := Nat.mod_add_div (Nat.nthRoot 3 m) 2
  have hr := Nat.mod_lt (Nat.nthRoot 3 m) (by decide : 0 < 2)
  unfold microSize
  omega

theorem microSize_cube_le (m : ℕ) : microSize m ^ 3 ≤ m := by
  exact (Nat.pow_le_pow_left (microSize_rounding m).1 3).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))







theorem totalSize_upper (m : ℕ) : 5 * totalSize m ≤ m := by
  have h := Nat.div_mul_le_self m (100 * microSize m)
  convert h using 1 <;> simp only [totalSize, blockCount] <;> ring

theorem totalSize_lower {m : ℕ} (hm : 0 < microSize m) :
    m < 5 * totalSize m + 100 * microSize m := by
  have hmod := Nat.mod_lt m (by omega : 0 < 100 * microSize m)
  have hdiv := Nat.mod_add_div m (100 * microSize m)
  have heq : 5 * totalSize m = 100 * microSize m * (m / (100 * microSize m)) := by
    simp only [totalSize, blockCount]
    ring
  omega

noncomputable section

theorem microSize_tendsto_atTop : Tendsto microSize atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) ^ 3)] with m hm
  have hr : b + 2 ≤ Nat.nthRoot 3 m :=
    (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr hm
  have hround := (microSize_rounding m).2
  omega

theorem microSize_cast_tendsto_atTop :
    Tendsto (fun m : ℕ => (microSize m : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp microSize_tendsto_atTop

theorem microSize_inv_tendsto_zero :
    Tendsto (fun m : ℕ => (microSize m : ℝ)⁻¹) atTop (𝓝 0) :=
  microSize_cast_tendsto_atTop.inv_tendsto_atTop

theorem microSize_square_ratio_bound {m : ℕ} (hm : 0 < microSize m) :
    (microSize m : ℝ) ^ 2 / m ≤ (microSize m : ℝ)⁻¹ := by
  have hx : (0 : ℝ) < microSize m := by exact_mod_cast hm
  have hcube : (microSize m : ℝ) ^ 3 ≤ (m : ℝ) := by
    exact_mod_cast microSize_cube_le m
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hcube
  apply (div_le_iff₀ hmpos).mpr
  rw [mul_comm ((microSize m : ℝ)⁻¹) (m : ℝ)]
  change (microSize m : ℝ) ^ 2 ≤ (m : ℝ) / microSize m
  apply (le_div_iff₀ hx).mpr
  nlinarith [hcube]

theorem microSize_square_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ microSize_inv_tendsto_zero
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    exact microSize_square_ratio_bound (by omega)

theorem microSize_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (microSize m : ℝ) / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ microSize_square_ratio_tendsto_zero
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hmr : (1 : ℝ) ≤ microSize m := by exact_mod_cast hm
    exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg m)

theorem totalSize_real_bounds {m : ℕ} (hm : 0 < microSize m) :
    (m : ℝ) / 5 - 20 * microSize m < totalSize m ∧
      (totalSize m : ℝ) ≤ (m : ℝ) / 5 := by
  have hu : (5 : ℝ) * totalSize m ≤ (m : ℝ) := by
    exact_mod_cast totalSize_upper m
  have hl : (m : ℝ) < 5 * totalSize m + 100 * microSize m := by
    exact_mod_cast totalSize_lower hm
  constructor <;> linarith

theorem totalSize_ratio_tendsto :
    Tendsto (fun m : ℕ => (totalSize m : ℝ) / m) atTop (𝓝 (1 / 5)) := by
  have hlo : Tendsto (fun m : ℕ => (1 / 5 : ℝ) - 20 * ((microSize m : ℝ) / m))
      atTop (𝓝 (1 / 5)) := by
    simpa using tendsto_const_nhds.sub (microSize_ratio_tendsto_zero.const_mul 20)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop (1 : ℕ)] with m hm hmpos
    have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hl := (totalSize_real_bounds (by omega : 0 < microSize m)).1.le
    apply (le_div_iff₀ hmp).mpr
    calc
      _ = (m : ℝ) / 5 - 20 * microSize m := by field_simp
      _ ≤ _ := hl
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    apply (div_le_iff₀ hmp).mpr
    have hu : (5 : ℝ) * totalSize m ≤ (m : ℝ) := by
      exact_mod_cast totalSize_upper m
    linarith

theorem inputBits_eq_floor (n : ℕ) : inputBits n = ⌊Real.logb 2 (n : ℝ)⌋₊ := by
  rw [inputBits, Nat.log2_eq_log_two]
  exact (Real.natFloor_logb_natCast 2 n).symm

theorem inputBits_tendsto_atTop : Tendsto inputBits atTop atTop := by
  have h := tendsto_nat_floor_atTop.comp
    ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  simpa [Function.comp_def, ← inputBits_eq_floor] using h

theorem inputBits_log_ratio_tendsto :
    Tendsto (fun n : ℕ => (inputBits n : ℝ) / Real.log n) atTop
      (𝓝 (1 / Real.log 2)) := by
  have h := tendsto_nat_floor_div_atTop.comp
    ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h' := h.div_const (Real.log 2)
  convert h' using 1
  funext n
  simp only [Function.comp_def, ← inputBits_eq_floor]
  rw [Real.logb, div_div, div_mul_cancel₀ _ Parameters.log_two_pos.ne']

theorem mu_log_ratio_tendsto :
    Tendsto (fun n : ℕ => (mu n : ℝ) / Real.log n) atTop
      (𝓝 (1 / (5 * Real.log 2))) := by
  have h := (totalSize_ratio_tendsto.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto
  have hlim : (1 / 5 : ℝ) * (1 / Real.log 2) = 1 / (5 * Real.log 2) := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, mu]
  field_simp






















































































































theorem natSqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b ^ 2)] with m hm
  exact Nat.le_sqrt'.mpr hm























theorem primeWindow_ge_two (n : ℕ) : 2 ≤ primeWindow n := by
  unfold primeWindow windowExponent
  rw [pow_succ]
  have hp : 0 < 2 ^ Nat.sqrt (inputBits n) := by positivity
  omega

theorem primeWindow_tendsto_atTop : Tendsto primeWindow atTop atTop := by
  have hs := natSqrt_tendsto_atTop.comp inputBits_tendsto_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hs.eventually (eventually_ge_atTop b)] with n hn
  have hp : Nat.sqrt (inputBits n) + 1 < 2 ^ (Nat.sqrt (inputBits n) + 1) :=
    Nat.lt_pow_self (by decide : 1 < 2)
  change b ≤ 2 ^ (Nat.sqrt (inputBits n) + 1)
  exact hn.trans ((Nat.le_succ _).trans hp.le)
















theorem actual_candidate_density :
    ∀ᶠ n : ℕ in atTop,
      (primeWindow n : ℝ) / (4 * Real.log (primeWindow n)) ≤
        (PrimeDensity.candidates (primeWindow n)).card :=
  primeWindow_tendsto_atTop.eventually PrimeDensity.eventually_candidate_density

theorem actual_candidates_nonempty :
    ∀ᶠ n : ℕ in atTop, (PrimeDensity.candidates (primeWindow n)).Nonempty :=
  primeWindow_tendsto_atTop.eventually PrimeDensity.eventually_candidates_nonempty

































theorem microHalf_tendsto_atTop : Tendsto microHalf atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop (2 * b))] with m hm
  change 2 * microHalf m ≥ 2 * b at hm
  omega



theorem even_output_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * Parameters.E)) := by
  have ht : Tendsto (fun h : ℕ => 2 * h) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with h hh
    omega
  have hr := BinomialEntropy.output_table_rate.comp ht
  convert hr using 1
  funext h
  simp only [Function.comp_def, LocalCoverBounds.outputCount, Nat.cast_mul, Nat.cast_ofNat]
  rw [show 256 * (2 * h) = 512 * h by omega]

theorem localThreshold_log_formula (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) =
      Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) +
        (2 * h : ℝ) * Real.log 2 := by
  have hM : (0 : ℝ) < LocalCoverBounds.outputCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 * h ≤ 512 * h))
  simp only [LocalCoverBounds.localThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (ne_of_gt hM) (by positivity), Real.log_pow]
  simp

theorem localThreshold_log_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localThreshold h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * Parameters.E + 1)) := by
  have hs := even_output_rate.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
  have hpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rw [localThreshold_log_formula]
  field_simp

theorem localPrime_log_interval (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) ≤
      2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ∧
    2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ≤
      Real.log 16 + Real.log (LocalCoverBounds.localThreshold h : ℝ) := by
  have hN : (0 : ℝ) < LocalCoverBounds.localThreshold h := by
    exact_mod_cast LocalCoverBounds.localThreshold_pos h
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  have hl : (LocalCoverBounds.localThreshold h : ℝ) ≤
      (LocalCoverBounds.localPrime h : ℝ) ^ 2 := by
    exact_mod_cast LocalCoverBounds.localPrime_sq_lower h
  have hu : (LocalCoverBounds.localPrime h : ℝ) ^ 2 ≤
      16 * (LocalCoverBounds.localThreshold h : ℝ) := by
    exact_mod_cast LocalCoverBounds.localPrime_sq_upper h
  constructor
  · simpa [Real.log_pow] using Real.log_le_log hN hl
  · simpa [Real.log_pow, Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hN.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (LocalCoverBounds.localPrime h : ℝ) ^ 2) hu

theorem localPrime_log_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localPrime h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (Parameters.E + 1 / 2)) := by
  have hmain := localThreshold_log_rate.div_const 2
  have hmain' : Tendsto (fun h : ℕ =>
      Real.log (LocalCoverBounds.localThreshold h : ℝ) / ((2 * h : ℝ) * Real.log 2) / 2)
      atTop (𝓝 (Parameters.E + 1 / 2)) := by
    convert hmain using 1 <;> ring
  have herr : Tendsto (fun h : ℕ => Real.log 16 / ((4 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 16 / (4 * Real.log 2))
  have hupper := hmain'.add herr
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain' hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (localPrime_log_interval h).1
    apply (le_div_iff₀ hden).mpr
    have heq : (Real.log (LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2) * ((2 * h : ℝ) * Real.log 2) =
        Real.log (LocalCoverBounds.localThreshold h : ℝ) / 2 := by field_simp
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (localPrime_log_interval h).2
    apply (div_le_iff₀ hden).mpr
    have heq : (Real.log (LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2 + Real.log 16 / ((4 * h : ℝ) * Real.log 2)) *
        ((2 * h : ℝ) * Real.log 2) =
        (Real.log (LocalCoverBounds.localThreshold h : ℝ) + Real.log 16) / 2 := by field_simp; ring
    rw [heq]
    linarith

theorem radix_log_ratio_tendsto :
    Tendsto (fun n : ℕ => Real.log (radix n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E + 1 / 2) / 5)) := by
  have hl := localPrime_log_rate.comp (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop)
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : (Parameters.E + 1 / 2) * (Real.log 2 * (1 / (5 * Real.log 2))) =
      (Parameters.E + 1 / 2) / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ microHalf (inputBits n) at hn
  have hn0 : (microHalf (inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, radix, Nat.cast_pow, Real.log_pow, localRadix]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) *
      (2 * microHalf (inputBits n)) := by simp [mu, totalSize, microSize, microHalf]
  rw [hmu]
  field_simp

theorem radix_pos (n : ℕ) : 0 < radix n := by
  unfold radix localRadix
  exact Nat.pow_pos (LocalCoverBounds.localPrime_pos _)

theorem radix_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (radix n : ℝ)) atTop atTop := by
  have hpositive : (0 : ℝ) < (Parameters.E + 1 / 2) / 5 := by
    have h := Parameters.E_bounds.1
    linarith
  have h := radix_log_ratio_tendsto.pos_mul_atTop hpositive
    Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem radix_eventually_ge_four : ∀ᶠ n : ℕ in atTop, 4 ≤ radix n := by
  filter_upwards [radix_log_tendsto_atTop.eventually (eventually_ge_atTop (Real.log 4))] with n hn
  have hr : (0 : ℝ) < radix n := by exact_mod_cast radix_pos n
  have h : (4 : ℝ) ≤ radix n := (Real.log_le_log_iff (by norm_num) hr).mp hn
  exact_mod_cast h



































































theorem input_log_le_bits_add_one {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ inputBits n + 1 := by
  have hpow : n ≤ 2 ^ (inputBits n + 1) := by
    simpa [inputBits, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowR : (n : ℝ) ≤ (2 : ℝ) ^ (inputBits n + 1) := by exact_mod_cast hpow
  have hl := Real.log_le_log hnpos hpowR
  rw [Real.log_pow] at hl
  have htwo : Real.log 2 ≤ 1 := by have := Parameters.log_two_upper; linarith
  have hm : (0 : ℝ) ≤ inputBits n + 1 := by positivity
  exact hl.trans (by simpa using mul_le_of_le_one_right hm htwo)

theorem log_difference_bound (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Real.log (3 * n ^ k : ℝ) ≤ ((k : ℝ) + 2) * (inputBits n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity), Real.log_pow]
  have hthree : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h
    exact h
  have hprod := mul_le_mul_of_nonneg_left (input_log_le_bits_add_one hn) (Nat.cast_nonneg k)
  have hm : (0 : ℝ) ≤ inputBits n := Nat.cast_nonneg _
  nlinarith [hm]

theorem actual_divisor_budget (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      divisorBudget k n * primeWindow n ≤
        (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)) := by
  filter_upwards [actual_candidate_density, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have hy := primeWindow_ge_two n
  have hlog : 0 < Real.log (primeWindow n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
  have hK : (divisorBudget k n : ℝ) ≤
      Real.log (3 * n ^ k : ℝ) / Real.log (primeWindow n : ℝ) := by
    simpa [divisorBudget, Real.logb] using
      Real.natLog_le_logb (3 * n ^ k) (primeWindow n)
  have hKmul := (le_div_iff₀ hlog).mp hK
  have hCmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log (primeWindow n : ℝ))).mp hC
  have hdiff := log_difference_bound k (by omega : 0 < n)
  have hr : (divisorBudget k n : ℝ) * primeWindow n ≤
      ((PrimeDensity.candidates (primeWindow n)).card : ℝ) *
        (4 * ((k : ℝ) + 2) * (inputBits n + 1)) := by
    calc
      (divisorBudget k n : ℝ) * primeWindow n ≤
          (divisorBudget k n : ℝ) *
            (((PrimeDensity.candidates (primeWindow n)).card : ℝ) *
              (4 * Real.log (primeWindow n : ℝ))) :=
        mul_le_mul_of_nonneg_left hCmul (Nat.cast_nonneg _)
      _ = (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          ((divisorBudget k n : ℝ) * Real.log (primeWindow n : ℝ)) := by ring
      _ ≤ (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          Real.log (3 * n ^ k : ℝ) := mul_le_mul_of_nonneg_left hKmul (by positivity)
      _ ≤ (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          (((k : ℝ) + 2) * (inputBits n + 1)) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by ring
  exact_mod_cast hr




































theorem windowExponent_tendsto_atTop : Tendsto windowExponent atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [natSqrt_tendsto_atTop.eventually (eventually_ge_atTop b)] with m hm
  change b ≤ Nat.sqrt m + 1
  omega

theorem bits_add_one_le_windowExponent_sq (m : ℕ) : m + 1 ≤ windowExponent m ^ 2 := by
  have h := Nat.lt_succ_sqrt' m
  simpa [windowExponent, Nat.succ_eq_add_one] using h
























































































theorem bits_over_candidateCount_tendsto_zero :
    Tendsto (fun n : ℕ => (inputBits n + 1 : ℝ) / candidateCount n) atTop (𝓝 0) := by
  have ht := windowExponent_tendsto_atTop.comp inputBits_tendsto_atTop
  have hu := ((tendsto_pow_const_div_const_pow_of_one_lt 3
    (by norm_num : (1 : ℝ) < 2)).comp ht).const_mul (4 * Real.log 2)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun n => by positivity)
  · filter_upwards [actual_candidate_density] with n hC
    have hy := primeWindow_ge_two n
    have hyl : 0 < Real.log (primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
    have hypo : (0 : ℝ) < primeWindow n := by exact_mod_cast (by omega : 0 < primeWindow n)
    have hlower : (0 : ℝ) < (primeWindow n : ℝ) / (4 * Real.log (primeWindow n)) := by positivity
    have hbits : (inputBits n + 1 : ℝ) ≤ (windowExponent (inputBits n) : ℝ) ^ 2 := by
      exact_mod_cast bits_add_one_le_windowExponent_sq (inputBits n)
    have hs : (0 : ℝ) ≤ windowExponent (inputBits n) := Nat.cast_nonneg _
    have hdiv := div_le_div_of_nonneg_left
      (by positivity : (0 : ℝ) ≤ inputBits n + 1) hlower hC
    change (inputBits n + 1 : ℝ) / candidateCount n ≤
      4 * Real.log 2 * ((windowExponent (inputBits n) : ℝ) ^ 3 /
        (2 : ℝ) ^ windowExponent (inputBits n))
    calc
      (inputBits n + 1 : ℝ) / candidateCount n ≤
          (inputBits n + 1 : ℝ) / ((primeWindow n : ℝ) / (4 * Real.log (primeWindow n))) := hdiv
      _ = ((inputBits n + 1 : ℝ) *
          (4 * (windowExponent (inputBits n) : ℝ) * Real.log 2)) /
            (2 : ℝ) ^ windowExponent (inputBits n) := by
        simp only [primeWindow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        field_simp
      _ ≤ ((windowExponent (inputBits n) : ℝ) ^ 2 *
          (4 * (windowExponent (inputBits n) : ℝ) * Real.log 2)) /
            (2 : ℝ) ^ windowExponent (inputBits n) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hbits (by positivity)
      _ = _ := by ring

theorem candidateCount_eventually_gt_multiple (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * (inputBits n + 1) < candidateCount n := by
  have hsmall := bits_over_candidateCount_tendsto_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((K : ℝ) + 1)))
  filter_upwards [hsmall, actual_candidates_nonempty] with n hn hC
  have hCpos : (0 : ℝ) < candidateCount n := by
    exact_mod_cast Finset.card_pos.mpr hC
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have h := (div_lt_div_iff₀ hCpos hKpos).mp hn
  have hNat : (inputBits n + 1) * (K + 1) < candidateCount n := by
    simpa only [one_mul] using (show (inputBits n + 1 : ℝ) * ((K : ℝ) + 1) <
      candidateCount n by simpa only [one_mul] using h) |> fun ht => by exact_mod_cast ht
  nlinarith

theorem log2_difference_bound (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Nat.log2 (3 * n ^ k) ≤ 2 * (k + 2) * (inputBits n + 1) := by
  have hl : (Nat.log2 (3 * n ^ k) : ℝ) ≤ Real.log (3 * n ^ k : ℝ) / Real.log 2 := by
    simpa [Nat.log2_eq_log_two, Real.logb] using Real.natLog_le_logb (3 * n ^ k) 2
  have hmul := (le_div_iff₀ Parameters.log_two_pos).mp hl
  have hdiff := log_difference_bound k hn
  have hk : (0 : ℝ) ≤ Nat.log2 (3 * n ^ k) := Nat.cast_nonneg _
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Parameters.log_two_lower; linarith
  have hhalf := mul_le_mul_of_nonneg_left hlog hk
  have hR : (Nat.log2 (3 * n ^ k) : ℝ) ≤ 2 * ((k : ℝ) + 2) * (inputBits n + 1) := by
    nlinarith [hhalf]
  exact_mod_cast hR

theorem actual_auxiliary_cardinality (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, Nat.log2 (3 * n ^ k) < candidateCount n := by
  filter_upwards [candidateCount_eventually_gt_multiple (2 * (k + 2)),
    eventually_ge_atTop (1 : ℕ)] with n hC hn
  exact (log2_difference_bound k (by omega)).trans_lt hC





























end

end ThreeSum.Scales

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_GlobalEncoding


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments


/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

def scheduleSize (h : ℕ) : ℕ := scheduleLength h (localPrime h)

theorem scheduleSize_eq_length (h : ℕ) : scheduleSize h = (localSchedule h).length := by
  rw [localSchedule_length]
  rfl

abbrev Occurrence (h : ℕ) := Fin (scheduleSize h)

def mapAt (h : ℕ) (i : Occurrence h) : Weight (512 * h) (LocalField h) :=
  (localSchedule h).get (Fin.cast (scheduleSize_eq_length h) i)











def Survives (h : ℕ) (i : Occurrence h) (e : Edge (512 * h) h) : Prop :=
  HashFamily.bucketSize (leftVertices (512 * h) h) (mapAt h i)
      (HashFamily.hashValue (mapAt h i) (left e)) ≤ localBucketCap h ∧
    HashFamily.bucketSize (rightVertices (512 * h) h) (mapAt h i)
      (HashFamily.hashValue (mapAt h i) (right e)) ≤ localBucketCap h

instance (h : ℕ) (i : Occurrence h) (e : Edge (512 * h) h) :
    Decidable (Survives h i e) := by unfold Survives; infer_instance

/-- A choice includes its schedule occurrence as well as its retained edge. -/
abbrev RetainedChoice (h : ℕ) :=
  {p : Occurrence h × Edge (512 * h) h // Survives h p.1 p.2}

def occurrence {h : ℕ} (c : RetainedChoice h) : Occurrence h := c.val.1
def edge {h : ℕ} (c : RetainedChoice h) : Edge (512 * h) h := c.val.2




/-- Sum of the canonical integer representatives of the selected symbol
weights. This is the raw integer sum before reduction modulo the prime. -/
def rawHash {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) : ℤ :=
  ∑ i, ((w (i, s i)).val : ℤ)



























def rawLeft {h : ℕ} (c : RetainedChoice h) : ℤ :=
  rawHash (mapAt h (occurrence c)) (left (edge c))

def rawRight {h : ℕ} (c : RetainedChoice h) : ℤ :=
  rawHash (mapAt h (occurrence c)) (right (edge c))





































































def representations (h J : ℕ) (a b : ℤ) : Finset (List (RetainedChoice h)) :=
  Radix.representations (localPrime h) rawLeft rawRight J a b

def globalModulus (h J : ℕ) : ℤ := (localPrime h : ℤ) ^ J

def representationCap (h J : ℕ) : ℕ :=
  (scheduleSize h * localBucketCap h ^ 2) ^ J





























/-- The integer difference contribution is determined by the equality
positions alone. Positions in the output subset contribute zero. -/
def rawOutput {h L : ℕ} (w : Weight L (LocalField h)) (Q : Finset (Fin L)) : ℤ :=
  ∑ i, if i ∈ Q then 0 else ((w (i, true)).val : ℤ) - ((w (i, false)).val : ℤ)












/-- An output record retains the chosen-map occurrence and the union of the
two disjoint endpoint subsets. It forgets the internal partition. -/
abbrev OutputBlock (h : ℕ) :=
  Occurrence h × {Q // Q ∈ LayerCounts.vertices (512 * h) (2 * h)}

def blockOfChoice {h : ℕ} (c : RetainedChoice h) : OutputBlock h :=
  (occurrence c, ⟨output (edge c), LayerCounts.mem_vertices.mpr (output_card (edge c))⟩)

def blockKey {h : ℕ} (b : OutputBlock h) : ℤ := rawOutput (mapAt h b.1) b.2.val










abbrev GlobalOutput (h J : ℕ) := Fin J → OutputBlock h






def globalKey {h J : ℕ} (q : GlobalOutput h J) : ℤ :=
  Radix.positionalHash (localPrime h) blockKey (List.ofFn q)


























































end ThreeSum.GlobalEncoding

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_WeightEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments


/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration

open LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]











/-- A dependent-list decoder matching `List.pi` exactly. The remaining
digits are decoded after removing the current most significant digit. -/
def decode (p : ℕ) : (l : List ι) → ℕ → (∀ i, i ∈ l → K)
  | [], _ => List.Pi.nil (fun _ => K)
  | i::l, k => List.Pi.cons i l ((k/p^l.length%p : ℕ) : K) (decode p l (k%p^l.length))

















































def liftCoordinate {L : ℕ} (i : Fin L × Bool) : Fin (L+1) × Bool := (i.1.succ,i.2)





























/-- The list order is `(0,false),(0,true),(1,false),(1,true),...`. -/
def coordinateIndex {L : ℕ} (i : Fin L × Bool) : ℕ :=
  2*i.1.val+(if i.2 then 1 else 0)































def digit (p width k coordinate : ℕ) : ℕ := k/p^(width-1-coordinate)%p

/-- The coefficient function obtained from one ordinary range index. -/
def decodedWeight (L p k : ℕ) : Weight L K :=
  fun i => (digit p (2*L) k (coordinateIndex i) : K)

























































end ThreeSum.WeightEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightRadixKeys


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists


/-!
# Complete positional-key product construction

The three fixed procedures build every product stage. Each stage has a
computed length header followed by its literal key array. The recursive
caller reads the previous header and appends Cartesian rows. Its final
array contains every record sequence, retaining repeated keys.
-/

namespace ThreeSum.LightRadixKeys

open Light RadixKeyLists

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def offset (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => offset m j+1+m^j






def space (dst m j : ℕ) : ℕ := dst+offset m j+1+m^j
def word (p U j : ℕ) : ℕ := LightRadixRows.word p U (U*(p+1)^j)

def time (m : ℕ) : ℕ → ℕ
  | 0 => 50
  | j+1 => time m j+LightRadixRows.time m (m^j)+200


















































/-- Source local keys and count, product length, radix, first output cell. -/
def body (pSelf pRows : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 2)))
    ((Light.Stmt.seq
       (.call pSelf [v 0, v 1, (Light.Expr.op Light.Op.sub) (v 2) (k 1), v 3, v 4] 5)
       (Light.Stmt.seq (.set 6 (M (v 5)))
         (Light.Stmt.seq
           (.set 7
             ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 5) (k 1))
               (v 6)))
           (Light.Stmt.seq (.store (v 7) ((Light.Expr.op Light.Op.mul) (v 1) (v 6)))
             (Light.Stmt.seq
               (.call pRows
                 [v 0, (Light.Expr.op Light.Op.add) (v 5) (k 1),
                   (Light.Expr.op Light.Op.add) (v 7) (k 1), v 1, v 6, v 3]
                 8)
               (.set 0 (v 7))))))))
    ((Light.Stmt.seq (.store (v 4) (k 1))
       (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 4) (k 1)) (k 0))
         (.set 0 (v 4)))))

variable {lim : Limits} {P : Program}























































































































end ThreeSum.LightRadixKeys

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightMaskUnion


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.MaskUnion
end ThreeSum.MaskUnion
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# General mask union and its cardinality on the bounded-word machine

The program tests each coordinate using the checked bit-deletion routine.
It constructs its own powers table, adds each new bit once, and writes the
union cardinality to one output cell. It never visits an ambient cube.
-/

namespace ThreeSum.LightMaskUnion

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion

variable {lim : Limits} {P : Program}

def roundBody (pErase : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pErase [v 0, v 9, v 3, v 0, v 5] 10)
    (Light.Stmt.seq (.call pErase [v 0, v 9, v 2, v 0, v 5] 11)
      (.ite (Light.Cond.lt (v 10) (v 3))
        (.ite (Light.Cond.lt (v 11) (v 2)) .skip
          (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.add) (v 7) (k 1)))
            (.set 8
              ((Light.Expr.op Light.Op.add) (v 8)
                (M ((Light.Expr.op Light.Op.add) (v 5) (v 9)))))))
        .skip)))

/-- Width, first cardinality and mask, second mask, cardinality output,
power-table scratch. The return value is the union mask. -/
def body (pPowers pErase : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 5, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 6)
    (Light.Stmt.seq (.set 7 (v 1))
      (Light.Stmt.seq (.set 8 (v 2))
        (Light.Stmt.seq (.for 9 (v 0) (roundBody pErase))
          (Light.Stmt.seq (.store (v 4) (v 7)) (.set 0 (v 8)))))))

def time (W : ℕ) : ℕ :=
  powTableTime (W+1)+W*(2*LightMaskErase.time W+180)+200

def Inv {W : ℕ} (μ : ℕ → ℤ) (A B : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ eB eA : ℤ,
    σ = ⟨frame [W,A.card,subsetMask A,subsetMask B,dst,work,powRet,
      (scanSet A B j).card,subsetMask (scanSet A B j),j,eB,eA],μ⟩








































































































































end ThreeSum.LightMaskUnion

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightQueryWeights


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}

def roundBody (pErase : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pErase [v 0, v 6, v 1, v 0, v 3] 7)
    (.ite (Light.Cond.lt (v 7) (v 1))
      (Light.Stmt.seq
        (.store ((Light.Expr.op Light.Op.add) (v 2) (v 5))
          (M ((Light.Expr.op Light.Op.add) (v 3) (v 6))))
        (.set 5 ((Light.Expr.op Light.Op.add) (v 5) (k 1))))
      .skip))

/-- Arguments: ambient width, query mask, output base, power scratch base. -/
def body (pPowers pErase : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 3, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 4)
    (Light.Stmt.seq (.set 5 (k 0))
      (Light.Stmt.seq (.for 6 (v 0) (roundBody pErase)) (.set 0 (v 5)))))

def time (W : ℕ) : ℕ := powTableTime (W+1)+W*(LightMaskErase.time W+100)+100

def Inv {W : ℕ} (μ : ℕ → ℤ) (Q : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,subsetMask Q,dst,work,powRet,(positions Q j).length,j,r],μ'⟩ ∧
    SegN μ' dst (selectedPowers Q j) ∧ Powers μ' work W ∧
    KeptBut μ μ' work dst W





































































































































end ThreeSum.LightQueryWeights

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPairEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A direct ordered enumeration of every local balanced row pair

First enumerate the h-subsets, then enumerate h-subsets of each complement.
The list contains every edge exactly once and has the exact local catalog
size, without scanning the ambient Boolean cube or all pairs of vertices.
-/

namespace ThreeSum.ReportingHostPairEnumeration

open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph

set_option linter.unusedSimpArgs false

def lefts (L h : ℕ) : List (Finset (Fin L)) := (enumerateLayer L h).map (MaskDecode.decode L)

def rights {L : ℕ} (S : Finset (Fin L)) (h : ℕ) : List (Finset (Fin L)) :=
  QueryCoordinates.missingSets (Finset.univ \ S) h

def pairs (L h : ℕ) : List (Finset (Fin L) × Finset (Fin L)) :=
  (lefts L h).flatMap fun S => (rights S h).map fun R => (S,R)




theorem lefts_mem {L h : ℕ} (S : Finset (Fin L)) : S ∈ lefts L h ↔ S.card = h := by
  constructor
  · intro hS
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hS
    exact MaskDecode.decode_card_layer hm
  · exact MaskDecode.decoded_layer_complete S
















@[simp] theorem rights_mem {L h : ℕ} (S R : Finset (Fin L)) :
    R ∈ rights S h ↔ R.card = h ∧ Disjoint S R := by
  rw [rights,QueryCoordinates.missingSets_mem]
  constructor
  · intro h
    refine ⟨h.2,Finset.disjoint_left.mpr ?_⟩
    intro a haS haR
    exact (Finset.mem_sdiff.mp (h.1 haR)).2 haS
  · rintro ⟨hc,hd⟩
    refine ⟨?_,hc⟩
    intro a haR
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,fun haS => Finset.disjoint_left.mp hd haS haR⟩








theorem pairs_mem {L h : ℕ} (p : Finset (Fin L) × Finset (Fin L)) :
    p ∈ pairs L h ↔ p ∈ edgeSet L h := by
  rw [LayerCounts.mem_edgeSet]
  constructor
  · intro hp
    obtain ⟨S,hS,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hp
    exact ⟨(lefts_mem S).mp hS,(rights_mem S R).mp hR⟩
  · rintro ⟨hS,hR,hd⟩
    exact List.mem_flatMap.mpr ⟨p.1,(lefts_mem p.1).mpr hS,
      List.mem_map.mpr ⟨p.2,(rights_mem p.1 p.2).mpr ⟨hR,hd⟩,rfl⟩⟩



























def leftAt (L h i : ℕ) : Finset (Fin L) := ((lefts L h)[i]?).getD ∅

def rightAt (L h i j : ℕ) : Finset (Fin L) := ((rights (leftAt L h i) h)[j]?).getD ∅






































end ThreeSum.ReportingHostPairEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SignedLeaf


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Signed leaf weights and the explicit part of sparse queries

The alternating sign is separated from the query cardinality, allowing
the same leaf weights to be used in stored boxes and direct leaf reads.
-/

namespace ThreeSum.SignedLeaf

open Finset ThreeSum.SubsetAddress
open scoped BigOperators






def value {W : ℕ} (f g : Finset (Fin W) → ℤ) (stage : ℕ)
    (preL preR S : Finset (Fin W)) : ℤ :=
  (-1 : ℤ)^S.card *
    (SubsetStages.stageValue f stage (preL ∪ S)*SubsetStages.stageValue g stage (preR ∪ S))
































/-- Missing sets in all layers strictly below `t`. -/
def explicitMissing {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) : List (Finset (Fin W)) :=
  (List.range t).flatMap (QueryCoordinates.missingSets Q)

def explicitLeaves {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) : List (Finset (Fin W)) :=
  (explicitMissing Q t).map fun U => Q \ U












































end ThreeSum.SignedLeaf

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDownsetAddress


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
# A fixed program for the complete compact downset address

The input gives a mask and its known cardinality. The program constructs
its own Pascal and power tables, computes the layer rank, scans the layer
offset, and returns their sum. No table-correctness or algorithmic runtime
premise is supplied by the caller.
-/

namespace ThreeSum.LightDownsetAddress

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def body (pFresh pOffset : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pFresh [v 0, v 1, v 2, v 3] 4)
    (Light.Stmt.seq (.call pOffset [v 3, v 0, v 1, v 0] 5)
      (.set 0 ((Light.Expr.op Light.Op.add) (v 4) (v 5)))))

def time (L : ℕ) : ℕ := LightSubsetSetup.time L + LightSubsetOffset.time L + 30





































































end ThreeSum.LightDownsetAddress

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDownsetSize


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
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: width, cutoff, polynomial scratch base. -/
def body (pSetup pOffset : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSetup [v 0, k 0, k 0, v 2] 3)
    (Light.Stmt.seq (.call pOffset [v 2, v 0, v 1, v 0] 4)
      (.set 0
        ((Light.Expr.op Light.Op.add) (v 4)
          (M
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v 2)
                ((Light.Expr.op Light.Op.mul) (v 0)
                  ((Light.Expr.op Light.Op.add) (v 0) (k 1))))
              (v 1)))))))

def time (L : ℕ) : ℕ := LightSubsetSetup.time L+LightSubsetOffset.time L+60



























































def program : Program :=
  [body 1 8,LightSubsetSetup.body 2 6 7,buildBody 3 4,fillBody,rowBody 5,
    LightArray.linearBody,powTableBody,rankBody 7,LightSubsetOffset.body]



















end ThreeSum.LightDownsetSize

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCounts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Executing the local graph counts

One constructed Pascal table and one constructed power table provide all
integer counts needed by the local hash cover. The zero-mask rank call in
the reused setup wrapper takes only linear additional time. In particular,
none of these counts is an input oracle.
-/

namespace ThreeSum.LightLocalCounts

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

open Light LocalCoverBounds LightPascal LightSubsetAddress

def values (h : ℕ) : List ℤ :=
  [outputCount (512*h) h,vertexCount (512*h) h,degree (512*h) h,
    groupSize h,2^(2*h),localThreshold h]

def body (pSetup : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.mul) (k 512) (v 0)))
    (Light.Stmt.seq (.set 4 ((Light.Expr.op Light.Op.mul) (k 2) (v 0)))
      (Light.Stmt.seq (.call pSetup [v 3, k 0, k 0, v 2] 5)
        (Light.Stmt.seq
          (.set 6
            (M
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 2)
                  ((Light.Expr.op Light.Op.mul) (v 3)
                    ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                (v 4))))
          (Light.Stmt.seq
            (.set 7
              (M
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) (v 2)
                    ((Light.Expr.op Light.Op.mul) (v 3)
                      ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                  (v 0))))
            (Light.Stmt.seq
              (.set 8
                (M
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v 2)
                      ((Light.Expr.op Light.Op.mul)
                        ((Light.Expr.op Light.Op.sub) (v 3) (v 0))
                        ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                    (v 0))))
              (Light.Stmt.seq
                (.set 9
                  (M
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add) (v 2)
                        ((Light.Expr.op Light.Op.mul) (v 4)
                          ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                      (v 0))))
                (Light.Stmt.seq
                  (.set 10
                    (M
                      ((Light.Expr.op Light.Op.add)
                        ((Light.Expr.op Light.Op.add) (v 2)
                          ((Light.Expr.op Light.Op.mul)
                            ((Light.Expr.op Light.Op.add) (v 3) (k 1))
                            ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                        (v 4))))
                  (Light.Stmt.seq
                    (.set 11 ((Light.Expr.op Light.Op.mul) (v 6) (v 10)))
                    (Light.Stmt.seq (.store (v 1) (v 6))
                      (Light.Stmt.seq
                        (.store ((Light.Expr.op Light.Op.add) (v 1) (k 1)) (v 7))
                        (Light.Stmt.seq
                          (.store ((Light.Expr.op Light.Op.add) (v 1) (k 2))
                            (v 8))
                          (Light.Stmt.seq
                            (.store ((Light.Expr.op Light.Op.add) (v 1) (k 3))
                              (v 9))
                            (Light.Stmt.seq
                              (.store ((Light.Expr.op Light.Op.add) (v 1) (k 4))
                                (v 10))
                              (Light.Stmt.seq
                                (.store ((Light.Expr.op Light.Op.add) (v 1) (k 5))
                                  (v 11))
                                (.set 0 (v 11)))))))))))))))))

def time (h : ℕ) : ℕ := LightSubsetSetup.time (512*h)+500
def space (work h : ℕ) : ℕ := work+tableSize (512*h)+(512*h+1)
def word (h : ℕ) : ℕ := 1024+4*(2^(512*h+1))^2

structure Procs (P : Program) (pMain : ℕ) where
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  main : P[pMain]? = some (body pSetup)

variable {lim : Limits} {P : Program} {d : ℕ}














































































































































end ThreeSum.LightLocalCounts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightZetaCell


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# An actual compact-table zeta-cell update

The fixed procedure builds its own Pascal and power tables, ranks the input
mask, deletes the requested coordinate, ranks the smaller mask if necessary,
and writes the zeta addition at the compact downset address. The scratch area
is polynomial in the width. Neither addresses nor table values are supplied
by an oracle.
-/

namespace ThreeSum.LightZetaCell

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Correct contents at all compact addresses within the stored downset. -/
def TableAt {L : ℕ} (μ : ℕ → ℤ) (src cut : ℕ) (f : Finset (Fin L) → ℤ) : Prop :=
  ∀ S, S.card ≤ cut → μ (src+subsetRank S) = f S

def KeptExcept (μ μ' : ℕ → ℤ) (work changed : ℕ) : Prop :=
  ∀ i < work, i ≠ changed → μ' i = μ i

/-- Arguments: width, cardinality, mask, coordinate, source, destination,
and scratch. The destination contains only `downsetCap` data cells. -/
def body (pSetup pOffset pErase pRank : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 10
      ((Light.Expr.op Light.Op.add) (v 6)
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 0) (k 1))
          ((Light.Expr.op Light.Op.add) (v 0) (k 1)))))
    (Light.Stmt.seq (.call pSetup [v 0, v 1, v 2, v 6] 7)
      (Light.Stmt.seq (.call pOffset [v 6, v 0, v 1, v 0] 8)
        (Light.Stmt.seq (.set 9 ((Light.Expr.op Light.Op.add) (v 7) (v 8)))
          (Light.Stmt.seq (.call pErase [v 0, v 3, v 2, v 0, v 10] 11)
            (.ite (Light.Cond.lt (v 11) (v 2))
              (Light.Stmt.seq
                (.call pRank
                  [v 0, (Light.Expr.op Light.Op.sub) (v 1) (k 1), v 11, v 0, v 6,
                    v 10]
                  12)
                (Light.Stmt.seq
                  (.call pOffset
                    [v 6, v 0, (Light.Expr.op Light.Op.sub) (v 1) (k 1), v 0] 13)
                  (Light.Stmt.seq
                    (.set 14 ((Light.Expr.op Light.Op.add) (v 12) (v 13)))
                    (.store ((Light.Expr.op Light.Op.add) (v 5) (v 9))
                      ((Light.Expr.op Light.Op.add)
                        (M ((Light.Expr.op Light.Op.add) (v 4) (v 9)))
                        (M ((Light.Expr.op Light.Op.add) (v 4) (v 14))))))))
              (.store ((Light.Expr.op Light.Op.add) (v 5) (v 9))
                (M ((Light.Expr.op Light.Op.add) (v 4) (v 9))))))))))

def time (L : ℕ) : ℕ := LightSubsetSetup.time L +
  LightMaskErase.time L + rankTime L + 2*LightSubsetOffset.time L + 200















































































































































end ThreeSum.LightZetaCell

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCoverGreedy


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy


/-!
# An actual exhaustive finite greedy-cover program

The candidate matrix is read-only. The routine initializes active targets,
computes every candidate score, chooses the first maximum, stores the
chosen index, and removes its covered targets. Its output is exactly the
pre-existing `Cover.greedyChoices` list, including repeated occurrences.
-/

namespace ThreeSum.LightCoverGreedy

open Light BooleanGreedy

set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

def out (activePtr rows cols : ℕ) : ℕ := activePtr+cols+rows

def total (rows cols rounds : ℕ) : ℕ := cols+rows+rounds

def roundBody (pSelect pUpdate : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSelect [v 0, v 1, v 5, v 2, v 3] 8)
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 6) (v 7)) (v 8))
      (.call pUpdate
        [(Light.Expr.op Light.Op.add) (v 0)
            ((Light.Expr.op Light.Op.mul) (v 8) (v 3)),
          v 1, v 3]
        9)))

def body (pFill pSelect pUpdate : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.add) (v 1) (v 3)))
    (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 5) (v 2)))
      (Light.Stmt.seq (.call pFill [v 1, v 3, k 1] 9)
        (Light.Stmt.seq (.for 7 (v 4) (roundBody pSelect pUpdate))
          (.set 0 (v 6))))))

def roundTime (rows cols : ℕ) : ℕ :=
  LightCoverSelect.time rows cols+LightCoverUpdate.time cols+200

def time (rows cols rounds : ℕ) : ℕ :=
  fillTime cols+rounds*(roundTime rows cols+8)+100

def Inv (μ : ℕ → ℤ) (matrix : ℕ → ℕ → ℕ)
    (src activePtr rows cols rounds i : ℕ) (σ : State) : Prop :=
  ∃ (r v : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [src,activePtr,rows,cols,rounds,activePtr+cols,out activePtr rows cols,i,r,v],μ'⟩ ∧
    (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols i j : ℤ)) ∧
    Seg μ' (out activePtr rows cols) ((choices matrix rows cols i).map (fun x : ℕ => (x : ℤ))) ∧
    SameOutside μ μ' activePtr (total rows cols rounds)

structure Procs (P : Program) (pMain : ℕ) where
  pFill : ℕ
  pSelect : ℕ
  pUpdate : ℕ
  fill : P[pFill]? = some fillBody
  select : LightCoverSelect.Procs P pSelect
  update : P[pUpdate]? = some LightCoverUpdate.body
  main : P[pMain]? = some (body pFill pSelect pUpdate)

variable {lim : Limits} {P : Program} {d : ℕ}

















































































































































end ThreeSum.LightCoverGreedy

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBucketFromHistogram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Retained code/count arrays to exact contiguous original-index buckets

This actual three-procedure program is generic in the residue code function.
It constructs prefix offsets and scatters every physical index exactly once.
The code and count arrays are retained for source stages and later joins.
-/

namespace ThreeSum.LightSourceBucketFromHistogram

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: code array, histogram, offsets, cursor scratch, flat index
output, input count, residue count. -/
def body (pOffsets pScatter : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pOffsets [v 1, v 2, v 3, v 6, v 5] 7)
    (.call pScatter [v 0, v 3, v 4, v 5, v 6] 7))

def time (N M : ℕ) : ℕ :=
  LightSourceBucketOffsets.time M+LightSourceBucketScatter.time N+80

structure Procs (P : Program) (pMain : ℕ) where
  pOffsets : ℕ
  pScatter : ℕ
  offsets : P[pOffsets]? = some LightSourceBucketOffsets.body
  scatter : P[pScatter]? = some LightSourceBucketScatter.body
  main : P[pMain]? = some (body pOffsets pScatter)

variable {lim : Limits} {P : Program} {d : ℕ}















































end ThreeSum.LightSourceBucketFromHistogram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_WantedPairs


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs

open Light SourceBuckets
open scoped BigOperators

set_option maxHeartbeats 1200000

def count (left right : ℕ → ℕ) (NR NL : ℕ) : ℕ :=
  ∑ i ∈ Finset.range NL, LightHistogram.count right (left i) NR












def row (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  (SourceBucketView.indices μ offsets flat (left i)).map (fun j => (i,j))

def pairs (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (row μ offsets flat left)






























































def cells (ps : List (ℕ × ℕ)) : List ℤ := ps.flatMap (fun p => [p.1,p.2])

theorem cells_length (ps : List (ℕ × ℕ)) : (cells ps).length=2*ps.length := by
  induction ps with
  | nil => simp [cells]
  | cons p ps ih => simp only [cells,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega











































































end ThreeSum.WantedPairs

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ColorScan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters


/-! # Correctness of a prefix of the literal coloring family -/

namespace ThreeSum.ColorScan

open ColorParameters

def Hit {n : ℕ} (x : Fin n → ℤ) (W t : ℕ) : Prop :=
  ∃ i, ∃ hi : i < count W, i < t ∧ ColorClassLists.witness (parameter hi) x































end ThreeSum.ColorScan

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorClasses


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists


/-!
# Original-array construction of all three color classes

A fixed six-procedure program builds the color array and extracts three
disjoint output segments with length headers. The third class is negated.
Original values and their multiplicities are kept until class normalization.
-/

namespace ThreeSum.LightColorClasses

open Light ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Source, length, binary width, two coordinates, four map entries,
color-array output, three class headers, scratch. -/
def body (pColors pFilter : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pColors [v 2, v 1, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 13] 14)
    (Light.Stmt.seq (.call pFilter [v 0, v 9, v 10, v 1, k 0, k 1] 14)
      (Light.Stmt.seq (.call pFilter [v 0, v 9, v 11, v 1, k 1, k 1] 14)
        (.call pFilter
          [v 0, v 9, v 12, v 1, k 2, (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
          14))))

def time (W n : ℕ) : ℕ := LightColorArray.time W n+3*LightClassFilter.time n+200

structure Output {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (μ ν : ℕ → ℤ) (colors dst0 dst1 dst2 : ℕ) : Prop where
  colorValues : ∀ i < n, ν (colors+i) = (LightColorIndex.color p i : ℤ)
  header0 : ν dst0 = ((classList p x 0 1).length : ℤ)
  values0 : Seg ν (dst0+1) (classList p x 0 1)
  header1 : ν dst1 = ((classList p x 1 1).length : ℤ)
  values1 : Seg ν (dst1+1) (classList p x 1 1)
  header2 : ν dst2 = ((classList p x 2 (-1)).length : ℤ)
  values2 : Seg ν (dst2+1) (classList p x 2 (-1))
  kept : Kept μ ν colors

structure Procs (P : Program) (pMain : ℕ) where
  pColors : ℕ
  pPowers : ℕ
  pColor : ℕ
  pErase : ℕ
  pFilter : ℕ
  colors : P[pColors]? = some (LightColorArray.body pPowers pColor)
  powers : P[pPowers]? = some powTableBody
  color : P[pColor]? = some (LightColorIndex.body pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  filter : P[pFilter]? = some LightClassFilter.body
  main : P[pMain]? = some (body pColors pFilter)

variable {lim : Limits} {P : Program} {d : ℕ}











































































































end ThreeSum.LightColorClasses

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingLeaf


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Executable residue selection and original-value leaf decision

The host reduces the two actual endpoint values, selects the independently
trimmed physical buckets, and tests original values. Its Boolean result has
a memory-independent physical-index specification, suitable for sequential
candidate batching with the exact sum of the selected pair costs.
-/

namespace ThreeSum.LightReportingLeaf

open Light SourceBuckets LightResidues ReportingHostBucketTest

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def Hit (a xL xR : ℤ) (left right : ℕ→ℤ) (keyL keyR : ℕ→ℕ)
    (NL NR Mo flagL flagR : ℕ) : Prop :=
  flagL=1 ∧ flagR=1 ∧ ∃ i<NL, ∃ j<NR,
    keyL i=residue Mo 1 xL ∧ keyR j=residue Mo 1 xR ∧ right j-left i-a=0

def body (pEmod pTest : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pEmod [v 5, v 13, (Light.Expr.op Light.Op.add) (v 14) (k 4)] 15)
    (Light.Stmt.seq
      (.call pEmod [v 9, v 13, (Light.Expr.op Light.Op.add) (v 14) (k 4)] 16)
      (Light.Stmt.seq
        (.call pTest
          [v 0, v 1, v 2, v 3, v 4, v 15, v 6, v 7, v 8, v 16, v 10, v 11, v 12,
            v 13, v 14]
          17)
        (.ite (Light.Cond.lt (k 0) (v 17)) (.set 0 (k 1)) (.set 0 (k 0))))))

def program : Program := LightReportingBucketTest.program ++ [emodBody,body 4 3]

def time (keyL keyR : ℕ→ℕ) (NL NR Mo flagL flagR U : ℕ) (xL xR : ℤ) : ℕ :=
  LightReportingBucketTest.time keyL keyR NL NR (residue Mo 1 xL) (residue Mo 1 xR) flagL flagR+
    2*residueBudget U+300












variable {lim : Limits}


















































































end ThreeSum.LightReportingLeaf

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBruteThreeSum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# A complete original-input solver for the finite exceptional sizes

This four-procedure program checks every original-position triple and all
three inequalities between its indices. Its time is polynomial but is not
the target subquadratic bound. It supplies the exact fallback needed before
the asymptotic parameter regime, with no hypothesis on the integer values
beyond the task's given magnitude bound.
-/

namespace ThreeSum.LightBruteThreeSum

open Light ThreeSumApsp.Spec

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 4
      ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (v 0) (v 0))
        (v 0)))
    (.call pScan [v 2, v 0, v 4] 0))

def time (n : ℕ) : ℕ := LightOriginalTripleScan.time n (n^3)+100

def need (n U : ℕ) : Need :=
  ⟨LightOriginalTripleRow.word n U,0,n^3+3⟩

def program : Program := LightOriginalTripleScan.program ++ [body 2]



variable {lim : Limits} {P : Program}
































































end ThreeSum.LightBruteThreeSum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceMaskFlags


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct


/-!
# Constructing independent endpoint flags directly from a global mask

The fixed program creates its own powers and Boolean coordinate row, then
performs the actual selected-block trimming scan. There is no Boolean-bit or
trim-flag oracle in the contract.
-/

namespace ThreeSum.LightSourceMaskFlags

open Light SourceFlagProduct

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- Arguments: block count, width, row size, local modulus, cap, occurrence
indices, schedule coefficients, occurrence-to-candidate indices, both
candidate histograms, global mask, output, bit scratch, row scratch,
and reusable arithmetic scratch. -/
def body (pBits pTrim : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pBits [(Light.Expr.op Light.Op.mul) (v 0) (v 1), v 10, v 12, v 14] 15)
    (.call pTrim
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 12, v 13, v 14, v 11]
      15))

def time (J L U : ℕ) : ℕ := LightMaskBits.time (J*L)+LightSourceTrim.time J L U+100

def word (J L p U V cap : ℕ) : ℕ := 2^(J*L+1)+LightSourceRowFlag.word L p U V cap

def space (work J L U : ℕ) : ℕ :=
  work+max (J*L+1) (3+(Nat.log 2 (L*U+1)+2))

structure Procs (P : Program) (pMain : ℕ) where
  pBits : ℕ
  pPowers : ℕ
  pErase : ℕ
  pTrim : ℕ
  bits : P[pBits]? = some (LightMaskBits.body pPowers pErase)
  powers : P[pPowers]? = some powTableBody
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  trim : LightSourceTrim.Procs P pTrim
  main : P[pMain]? = some (body pBits pTrim)

variable {lim : Limits} {P : Program} {d : ℕ}














































































































end ThreeSum.LightSourceMaskFlags

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LocalMaskHashes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph


/-!
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes

open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds

variable {h L k : ℕ}

def coeff (b : Bool) (w : Weight L (LocalField h)) : ℕ → ℕ :=
  OneHotMask.extend (fun i => (w (i,b)).val)






def leftCode (w : Weight L (LocalField h)) (k i : ℕ) : ℕ :=
  LightHashHistogram.code L (localPrime h) (maskAt L k) (coeff false w) (coeff true w) i

def rightCode (w : Weight L (LocalField h)) (k i : ℕ) : ℕ :=
  LightHashHistogram.code L (localPrime h) (maskAt L k) (coeff true w) (coeff false w) i



















































































end ThreeSum.LocalMaskHashes

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalKeys


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Complete occurrence-by-output local key array

The loop reads the two stored coefficient rows for each schedule occurrence,
constructs every signed local output key, and copies that row into the final
contiguous array. It reuses the row scratch and preserves earlier rows.
-/

namespace ThreeSum.LightLocalKeys

open Light

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

/-- Width, masks, masks per row, packed coefficient rows, occurrences, output, free. -/
def body (pRow pCopy : ℕ) : Stmt :=
  .for 7 (v 4) (
    (Light.Stmt.seq
      (.call pRow
        [v 0, v 1, v 2,
          (Light.Expr.op Light.Op.add) (v 3)
            ((Light.Expr.op Light.Op.mul) (v 7)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 0))),
          (Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v 3)
              ((Light.Expr.op Light.Op.mul) (v 7)
                ((Light.Expr.op Light.Op.mul) (k 2) (v 0))))
            (v 0),
          v 6]
        8)
      (.call pCopy
        [v 8,
          (Light.Expr.op Light.Op.add) (v 5)
            ((Light.Expr.op Light.Op.mul) (v 7) (v 2)),
          v 2]
        9)))

def time (L n rows : ℕ) : ℕ := rows*(LightLocalKeyRow.time L n+copyTime n+130)+20
def word (L U rows : ℕ) : ℕ := LightLocalKeyRow.word L U+rows+2*L+1

def Inv (μ : ℕ → ℤ) (L masks n maps rows dst free : ℕ)
    (mask : ℕ → ℕ) (wFalse wTrue : ℕ → ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r s : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [L,masks,n,maps,rows,dst,free,j,r,s],ν⟩ ∧
    (∀ k < j, ∀ i < n, ν (dst+k*n+i)=
      (OneHotMask.eval (wTrue k) (fun _ => 0) L (mask i) : ℤ)-
      (OneHotMask.eval (wFalse k) (fun _ => 0) L (mask i) : ℤ)) ∧ Kept μ ν dst

structure Procs (P : Program) (pMain : ℕ) where
  pRow : ℕ
  pCopy : ℕ
  main : P[pMain]? = some (body pRow pCopy)
  row : LightLocalKeyRow.Procs P pRow
  copy : P[pCopy]? = some copyBody

variable {lim : Limits} {P : Program} {d : ℕ}










































































































end ThreeSum.LightLocalKeys

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceOccurrenceArray


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder


/-!
# Actual big-endian occurrence-vector array

The finite loop decodes each physical bank index once, using the verified
logarithmic quotient routine. Its contiguous rows contain exactly J radix
digits. The shared source catalog consumes these rows without supplying an
enumeration oracle or running a loop over output subsets.
-/

namespace ThreeSum.LightSourceOccurrenceArray

open Light OutputDecodeOrder

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pDigits : ℕ) : Stmt :=
  .for 5 (v 0) (
    .call pDigits [v 5,v 1,v 2,((Light.Expr.op Light.Op.add) (v 3) ((Light.Expr.op Light.Op.mul) (v 5) (v 1))),v 4] 6)

def time (N J : ℕ) : ℕ := N*(LightOutputDecodeDigits.time J N+150)+10

def Inv (μ : ℕ → ℤ) (N J m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,J,m,dst,work,i,r],ν⟩ ∧
    (∀ j < i, ∀ s < J, ν (dst+j*J+s)=((indices m J j).getD s 0 : ℤ)) ∧
    Kept μ ν dst

variable {lim : Limits} {P : Program} {d : ℕ}















































































end ThreeSum.LightSourceOccurrenceArray

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOutputDecode


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Complete physical output-index decoding

The first pass writes the actual big-endian local-record digit array.
The second pass splits each digit, reads its retained layer mask, and
accumulates the occurrence-only source-bank code. Both output rows are
in forward original block order, including repeated record values.
-/

namespace ThreeSum.LightOutputDecode

open Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

def body (pDigits pStep : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.mul) (v 2) (v 3)))
    (Light.Stmt.seq (.call pDigits [v 0, v 1, v 7, v 5, v 6] 8)
      (Light.Stmt.seq (.set 9 (k 0))
        (Light.Stmt.seq (.set 10 (k 1))
          (Light.Stmt.seq
            (.for 11 (v 1)
              (Light.Stmt.seq
                (.set 12
                  (M
                    ((Light.Expr.op Light.Op.sub)
                      ((Light.Expr.op Light.Op.sub)
                        ((Light.Expr.op Light.Op.add) (v 5) (v 1)) (k 1))
                      (v 11))))
                (Light.Stmt.seq
                  (.call pStep
                    [v 12, v 2, v 3, v 4, v 9, v 10,
                      (Light.Expr.op Light.Op.sub)
                        ((Light.Expr.op Light.Op.sub)
                          ((Light.Expr.op Light.Op.add) (v 5) (v 1)) (k 1))
                        (v 11),
                      (Light.Expr.op Light.Op.sub)
                        ((Light.Expr.op Light.Op.sub)
                          ((Light.Expr.op Light.Op.add)
                            ((Light.Expr.op Light.Op.add) (v 5) (v 1)) (v 1))
                          (k 1))
                        (v 11),
                      v 6]
                    9)
                  (.set 10 ((Light.Expr.op Light.Op.mul) (v 10) (v 2))))))
            (.set 0 (v 9)))))))

def time (J V : ℕ) : ℕ :=
  LightOutputDecodeDigits.time J V+J*(LightOutputDecodeStep.time V+100)+100

def word (V T M J U : ℕ) : ℕ := 32*(V+T*M+T+M+J+T^J+U+10)

def space (work V : ℕ) : ℕ := work+(Nat.log 2 (V+1)+2)

def Inv (μ : ℕ → ℤ) (k J T M masks dst work : ℕ) (q : ℤ)
    (f : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [k,J,T,M,masks,dst,work,T*M,q,
      OutputDecodeOccurrenceCode.code T M i k,T^i,i,x],ν⟩ ∧
    (∀ j, i ≤ j → j < J →
      ν (dst+J-1-j)=(((k/(T*M)^j)%(T*M) : ℕ) : ℤ)) ∧
    (∀ j < i,
      ν (dst+J-1-j)=(((k/(T*M)^j)%(T*M)/M : ℕ) : ℤ) ∧
      ν (dst+J+J-1-j)=(f ((k/(T*M)^j)%(T*M)%M) : ℤ)) ∧
    Kept μ ν dst

structure Procs (P : Program) (pMain : ℕ) where
  pDigits : ℕ
  pStep : ℕ
  pDivide : ℕ
  digits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide)
  step : P[pStep]?=some (LightOutputDecodeStep.body pDivide)
  divide : P[pDivide]?=some LightOutputDecodeDivide.body
  main : P[pMain]?=some (body pDigits pStep)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J T M masks dst work V U : ℕ} {f : ℕ → ℕ}








































































































































def program : Program :=
  [body 1 2,LightOutputDecodeDigits.body 3,
    LightOutputDecodeStep.body 3,LightOutputDecodeDivide.body]























end ThreeSum.LightOutputDecode

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBalancedOffset


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
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset

open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators

def offset {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : ℕ :=
  LightMinimum.least (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) p

















def body (pCyclic pMinimum : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCyclic [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 7)
    (.call pMinimum [v 4, v 6] 0))

def time (k p : ℕ) : ℕ :=
  LightCyclic.combinedTime k p + LightMinimum.time p + 100

variable {lim : Limits} {P : Program} {d : ℕ}






































































end ThreeSum.LightBalancedOffset

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightModuloCounts


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
# A complete modular triple-counting procedure

Starting with three arrays of original signed integers and a positive modulus,
this fixed procedure computes its own power-of-two capacity, builds two padded
histograms, multiplies them with Karatsuba, folds the product into a correlation,
and looks up the residues of the A array. The result is exactly the modular
triple count used by the prime-score construction, including all multiplicities.
-/

namespace ThreeSum.LightModuloCounts

open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Arguments: A, B, C, their three lengths, modulus, maximum length, scratch.
Local 9 holds the computed capacity; 10--14 are scratch-region pointers. -/
def body (pCapacity pHist pCyclic pResidues pLookup : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCapacity [v 6] 9)
    (Light.Stmt.seq (.set 10 ((Light.Expr.op Light.Op.add) (v 8) (v 9)))
      (Light.Stmt.seq
        (.set 11
          ((Light.Expr.op Light.Op.add) (v 8)
            ((Light.Expr.op Light.Op.mul) (k 2) (v 9))))
        (Light.Stmt.seq
          (.set 12
            ((Light.Expr.op Light.Op.add) (v 8)
              ((Light.Expr.op Light.Op.mul) (k 3) (v 9))))
          (Light.Stmt.seq
            (.set 13
              ((Light.Expr.op Light.Op.add) (v 8)
                ((Light.Expr.op Light.Op.mul) (k 5) (v 9))))
            (Light.Stmt.seq (.set 14 ((Light.Expr.op Light.Op.add) (v 13) (v 7)))
              (Light.Stmt.seq
                (.call pHist
                  [v 1, v 11, v 4, v 6, v 9, v 13, v 14,
                    (Light.Expr.op Light.Op.sub) (k 0) (k 1)]
                  15)
                (Light.Stmt.seq
                  (.call pHist [v 2, v 10, v 5, v 6, v 9, v 13, v 14, k 1] 15)
                  (Light.Stmt.seq
                    (.call pCyclic [v 9, v 10, v 11, v 12, v 8, v 14, v 6] 15)
                    (Light.Stmt.seq
                      (.call pResidues [v 0, v 13, v 3, v 6, v 14, k 1] 15)
                      (.call pLookup [v 13, v 8, v 3, v 6] 0)))))))))))

def time (p nA nB nC U : ℕ) : ℕ :=
  LightCapacity.time p + LightResidueHistogram.time nB (capacity p) U +
    LightResidueHistogram.time nC (capacity p) U +
    LightCyclic.combinedTime (Nat.clog 2 p) p +
    residuesTime nA U + LightLookupSum.time nA + 400

def space (free p N U : ℕ) : ℕ :=
  free + 13 * capacity p + N + Nat.log 2 (U+1) + 2

def word (p N U : ℕ) : ℕ :=
  LightKaratsuba.wordBound (capacity p) N + 4*U + 4*p + 16 + N^3

























































































































































/-- Every procedure reference is tied to concrete syntax, including the
recursive multiplication closure. This structure contains no semantic oracle. -/
structure Procs (P : Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pCyclic : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pFill : ℕ
  pLookup : ℕ
  main : P[pMain]? = some (body pCapacity pHist pCyclic pResidues pLookup)
  capacity : P[pCapacity]? = some LightCapacity.body
  hist : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  histogram : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  cyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear)
  multiply : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  lookup : P[pLookup]? = some LightLookupSum.body


































































end ThreeSum.LightModuloCounts

end


