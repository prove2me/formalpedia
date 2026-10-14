-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle08
-- name    : ThreeSum1962Source_Bundle08
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:12:29.123531+00:00
-- url     : https://prove2.me/theorems/a4fb2f26-59ca-48cf-a8ee-2cfd07b7816b
-- title:
--   Rounded band scales, physical incidence domains, and transform passes
-- statement:
--   This bundle defines the rounded band size from the typed output count $T(n)$ and total inner size $\mu(n)$:
--   $$
--   g(n)=\left\lceil\frac{\lceil\sqrt{T(n)}\rceil}{2^{\lfloor\mu(n)/20\rfloor}}\right\rceil.
--   $$
--   It introduces owner-indexed A-incidence products, storage predicates for parallel incidence arrays, original-band sources, weighted modular scores, and raw encoding witnesses retaining original indices, arithmetic lifts, and schedule occurrences. Further objects include the integer cubic switch, trimmed-bucket scales, ordered global output records, and representation caps. Light bodies specify normalization with endpoint headers, execution of size parameters, query-subset enumeration, compact stage lookups, and layer-by-layer zeta passes, together with their resource expressions.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAIndex.lean#L18-L22
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAMemory.lean#L12-L16
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAProduct.lean#L21-L77
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAScore.lean#L19-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandScales.lean#L16-L58
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ColorBandBounds.lean#L12-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorWantedConsumerRetention.lean#L18-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ExplicitLayers.lean#L26-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/GlobalKeyEnumeration.lean#L23-L118
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandCandidatesRow.lean#L12-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorParametersCosts.lean#L10-L10
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDenseCap.lean#L15-L89
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightGlobalSizes.lean#L22-L176
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightHeaderBands.lean#L20-L37
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightQueryEnumeration.lean#L17-L75
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightScales.lean#L56-L187
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSortedBands.lean#L24-L61
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightStageLookup.lean#L20-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSwitchCosts.lean#L11-L12
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightRow.lean#L19-L32
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightZetaBatch.lean#L21-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightZetaPass.lean#L21-L52
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RawIncidences.lean#L25-L335
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPairSegments.lean#L37-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsWantedIndices.lean#L21-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandData.lean#L10-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandPartition.lean#L9-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Switch.lean#L20-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/TrimScales.lean#L17-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WeightedScore.lean#L17-L30

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ColorBandBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition


/-! # Uniform band resources for three classes whose lengths sum to n -/

namespace ThreeSum.ColorBandBounds

open BandPartition

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def count (n g : ℕ) : ℕ := 3*(size n g)^2
def width (n g : ℕ) : ℕ := LightBandEnumeration.width (size n g) (size n g) (size n g)
def time (n g : ℕ) : ℕ :=
  2100*(n+1)*(Nat.clog 2 n+1)+1000*(count n g+n+1)*(width n g+1)+400
def space (work n g : ℕ) : ℕ := work+n+count n g+width n g+1
def word (n g U : ℕ) : ℕ := n+g+2+
  LightBandEnumeration.word (size n g) (size n g) (size n g) U
def depth (n g : ℕ) : ℕ := n+Nat.clog 2 n+width n g+10












































end ThreeSum.ColorBandBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightHeaderBands


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration


/-!
# Running the owner tables directly from constructed class headers

This wrapper reads the three stored distinct-value lengths and band counts.
All six endpoint pointers and all three counts passed to the owner-table
program are therefore obtained by actual RAM expressions.
-/

namespace ThreeSum.LightHeaderBands

open Light ThreeSum.BandEnumeration

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : Limits} {P : Program}

def At (μ : ℕ → ℤ) (header n : ℕ) (A : Family) : Prop :=
  μ header = (n : ℤ) ∧ μ (header+1) = (A.size : ℤ) ∧
    LightBandEnumeration.At μ (header+2) (header+2+n) A

/-- Arguments: three endpoint-header addresses and output address. -/
def body (pEnumerate : ℕ) : Stmt :=
  .call pEnumerate
    [((Light.Expr.op Light.Op.add) (v 0) (k 2)),((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 0) (k 2))
                                                  (M (v 0))),
      ((Light.Expr.op Light.Op.add) (v 1) (k 2)),((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 1) (k 2))
                                                   (M (v 1))),
      ((Light.Expr.op Light.Op.add) (v 2) (k 2)),((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 2) (k 2))
                                                   (M (v 2))),
      M (((Light.Expr.op Light.Op.add) (v 0) (k 1))),M (((Light.Expr.op Light.Op.add) (v 1) (k 1))),M (((Light.Expr.op Light.Op.add) (v 2) (k 1))),v 3] 0

def time (a b c : ℕ) : ℕ := LightBandEnumeration.time a b c+100

structure Procs (P : Program) (pMain : ℕ) where
  pEnumerate : ℕ
  enumerate : LightBandEnumeration.Procs P pEnumerate
  main : P[pMain]? = some (body pEnumerate)


















































end ThreeSum.LightHeaderBands

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandCandidatesRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-! # One actual row of flagged band-owner records -/

namespace ThreeSum.LightBandCandidatesRow

open Light BandCandidateRows

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

def body (pCell : ℕ) : Stmt :=
  .for 4 (v 2) (
    (Light.Stmt.seq (.set 5 (M ((Light.Expr.op Light.Op.add) (v 0) (v 4))))
      (.call pCell
        [v 5, v 3, v 4,
          (Light.Expr.op Light.Op.add) (v 1)
            ((Light.Expr.op Light.Op.mul) (k 4) (v 4))]
        6)))

def time (n : ℕ) : ℕ := n*(LightBandCandidatesCell.time+100)+6

def Inv (μ : ℕ → ℤ) (mode : Mode) (f : ℕ → ℕ)
    (src dst n outer j : ℕ) (σ : State) : Prop :=
  ∃ (x r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [src,dst,n,outer,j,x,r],ν⟩ ∧
    (∀ k < j, Seg ν (dst+4*k) (make mode outer k (f k)).cells) ∧
    SameOutside μ ν dst (4*n)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst n outer U : ℕ} {f : ℕ → ℕ}


















































end ThreeSum.LightBandCandidatesRow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAIndex


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

def labelAt (n g : ℕ) (rs : List Record) (i : ℕ) : Label :=
  (items n g rs).getD i default

def ownerRecord (n g : ℕ) (rs : List Record) (i : ℕ) : Record :=
  rs.getD (labelAt n g rs i).owner default



































































































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAMemory


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-! # The three retained parallel arrays of A-value incidences -/

namespace ThreeSum.BandRawA

open Light BandCandidateRows

set_option maxHeartbeats 1400000

structure Stored (μ : ℕ → ℤ) (vals owners positions : ℕ)
    (f : ℕ → ℤ) (ls : List Label) : Prop where
  valueRows : Seg μ vals (values f ls)
  ownerRows : Seg μ owners (ownerLabels ls)
  positionRows : Seg μ positions (positionLabels ls)














































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAProduct


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

def aIndices (n g : ℕ) (rs : List Record) (s : ℕ) : Finset ℕ :=
  (range (row n g s (rs.getD s default)).length).image (fun j => count n g rs s+j)

def bandPositions (n g a : ℕ) : Finset ℕ :=
  (range (bandLength n g a)).image (fun j => BandPartition.start g a+j)

def ownerProduct (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  aIndices nA g rs s ×ˢ (bandPositions nB g (rs.getD s default).b ×ˢ
    bandPositions nC g (rs.getD s default).c)

def allProducts (nA nB nC g : ℕ) (rs : List Record) : Finset (ℕ × ℕ × ℕ) :=
  (range rs.length).biUnion (ownerProduct nA nB nC g rs)






























theorem mem_bandPositions {n g a p : ℕ} :
    p ∈ bandPositions n g a ↔
      BandPartition.start g a ≤ p ∧ p < BandPartition.stop n g a := by
  constructor
  · intro hp
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hp
    have hj' : j < bandLength n g a := mem_range.mp hj
    unfold bandLength at hj'
    omega
  · rintro ⟨hs,he⟩
    exact mem_image.mpr ⟨p-BandPartition.start g a,
      mem_range.mpr (by unfold bandLength; omega),by omega⟩

theorem bandPositions_lt {n g a p : ℕ} (hp : p ∈ bandPositions n g a) : p < n :=
  (mem_bandPositions.mp hp).2.trans_le (BandPartition.stop_le n g a)






































































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAScore


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

def valueAt (n g : ℕ) (rs : List Record) (A : ℕ → ℤ) (i : ℕ) : ℤ :=
  (values A (items n g rs)).getD i 0






























































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSortedBands


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition


/-!
# Normalizing one color class and constructing all its band endpoints

This closed eleven-procedure program joins the actual merge sort, adjacent
deduplication, quotient computation, and endpoint passes. It writes the
distinct-value length and band count in a two-cell header. The following
cells are the lower endpoints and, after the distinct-value length, the
upper endpoints. The membership witness still refers to the original class.
-/

namespace ThreeSum.LightSortedBands

open Light ThreeSum.BandPartition

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : Limits} {P : Program}

theorem getD_strict {L : List ℤ} (hs : L.Pairwise (· < ·)) :
    ∀ i j, i < j → j < L.length → L.getD i 0 < L.getD j 0 := by
  intro i j hij hj
  rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hs i j (by omega) hj hij

def Prepared (μ : ℕ → ℤ) (values endpoints g : ℕ) (original : List ℤ) : Prop :=
  ∃ L : List ℤ,
    Seg μ values L ∧ L.Pairwise (· < ·) ∧ L.length ≤ original.length ∧
    (∀ z, z ∈ L ↔ z ∈ original) ∧
    μ endpoints = (L.length : ℤ) ∧ μ (endpoints+1) = (size L.length g : ℤ) ∧
    (∀ i < size L.length g, μ (endpoints+2+i) = L.getD (start g i) 0) ∧
    (∀ i < size L.length g, μ (endpoints+2+L.length+i) = L.getD (stop L.length g i-1) 0)

/-- Arguments: class source and length, band size, values output, endpoint
header, merge scratch. -/
def body (pNormalize pPartition : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pNormalize [v 0, v 1, v 3, v 5] 6)
    (Light.Stmt.seq
      (.call pPartition [v 3, v 6, v 2, (Light.Expr.op Light.Op.add) (v 4) (k 2)]
        7)
      (Light.Stmt.seq (.store (v 4) (v 6))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 4) (k 1)) (v 7))
          (.set 0 (v 7))))))

def time (n : ℕ) : ℕ := LightNormalize.time n+200*n+300
def space (work n : ℕ) : ℕ := work+n

structure Procs (P : Program) (pMain : ℕ) where
  pNormalize : ℕ
  pPartition : ℕ
  pDivide : ℕ
  pLower : ℕ
  pUpper : ℕ
  normalize : LightNormalize.Procs P pNormalize
  partition : P[pPartition]? = some (LightBandPartition.body pDivide pLower pUpper)
  divide : P[pDivide]? = some LightSmallDivide.body
  lower : P[pLower]? = some LightBandPartition.lowerBody
  upper : P[pUpper]? = some LightBandPartition.upperBody
  main : P[pMain]? = some (body pNormalize pPartition)



















































































































































































end ThreeSum.LightSortedBands

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout


/-! # Retained original-band headers, histograms, and physical position fibers -/

namespace ThreeSum.SourceBandData

open Light BandPartition SourceBandLayout

structure At (μ : ℕ → ℤ) (f : ℕ → ℤ) (base n g p m : ℕ) (shift : ℤ) (i : ℕ) : Prop where
  headStart : μ (base+6*i) = (start g i : ℤ)
  headLength : μ (base+6*i+1) = (len n g i : ℤ)
  headCodes : μ (base+6*i+2) = (codes base n g m i : ℤ)
  headHist : μ (base+6*i+3) = (hist base n g m i : ℤ)
  headOffsets : μ (base+6*i+4) = (offsets base n g m i : ℤ)
  headFlat : μ (base+6*i+5) = (flat base n g m i : ℤ)
  codesRead : ∀ j < len n g i, μ (codes base n g m i+j) = (key f g p m shift i j : ℤ)
  histRead : ∀ r < m, μ (hist base n g m i+r) = (LightHistogram.count (key f g p m shift i) r (len n g i) : ℤ)
  buckets : SourceBuckets.Stored μ (key f g p m shift i) (len n g i) m
    (offsets base n g m i) (flat base n g m i)































































































end ThreeSum.SourceBandData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandPartition


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout


/-! # Exact finite original-position sources for real and padded bands -/

namespace ThreeSum.SourceBandPartition

open BandPartition SourceBandLayout

def source (n g i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => start g i ≤ t.val ∧ t.val < stop n g i)

theorem mem_source {n g i : ℕ} {t : Fin n} :
    t ∈ source n g i ↔ start g i ≤ t.val ∧ t.val < stop n g i := by
  simp only [source,Finset.mem_filter,Finset.mem_univ,true_and]

theorem physical_lt {n g i j : ℕ} (hj : j < len n g i) : start g i+j < n := by
  have hs := stop_le n g i
  unfold len at hj
  omega

def equiv (n g i : ℕ) : Fin (len n g i) ≃ source n g i where
  toFun j := ⟨⟨start g i+j.val,physical_lt j.isLt⟩,mem_source.mpr
    ⟨by change start g i ≤ start g i+j.val; omega,
      by change start g i+j.val < stop n g i
         have hj := j.isLt
         unfold len at hj
         omega⟩⟩
  invFun t := ⟨t.val.val-start g i,by
    obtain ⟨hlo,hhi⟩ := mem_source.mp t.property
    unfold len
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    omega
  right_inv t := by
    apply Subtype.ext
    apply Fin.ext
    obtain ⟨hlo,hhi⟩ := mem_source.mp t.property
    simp only
    omega







































end ThreeSum.SourceBandPartition

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_WeightedScore


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli


/-!
# Array-order identities for the weighted modular score

The auxiliary primes are read in a fixed array order.  Every partial
correction is at most the initial `s * N_q`, so the corresponding machine
subtractions stay nonnegative.  Shared factors with `q` use `joint`.
-/

namespace ThreeSum.WeightedScore

open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

def auxiliarySet (primes : ℕ → ℕ) (s : ℕ) : Finset ℕ :=
  (range s).image primes

def corrections (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) : ℕ :=
  ∑ j ∈ range i, count (joint q (primes j)) nA nB nC a b c

def remaining (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) : ℕ :=
  s * count q nA nB nC a b c - corrections primes q nA nB nC a b c i

def score (primes : ℕ → ℕ) (s q nA nB nC : ℕ) (a b c : ℕ → ℤ) : ℕ :=
  weightedFalseCount (triples nA nB nC) (difference a b c)
    (Auxiliary.moduli (auxiliarySet primes s)) q

















































































































end ThreeSum.WeightedScore

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^(mu/20)`. Since the block schedule
has `20 ∣ mu`, the denominator exponent has no divisibility error.
-/

namespace ThreeSum.BandScales

open Filter Real ThreeSum.Scales
open scoped Topology

def bandRoot (n : ℕ) : ℕ := LocalCoverBounds.rootCeiling (typedOutputs n)

def bandDivisor (n : ℕ) : ℕ := 2 ^ (mu n / 20)

def bandSize (n : ℕ) : ℕ := bandRoot n ⌈/⌉ bandDivisor n









theorem bandRoot_pos (n : ℕ) : 0 < bandRoot n := LocalCoverBounds.rootCeiling_pos _

theorem bandDivisor_pos (n : ℕ) : 0 < bandDivisor n := by
  unfold bandDivisor
  positivity

theorem bandSize_mul_bounds (n : ℕ) :
    bandRoot n ≤ bandDivisor n * bandSize n ∧
      bandDivisor n * bandSize n < bandRoot n + bandDivisor n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := bandDivisor n) (b := bandRoot n)
      (c := bandSize n) (bandDivisor_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (bandRoot n + bandDivisor n - 1) (bandDivisor n)
    simp only [bandSize, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (bandDivisor n)]
    have hpos := bandDivisor_pos n
    omega

theorem bandSize_pos (n : ℕ) : 0 < bandSize n := by
  have hl := (bandSize_mul_bounds n).1
  have hp := bandRoot_pos n
  by_contra h
  have hb : bandSize n = 0 := by omega
  rw [hb, Nat.mul_zero] at hl
  omega

noncomputable section

def unroundedBand (n : ℕ) : ℝ := (bandRoot n : ℝ) / bandDivisor n































































































































end

end ThreeSum.BandScales

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorWantedConsumerRetention


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData


/-!
# Retain the selected-color inputs while the wanted counter changes

Only the first dense-header cell is mutable during the scan. The encoded
payload, shared reporting catalog, threshold, cap and original false score
remain available with exactly the same normalized-list witnesses.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def DenseMetadata (μ : ℕ→ℤ) (counter cap score : ℕ) : Prop :=
  μ (counter+1)=((cap*score : ℕ) : ℤ) ∧
    μ (counter+2)=(cap : ℤ) ∧ μ (counter+3)=(score : ℤ)

variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

























































end ThreeSum.EncodedColorWantedConsumerData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorParametersCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Finite and asymptotic cost of executing the small coloring family -/

namespace ThreeSum.LightColorParametersCosts

open ColorParameters Scales StageBounds

def width (n : ℕ) : ℕ := inputBits n+1





















open Filter Real
open scoped Topology

noncomputable section



















end
end ThreeSum.LightColorParametersCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightGlobalSizes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Executing global powers and rounded band sizes

This routine consumes the already computed local output count, local prime,
block count, and total inner size. All global powers, the square-root
rounding, and the final ceiling division are actual Light computations.
The square-root loop and quotient loop are included in the stated time.
-/

namespace ThreeSum.LightGlobalSizes

set_option maxHeartbeats 1000000

open Light LocalCoverBounds

def divisor (mu : ℕ) : ℕ := 2^(mu/20)
def root (C J : ℕ) : ℕ := rootCeiling (C^J)
def numerator (C J mu : ℕ) : ℕ := root C J+divisor mu-1
def band (C J mu : ℕ) : ℕ := numerator C J mu/divisor mu

def values (C p J mu : ℕ) : List ℤ :=
  [((C^J : ℕ) : ℤ),((p^J : ℕ) : ℤ),root C J,divisor mu,band C J mu]

def body (pPower pDiv pSqrt : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pPower [v 0, v 2] 5)
    (Light.Stmt.seq (.call pPower [v 1, v 2] 6)
      (Light.Stmt.seq (.call pDiv [v 3, k 20] 7)
        (Light.Stmt.seq (.call pPower [k 2, v 7] 8)
          (Light.Stmt.seq
            (.call pSqrt [(Light.Expr.op Light.Op.sub) (v 5) (k 1)] 9)
            (Light.Stmt.seq (.set 10 ((Light.Expr.op Light.Op.add) (v 9) (k 1)))
              (Light.Stmt.seq
                (.set 11
                  ((Light.Expr.op Light.Op.sub)
                    ((Light.Expr.op Light.Op.add) (v 10) (v 8)) (k 1)))
                (Light.Stmt.seq (.call pDiv [v 11, v 8] 12)
                  (Light.Stmt.seq (.store (v 4) (v 5))
                    (Light.Stmt.seq
                      (.store ((Light.Expr.op Light.Op.add) (v 4) (k 1)) (v 6))
                      (Light.Stmt.seq
                        (.store ((Light.Expr.op Light.Op.add) (v 4) (k 2)) (v 10))
                        (Light.Stmt.seq
                          (.store ((Light.Expr.op Light.Op.add) (v 4) (k 3))
                            (v 8))
                          (Light.Stmt.seq
                            (.store ((Light.Expr.op Light.Op.add) (v 4) (k 4))
                              (v 12))
                            (.set 0 (v 6)))))))))))))))

def time (C J mu : ℕ) : ℕ := 2*LightNatPower.time J+
  LightSmallDivide.time mu 20+LightNatPower.time (mu/20)+sqrtTime (C^J-1)+
  LightSmallDivide.time (numerator C J mu) (divisor mu)+300

def word (C p J mu : ℕ) : ℕ := 1000*(C+p+J+mu+C^J+p^J+divisor mu+1)

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pDiv : ℕ
  pSqrt : ℕ
  power : P[pPower]? = some LightNatPower.body
  divide : P[pDiv]? = some LightSmallDivide.body
  sqrt : P[pSqrt]? = some sqrtBody
  main : P[pMain]? = some (body pPower pDiv pSqrt)

variable {lim : Limits} {P : Program} {d : ℕ}

















































































































def localCount (n : ℕ) : ℕ :=
  outputCount (512*Scales.microHalf (Scales.inputBits n)) (Scales.microHalf (Scales.inputBits n))



















end ThreeSum.LightGlobalSizes

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales

open Light ThreeSum.Scales

variable {lim : Limits} {P : Program}





































def values (n : ℕ) : List ℤ :=
  [inputBits n,microHalf (inputBits n),muZero n,blockCount (inputBits n),mu n]

/-- Arguments: original input length and destination of the five parameters.
The result is `mu`; the destination stores bits, micro-half, micro-size,
block count, and total size in that order. -/
def body (pLog pCube pHalf pDiv : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pLog [v 0] 2)
    (Light.Stmt.seq (.call pCube [(Light.Expr.op Light.Op.add) (v 2) (k 1)] 3)
      (Light.Stmt.seq (.call pHalf [v 3] 4)
        (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.sub) (v 4) (k 1)))
          (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.mul) (k 2) (v 5)))
            (Light.Stmt.seq
              (.call pDiv [v 2, (Light.Expr.op Light.Op.mul) (k 100) (v 6)] 7)
              (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.mul) (k 20) (v 7)))
                (Light.Stmt.seq
                  (.set 9 ((Light.Expr.op Light.Op.mul) (v 8) (v 6)))
                  (Light.Stmt.seq (.store (v 1) (v 2))
                    (Light.Stmt.seq
                      (.store ((Light.Expr.op Light.Op.add) (v 1) (k 1)) (v 5))
                      (Light.Stmt.seq
                        (.store ((Light.Expr.op Light.Op.add) (v 1) (k 2)) (v 6))
                        (Light.Stmt.seq
                          (.store ((Light.Expr.op Light.Op.add) (v 1) (k 3))
                            (v 8))
                          (Light.Stmt.seq
                            (.store ((Light.Expr.op Light.Op.add) (v 1) (k 4))
                              (v 9))
                            (.set 0 (v 9)))))))))))))))

def time (n : ℕ) : ℕ := log2Time n + cbrtCeilTime (inputBits n+1) +
  halfTime (cbrtLeast (inputBits n+1)) +
  LightSmallDivide.time (inputBits n) (100*muZero n)+200































































































/-- A syntax-only placement interface for embedding the initializer into a
larger fixed program. -/
structure Procs (P : Program) (pMain : ℕ) where
  pLog : ℕ
  pCube : ℕ
  pHalf : ℕ
  pDiv : ℕ
  main : P[pMain]? = some (body pLog pCube pHalf pDiv)
  log : P[pLog]? = some log2Body
  cube : P[pCube]? = some cbrtCeilBody
  half : P[pHalf]? = some halfBody
  divide : P[pDiv]? = some LightSmallDivide.body









end ThreeSum.LightScales

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSwitchCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Uniform finite and exponent bounds for the actual switch controls -/

namespace ThreeSum.LightSwitchCosts

open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology

def timeBudget (n : ℕ) : ℕ := 100*(inputBits n+1)+50
def depthBudget (n : ℕ) : ℕ := 5200*inputBits n+90























































noncomputable section


























end
end ThreeSum.LightSwitchCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsWantedIndices


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout


/-!
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales GlobalEncoding LocalCoverBounds OutputDecodeRecords
open SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def wantedDecodeV (n : ℕ) : ℕ := 2^(8192*(inputBits n+1))


































































































end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Switch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0

def cubicNumerator (r q : ℕ) : ℕ := 799 * q * r ^ 2 + 72 * q ^ 2 * r + 24 * q ^ 3

def accepts (J j r q : ℕ) : Prop :=
  (291 * J + 1000 * j) * r ^ 3 ≤ 10 * (J - j) * cubicNumerator r q

instance (J j r q : ℕ) : Decidable (accepts J j r q) :=
  inferInstanceAs (Decidable (_ ≤ _))

def candidates (J j r : ℕ) : Finset ℕ :=
  (Finset.range (r / 2 + 1)).filter (accepts J j r)

def switchIndex (J j r : ℕ) : ℕ :=
  if h : (candidates J j r).Nonempty then (candidates J j r).min' h else 0

def residualSize (n j : ℕ) : ℕ := (blockCount (inputBits n) - j) * muZero n

def actualSwitch (n j : ℕ) : ℕ :=
  switchIndex (blockCount (inputBits n)) j (residualSize n j)

def terminalDepth (n : ℕ) : ℕ := 13 * blockCount (inputBits n) / 20
















noncomputable section









































































































































































































end
end ThreeSum.Switch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_TrimScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales

open Filter Real ThreeSum.Scales
open scoped Topology

def replicatedHalf (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  f (microHalf (inputBits n)) ^ blockCount (inputBits n)




def trimMultiplicity (n : ℕ) : ℕ :=
  LocalCoverBounds.localBucketCap (microHalf (inputBits n)) ^ (2 * blockCount (inputBits n))

def localLength (h : ℕ) : ℕ := (LocalHashMoments.localSchedule h).length

def scheduleCount (n : ℕ) : ℕ := replicatedHalf localLength n

def representationBound (n : ℕ) : ℕ :=
  (localLength (microHalf (inputBits n)) *
    LocalCoverBounds.localBucketCap (microHalf (inputBits n)) ^ 2) ^ blockCount (inputBits n)

def fullOutputs (n : ℕ) : ℕ := (256 * mu n).choose (mu n)



noncomputable section

def vertexLoad (h : ℕ) : ℝ :=
  (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h































































































































































































































































































end

end ThreeSum.TrimScales

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_GlobalKeyEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists


/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000

def layerRecord (h : ℕ) (i : Fin ((512*h).choose (2*h))) :
    {Q // Q ∈ LayerCounts.vertices (512*h) (2*h)} :=
  ⟨LocalMaskGraph.setAt (512*h) (2*h) i,
    LayerCounts.mem_vertices.mpr (LocalMaskGraph.setAt_card i.isLt)⟩












def layers (h : ℕ) := List.ofFn (layerRecord h)

theorem layers_length (h : ℕ) : (layers h).length=outputCount (512*h) h := by
  simp [layers,outputCount]









def localRecords (h : ℕ) : List (OutputBlock h) :=
  (List.finRange (scheduleSize h)).product (layers h)

theorem localRecords_length (h : ℕ) :
    (localRecords h).length=scheduleSize h*outputCount (512*h) h := by
  calc
    _ = (List.finRange (scheduleSize h)).length*(layers h).length :=
      List.length_product _ _
    _ = _ := by rw [List.length_finRange,layers_length]







def localKeys (h : ℕ) : List ℤ := (localRecords h).map blockKey

def tupleOfList {α : Type*} {J : ℕ} (xs : List α) (hlen : xs.length=J) : Fin J → α :=
  fun i => xs.get (Fin.cast hlen.symm i)

theorem ofFn_tupleOfList {α : Type*} {J : ℕ} (xs : List α) (hlen : xs.length=J) :
    List.ofFn (tupleOfList xs hlen)=xs := by
  subst J
  exact List.ofFn_get xs

def globalRecords (h J : ℕ) : List (GlobalOutput h J) :=
  (tuples (localRecords h) J).attach.map fun xs =>
    tupleOfList xs.val ((mem_tuples _ _ _).mp xs.property).1

theorem globalRecords_length (h J : ℕ) :
    (globalRecords h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  simp [globalRecords,tuples_length,localRecords_length,mul_pow]

















def globalKeys (h J : ℕ) : List ℤ :=
  values (localPrime h : ℤ) (localKeys h) J

/-- Exact array identity, not merely equality of the set of key values. -/
theorem globalKeys_eq_map (h J : ℕ) :
    globalKeys h J=(globalRecords h J).map globalKey := by
  rw [globalKeys,localKeys,values_eq_map]
  unfold globalRecords
  rw [List.map_map]
  symm
  calc
    _ = (tuples (localRecords h) J).attach.map
        (fun xs => Radix.positionalHash (localPrime h) blockKey xs.val) := by
      apply List.map_congr_left
      intro xs _
      simp only [Function.comp_def,globalKey,ofFn_tupleOfList]
    _ = _ := by simp



































end ThreeSum.GlobalKeyEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDenseCap


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Compute the representation cap from the actual retained cover

The two factors are read from the verified cover header. An actual scalar
power loop computes the J-fold cap; no cap value is supplied as an input.
-/

namespace ThreeSum.LightDenseCap

open Light GlobalEncoding LocalCoverBounds

def base (h : ℕ) : ℕ := scheduleSize h*localBucketCap h^2

def word (h J : ℕ) : ℕ :=
  (base h+1)^(J+1)+base h+J+scheduleSize h+localBucketCap h^2+localBucketCap h+20

def body (pPower : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 2 (M ((Light.Expr.op Light.Op.add) (v 0) (k 7))))
    (Light.Stmt.seq (.set 3 (M ((Light.Expr.op Light.Op.add) (v 0) (k 10))))
      (Light.Stmt.seq (.set 4 ((Light.Expr.op Light.Op.mul) (v 2) (v 2)))
        (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.mul) (v 3) (v 4)))
          (.call pPower [v 5, v 1] 0)))))

def time (J : ℕ) : ℕ := LightNatPower.time J+150






















variable {lim : Limits} {P : Program} {μ : ℕ → ℤ} {free h J d : ℕ}






































def program : Program := [body 1,LightNatPower.body]








end ThreeSum.LightDenseCap

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_RawIncidences


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds

def lift (j : Fin 3) : ℤ := (j.val : ℤ) - 1
















abbrev ChoiceTuple (h J : ℕ) := Fin J → RetainedChoice h

instance retainedChoiceDecidableEq (h : ℕ) : DecidableEq (RetainedChoice h) := inferInstance

instance choiceTupleDecidableEq (h J : ℕ) : DecidableEq (ChoiceTuple h J) :=
  Fintype.decidablePiFintype

def tupleLeft {h J : ℕ} (t : ChoiceTuple h J) : ℤ :=
  Radix.positionalHash (localPrime h) rawLeft (List.ofFn t)

def tupleRight {h J : ℕ} (t : ChoiceTuple h J) : ℤ :=
  Radix.positionalHash (localPrime h) rawRight (List.ofFn t)

def tupleOutput {h J : ℕ} (t : ChoiceTuple h J) : GlobalOutput h J :=
  fun i => blockOfChoice (t i)

def tupleKey {h J : ℕ} (t : ChoiceTuple h J) : ℤ := globalKey (tupleOutput t)




















































def tupleOfList {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    ChoiceTuple h J := fun i => xs.get (Fin.cast hlen.symm i)




















abbrev Witness (h J : ℕ) := ChoiceTuple h J × Fin 3

instance witnessDecidableEq (h J : ℕ) : DecidableEq (Witness h J) := inferInstance

/-- Retained representations of a fixed original triple. The C target is
shifted by the common balancing offset, and the A key uses the same shift. -/
def witnesses (h J : ℕ) (P d a b c : ℤ) : Finset (Witness h J) :=
  Finset.univ.filter fun w : Witness h J =>
    List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
      globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1









































































































section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

abbrev Original (α β γ : Type*) := α × (β × γ)

def difference (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (t : Original α β γ) : ℤ :=
  c t.2.2 - b t.2.1 - a t.1

abbrev RawItem (h J : ℕ) (α β γ : Type*) := Σ _t : Original α β γ, Witness h J

/-- The band is a finite set of original index triples. It is part of the
owner data, rather than an additional representation choice. -/
def rawOn (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : Finset (RawItem h J α β γ) :=
  T.sigma fun t => witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)






















































def rawMass (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : ℕ := (rawOn h J P d T a b c).card







/-- Bucket multiplicity counts original B indices, including indices that
carry equal values. Only the left representation is inspected. -/
def leftBucket {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (t : ChoiceTuple h J) : ℕ :=
  ∑ j ∈ B, if globalModulus h J ∣ b j % P - tupleLeft t then 1 else 0

/-- The right bucket uses the same common offset as the A query keys. -/
def rightBucket {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (t : ChoiceTuple h J) : ℕ :=
  ∑ j ∈ C, if globalModulus h J ∣ c j % P + d - tupleRight t then 1 else 0







































































































































end OriginalIndices

end ThreeSum.RawIncidences

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWeightRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Reading one strided row of an ordered radix weight

The power table is ordinary memory. Each output coefficient is computed by
the checked radix-digit procedure; the caller supplies the table's exact
contents and this procedure preserves every cell outside its output row.
-/

namespace ThreeSum.LightWeightRow

open Light

set_option maxHeartbeats 1200000

def body (pDigit : ℕ) : Stmt :=
  .for 8 (v 7) (
    (Light.Stmt.seq
      (.call pDigit
        [v 2,
          M
            ((Light.Expr.op Light.Op.add) (v 3)
              ((Light.Expr.op Light.Op.sub)
                ((Light.Expr.op Light.Op.sub) (v 0) (k 1))
                ((Light.Expr.op Light.Op.add) (v 4)
                  ((Light.Expr.op Light.Op.mul) (v 5) (v 8))))),
          v 1]
        9)
      (.store ((Light.Expr.op Light.Op.add) (v 6) (v 8)) (v 9))))

def time (n k : ℕ) : ℕ := n*(LightRadixDigit.time k+100)+6
def word (W p k start stride : ℕ) : ℕ :=
  4*(k+p^(W+1)+p+W+start+stride+2)

def Inv (μ : ℕ → ℤ) (W p k powers start stride dst n i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,p,k,powers,start,stride,dst,n,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (WeightEnumeration.digit p W k (start+stride*j) : ℤ)) ∧
    SameOutside μ μ' dst n

variable {lim : Limits} {P : Program} {d : ℕ}

































































































end ThreeSum.LightWeightRow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightQueryEnumeration


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A complete output-sensitive subset enumerator inside an arbitrary query mask

The routine constructs its own compact coordinate weights, then invokes
the existing recursion on the number of selected coordinates. Every emitted
word is already a global mask; no ambient layer or Boolean cube is scanned.
-/

namespace ThreeSum.LightQueryEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates

variable {lim : Limits} {P : Program}

/-- Arguments: ambient width, query mask, missing cardinality, output base, scratch. -/
def body (pWeights pEnum : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 5
      ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 4) (v 0))
        (k 1)))
    (Light.Stmt.seq (.call pWeights [v 0, v 1, v 4, v 5] 6)
      (.call pEnum [v 6, v 2, k 0, v 3, v 4] 0)))

def time (W c t : ℕ) : ℕ :=
  LightQueryWeights.time W+LightSubsetEnumeration.time c t+60
















































def program : Program :=
  [body 1 4,LightQueryWeights.body 2 3,powTableBody,
    LightMaskErase.body 3,LightSubsetEnumeration.body 4]


























end ThreeSum.LightQueryEnumeration

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPairSegments


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # The constructed local pair arrays are aligned segments in one exact record order -/

namespace ThreeSum.ReportingHostPairSegments

open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration

set_option linter.unusedSimpArgs false

variable {α β : Type*}

























def leftMasks (L h : ℕ) : List ℤ := (pairs L h).map fun p => (subsetMask p.1 : ℤ)
def rightMasks (L h : ℕ) : List ℤ := (pairs L h).map fun p => (subsetMask p.2 : ℤ)


































































end ThreeSum.ReportingHostPairSegments

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ExplicitLayers


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Exact values and sizes of the explicitly evaluated missing layers -/

namespace ThreeSum.ExplicitLayers

open Finset ThreeSum.SubsetAddress
open scoped BigOperators
















def valueSum {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) : ℤ :=
  ((SignedLeaf.explicitLeaves Q t).map weight).sum



































end ThreeSum.ExplicitLayers

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightStageLookup


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
# Executing a stored partial-zeta or box lookup

This fixed program computes the compact downset stride and the queried
subset rank from freshly built tables. It then reads exactly one stored
stage cell. The specialized contracts connect that machine read to the
forced-prefix sum and to the canonical sparse-box sum.
-/

namespace ThreeSum.LightStageLookup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def readAddr {L : ℕ} (cut base j : ℕ) (S : Finset (Fin L)) : ℕ :=
  base+j*downsetCap L cut+subsetRank S

/-- Arguments: width, cutoff, cardinality, mask, stage, table base,
polynomial scratch base. -/
def body (pSize pAddress : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSize [v 0, v 1, v 6] 7)
    (Light.Stmt.seq (.call pAddress [v 0, v 2, v 3, v 6] 8)
      (.set 0
        (M
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v 5)
              ((Light.Expr.op Light.Op.mul) (v 4) (v 7)))
            (v 8))))))

def time (L : ℕ) : ℕ := LightDownsetSize.time L+LightDownsetAddress.time L+50





































































































end ThreeSum.LightStageLookup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightZetaBatch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A compact layer pass of zeta updates

The input masks occupy an actual memory segment. Each loop iteration
loads one mask and invokes the verified compact-cell routine. The source
and mask segments are preserved, and all destination entries omitted
from the mask list retain their previous values. There is no scan of
the ambient cube in this procedure.
-/

namespace ThreeSum.LightZetaBatch

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode

variable {lim : Limits} {P : Program}

/-- Arguments: width, cardinality, number of masks, mask base,
coordinate, source, destination, scratch. -/
def body (pCell : ℕ) : Stmt :=
  .for 8 (v 2)
    (.call pCell [v 0,v 1,M (((Light.Expr.op Light.Op.add) (v 3) (v 8))),v 4,v 5,v 6,v 7] 9)

def time (L n : ℕ) : ℕ := n*(LightZetaCell.time L+40)+10

def values {L : ℕ} (μ : ℕ → ℤ) (dst : ℕ) (masks : List ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) : ℤ :=
  if subsetMask S ∈ masks then Subset.zetaStep a f S else μ (dst+subsetRank S)

def Inv {L : ℕ} (μ : ℕ → ℤ) (cut cardinal maskBase src dst work : ℕ)
    (masks : List ℕ) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cardinal,masks.length,maskBase,a.val,src,dst,work,j,r],μ'⟩ ∧
    KeptBut μ μ' work dst (downsetCap L cut) ∧
    TableAt μ' dst cut (values μ dst (masks.take j) a f)







































































































end ThreeSum.LightZetaBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightZetaPass


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A complete coordinate pass over a compact downset

For each stored cardinality the fixed procedure constructs its layer of
masks, then runs the compact-cell update on that layer. Only the compact
downset and polynomial workspace are allocated; the program never visits
all integers below `2^L`. The source table remains unchanged throughout
the pass.
-/

namespace ThreeSum.LightZetaPass

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def enumBudget (L cut : ℕ) : ℕ := 800*(L+1)*(downsetCap L cut+1)
def batchBudget (L cut : ℕ) : ℕ := 2100*(L+1)^2*(downsetCap L cut+1)
def roundBudget (L cut : ℕ) : ℕ := enumBudget L cut+batchBudget L cut+60








def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnumSetup [v 0, v 7, v 5, v 6] 8)
    (.call pBatch [v 0, v 7, v 8, v 5, v 2, v 3, v 4, v 6] 9))

/-- Arguments: width, cutoff, coordinate, source, destination,
mask workspace, polynomial workspace. -/
def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 7 (((Light.Expr.op Light.Op.add) (v 1) (k 1))) (roundBody pEnumSetup pBatch)

def time (L cut : ℕ) : ℕ := (cut+1)*(roundBudget L cut+20)+20

def stageValues {L : ℕ} (μ : ℕ → ℤ) (dst j : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) : ℤ :=
  if S.card < j then Subset.zetaStep a f S else μ (dst+subsetRank S)

def Inv {L : ℕ} (μ : ℕ → ℤ) (cut src dst maskBase work : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,a.val,src,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap L cut) ∧
    TableAt μ' dst cut (stageValues μ dst j a f)























































































































































end ThreeSum.LightZetaPass

end


