-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle10
-- name    : ThreeSum1962Source_Bundle10
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:16:23.121466+00:00
-- url     : https://prove2.me/theorems/2d62a952-6096-4c88-8bb3-d9009af96487
-- title:
--   Common-prime selection, retained transforms, and finite stage counts
-- statement:
--   This bundle defines a common modulus chain for all owner records. Starting from $q_0=1$, a nonempty prime pool supplies
--   $$
--   q_{r+1}=q_r p_{i_r},
--   $$
--   where $i_r$ is the first index minimizing the aggregate score at $q_rp_i$. It also defines retained prefix- and suffix-zeta stages, packed bucket setup, selected-map endpoint preparation, local greedy schedule indices, and original-color incidence interfaces. Row-major block coordinates, occurrence-bank order, forced-prefix decompositions, and raw bucket-product counts describe reporting inputs. Explicit wanted- and false-mass expressions and six principal work counts form the finite resource ledger; program bodies provide color-band construction, candidate scoring, coefficient preparation, and prefix-mask arrays.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandPrimeChoice.lean#L19-L64
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandPrimeCosts.lean#L19-L113
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAColorOriginal.lean#L20-L23
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAFiniteSlices.lean#L18-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockForced.lean#L24-L263
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockIndex.lean#L22-L99
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockSourceOccurrenceOrder.lean#L19-L23
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/DenseGuardAuxiliary.lean#L11-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorPrimeData.lean#L10-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/GlobalKeyOffset.lean#L53-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandCandidates.lean#L18-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandWeightedScoreCell.lean#L20-L164
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBoxStages.lean#L22-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorBands.lean#L20-L133
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverCandidate.lean#L21-L53
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverSchedule.lean#L18-L108
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOutputDecodeOriginal.lean#L18-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingPrefixArrays.lean#L22-L36
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSelectedPrime.lean#L31-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSignedLeafGeneral.lean#L18-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandStep.lean#L12-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketSetup.lean#L20-L78
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourcePreparation.lean#L19-L161
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumColorDriver.lean#L20-L43
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightZetaStages.lean#L22-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/MassScales.lean#L23-L77
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RawPrefixCounts.lean#L24-L103
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostBlockBucketTest.lean#L20-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandPairSlices.lean#L10-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/StageBounds.lean#L23-L52

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSignedLeafGeneral


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
# Signed leaves with arbitrary prefix overlap

Two bounded width scans construct the actual prefix unions and their
cardinalities. The compact source-table reads and signed multiplication
then give the same leaf function used by the sparse query theorem.
-/

namespace ThreeSum.LightSignedLeafGeneral

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- The arguments agree with `LightSignedLeaf`; no disjointness is required.
One extra scratch cell receives each actual union cardinality. -/
def body (pUnion pLookup pSign : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pUnion
      [v 0, v 3, v 4, v 8, v 11, (Light.Expr.op Light.Op.add) (v 11) (k 1)] 12)
    (Light.Stmt.seq (.set 13 (M (v 11)))
      (Light.Stmt.seq
        (.call pLookup
          [v 0, v 1, v 13, v 12, v 2, v 9,
            (Light.Expr.op Light.Op.add) (v 11) (k 1)]
          14)
        (Light.Stmt.seq
          (.call pUnion
            [v 0, v 5, v 6, v 8, v 11, (Light.Expr.op Light.Op.add) (v 11) (k 1)]
            15)
          (Light.Stmt.seq (.set 16 (M (v 11)))
            (Light.Stmt.seq
              (.call pLookup
                [v 0, v 1, v 16, v 15, v 2, v 10,
                  (Light.Expr.op Light.Op.add) (v 11) (k 1)]
                17)
              (Light.Stmt.seq
                (.set 18 ((Light.Expr.op Light.Op.mul) (v 14) (v 17)))
                (.call pSign [v 18, v 7] 0))))))))

def time (W : ℕ) : ℕ :=
  2*LightMaskUnion.time W+2*LightStageLookup.time W+LightSign.time W+160














































































































































end ThreeSum.LightSignedLeafGeneral

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBoxStages


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BoxStages
end ThreeSum.BoxStages
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Building and retaining every compact prefix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for canonical
sparse-box queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightBoxStages

open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def stageBase (base cap j : ℕ) : ℕ := base+j*cap

def StoredThrough {L : ℕ} (μ : ℕ → ℤ) (base cut : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) : Prop :=
  ∀ i ≤ j, TableAt μ (stageBase base (downsetCap L cut) i) cut (stageValue f i)

def roundBody (pPass : ℕ) : Stmt :=
  .call pPass [v 0,v 1,v 6,
    ((Light.Expr.op Light.Op.add) (v 2) ((Light.Expr.op Light.Op.mul) (v 6) (v 5))),((Light.Expr.op Light.Op.add) (v 2)
                                                                                      ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 6) (k 1))
                                                                                        (v 5))),v 3,v 4] 7

/-- Arguments: width, cutoff, base of all stage tables,
mask workspace, polynomial workspace. Stage zero initially holds `f`. -/
def body (pSize pPass : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSize [v 0, v 1, v 4] 5) (.for 6 (v 0) (roundBody pPass)))

def time (L cut : ℕ) : ℕ :=
  LightDownsetSize.time L+L*(LightZetaPass.time L cut+80)+80

def Inv {L : ℕ} (μ : ℕ → ℤ) (cut base maskBase work : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,base,maskBase,work,downsetCap L cut,j,r],μ'⟩ ∧
    StoredThrough μ' base cut f j ∧
    KeptBut μ μ' maskBase base ((L+1)*downsetCap L cut)





























































































































































































end ThreeSum.LightBoxStages

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightZetaStages


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
namespace ThreeSum.SubsetStages
end ThreeSum.SubsetStages


/-!
# Building and retaining every compact suffix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for forced
prefix queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightZetaStages

open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def stageBase (base cap j : ℕ) : ℕ := base+j*cap

def StoredThrough {L : ℕ} (μ : ℕ → ℤ) (base cut : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) : Prop :=
  ∀ i ≤ j, TableAt μ (stageBase base (downsetCap L cut) i) cut (stageValue f i)

def roundBody (pPass : ℕ) : Stmt :=
  .call pPass [v 0,v 1,((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.sub) (v 0) (k 1)) (v 6)),
    ((Light.Expr.op Light.Op.add) (v 2) ((Light.Expr.op Light.Op.mul) (v 6) (v 5))),((Light.Expr.op Light.Op.add) (v 2)
                                                                                      ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 6) (k 1))
                                                                                        (v 5))),v 3,v 4] 7

/-- Arguments: width, cutoff, base of all stage tables,
mask workspace, polynomial workspace. Stage zero initially holds `f`. -/
def body (pSize pPass : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSize [v 0, v 1, v 4] 5) (.for 6 (v 0) (roundBody pPass)))

def time (L cut : ℕ) : ℕ :=
  LightDownsetSize.time L+L*(LightZetaPass.time L cut+80)+80

def Inv {L : ℕ} (μ : ℕ → ℤ) (cut base maskBase work : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,base,maskBase,work,downsetCap L cut,j,r],μ'⟩ ∧
    StoredThrough μ' base cut f j ∧
    KeptBut μ μ' maskBase base ((L+1)*downsetCap L cut)

























































































































































































end ThreeSum.LightZetaStages

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBucketSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Packed generic residue buckets from four scalar arguments

Only the code-array base, item count, positive residue count, and free pointer are
supplied. The program computes every histogram/offset/cursor/index address
and returns the next free address. Its exact fibers serve both source
reporting and the wanted-record residue join.
-/

namespace ThreeSum.LightSourceBucketSetup

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def hist (base : ℕ) : ℕ := base
def offsets (base M : ℕ) : ℕ := base+M
def cursor (base M : ℕ) : ℕ := base+2*M+1
def flat (base M : ℕ) : ℕ := base+3*M+1
def next (base N M : ℕ) : ℕ := base+3*M+1+N

def body (pBuild : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 4 ((Light.Expr.op Light.Op.add) (v 3) (v 2)))
    (Light.Stmt.seq
      (.set 5
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v 3)
            ((Light.Expr.op Light.Op.mul) (k 2) (v 2)))
          (k 1)))
      (Light.Stmt.seq
        (.set 6
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v 3)
              ((Light.Expr.op Light.Op.mul) (k 3) (v 2)))
            (k 1)))
        (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.add) (v 6) (v 1)))
          (Light.Stmt.seq (.call pBuild [v 0, v 3, v 4, v 5, v 6, v 1, v 2] 8)
            (.set 0 (v 7)))))))

def time (N M : ℕ) : ℕ := LightSourceBucketBuild.time N M+200

structure Procs (P : Program) (pMain : ℕ) where
  pBuild : ℕ
  build : LightSourceBucketBuild.Procs P pBuild
  main : P[pMain]? = some (body pBuild)

variable {lim : Limits} {P : Program} {d : ℕ}































def program : Program :=
  [body 1,LightSourceBucketBuild.body 2 4,histogramBody 3,fillBody,
    LightSourceBucketFromHistogram.body 5 6,LightSourceBucketOffsets.body,LightSourceBucketScatter.body]

def programProcs : Procs program 0 :=
  ⟨1,⟨2,3,4,rfl,rfl,⟨5,6,rfl,rfl,rfl⟩,rfl⟩,rfl⟩








end ThreeSum.LightSourceBucketSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandStep


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout


/-! # One actual original-band histogram, buckets, and six pointer headers -/

namespace ThreeSum.LightSourceBandStep

open Light BandPartition SourceBandLayout

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

def tailBody (pOriginal : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 15 ((Light.Expr.op Light.Op.sub) (v 14) (v 13)))
    (Light.Stmt.seq
      (.set 16
        ((Light.Expr.op Light.Op.add) (v 9)
          ((Light.Expr.op Light.Op.mul) (v 12) (v 10))))
      (Light.Stmt.seq (.set 17 ((Light.Expr.op Light.Op.add) (v 16) (v 4)))
        (Light.Stmt.seq (.set 18 ((Light.Expr.op Light.Op.add) (v 17) (v 7)))
          (Light.Stmt.seq
            (.set 19
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 18) (v 4)) (k 1)))
            (Light.Stmt.seq (.set 20 ((Light.Expr.op Light.Op.add) (v 19) (v 4)))
              (Light.Stmt.seq
                (.call pOriginal
                  [(Light.Expr.op Light.Op.add) (v 0) (v 13), v 15, v 3, v 4, v 5,
                    v 16, v 17, v 18, v 19, v 20, v 11]
                  21)
                (Light.Stmt.seq
                  (.store
                    ((Light.Expr.op Light.Op.add) (v 6)
                      ((Light.Expr.op Light.Op.mul) (k 6) (v 12)))
                    (v 13))
                  (Light.Stmt.seq
                    (.store
                      ((Light.Expr.op Light.Op.add)
                        ((Light.Expr.op Light.Op.add) (v 6)
                          ((Light.Expr.op Light.Op.mul) (k 6) (v 12)))
                        (k 1))
                      (v 15))
                    (Light.Stmt.seq
                      (.store
                        ((Light.Expr.op Light.Op.add)
                          ((Light.Expr.op Light.Op.add) (v 6)
                            ((Light.Expr.op Light.Op.mul) (k 6) (v 12)))
                          (k 2))
                        (v 17))
                      (Light.Stmt.seq
                        (.store
                          ((Light.Expr.op Light.Op.add)
                            ((Light.Expr.op Light.Op.add) (v 6)
                              ((Light.Expr.op Light.Op.mul) (k 6) (v 12)))
                            (k 3))
                          (v 16))
                        (Light.Stmt.seq
                          (.store
                            ((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add) (v 6)
                                ((Light.Expr.op Light.Op.mul) (k 6) (v 12)))
                              (k 4))
                            (v 18))
                          (.store
                            ((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add) (v 6)
                                ((Light.Expr.op Light.Op.mul) (k 6) (v 12)))
                              (k 5))
                            (v 20))))))))))))))

def body (pOriginal : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 13 ((Light.Expr.op Light.Op.mul) (v 12) (v 2)))
    (Light.Stmt.seq
      (.set 14
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 12) (k 1))
          (v 2)))
      (Light.Stmt.seq (.ite (Light.Cond.lt (v 1) (v 14)) (.set 14 (v 1)) .skip)
        (tailBody pOriginal))))

def charge (n g p m U D : ℕ) : ℕ :=
  498*cap n g*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+233*m+333

def tailTime (n g p m U D : ℕ) : ℕ := charge n g p m U D+1000
def time (n g p m U D : ℕ) : ℕ := charge n g p m U D+1200

def word (n g p m U D : ℕ) : ℕ := LightSourceResidues.word p m U D+n+g+2

structure Procs (P : Program) (pMain : ℕ) where
  pOriginal : ℕ
  original : LightSourceBucketOriginal.Procs P pOriginal
  main : P[pMain]? = some (body pOriginal)

variable {lim : Limits} {P : Program} {d : ℕ}




































































































































































end ThreeSum.LightSourceBandStep

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourcePreparation


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows


/-!
# Actual endpoint and independent-flag preparation from stored selected maps

The host constructs radix coefficient rows, both raw endpoint arrays, and
both independent trim-flag arrays. All four arrays are retained for the
original-input histogram/source-stage constructors.
-/

namespace ThreeSum.LightSourcePreparation

open Light BlockCoefficientRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

/-- Arguments: J, L, required row size, local prime, cap; occurrence/maps/
candidate/table pointers; mask array/count; coefficient rows, raw arrays,
paired flag arrays, and reusable scratch. -/
def body (pHashes pFlags : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pHashes
      [v 0, v 1, v 3, v 5, v 6, v 12, v 13, v 10, v 14, v 15, v 11, v 19] 20)
    (.call pFlags
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 16, v 17,
        v 18, v 19]
      20))

def time (n J L U : ℕ) : ℕ :=
  LightBlockSourceHashes.time J L n+LightSourceFlagArray.time n J L U+200

def word (J L p U V cap : ℕ) : ℕ :=
  LightBlockSourceHashes.word J L p U+LightSourceMaskFlags.word J L p U V cap

def space (work J L U : ℕ) : ℕ :=
  max (LightBlockSourceHashes.space work J L) (LightSourceMaskFlags.space work J L U)

structure Procs (P : Program) (pMain : ℕ) where
  pHashes : ℕ
  pFlags : ℕ
  hashes : LightBlockSourceHashes.Procs P pHashes
  flags : LightSourceFlagArray.Procs P pFlags
  main : P[pMain]? = some (body pHashes pFlags)

variable {lim : Limits} {P : Program} {d : ℕ}












































































































def program : Program :=
  [body 1 7,LightBlockSourceHashes.body 2 5,LightBlockCoefficients.body 3 4,
    powTableBody,LightScaleArray.body,LightMaskHashes.body 3 6,LightOneHot.body 6,
    LightSourceFlagArray.body 8,LightSourceMaskFlags.body 9 12,
    LightMaskBits.body 10 11,powTableBody,LightMaskErase.body 11,
    LightSourceTrim.body 13,LightSourceRowFlag.body 14 15 16,LightSourceRowScan.body,
    emodBody,LightSourceFlagTest.body]

def programProcs : Procs program 0 :=
  ⟨1,7,⟨2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨8,⟨9,10,11,12,rfl,rfl,rfl,⟨13,14,15,16,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩









end ThreeSum.LightSourcePreparation

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverSchedule


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments


/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule

open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

def rows (h : ℕ) : ℕ := (localPrime h)^(2*(512*h))
def cols (h : ℕ) : ℕ := localPrime h*localPrime h
def candidate (h i : ℕ) : Weight (512*h) (LocalField h) :=
  WeightEnumeration.decodedWeight (512*h) (localPrime h) i
def target (h r : ℕ) : LocalField h × LocalField h :=
  (((r/localPrime h : ℕ) : LocalField h),((r%localPrime h : ℕ) : LocalField h))
def matrix (h i r : ℕ) : ℕ :=
  LocalCoverMatrix.entry (candidate h i) h (localBucketCap h) r
def indices (h : ℕ) : List ℕ :=
  BooleanGreedy.choices (matrix h) (rows h) (cols h) (scheduleSize h)
















































































def candidateAt (h : ℕ) (s : Occurrence h) : ℕ := (indices h).getD s.val 0
























































end ThreeSum.LightLocalCoverSchedule

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_GlobalKeyOffset


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration


/-!
# The actual array-selected offset balances original output records

The program's right histogram is indexed by literal key-array positions.
This module transports that count bijectively to the original global output
type, retaining distinct outputs that happen to have equal integer keys.
-/

namespace ThreeSum.GlobalKeyOffset

open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators

set_option maxHeartbeats 1800000


































def selected (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) : ℕ :=
  LightOriginalOffset.selected p (fun i => left.getD i 0)
    (fun i => (globalKeys h J).getD i 0) left.length (globalKeys h J).length































end ThreeSum.GlobalKeyOffset

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandCandidates


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration


/-!
# All actual flagged band-owner records

The fixed program reads the three retained rectangular lookup tables and
writes one four-cell record for each cell, in the same BC, AB, AC order.
The record position is its permanent owner-slot identity.
-/

namespace ThreeSum.LightBandCandidates

open Light BandEnumeration BandCandidateRows

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

def body (pBC pAB pAC : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.mul) (v 3) (v 4)))
    (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.mul) (v 2) (v 3)))
      (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.mul) (v 2) (v 4)))
        (Light.Stmt.seq
          (.set 8
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v 5) (v 6)) (v 7)))
          (Light.Stmt.seq (.call pBC [v 0, v 1, v 3, v 4] 9)
            (Light.Stmt.seq
              (.call pAB
                [(Light.Expr.op Light.Op.add) (v 0) (v 5),
                  (Light.Expr.op Light.Op.add) (v 1)
                    ((Light.Expr.op Light.Op.mul) (k 4) (v 5)),
                  v 2, v 3]
                9)
              (Light.Stmt.seq
                (.call pAC
                  [(Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add) (v 0) (v 5)) (v 6),
                    (Light.Expr.op Light.Op.add) (v 1)
                      ((Light.Expr.op Light.Op.mul) (k 4)
                        ((Light.Expr.op Light.Op.add) (v 5) (v 6))),
                    v 2, v 4]
                  9)
                (.set 0 (v 8)))))))))

def time (a b c : ℕ) : ℕ :=
  LightBandCandidatesTable.time b c+LightBandCandidatesTable.time a b+
    LightBandCandidatesTable.time a c+250

def word (a b c : ℕ) : ℕ := a+b+c+10

def space (dst a b c : ℕ) : ℕ := dst+4*LightBandEnumeration.count a b c

structure Procs (P : Program) (pMain : ℕ) where
  pBC : ℕ
  pAB : ℕ
  pAC : ℕ
  pRowBC : ℕ
  pRowAB : ℕ
  pRowAC : ℕ
  pCellBC : ℕ
  pCellAB : ℕ
  pCellAC : ℕ
  bc : P[pBC]?=some (LightBandCandidatesTable.body pRowBC)
  ab : P[pAB]?=some (LightBandCandidatesTable.body pRowAB)
  ac : P[pAC]?=some (LightBandCandidatesTable.body pRowAC)
  rowBC : P[pRowBC]?=some (LightBandCandidatesRow.body pCellBC)
  rowAB : P[pRowAB]?=some (LightBandCandidatesRow.body pCellAB)
  rowAC : P[pRowAC]?=some (LightBandCandidatesRow.body pCellAC)
  cellBC : P[pCellBC]?=some (LightBandCandidatesCell.body .bc)
  cellAB : P[pCellAB]?=some (LightBandCandidatesCell.body .ab)
  cellAC : P[pCellAC]?=some (LightBandCandidatesCell.body .ac)
  main : P[pMain]?=some (body pBC pAB pAC)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}




















































































































































end ThreeSum.LightBandCandidates

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAColorOriginal


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists


/-!
# Distinct original-position semantics of the finite owner catalog

Incidence coordinates remain physical coordinates in the flattened A row.
Original input indices are recovered from retained class membership. Their
different colors prove that the three recovered positions are distinct,
even when the input contains repeated values.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

def finiteEquation (A B C : List ℤ) (g : ℕ) (rs : List Record) : Prop :=
  ∃ t ∈ finiteAllProducts A.length B.length C.length g rs,
    valueAt A.length g rs (fun i => A.getD i 0) t.1.val+
      B.getD t.2.1.val 0=C.getD t.2.2.val 0






































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandRawAFiniteSlices


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# Forward enumeration equivalences for the finite owner slices

B/C local index `j` denotes retained sorted position `band*g+j`.
The A local index denotes physical incidence `count owner+j`, carrying
its exact owner and sorted A coordinate.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset

set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem local_band_mem {n g a j : ℕ} (hj : j < bandLength n g a) :
    BandPartition.start g a+j ∈ bandPositions n g a :=
  mem_image.mpr ⟨j,mem_range.mpr hj,rfl⟩

def finiteBandAt (n g a : ℕ) (j : Fin (bandLength n g a)) : Fin n :=
  ⟨BandPartition.start g a+j.val,bandPositions_lt (local_band_mem j.isLt)⟩

def finiteBandEquiv (n g a : ℕ) :
    Fin (bandLength n g a) ≃ {p : Fin n // p ∈ finiteBandPositions n g a} where
  toFun j := ⟨finiteBandAt n g a j,mem_finiteBandPositions.mpr (local_band_mem j.isLt)⟩
  invFun p := ⟨p.val.val-BandPartition.start g a,by
    have hp := mem_bandPositions.mp (mem_finiteBandPositions.mp p.property)
    unfold bandLength
    omega⟩
  left_inv j := by
    apply Fin.ext
    change BandPartition.start g a+j.val-BandPartition.start g a=j.val
    omega
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    change BandPartition.start g a+(p.val.val-BandPartition.start g a)=p.val.val
    have hp := mem_bandPositions.mp (mem_finiteBandPositions.mp p.property)
    omega



































































end ThreeSum.BandRawA

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorBands


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists


/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands

open Light ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Original array/length/width, six coloring parameters, color and class
buffers, band size, three value/endpoint pairs, and scratch. -/
def body (pClasses pBands : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pClasses
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 20]
      21)
    (.call pBands
      [(Light.Expr.op Light.Op.add) (v 10) (k 1), M (v 10),
        (Light.Expr.op Light.Op.add) (v 11) (k 1), M (v 11),
        (Light.Expr.op Light.Op.add) (v 12) (k 1), M (v 12), v 13, v 14, v 15,
        v 16, v 17, v 18, v 19, v 20]
      0))

def time (W n g : ℕ) : ℕ := LightColorClasses.time W n+ColorBandBounds.time n g+300
def space (work W n g : ℕ) : ℕ := ColorBandBounds.space work n g+W+1
def word (W n g U : ℕ) : ℕ := 2^(W+1)+ColorBandBounds.word n g U+U
def depth (W n g : ℕ) : ℕ := W+ColorBandBounds.depth n g+5















structure Procs (P : Program) (pMain : ℕ) where
  pClasses : ℕ
  pBands : ℕ
  classes : LightColorClasses.Procs P pClasses
  bands : LightBandPreprocessing.Procs P pBands
  main : P[pMain]? = some (body pClasses pBands)

variable {lim : Limits} {P : Program} {d : ℕ}











































































/-- Keep the already checked twenty-procedure band implementation at its
original indices; append the original-array constructor and its callees. -/
def program : Program := LightBandPreprocessing.program ++
  [body 21 0,LightColorClasses.body 22 26,LightColorArray.body 23 24,powTableBody,
    LightColorIndex.body 25,LightMaskErase.body 25,LightClassFilter.body]









































end ThreeSum.LightColorBands

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandPairSlices


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData


/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices

open Light BandPartition SourceBandLayout SourceBandPairData

def histogramPtr (base n g m zero i : ℕ) : ℕ :=
  if i < size n g then hist base n g m i else zero

def histLeft (base NL NR g m i : ℕ) : ℕ :=
  histogramPtr (leftBase base) NL g m (zeroBase base NL NR g m) i

def histRight (base NL NR g m i : ℕ) : ℕ :=
  histogramPtr (rightBase base NL g m) NR g m (zeroBase base NL NR g m) i

def count (NL NR g : ℕ) : ℕ := max (size NL g) (size NR g)

























































end ThreeSum.SourceBandPairSlices

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandPrimeChoice


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore


/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice

open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

def candidateScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (i : ℕ) : ℤ :=
  (score primes s (q*primes i) nA nB nC g A B C rs : ℤ)

def chosenIndex (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  LightMinimum.least (candidateScore primes s q nA nB nC g A B C rs) s

def chosenPrime (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  primes (chosenIndex primes s q nA nB nC g A B C rs)





























def modulus (primes : ℕ → ℕ) (s nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ → ℕ
  | 0 => 1
  | r+1 =>
    let q := modulus primes s nA nB nC g A B C rs r
    q*chosenPrime primes s q nA nB nC g A B C rs


















































































end ThreeSum.BandPrimeChoice

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_DenseGuardAuxiliary


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # The actually generated auxiliary prime pool separates all bounded differences -/

namespace ThreeSum.DenseGuard

open Filter Scales RawIncidences
open scoped Topology

def actualAux (n : ℕ) : Finset ℤ :=
  Auxiliary.moduli (WeightedScore.auxiliarySet (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)))

theorem actualAux_eq (n : ℕ) :
    actualAux n=Auxiliary.moduli (PrimeDensity.candidates (primeWindow n)) := by
  rw [actualAux,LightPrimePool.auxiliarySet_eq_candidates]

theorem actual_aux_separates (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ 3*n^k →
      ∃ l ∈ actualAux n, ¬ l ∣ z := by
  filter_upwards [actual_auxiliary_cardinality k] with n hn
  intro z hz hb
  rw [actualAux_eq]
  exact Auxiliary.candidate_pool_separates (primeWindow n) (3*n^k)
    (by simpa only [Nat.log2_eq_log_two,candidateCount] using hn) hz hb


























end ThreeSum.DenseGuard

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorPrimeData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Retained common-prime metadata for one actual color execution -/

namespace ThreeSum.EncodedColorPrimeData

open Light

def poolBase (free : ℕ) : ℕ := free+6
def prefixBase (free y : ℕ) : ℕ := poolBase free+3*y
def nextFree (free M y : ℕ) : ℕ := prefixBase free y+LightBandPrimeDepth.depth M y+1

def values (free M y p : ℕ) : List ℤ :=
  [p,LightBandPrimeDepth.depth M y,nextFree free M y,poolBase free,LightPrimePool.size y,prefixBase free y]

structure Stored (μ : ℕ → ℤ) (free M y : ℕ) (qs : ℕ → ℕ) : Prop where
  header : Seg μ free (values free M y (qs (LightBandPrimeDepth.depth M y)))
  pool : SegN μ (poolBase free) (LightPrimePool.values y)
  prefixes : ∀ i ≤ LightBandPrimeDepth.depth M y, μ (prefixBase free y+i)=(qs i : ℤ)
































end ThreeSum.EncodedColorPrimeData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSelectedPrime


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Executing the deterministic square-root prime selection

The candidate pool is scanned by the verified primality program. Its first
entry is exactly the minimum used by `LocalCoverBounds.selectedPrime`.
The input threshold is positive; the routine has no primality oracle or
externally supplied list of candidates.
-/

namespace ThreeSum.LightSelectedPrime

open Light LocalCoverBounds LightResidues

set_option maxHeartbeats 1000000












def body (pSqrt pPool : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSqrt [(Light.Expr.op Light.Op.sub) (v 0) (k 1)] 2)
    (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.add) (v 2) (k 1)))
      (Light.Stmt.seq (.call pPool [v 3, v 1] 4) (.set 0 (M (v 1))))))

def time (N : ℕ) : ℕ := sqrtTime (N-1)+LightPrimePool.time (rootCeiling N)+100
def space (free N : ℕ) : ℕ := LightPrimePool.space free (rootCeiling N)
def word (N : ℕ) : ℕ := 100*(N+1)

structure Procs (P : Program) (pMain : ℕ) where
  pSqrt : ℕ
  pPool : ℕ
  sqrt : P[pSqrt]? = some sqrtBody
  pool : LightPrimePool.Procs P pPool
  main : P[pMain]? = some (body pSqrt pPool)

variable {lim : Limits} {P : Program} {d : ℕ}
































































































end ThreeSum.LightSelectedPrime

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandWeightedScoreCell


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore


/-!
# Compute one flagged owner's weighted modular score

The actual record supplies its three band indices. This routine computes
their truncated lengths and invokes the existing exact counting program on
those slices. An unflagged record contributes zero without a counting call.
-/

namespace ThreeSum.LightBandWeightedScoreCell

open Light BandCandidateRows BandWeightedScore

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pLength pScore : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 12 (M (v 7)))
    (.ite (Light.Cond.eq (v 12) (k 1))
      (Light.Stmt.seq (.set 13 (M ((Light.Expr.op Light.Op.add) (v 7) (k 1))))
        (Light.Stmt.seq (.set 14 (M ((Light.Expr.op Light.Op.add) (v 7) (k 2))))
          (Light.Stmt.seq (.set 15 (M ((Light.Expr.op Light.Op.add) (v 7) (k 3))))
            (Light.Stmt.seq (.call pLength [v 3, v 6, v 13] 16)
              (Light.Stmt.seq (.call pLength [v 4, v 6, v 14] 17)
                (Light.Stmt.seq (.call pLength [v 5, v 6, v 15] 18)
                  (.call pScore
                    [(Light.Expr.op Light.Op.add) (v 0)
                        ((Light.Expr.op Light.Op.mul) (v 13) (v 6)),
                      (Light.Expr.op Light.Op.add) (v 1)
                        ((Light.Expr.op Light.Op.mul) (v 14) (v 6)),
                      (Light.Expr.op Light.Op.add) (v 2)
                        ((Light.Expr.op Light.Op.mul) (v 15) (v 6)),
                      v 16, v 17, v 18, v 8, v 6, v 9, v 10, v 11]
                    0)))))))
      (.set 0 (k 0))))

def time (maxMod g s U : ℕ) : ℕ :=
  3*LightBandWeightedScoreSlice.time+LightWeightedScore.runtimeTime maxMod g g g s U+250

def word (maxMod nA nB nC g s U : ℕ) : ℕ :=
  LightWeightedScore.word maxMod g s U+nA+nB+nC+g+8

















variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}





























































































def program : Program := LightWeightedScore.program ++
  [LightBandWeightedScoreSlice.body,body 14 0]



def programProcs : LightWeightedScore.Procs program 0 where
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

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumColorDriver


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts


/-!
# Close the actual color decoder and scan around a concrete color program

The supplied program stays at its original indices. Four actual procedures
are appended: the six-cell decoder, scalar division, recursive short-circuit
scan, and parameter-header reader. The resulting program can then be
relocated by the already verified general relocation theorem.
-/

namespace ThreeSum.LightThreeSumColorDriver

open Light ColorParameters LightColorParametersCosts

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

def extra (colorProgram : Program) (pColor : ℕ) : Program :=
  [LightColorParameters.body (colorProgram.length+1),LightSmallDivide.body,
    LightColorScan.body (colorProgram.length+2) colorProgram.length pColor,
    LightColorScanHost.body (colorProgram.length+2)]

def program (colorProgram : Program) (pColor : ℕ) : Program := colorProgram++extra colorProgram pColor




def procs (colorProgram : Program) (pColor : ℕ) :
    LightColorScanHost.Procs (program colorProgram pColor) (colorProgram.length+3) where
  pScan := colorProgram.length+2
  scan := {
    pParameters := colorProgram.length
    pDivide := colorProgram.length+1
    pColor := pColor
    main := by apply getElem?_append_length_add; rfl
    parameters := by
      change (colorProgram++extra colorProgram pColor)[colorProgram.length+0]?=_
      apply getElem?_append_length_add
      rfl
    divide := by apply getElem?_append_length_add; rfl }
  main := by apply getElem?_append_length_add; rfl





















end ThreeSum.LightThreeSumColorDriver

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandPrimeCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# Charge the executed common-prime setup

The bound includes the generated pool, every aggregate candidate minimum,
all original band-score calls, and the computed chain depth. The size-only
budget uses the same quadratic owner bound as the physical mass theorem.
-/

namespace ThreeSum.BandPrimeCosts

open Scales BandScales CostLedger ArithmeticStageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def unit (p g U : ℕ) : ℕ :=
  LightModuloCounts.time p g g g U+LightWeightedScore.jointTime p+1000




































def core (p g R s U : ℕ) : ℕ := (R+1)*(s+1)^2*unit p g U





















































def timeBudget (k n : ℕ) : ℕ := LightPrimePool.time (primeWindow n)+
  15*(primeDepth radix n+1)*(3*bandCount n^2+1)*
    (LightPrimePool.size (primeWindow n)+1)^2*perTripleBudget k n

















end ThreeSum.BandPrimeCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_MassScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def wantedNumerator (n : ℕ) : ℕ :=
  9 * scheduleCount n * typedOutputs n * bandCount n ^ 2 * bandSize n

def rawTripleBound (n : ℕ) : ℕ := 3 * bandCount n ^ 2 * bandSize n ^ 3

def falseNumerator (k n : ℕ) : ℕ :=
  candidateCount n * rawTripleBound n * scoreLoss k n * primeLoss radix n











































noncomputable section

def wantedMajorant (n : ℕ) : ℝ := (wantedNumerator n : ℝ) / radix n

def falseMajorant (k n : ℕ) : ℝ := (falseNumerator k n : ℝ) / radix n

























































































































































end
end ThreeSum.MassScales

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_StageBounds


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
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def tableCount (n : ℕ) : ℕ := scheduleCount n * fullOutputs n

def encoderCount (n : ℕ) : ℕ := 2 * bandCount n * scheduleCount n * fullOutputs n

def boxCount (n : ℕ) : ℕ := 3 * bandCount n ^ 2 * scheduleCount n * allPrefixBoxes n

def initialCount (W : ℕ → ℕ) (n : ℕ) : ℕ := W n * queryTerms n 0

def activeCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  H n * representationBound n * microPartitions n * allQueryTerms n

def terminalChoices (n : ℕ) : ℕ := 2 ^ residualSize n (terminalDepth n)

def terminalCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * H n * representationBound n * terminalChoices n










noncomputable section

/-- A proved power upper bound with arbitrarily small positive slack. -/
def PowerBound (f : ℕ → ℕ) (a : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d)

namespace PowerBound














































end PowerBound










































































































































































end
end ThreeSum.StageBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOutputDecodeOriginal


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords


/-!
# The actual decoder specializes to the original global output record

The physical right-hand key index selects exactly the unchanged original
record, even when several records have equal key values. This module
identifies the two constructed rows with that record's original schedule
occurrences and Q masks, and exposes the source occurrence array directly.
-/

namespace ThreeSum.LightOutputDecodeOriginal

open Light GlobalEncoding OutputDecodeRecords

set_option maxHeartbeats 1200000

abbrev output (h J k : ℕ) : GlobalOutput h J :=
  (GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)

structure Rows (ν : ℕ → ℤ) (dst h J k : ℕ) : Prop where
  occurrences : ∀ j : Fin J, ν (dst+j.val)=(((output h J k j).1.val : ℕ) : ℤ)
  masks : ∀ j : Fin J,
    ν (dst+J+j.val)=(SubsetAddress.subsetMask (output h J k j).2.val : ℤ)
























variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {h J k masks dst work V : ℕ}









































end ThreeSum.LightOutputDecodeOriginal

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockIndex


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments


/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex

open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

def coordEquiv (J L : ℕ) : Coord J L ≃ Fin (J*L) :=
  (Equiv.sigmaEquivProd (Fin J) (Fin L)).trans finProdFinEquiv





def indexSet {J L : ℕ} (S : Finset (Coord J L)) : Finset (Fin (J*L)) :=
  S.map (coordEquiv J L).toEmbedding

def unindexSet {J L : ℕ} (S : Finset (Fin (J*L))) : Finset (Coord J L) :=
  S.map (coordEquiv J L).symm.toEmbedding
























































def coefficient {h J : ℕ} (o : Occurrences h J) (b : Bool)
    (c : Coord J (512*h)) : ℕ :=
  localPrime h ^ c.1.val * (mapAt h (o c.1) (c.2,b)).val

def maskHash {h J : ℕ} (o : Occurrences h J) (flip : Bool)
    (S : Finset (Coord J (512*h))) : ℕ :=
  OneHotMask.eval
    (OneHotMask.extend (coefficient o flip ∘ (coordEquiv J (512*h)).symm))
    (OneHotMask.extend (coefficient o (!flip) ∘ (coordEquiv J (512*h)).symm))
    (J*(512*h)) (SubsetAddress.subsetMask (indexSet S))







































end ThreeSum.BlockIndex

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockSourceOccurrenceOrder


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords


/-!
# Exact source-bank order and reuse by decoded global outputs

A source-bank row is the big-endian radix expansion of its physical index.
Its representative carries a fixed legal output subset solely to reuse the
original source definitions. No output-subset choice enters the stored row
or the source function. The actual global-output decoder supplies exactly
the bank index needed by a query.
-/

namespace ThreeSum.BlockSourceOccurrenceOrder

open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration

def occurrences (h J k : ℕ) : Occurrences h J := fun j =>
  ⟨(indices (scheduleSize h) J k).getD j.val 0,indices_getD_lt (schedule_pos h) j.isLt⟩

def representative (h J k : ℕ) : GlobalOutput h J :=
  fun j => (occurrences h J k j,(blockDefault h).2)

































end ThreeSum.BlockSourceOccurrenceOrder

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostBlockBucketTest


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Original endpoint semantics and exact Cartesian-test cost

The selected physical lengths are the original independently trimmed source
weights, after transport by the original-index enumeration. Thus the actual
tuple tester's pair charge is exactly the raw leaf weight.
-/

namespace ThreeSum.ReportingHostBlockBucketTest

open Light Finset BlockRows BlockEncoding BlockSourceEncoding LightSourceResidues
open SourceBuckets LightSourceBucketSelect ReportingHostBucketTest
open GlobalEncoding RawIncidences

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def leftResidue {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  LightResidues.residue (modulus h J) 1 (endpointLeft o S)

def rightResidue {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  LightResidues.residue (modulus h J) 1 (endpointRight o S)

def leftFlag {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  if LeftAllowed o S then 1 else 0

def rightFlag {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  if RightAllowed o S then 1 else 0





















































end ThreeSum.ReportingHostBlockBucketTest

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockForced


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
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
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting


/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

section FiniteRows

variable {J L : ℕ}

def prefixLeft (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) := join I u

def prefixRight (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L)) :=
  join I fun i => Q i \ u i

def remaining (I : Finset (Fin J)) (Q : Fin J → Finset (Fin L)) := join Iᶜ Q

def suffixDomain (I : Finset (Fin J)) : Finset (Coord J L) := join Iᶜ fun _ => univ


























































































end FiniteRows

def outputRows {h J : ℕ} (q : GlobalOutput h J) : Fin J → Finset (Fin (512 * h)) :=
  fun i => (q i).2.val

def completedTuples {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : Finset (ChoiceTuple h J) :=
  univ.filter fun t => tupleOutput t = q ∧ ∀ i ∈ I, (edge (t i)).val.1 = u i

def residual {h J : ℕ} (I : Finset (Fin J)) (t : ChoiceTuple h J) :=
  join Iᶜ fun i => (edge (t i)).val.1
































def admissibleResiduals {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : Finset (Finset (Coord J (512 * h))) :=
  (remaining I (outputRows q)).powerset.filter fun x =>
    LeftAllowed (outputOccurrences q) (prefixLeft I u ∪ x) ∧
    RightAllowed (outputOccurrences q)
      (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x))











































section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]




































/-- The stored suffix stages evaluated by the signed subset query. -/
def transformPrefixValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : ℤ :=
  Subset.mobius (fun z =>
    Subset.partialZeta (suffixDomain I)
      (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ)) (prefixLeft I u ∪ z) *
    Subset.partialZeta (suffixDomain I)
      (fun V => (rightWeights (outputOccurrences q) P d C c V : ℤ))
      (prefixRight I (outputRows q) u ∪ z))
    (remaining I (outputRows q))


























end WeightedCounts

end ThreeSum.BlockForced

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_RawPrefixCounts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting


/-!
# Exact bucket products at a wanted reporting prefix

The raw fiber used by the reporting theorem is here expanded into independently
counted B and C buckets. The wanted query fixes its original A index, lift,
and all chosen-map occurrences and output subsets.
-/

namespace ThreeSum.RawPrefixCounts

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding RawIncidences RawReporting

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def prefixItems {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :=
  (domain I w).filter fun r => (word r).take k = pre







def compatiblePairs {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :=
  (B ×ˢ C).filter fun p => globalModulus h J ∣ b p.1 % P - tupleLeft t ∧
    globalModulus h J ∣ c p.2 % P + d - tupleRight t

def completions {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Finset (ChoiceTuple h J) :=
  Finset.univ.filter fun t => tupleOutput t = q ∧ (partitionWord t).take k = pre

 def pack {h J : ℕ} (w : Wanted h J α)
    (s : Σ _t : ChoiceTuple h J, β × γ) : RawItem h J α β γ :=
  ⟨(w.1, s.2), (s.1, w.2.1)⟩
















































/-- The query first checks the fixed A key. Its remaining natural mass is
exactly a sum of products of the original-index B and C bucket sizes. -/
def bucketPrefixMass {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  if w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2 then
    ∑ t ∈ completions w.2.2 k pre, leftBucket P B b t * rightBucket P d C c t
  else 0








































end Indices

end ThreeSum.RawPrefixCounts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverCandidate


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# One complete local candidate: coefficients, bucket counts, and cover row

All data are constructed by fixed benchmark-language procedures. Separate
candidate histograms and coefficient rows are retained, while raw hash and
residue buffers are reusable. The preservation contract supports the outer
exhaustive candidate loop without forgetting previously completed rows.
-/

namespace ThreeSum.LightLocalCoverCandidate

open Light

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

def body (pDecode pHash pRow : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDecode [v 0, v 1, v 2, v 7, v 13] 14)
    (Light.Stmt.seq
      (.call pHash
        [v 0, v 5, v 8, (Light.Expr.op Light.Op.add) (v 8) (v 3), v 10, v 3, v 7,
          (Light.Expr.op Light.Op.add) (v 7) (v 0), v 1, v 13]
        14)
      (Light.Stmt.seq
        (.call pHash
          [v 0, v 5, v 9, (Light.Expr.op Light.Op.add) (v 9) (v 3), v 11, v 3,
            (Light.Expr.op Light.Op.add) (v 7) (v 0), v 7, v 1, v 13]
          14)
        (.call pRow
          [v 6, (Light.Expr.op Light.Op.add) (v 8) (v 3),
            (Light.Expr.op Light.Op.add) (v 9) (v 3), v 10, v 11, v 12, v 3, v 0,
            v 1, v 4, v 13]
          14))))

def time (L n p index : ℕ) : ℕ := LightWeightDecode.time L index+
  2*LightHashHistogram.time L n p p+LightLocalCoverRow.time L n p+200
def word (L n p cap index : ℕ) : ℕ := LightWeightDecode.word L p index+
  LightHashHistogram.word L p p+LightPairFlags.word L n p cap
def space (work L n p : ℕ) : ℕ :=
  work+2*(n*n)+(2*L+1)+max (L+1) (Nat.log 2 (L*p+1)+2)

def entry (L n p cap : ℕ) (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (w0 w1 : ℕ → ℕ) (r : ℕ) : ℕ :=
  let left := LightHashHistogram.code L p mask w0 w1
  let right := LightHashHistogram.code L p mask w1 w0
  LightSupportMark.bit (LightPairFlags.pairKey n p left right)
    (LightPairFlags.pairFlag L n cap bits left right
      (fun r => LightHistogram.count left r n) (fun r => LightHistogram.count right r n)) r (n*n)

def Preserved (μ ν : ℕ → ℤ) (work coef raw0 raw1 hist0 hist1 dst L n p : ℕ) : Prop :=
  ∀ a, a < work → Outside coef (2*L) a → Outside raw0 (2*n) a → Outside raw1 (2*n) a →
    Outside hist0 p a → Outside hist1 p a → Outside dst (p*p) a → ν a = μ a

structure Procs (P : Program) (pMain : ℕ) where
  pDecode : ℕ
  pHash : ℕ
  pRow : ℕ
  decode : LightWeightDecode.Procs P pDecode
  hash : LightHashHistogram.Procs P pHash
  row : LightLocalCoverRow.Procs P pRow
  main : P[pMain]? = some (body pDecode pHash pRow)

variable {lim : Limits} {P : Program} {d : ℕ}






























































































































































end ThreeSum.LightLocalCoverCandidate

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingPrefixArrays


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
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Constructing both complete prefix-mask product arrays in the same record order

The local pair arrays are built directly, then the verified positional-key
host is used twice with radix 2^L. Both results share the literal tuple order,
including separate entries for pairs with equal left or right projections.
-/

namespace ThreeSum.LightReportingPrefixArrays

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

variable {lim : Limits}

def localCount (L h : ℕ) : ℕ := L.choose (2*h)*(2*h).choose h

def body (pPairs pPowers pKeys : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pPairs [v 0, v 1, v 3, v 4, v 5, v 8] 9)
    (Light.Stmt.seq
      (.call pPowers [v 8, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 10)
      (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 8) (v 0))))
        (Light.Stmt.seq (.call pKeys [v 4, v 9, v 2, v 11, v 6] 12)
          (Light.Stmt.seq (.call pKeys [v 5, v 9, v 2, v 11, v 7] 13)
            (.set 0 (v 12)))))))

def program : Program := LightReportingPairRows.program ++
  [LightRadixKeys.body 8 9,LightRadixRows.body 6,body 7 2 8]

def time (L h k : ℕ) : ℕ :=
  LightReportingPairRows.time L h+powTableTime (L+1)+2*LightRadixKeys.time (localCount L h) k+250




































































































end ThreeSum.LightReportingPrefixArrays

end


