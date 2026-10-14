-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle11
-- name    : ThreeSum1962Source_Bundle11
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:18:03.296992+00:00
-- url     : https://prove2.me/theorems/4d804024-80ad-477c-91d1-b42744c63580
-- title:
--   Wanted-pair records, local-cover layouts, and stored reporting queries
-- statement:
--   This bundle defines the shifted wanted-pair output and its retained header. For pair count $c$, pair-array base $z$, and shift $\delta$, the four fields are
--   $$
--   [c,z,z+2c,\delta].
--   $$
--   It specifies lift-major A-key lists, pair decoding, physical owner catalogs, and the selected-color layout. Local-cover storage allocates coefficient rows, endpoint histograms, the support matrix, greedy workspace, and gathered schedule rows. Block-mask packing, selected-map flags, coordinate transport, valid reporting prefixes, and stored query values connect these arrays to reporting data. Light bodies cover source transforms, terminal endpoint preparation, canonical box sums, signed-box preprocessing, aggregate band scoring, and local parameter initialization.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockCoefficientRows.lean#L15-L62
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockIndexedQuery.lean#L28-L170
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockMaskLayout.lean#L11-L69
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockSourceFlags.lean#L20-L36
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockSourceRows.lean#L20-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockSourceTableLayout.lean#L10-L11
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorLayout.lean#L8-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawACatalog.lean#L22-L45
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandWeightedScore.lean#L18-L37
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBoxSum.lean#L20-L57
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCanonicalBoxSum.lean#L19-L57
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDenseSetupCosts.lean#L38-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverLayout.lean#L9-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverMatrix.lean#L18-L45
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalParameters.lean#L18-L51
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixCell.lean#L18-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingTerminalPreparation.lean#L21-L48
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSignedBoxSetup.lean#L17-L110
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSignedLeafCell.lean#L12-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandBatch.lean#L12-L28
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceRetainedStages.lean#L19-L56
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceStages.lean#L21-L48
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWantedDecode.lean#L19-L166
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWantedSetup.lean#L22-L72
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RawAKeyLists.lean#L19-L129
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostMasks.lean#L17-L69
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsWantedAccess.lean#L50-L70
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/StoredReporting.lean#L37-L109
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumWantedHostConditions.lean#L20-L48
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/UniformStageBounds.lean#L23-L25

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBoxSum


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
# Summing the canonical boxes of a sparse query

The missing-subset masks are loaded from an actual array, and every
summand is produced by the verified box-query procedure. Signed
accumulator bounds follow from bounds on the original leaf weights.
The final theorem identifies the sum with the canonical powerset-card
sum whenever the mask array is an exact enumeration of that family.
-/

namespace ThreeSum.LightBoxSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def boxValue {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (U : Finset (Fin L)) : ℤ := SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight

def partialSum {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (j : ℕ) : ℤ :=
  ((missing.map (boxValue Q weight)).take j).sum














def roundBody (pBox : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pBox
      [v 0, v 1, v 2, v 3, v 4, M ((Light.Expr.op Light.Op.add) (v 6) (v 10)),
        v 7, v 8]
      11)
    (.set 9 ((Light.Expr.op Light.Op.add) (v 9) (v 11))))

/-- Arguments: width, cutoff, Q cardinality and mask, missing cardinality,
number of masks, mask base, box-table base, polynomial scratch base. -/
def body (pBox : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 9 (k 0))
    (Light.Stmt.seq (.for 10 (v 5) (roundBody pBox)) (.set 0 (v 9))))

def time (L n : ℕ) : ℕ := n*(LightQueryBox.time L+60)+40

def Inv {L : ℕ} (μ : ℕ → ℤ) (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (cut t maskBase base work j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work,
      partialSum Q weight missing j,j,r],μ'⟩ ∧ Kept μ μ' work












































































































































end ThreeSum.LightBoxSum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixCell


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
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# A concrete box-leaf cell with global source and local box addresses

Multiplication lifts the local mask into the global suffix. The actual source
reader uses width W; a second actual compact-address computation uses width V.
Only the local compact box cell and polynomial scratch are modified.
-/

namespace ThreeSum.LightReportingSuffixCell

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell ReportingHostSuffix

variable {lim : Limits} {P : Program}

def body (pLeaf pAddress : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 15 ((Light.Expr.op Light.Op.mul) (v 9) (v 10)))
    (Light.Stmt.seq
      (.call pLeaf
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 8, v 15, v 11, v 12, v 14] 16)
      (Light.Stmt.seq (.call pAddress [v 7, v 8, v 9, v 14] 17)
        (.store ((Light.Expr.op Light.Op.add) (v 13) (v 17)) (v 16)))))

def time (W V : ℕ) : ℕ := LightSignedLeafGeneral.time W+LightDownsetAddress.time V+90


























































































































end ThreeSum.LightReportingSuffixCell

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSignedLeafCell


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


/-! # Writing one initial signed-product cell at its compact address -/

namespace ThreeSum.LightSignedLeafCell

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell

variable {lim : Limits} {P : Program}

/-- The actual leaf and address subprograms, with all of their dependencies. -/
structure Procs (P : Program) (pLeaf pAddress : ℕ) where
  (pUnion pLookup pSign pSize pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ)
  leaf : P[pLeaf]? = some (LightSignedLeafGeneral.body pUnion pLookup pSign)
  union : P[pUnion]? = some (LightMaskUnion.body pPowers pErase)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  sign : P[pSign]? = some LightSign.body
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
  erase : P[pErase]? = some (LightMaskErase.body pErase)

/-- Width, source cutoff, suffix stage, both prefix cardinalities and masks,
leaf cardinality and mask, source bases, destination, polynomial scratch. -/
def body (pLeaf pAddress : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pLeaf [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 12]
      13)
    (Light.Stmt.seq (.call pAddress [v 0, v 7, v 8, v 12] 14)
      (.store ((Light.Expr.op Light.Op.add) (v 11) (v 14)) (v 13))))

























































































end ThreeSum.LightSignedLeafCell

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceStages


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
# Original-input histogram construction followed by all suffix zeta stages

This fixed program constructs a trimmed source table from the physical input
array, then feeds that exact table into the existing costed suffix transform.
The rank/enumeration proof connects the sequential source writes to the
compact addresses. No initially populated source or zeta table is assumed.
-/

namespace ThreeSum.LightSourceStages

open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

/-- This record identifies literal bodies of the existing zeta program;
it contains no execution or semantic assumptions. -/
structure ZetaProcs (P : Program) (pMain : ℕ) where
  pSize : ℕ
  pPass : ℕ
  pEnumSetup : ℕ
  pEnum : ℕ
  pBatch : ℕ
  pCell : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  pOffset : ℕ
  pErase : ℕ
  main : P[pMain]? = some (LightZetaStages.body pSize pPass)
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  pass : P[pPass]? = some (LightZetaPass.body pEnumSetup pBatch)
  enumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum)
  enumeration : P[pEnum]? = some (LightSubsetEnumeration.body pEnum)
  batch : P[pBatch]? = some (LightZetaBatch.body pCell)
  cell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
  erase : P[pErase]? = some (LightMaskErase.body pErase)

variable {lim : Limits} {P : Program} {d : ℕ}

















































































































































end ThreeSum.LightSourceStages

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWantedSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys


/-!
# Original signed arrays to an actual shifted wanted-pair array

The closed host computes all residue and bucket addresses, runs both signed
scans, builds the right fibers, and executes the output-sensitive join. Four
header cells retain the pair count, pair-array address, next free address and
the actual shift. No residue array, histogram or matching list is supplied.
-/

namespace ThreeSum.LightWantedSetup

open Light WantedResidueKeys

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def leftCodes (free : ℕ) : ℕ := free+4
def rightCodes (free NL : ℕ) : ℕ := leftCodes free+NL
def bucketBase (free NL NR : ℕ) : ℕ := rightCodes free NL+NR
def pairBase (free NL NR M : ℕ) : ℕ :=
  LightSourceBucketSetup.next (bucketBase free NL NR) NR M

/-- Left/right signed arrays, lengths, modulus, shift, and free address. -/
def body (pResidues pBuckets pJoin : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.add) (v 6) (k 4)))
    (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 7) (v 2)))
      (Light.Stmt.seq (.set 9 ((Light.Expr.op Light.Op.add) (v 8) (v 3)))
        (Light.Stmt.seq (.set 10 ((Light.Expr.op Light.Op.add) (v 9) (v 4)))
          (Light.Stmt.seq
            (.set 11
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 9)
                  ((Light.Expr.op Light.Op.mul) (k 3) (v 4)))
                (k 1)))
            (Light.Stmt.seq (.set 12 ((Light.Expr.op Light.Op.add) (v 11) (v 3)))
              (Light.Stmt.seq
                (.call pResidues [v 0, v 7, v 2, v 4, v 4, v 12, v 5] 13)
                (Light.Stmt.seq
                  (.call pResidues [v 1, v 8, v 3, v 4, v 4, v 12, k 0] 13)
                  (Light.Stmt.seq (.call pBuckets [v 8, v 3, v 4, v 9] 13)
                    (Light.Stmt.seq
                      (.call pJoin [v 7, v 10, v 11, v 2, v 3, v 4, v 12] 14)
                      (Light.Stmt.seq (.store (v 6) (v 14))
                        (Light.Stmt.seq
                          (.store ((Light.Expr.op Light.Op.add) (v 6) (k 1))
                            (v 12))
                          (Light.Stmt.seq
                            (.store ((Light.Expr.op Light.Op.add) (v 6) (k 2))
                              ((Light.Expr.op Light.Op.add) (v 12)
                                ((Light.Expr.op Light.Op.mul) (k 2) (v 14))))
                            (Light.Stmt.seq
                              (.store ((Light.Expr.op Light.Op.add) (v 6) (k 3))
                                (v 5))
                              (.set 0 (v 6))))))))))))))))

def bucketProgram : Program := ReportingHostRelocation.program
  LightSourceResidues.program LightSourceBucketSetup.program

def joinedProgram : Program := ReportingHostRelocation.program
  bucketProgram LightWantedJoin.program

def program : Program := joinedProgram ++ [body 0 2 9]



def time (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) : ℕ :=
  LightSourceResidues.time NL M U D+LightSourceResidues.time NR M U D+
    LightSourceBucketSetup.time NR M+
    LightWantedJoin.time (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL+500

def space (free M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) : ℕ :=
  max (LightSourceResidues.space (pairBase free NL NR M) M U D)
    (pairBase free NL NR M+2*total M left right NL NR shift)

def Output (ν : ℕ → ℤ) (free M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : Prop :=
  ν free=(total M left right NL NR shift : ℤ) ∧
  ν (free+1)=(pairBase free NL NR M : ℤ) ∧
  ν (free+2)=((pairBase free NL NR M+2*total M left right NL NR shift : ℕ) : ℤ) ∧
  ν (free+3)=shift ∧
  ∃ ps : List (ℕ × ℕ), ps.length=total M left right NL NR shift ∧ ps.Nodup ∧
    (∀ i j, (i,j) ∈ ps ↔ i < NL ∧ j < NR ∧ (M : ℤ) ∣ left i+shift-right j) ∧
    Seg ν (pairBase free NL NR M) (WantedPairs.cells ps)

variable {lim : Limits}




































































































































end ThreeSum.LightWantedSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandBatch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout


/-! # Actual once-per-original-band histogram and bucket loop -/

namespace ThreeSum.LightSourceBandBatch

open Light BandPartition SourceBandLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

def body (pStep : ℕ) : Stmt :=
  .for 12 (v 8) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 13)

def time (n g p m U D : ℕ) : ℕ :=
  size n g*(LightSourceBandStep.time n g p m U D+180)+20

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightSourceBandStep.Procs P pStep
  main : P[pMain]? = some (body pStep)

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (src n g p m base : ℕ) (shift : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,n,g,p,m,shift,base,cap n g,size n g,data base n g,stride n g m,
      work base n g m,i,r],ν⟩ ∧
    (∀ j < i, SourceBandData.At ν f base n g p m shift j) ∧ Kept μ ν base

variable {lim : Limits} {P : Program} {d : ℕ}





























































end ThreeSum.LightSourceBandBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingTerminalPreparation


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
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Actual terminal endpoint and independent flag arrays

The two complete endpoint-mask arrays are prepared using the actual selected
occurrence, coefficient, and local trimming tables. Their buffers are
allocated by the host. Only the left orientation of the first array and the
right orientation of the second array are needed by the physical leaf scan.
-/

namespace ThreeSum.LightReportingTerminalPreparation

open Light BlockRows BlockIndex BlockEncoding BlockCoefficientRows BlockSourceFlags
open GlobalEncoding LocalCoverBounds

set_option maxHeartbeats 2600000
set_option maxRecDepth 12000

def span (W n : ℕ) : ℕ := 2*W+4*n+2
def second (base W n : ℕ) : ℕ := base+span W n
def leftRaw (base W : ℕ) : ℕ := base+2*W
def leftFlags (base W n : ℕ) : ℕ := base+2*W+2*n
def rightRaw (base W n : ℕ) : ℕ := second base W n+2*W+n
def rightFlags (base W n : ℕ) : ℕ := second base W n+2*W+3*n
def stop (base W n : ℕ) : ℕ := base+2*span W n

/-- J, L, h, local prime and cap; retained control pointers; two full-mask
arrays and their count; output base; bit, row, and arithmetic scratch. -/
def body (pPrepare : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 17 ((Light.Expr.op Light.Op.mul) (v 0) (v 1)))
    (Light.Stmt.seq
      (.set 18
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.mul) (k 2) (v 17))
            ((Light.Expr.op Light.Op.mul) (k 4) (v 12)))
          (k 2)))
      (Light.Stmt.seq (.set 19 ((Light.Expr.op Light.Op.add) (v 13) (v 17)))
        (Light.Stmt.seq
          (.set 20
            ((Light.Expr.op Light.Op.add) (v 13)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 17))))
          (Light.Stmt.seq (.set 21 ((Light.Expr.op Light.Op.add) (v 20) (v 12)))
            (Light.Stmt.seq (.set 22 ((Light.Expr.op Light.Op.add) (v 21) (v 12)))
              (Light.Stmt.seq
                (.set 23 ((Light.Expr.op Light.Op.add) (v 13) (v 18)))
                (Light.Stmt.seq
                  (.set 24 ((Light.Expr.op Light.Op.add) (v 23) (v 17)))
                  (Light.Stmt.seq
                    (.set 25
                      ((Light.Expr.op Light.Op.add) (v 23)
                        ((Light.Expr.op Light.Op.mul) (k 2) (v 17))))
                    (Light.Stmt.seq
                      (.set 26 ((Light.Expr.op Light.Op.add) (v 25) (v 12)))
                      (Light.Stmt.seq
                        (.set 27 ((Light.Expr.op Light.Op.add) (v 26) (v 12)))
                        (Light.Stmt.seq
                          (.call pPrepare
                            [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9,
                              v 10, v 12, v 13, v 19, v 20, v 21, v 22, v 14,
                              v 15, v 16]
                            28)
                          (Light.Stmt.seq
                            (.call pPrepare
                              [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9,
                                v 11, v 12, v 23, v 24, v 25, v 26, v 27, v 14,
                                v 15, v 16]
                              28)
                            (.set 0
                              ((Light.Expr.op Light.Op.add) (v 23)
                                (v 18))))))))))))))))

def program : Program := LightSourcePreparation.program ++ [body 0]
def time (h J n : ℕ) : ℕ := 2*LightSourcePreparation.time n J (512*h) (localPrime h)+800

variable {lim : Limits}



























































































end ThreeSum.LightReportingTerminalPreparation

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsWantedAccess


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored


/-!
# Every selected persistent row remains before the counter

The bounds keep the selected B and C bands independent. Each incidence and
occurrence is selected by its retained physical label, and every translated
pointer is bounded individually by the already occupied prefix.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2800000
set_option maxRecDepth 15000































structure WantedSourceEnds (X : Pointers) (pair bank cover srcB srcC i j code h J cut stop : ℕ) : Prop where
  pairHeader : pair+3≤stop
  bankHeader : bank+5≤stop
  coverHeader : cover+16≤stop
  leftHead : ReportingHostSourceSelection.leftHead X i+6≤stop
  rightHead : ReportingHostSourceSelection.rightHead X j+6≤stop
  leftCell : leftStageCell X i code+1≤stop
  rightCell : rightStageCell X j code+1≤stop
  sourceL : srcB+X.startL+X.sizeL≤stop
  sourceR : srcC+X.startR+X.sizeR≤stop
  offsetsL : X.offsetsL+modulus h J+1≤stop
  offsetsR : X.offsetsR+modulus h J+1≤stop
  flatL : X.flatL+X.sizeL≤stop
  flatR : X.flatR+X.sizeR≤stop
  occurrence : occurrenceRow X code J+J≤stop
  maps : X.maps+2*(512*h)*scheduleSize h≤stop
  candidates : X.candidates+scheduleSize h≤stop
  histL : X.histL+LightLocalCoverSchedule.rows h*localPrime h≤stop
  histR : X.histR+LightLocalCoverSchedule.rows h*localPrime h≤stop
  stagesL : X.stagesL+(J*(512*h)+1)*SubsetAddress.downsetCap (J*(512*h)) cut≤stop
  stagesR : X.stagesR+(J*(512*h)+1)*SubsetAddress.downsetCap (J*(512*h)) cut≤stop





























































































end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_RawAKeyLists


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
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences


/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists

open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option maxHeartbeats 900000

abbrev Record (xs : List ℤ) := Fin 3 × Fin xs.length

def records (xs : List ℤ) : List (Record xs) :=
  (List.finRange 3).product (List.finRange xs.length)

def key (P : ℤ) (xs : List ℤ) (r : Record xs) : ℤ :=
  xs.getD r.2.val 0 % P+lift r.1*P

def keys (P : ℤ) (xs : List ℤ) : List ℤ := (records xs).map (key P xs)

theorem records_length (xs : List ℤ) : (records xs).length=3*xs.length := by
  calc
    _ = (List.finRange 3).length*(List.finRange xs.length).length := List.length_product _ _
    _ = _ := by rw [List.length_finRange,List.length_finRange]











































































def selected (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) : ℕ :=
  GlobalKeyOffset.selected M (keys P xs) h J










def wanted (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    Finset (RawReporting.Wanted h J (Fin xs.length)) :=
  Finset.univ.filter fun w =>
    (M : ℤ) ∣ xs.getD w.1.val 0%P+lift w.2.1*P+d-globalKey w.2.2

theorem mem_wanted {M h J : ℕ} {P d : ℤ} {xs : List ℤ}
    {w : RawReporting.Wanted h J (Fin xs.length)} :
    w ∈ wanted M P xs h J d ↔
      (M : ℤ) ∣ xs.getD w.1.val 0%P+lift w.2.1*P+d-globalKey w.2.2 := by
  simp only [wanted,Finset.mem_filter,Finset.mem_univ,true_and]



















end ThreeSum.RawAKeyLists

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandRawACatalog


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA


/-!
# Read the retained headers, build owner records, and extract A incidences

The fixed program reads the actual sorted-A length and all three actual
band counts from the retained headers. It constructs the exact physical
BC, AB, AC records, then copies their flagged A bands into the three packed
value/owner/position arrays. No supplied enumeration or hidden input list
is used by either machine loop.
-/

namespace ThreeSum.LightBandRawACatalog

open Light BandEnumeration BandCandidateRows BandRawA

set_option maxHeartbeats 2100000
set_option maxRecDepth 8000

/-- Tables, record output, sorted A, A/B/C headers, g, value output. -/
def body (pCandidates pRaw : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 8 (M (v 3)))
    (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
      (Light.Stmt.seq (.set 10 (M ((Light.Expr.op Light.Op.add) (v 4) (k 1))))
        (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 5) (k 1))))
          (Light.Stmt.seq (.call pCandidates [v 0, v 1, v 9, v 10, v 11] 12)
            (.call pRaw [v 1, v 12, v 2, v 8, v 6, v 7] 0))))))

def time (a b c g : ℕ) : ℕ :=
  LightBandCandidates.time a b c+LightBandRawA.time (LightBandEnumeration.count a b c) g+300

def word (n a b c g : ℕ) : ℕ :=
  LightBandCandidates.word a b c+LightBandRawA.word n g (LightBandEnumeration.count a b c)+20

def space (vals a b c g : ℕ) : ℕ :=
  LightBandRawA.space vals (LightBandEnumeration.count a b c) g

structure Procs (P : Program) (pMain : ℕ) where
  pCandidates : ℕ
  pRaw : ℕ
  candidates : LightBandCandidates.Procs P pCandidates
  raw : LightBandRawA.Procs P pRaw
  main : P[pMain]?=some (body pCandidates pRaw)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}



























































































































end ThreeSum.LightBandRawACatalog

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumWantedHostConditions


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# Uniform size conditions and original-color semantics for the wanted consumer

The cutoff is chosen before any memory, color, or original array. The
auxiliary-prime separation premise is proved for the actual generated pool.
-/

namespace ThreeSum.ThreeSumWantedHostConditions

open Light Scales BandScales Filter RawIncidences BandRawA ColorClassLists
open scoped Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

structure Ready (k n : ℕ) : Prop where
  positive : 0<n
  half : 0<microHalf (inputBits n)
  radix : 4≤Scales.radix n
  divisor : divisorBudget k n*primeWindow n≤candidateCount n*(4*(k+2)*(inputBits n+1))
  separates : ∀ z : ℤ, z≠0 → z.natAbs≤3*n^k → ∃ l∈DenseGuard.actualAux n, ¬l∣z

theorem ready_eventually (k : ℕ) : ∀ᶠ n : ℕ in atTop, Ready k n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually (eventually_ge_atTop 1),
    radix_eventually_ge_four,actual_divisor_budget k,DenseGuard.actual_aux_separates k]
      with n hn hh hr hd hs
  simp only [Function.comp_apply] at hh
  exact ⟨by omega,by omega,hr,hd,hs⟩

theorem exists_cutoff (k : ℕ) : ∃ N : ℕ, ∀ n≥N, Ready k n :=
  eventually_atTop.mp (ready_eventually k)

noncomputable def cutoff (k : ℕ) : ℕ := Classical.choose (exists_cutoff k)




def OriginalZero (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop :=
  let rs := sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
  ∃ t∈finiteAllProducts A.length B.length C.length (bandSize n) rs,
    difference (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t=0






















































end ThreeSum.ThreeSumWantedHostConditions

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout

def colors (free : ℕ) : ℕ := free+8
def class0 (free n : ℕ) : ℕ := colors free+n
def class1 (free n : ℕ) : ℕ := class0 free n+n+1
def class2 (free n : ℕ) : ℕ := class1 free n+n+1
def av (free n : ℕ) : ℕ := class2 free n+n+1
def ae (free n : ℕ) : ℕ := av free n+n
def bv (free n : ℕ) : ℕ := ae free n+2+2*n
def be (free n : ℕ) : ℕ := bv free n+n
def cv (free n : ℕ) : ℕ := be free n+2+2*n
def ce (free n : ℕ) : ℕ := cv free n+n
def tables (free n : ℕ) : ℕ := ce free n+2+2*n
def rec (free n g : ℕ) : ℕ := tables free n+ColorBandBounds.count n g
def vals (free n g : ℕ) : ℕ := rec free n g+4*ColorBandBounds.count n g
def normalizedEnd (free n g : ℕ) : ℕ := LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g
def prime (free n g : ℕ) : ℕ := normalizedEnd free n g+1
def cover (free n g M y : ℕ) : ℕ := EncodedColorPrimeData.nextFree (prime free n g) M y

def normalizedHeads (free n g : ℕ) : List ℤ :=
  [av free n,ae free n,bv free n,be free n,cv free n,ce free n,rec free n g,vals free n g]
















































end ThreeSum.EncodedColorLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalParameters


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Complete local integer parameter initialization

From the microblock half-size this program constructs the graph counts,
selects the deterministic prime, and computes the exact separable bucket
cap. The first six output cells are the graph counts; the next two contain
the prime and cap. Scratch may be reused by every stage.
-/

namespace ThreeSum.LightLocalParameters

open Light LocalCoverBounds

def numerator (h : ℕ) : ℕ :=
  4*(localPrime h+vertexCount (512*h) h)+localPrime h-1

def values (h : ℕ) : List ℤ :=
  LightLocalCounts.values h ++ [(localPrime h : ℤ),localBucketCap h]

def body (pCounts pPrime pDiv : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCounts [v 0, v 1, v 2] 3)
    (Light.Stmt.seq (.call pPrime [v 3, v 2] 4)
      (Light.Stmt.seq (.set 5 (M ((Light.Expr.op Light.Op.add) (v 1) (k 1))))
        (Light.Stmt.seq
          (.set 6
            ((Light.Expr.op Light.Op.sub)
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.mul) (k 4)
                  ((Light.Expr.op Light.Op.add) (v 4) (v 5)))
                (v 4))
              (k 1)))
          (Light.Stmt.seq (.call pDiv [v 6, v 4] 7)
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 1) (k 6)) (v 4))
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 1) (k 7)) (v 7))
                (.set 0 (v 4)))))))))

def time (h : ℕ) : ℕ := LightLocalCounts.time h+
  LightSelectedPrime.time (localThreshold h)+
  LightSmallDivide.time (numerator h) (localPrime h)+200

def space (work h : ℕ) : ℕ :=
  max (LightLocalCounts.space work h) (LightSelectedPrime.space work (localThreshold h))

def word (h : ℕ) : ℕ := LightLocalCounts.word h+
  LightSelectedPrime.word (localThreshold h)+20*(localPrime h+vertexCount (512*h) h+1)

structure Procs (P : Program) (pMain : ℕ) where
  pCounts : ℕ
  pPrime : ℕ
  pDiv : ℕ
  counts : LightLocalCounts.Procs P pCounts
  prime : LightSelectedPrime.Procs P pPrime
  divide : P[pDiv]? = some LightSmallDivide.body
  main : P[pMain]? = some (body pCounts pPrime pDiv)

variable {lim : Limits} {P : Program} {d : ℕ}






























































































end ThreeSum.LightLocalParameters

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandWeightedScore


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore


/-!
# Actual aggregate weighted scoring over the band-owner catalog

The fixed program scans the physical four-cell records once, reuses the
same counting scratch for every flagged owner, and sums their exact scores.
Both the original arrays and complete owner catalog are retained.
-/

namespace ThreeSum.LightBandWeightedScore

open Light BandCandidateRows BandWeightedScore

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def body (pCell : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 13 (k 0))
    (Light.Stmt.seq
      (.for 14 (v 8)
        (Light.Stmt.seq
          (.call pCell
            [v 0, v 1, v 2, v 3, v 4, v 5, v 6,
              (Light.Expr.op Light.Op.add) (v 7)
                ((Light.Expr.op Light.Op.mul) (k 4) (v 14)),
              v 9, v 10, v 11, v 12]
            15)
          (.set 13 ((Light.Expr.op Light.Op.add) (v 13) (v 15)))))
      (.set 0 (v 13))))

def program : Program := LightBandWeightedScoreCell.program ++ [body 15]



def time (maxMod g R s U : ℕ) : ℕ := R*(LightBandWeightedScoreCell.time maxMod g s U+100)+50

def word (maxMod nA nB nC g R s U : ℕ) : ℕ :=
  LightBandWeightedScoreCell.word maxMod nA nB nC g s U+R*(s*g^3)+R+8

def Inv (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (a b c nA nB nC g recs R q aux s free i : ℕ) (σ : State) : Prop :=
  ∃ (value : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,q,aux,s,free,f i,i,value],ν⟩ ∧ Kept μ ν free

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}
















































































































end ThreeSum.LightBandWeightedScore

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDenseSetupCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# Charge the actual threshold construction

One final aggregate score is covered by the existing executed arithmetic
budget. Computing the cap and storing its product adds only O(J) work.
This is a cost theorem for this concrete stage, not a full solver claim.
-/

namespace ThreeSum.LightDenseSetupCosts

open Scales BandScales CostLedger ArithmeticStageBounds Parameters

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000



















def timeBudget (k n : ℕ) : ℕ :=
  BandPrimeCosts.timeBudget k n+20*blockCount (inputBits n)+570









open Filter Real StageBounds
open scoped Topology

noncomputable section




























end
end ThreeSum.LightDenseSetupCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_UniformStageBounds


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
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-!
# A uniform size-only budget for the six principal stage counts

Both mass budgets are executable integer divisions of the concrete size
majorants.  The final bound is uniform in the input-dependent masses: the
eventual size threshold is chosen before `W`, `H`, `P`, or `H1` are quantified.
This remains a theorem about the specified finite work quantities, not a
claim that a complete machine has been proved to execute within them.
-/

namespace ThreeSum.UniformStageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def wantedBudget (n : ℕ) : ℕ := wantedNumerator n / radix n

def falseBudget (k n : ℕ) : ℕ := falseNumerator k n / radix n









noncomputable section






























































































































end
end ThreeSum.UniformStageBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWantedDecode


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords


/-!
# Decode an actual emitted wanted-pair cell

The host loads the two physical indices, splits the left index into its
incidence position and lift, and decodes the right index into the original
occurrence and Q-mask rows. Its four-cell header retains both source labels
and the occurrence-only bank index. Division is the verified binary routine.
-/

namespace ThreeSum.LightWantedDecode

open Light GlobalEncoding OutputDecodeRecords

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

/-- Pair array, pair slot, incidence count, block count, schedule count,
layer count, retained layer masks, destination, and scratch pointer. -/
def body (pDivide pDecode : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 9
      (M
        ((Light.Expr.op Light.Op.add) (v 0)
          ((Light.Expr.op Light.Op.mul) (k 2) (v 1)))))
    (Light.Stmt.seq
      (.set 10
        (M
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v 0)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 1)))
            (k 1))))
      (Light.Stmt.seq (.call pDivide [v 9, v 2, v 8] 11)
        (Light.Stmt.seq
          (.set 12
            ((Light.Expr.op Light.Op.sub) (v 9)
              ((Light.Expr.op Light.Op.mul) (v 11) (v 2))))
          (Light.Stmt.seq
            (.call pDecode
              [v 10, v 3, v 4, v 5, v 6, (Light.Expr.op Light.Op.add) (v 7) (k 4),
                v 8]
              13)
            (Light.Stmt.seq (.store (v 7) (v 12))
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 7) (k 1)) (v 11))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 7) (k 2)) (v 10))
                  (Light.Stmt.seq
                    (.store ((Light.Expr.op Light.Op.add) (v 7) (k 3)) (v 13))
                    (.set 0 (v 13)))))))))))

def time (J V : ℕ) : ℕ :=
  LightOutputDecodeDivide.budget V+LightOutputDecode.time J V+250

def word (V N h J : ℕ) : ℕ :=
  LightOutputDecode.word V (scheduleSize h) (layerCount h) J (2^(512*h))+
    4*V+4*N+32

abbrev space := LightOutputDecode.space






structure Stored (ν : ℕ → ℤ) (dst N h J i j : ℕ) : Prop where
  position : ν dst=((i%N : ℕ) : ℤ)
  liftIndex : ν (dst+1)=((i/N : ℕ) : ℤ)
  outputIndex : ν (dst+2)=(j : ℤ)
  bankIndex : ν (dst+3)=(OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ)
  rows : LightOutputDecodeOriginal.Rows ν (dst+4) h J j

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}














































































































def program : Program := LightOutputDecode.program ++ [body 3 0]


























end ThreeSum.LightWantedDecode

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockCoefficientRows


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows

open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

def flat (J L p : ℕ) (sel : ℕ → ℕ) (w : ℕ → ℕ → ℕ) : ℕ → ℕ :=
  OneHotMask.extend fun i : Fin (J*L) =>
    let c := (coordEquiv J L).symm i
    p^c.1.val * w (sel c.1.val) c.2.val

































def occurrenceIndices {h J : ℕ} (o : Occurrences h J) : ℕ → ℕ :=
  OneHotMask.extend fun i => (o i).val





def mapRow (h : ℕ) (b : Bool) (s : ℕ) : ℕ → ℕ :=
  if hs : s < scheduleSize h then
    OneHotMask.extend fun i : Fin (512*h) => (mapAt h ⟨s,hs⟩ (i,b)).val
  else fun _ => 0








































end ThreeSum.BlockCoefficientRows

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockMaskLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout

open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators

def rowMask {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) : ℕ :=
  2^(i.val*L)*subsetMask (rows i)

def prefixMask {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) : ℕ :=
  subsetMask (indexSet (join (prefixIndices J k) rows))


















































def rawMasks {J L : ℕ} (rows : Fin J → Finset (Fin L)) : List ℕ :=
  List.ofFn (fun i => subsetMask (rows i))

def packedMasks {J L : ℕ} (rows : Fin J → Finset (Fin L)) : List ℕ := List.ofFn (rowMask rows)












end ThreeSum.BlockMaskLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockSourceFlags


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments


/-!
# Concrete trimming flags equal the original independent endpoint conditions

The exact greedy occurrence-to-candidate bridge connects retained candidate
bucket tables to the unchanged `mapAt` schedule. A product of row flags is
therefore exactly the original `LeftAllowed` or `RightAllowed` condition.
-/

namespace ThreeSum.BlockSourceFlags

open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding

set_option maxHeartbeats 1200000

def candidateIndices (h s : ℕ) : ℕ := (LightLocalCoverSchedule.indices h).getD s 0








def bits {J L : ℕ} (S : Finset (Coord J L)) : ℕ → ℕ :=
  LightMaskBits.bit (J*L) (SubsetAddress.subsetMask (indexSet S))

def leftCount (h k : ℕ) : ℕ → ℕ :=
  LocalCoverMatrix.leftCount (LightLocalCoverSchedule.candidate h k) h

def rightCount (h k : ℕ) : ℕ → ℕ :=
  LocalCoverMatrix.rightCount (LightLocalCoverSchedule.candidate h k) h























































































end ThreeSum.BlockSourceFlags

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockSourceRows


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightSourceRowScan
end ThreeSum.LightSourceRowScan
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments


/-!
# Global mask bits are the exact local block rows

The physical row scan's cardinality and two raw hashes agree with the local
subsets and one-hot words in `BlockEncoding`. This bridge allows independent
trimming to use the selected map's exact retained bucket-count table.
-/

namespace ThreeSum.BlockSourceRows

open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators

set_option maxHeartbeats 1000000

def bits {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) (i : ℕ) : ℕ :=
  LightMaskBits.bit (J*L) (SubsetAddress.subsetMask (indexSet S)) (j.val*L+i)











































end ThreeSum.BlockSourceRows

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockSourceTableLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Compact source arrays in the unchanged block-query coordinate system -/

namespace ThreeSum.BlockSourceTableLayout

open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding

def sets (h J cut i : ℕ) : Finset (Coord J (512*h)) :=
  unindexSet (SourceTableLayout.setAt (J*(512*h)) cut i)




























end ThreeSum.BlockSourceTableLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostMasks


set_option autoImplicit false
set_option relaxedAutoImplicit false
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
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks

open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

def blockSet {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (join {i} (fun _ => S))






















def localRow {J L : ℕ} (i : Fin J) (T : Finset (Fin (J*L))) : Finset (Fin L) :=
  row (unindexSet T) i






















def globalChildren {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :=
  QueryCoordinates.missingSets (blockSet i Q) h

def localChildren {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :=
  (globalChildren i Q h).map (localRow i)




























































































































































































end ThreeSum.ReportingHostMasks

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockIndexedQuery


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting


/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery

open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false





def suffixStage (J L k : ℕ) : ℕ := (J-k)*L
























def leftPrefix {J L : ℕ} (k : ℕ) (u : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (prefixLeft (prefixIndices J k) u)

def rightPrefix {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (prefixRight (prefixIndices J k) Q u)

def querySet {J L : ℕ} (k : ℕ) (Q : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (remaining (prefixIndices J k) Q)

























































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftSource {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h))
    (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ))

def rightSource {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (q : GlobalOutput h J) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h))
    (fun S => (rightWeights (outputOccurrences q) P d C c S : ℤ))

































def queryValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (k : ℕ)
    (u : Fin J → Finset (Fin (512*h))) : ℤ :=
  Subset.mobius (fun S =>
    SubsetStages.stageValue (leftSource P B b q) (suffixStage J (512*h) k) (leftPrefix k u ∪ S) *
    SubsetStages.stageValue (rightSource P d C c q) (suffixStage J (512*h) k)
      (rightPrefix k (outputRows q) u ∪ S)) (querySet k (outputRows q))




















end Histograms

end ThreeSum.BlockIndexedQuery

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_StoredReporting


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
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
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced


















def prefixRows {J L : ℕ} (pre : List (Finset (Fin L))) : Fin J → Finset (Fin L) :=
  fun i => pre[i.val]?.getD ∅

























def ValidPrefix {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Prop :=
  pre.length = k ∧ ∀ i : Fin J, i.val < k →
    prefixRows pre i ⊆ outputRows q i ∧ (prefixRows pre i).card = h

instance {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Decidable (ValidPrefix q k pre) := by
  unfold ValidPrefix
  infer_instance

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




















/-- A signed subset query, with the inexpensive validity and fixed A-key
checks displayed explicitly. Its natural value is established below. -/
def storedQueryValue {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℤ :=
  if ValidPrefix w.2.2 k pre then
    if w.1 ∈ A ∧ globalModulus h J ∣
        (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2 then
      transformPrefixValue P d B C b c w.2.2 (prefixIndices J k) (prefixRows pre)
    else 0
  else 0



































































































end Indices

end ThreeSum.StoredReporting

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverLayout


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


/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

def vertices (h : ℕ) : ℕ := LocalMaskGraph.vertexCount (512*h) h
def bitPtr (base h : ℕ) : ℕ := base+vertices h
def maps (base h : ℕ) : ℕ := bitPtr base h+vertices h*(512*h)
def raw0 (base h : ℕ) : ℕ := maps base h+rows h*(2*(512*h))
def raw1 (base h : ℕ) : ℕ := raw0 base h+2*vertices h
def hist0 (base h : ℕ) : ℕ := raw1 base h+2*vertices h
def hist1 (base h : ℕ) : ℕ := hist0 base h+rows h*localPrime h
def matrixPtr (base h : ℕ) : ℕ := hist1 base h+rows h*localPrime h
def work (base h : ℕ) : ℕ := matrixPtr base h+rows h*cols h
def scheduleMaps (base h : ℕ) : ℕ :=
  work base h+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h)
def candidates (base h : ℕ) : ℕ := LightCoverGreedy.out (work base h) (rows h) (cols h)

def space (base h : ℕ) : ℕ :=
  max (LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h))
    (scheduleMaps base h+scheduleSize h*(2*(512*h)))

































end ThreeSum.LightLocalCoverLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverMatrix


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Constructing every candidate coefficient, histogram, and cover-matrix row

One literal loop visits the radix candidates in increasing index order.
Temporary raw/residue buffers are reused. All candidate coefficient rows,
both histogram tables, and all Boolean matrix rows remain in memory.
-/

namespace ThreeSum.LightLocalCoverMatrix

open Light

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

def body (pCandidate : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 16 ((Light.Expr.op Light.Op.mul) (v 1) (v 1)))
    (.for 14 (v 2)
      (.call pCandidate
        [v 0, v 1, v 14, v 3, v 4, v 5, v 6,
          (Light.Expr.op Light.Op.add) (v 7)
            ((Light.Expr.op Light.Op.mul) (v 14)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 0))),
          v 8, v 9,
          (Light.Expr.op Light.Op.add) (v 10)
            ((Light.Expr.op Light.Op.mul) (v 14) (v 1)),
          (Light.Expr.op Light.Op.add) (v 11)
            ((Light.Expr.op Light.Op.mul) (v 14) (v 1)),
          (Light.Expr.op Light.Op.add) (v 12)
            ((Light.Expr.op Light.Op.mul) (v 14) (v 16)),
          v 13]
        15)))

def time (L n p N : ℕ) : ℕ := N*(LightLocalCoverCandidate.time L n p N+200)+30

def Tables (μ : ℕ → ℤ) (L n p cap maps hist0 hist1 dst : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ j < N,
    LightWeightDecode.Rows μ (maps+j*(2*L)) L p j ∧
    (∀ r < p,
      μ (hist0+j*p+r) = (LightHistogram.count (LightHashHistogram.code L p mask (w0 j) (w1 j)) r n : ℤ) ∧
      μ (hist1+j*p+r) = (LightHistogram.count (LightHashHistogram.code L p mask (w1 j) (w0 j)) r n : ℤ)) ∧
    (∀ r < p*p, μ (dst+j*(p*p)+r) = (LightLocalCoverCandidate.entry L n p cap mask bits (w0 j) (w1 j) r : ℤ))

def Inv (μ : ℕ → ℤ) (L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work,i,r,p*p],μ'⟩ ∧
    Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 i ∧ Kept μ μ' maps

structure Procs (P : Program) (pMain : ℕ) where
  pCandidate : ℕ
  candidate : LightLocalCoverCandidate.Procs P pCandidate
  main : P[pMain]? = some (body pCandidate)

variable {lim : Limits} {P : Program} {d : ℕ}










































































































































































end ThreeSum.LightLocalCoverMatrix

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCanonicalBoxSum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Complete execution of the canonical box part of a sparse query

The query builds its own missing-subset array inside the actual query mask,
then evaluates every canonical box. Enumeration completeness and uniqueness
are discharged by the verified query-coordinate construction.
-/

namespace ThreeSum.LightCanonicalBoxSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}

/-- Procedure layout shared by complete sparse queries. -/
structure Procs (P : Program) (pEnum pSum : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pCore : ℕ
  pBox : ℕ
  pMinimum : ℕ
  pLookup : ℕ
  pSize : ℕ
  pAddress : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pRank : ℕ
  pOffset : ℕ
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightBoxSum.body pBox)
  box : P[pBox]? = some (LightQueryBox.body pMinimum pLookup)
  minimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  table : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body

/-- Width, cutoff, query cardinality and mask, missing cardinality,
box-table base, output-mask buffer, polynomial scratch. -/
def body (pEnum pSum : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnum [v 0, v 3, v 4, v 6, v 7] 8)
    (.call pSum [v 0, v 1, v 2, v 3, v 4, v 8, v 6, v 5, v 7] 0))

def time (W c t : ℕ) : ℕ :=
  LightQueryEnumeration.time W c t+LightBoxSum.time W (c.choose t)+50



























































































































end ThreeSum.LightCanonicalBoxSum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSignedBoxSetup


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
# Complete compact box preprocessing from the two stored source transforms

The initial signed-product leaf table is computed by machine execution.
The program then constructs every compact prefix-zeta stage, yielding the
exact box-table contract consumed by the sparse query machine.
-/

namespace ThreeSum.LightSignedBoxSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- The arguments agree with the initial leaf-table builder. -/
def body (pLeafTable pBoxStages : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pLeafTable
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12] 13)
    (.call pBoxStages [v 0, v 2, v 10, v 11, v 12] 0))

















































































def program : Program :=
  [body 1 2,LightSignedLeafTable.body 3 4,LightBoxStages.body 9 21,
    LightSubsetEnumerationSetup.body 14 20,LightSignedLeafBatch.body 5,
    LightSignedLeafCell.body 6 10,LightSignedLeafGeneral.body 7 8 19,LightMaskUnion.body 14 18,
    LightStageLookup.body 9 10,LightDownsetSize.body 11 17,LightDownsetAddress.body 11 17,
    LightSubsetSetup.body 12 14 16,buildBody 13 15,fillBody,powTableBody,rowBody 24,
    rankBody 16,LightSubsetOffset.body,LightMaskErase.body 18,LightSign.body,
    LightSubsetEnumeration.body 20,LightZetaPass.body 3 22,LightZetaBatch.body 23,
    LightZetaCell.body 11 17 18 16,LightArray.linearBody]


































































end ThreeSum.LightSignedBoxSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceRetainedStages


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
# Source stages gathered from a retained original-input histogram

The histogram is built once for a source band and fixed modulus/offset by
`LightSourceHistogram`. This program then gathers the independently trimmed
source for each occurrence vector and runs the actual suffix transforms.
Neither the original array nor the full histogram is rescanned in this loop.
-/

namespace ThreeSum.LightSourceRetainedStages

open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def source {L : ℕ} (m : ℕ) (endpoint : Finset (Fin L) → ℤ)
    (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ) (S : Finset (Fin L)) : ℤ :=
  ((if flag S = 1 then hist (LightResidues.residue m 1 (endpoint S)) else 0 : ℕ) : ℤ)












/-- Arguments: raw endpoints, independent flags, retained histogram, output
stage base, modulus, reusable work, width, cutoff, mask scratch, exact cap. -/
def body (pGather pZeta : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pGather [v 0, v 1, v 2, v 3, v 9, v 4, v 5] 10)
    (.call pZeta [v 6, v 7, v 3, v 8, v 5] 10))

def time (L cut E : ℕ) : ℕ :=
  LightSourceGather.time (downsetCap L cut) E+LightZetaStages.time L cut+100

def space (work L E : ℕ) : ℕ :=
  max (work+(Nat.log 2 (E+1)+2)) (work+tableSize L+(L+1))

def word (L m E B : ℕ) : ℕ :=
  4*E+4*m+16+B+(L+1)*2^(L+1)+2^L*B

structure Procs (P : Program) (pMain : ℕ) where
  pGather : ℕ
  pEmod : ℕ
  pZeta : ℕ
  gather : P[pGather]? = some (LightSourceGather.body pEmod)
  emod : P[pEmod]? = some emodBody
  zeta : LightSourceStages.ZetaProcs P pZeta
  main : P[pMain]? = some (body pGather pZeta)

variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightSourceRetainedStages

end


