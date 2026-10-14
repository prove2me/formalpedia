-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle13
-- name    : ThreeSum1962Source_Bundle13
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:21:27.544961+00:00
-- url     : https://prove2.me/theorems/0d97bef8-f79a-40d1-b19c-82996a43457e
-- title:
--   Suffix-query composition, retained source batches, and packed prefix records
-- statement:
--   This bundle defines the explicit-subset and canonical-box portions of suffix queries, their signed sums and local tables, and terminal mask enumeration and endpoint preparation. For $N$ physical prefix records with natural keys $k_i$, their packed codes are
--   $$\operatorname{code}_i=k_i(N+1)+i\qquad(0\le i<N).$$
--   The original record index occupies the low digit. Further definitions assemble local-cover setup, retained left/right source-bank batches, and common-prime construction for selected colors. Wanted-workspace layouts specify counter, decoding, access, and frontier regions, while cumulative root-mass and terminal-cost functions describe the quantities used by later traversal contracts.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandPrimeScales.lean#L20-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/DenseGuard.lean#L24-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPrimeConstruction.lean#L20-L61
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPrimeSetup.lean#L28-L29
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceBatch.lean#L21-L81
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceBatchStep.lean#L20-L42
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceRetainedProgram.lean#L19-L65
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorPrime.lean#L14-L42
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorPrimeCore.lean#L18-L50
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverBuild.lean#L21-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverSetup.lean#L21-L223
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixBatch.lean#L12-L28
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixBoxes.lean#L14-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixExplicit.lean#L13-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixLower.lean#L18-L64
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixQuery.lean#L20-L88
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixSetup.lean#L18-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixSum.lean#L13-L59
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixTable.lean#L18-L160
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingTerminalMasks.lean#L21-L35
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingTerminalPrepared.lean#L23-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedLayout.lean#L22-L83
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L20-L121
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L25-L33
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L51-L102
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L19-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostTerminalBatch.lean#L26-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostTerminalCosts.lean#L32-L42
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedLayout.lean#L21-L85
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandBanksCosts.lean#L99-L101

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
import Definitions.Def_ThreeSum1962Source_Bundle12
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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixBatch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Evaluating one locally enumerated suffix layer against global source tables -/

namespace ThreeSum.LightReportingSuffixBatch

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
open ReportingHostSuffix

variable {lim : Limits} {P : Program}

def body (pCell : ℕ) : Stmt :=
  .for 16 (v 10)
    (.call pCell [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 9,M (((Light.Expr.op Light.Op.add) (v 11) (v 16))),
      v 8,v 12,v 13,v 14,v 15] 17)

def time (W V n : ℕ) : ℕ := n*(LightReportingSuffixCell.time W V+65)+20

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage cardinal maskBase baseL baseR dst work : ℕ)
    (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work,j,r],μ'⟩ ∧
    KeptBut μ μ' work dst (downsetCap V boxCut) ∧
    TableAt μ' dst boxCut
      (LightSignedLeafBatch.values μ dst (masks.take j) (leafWeight hfit f g stage preL preR))




















































































































end ThreeSum.LightReportingSuffixBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixBoxes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix

variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def localLeaf {h J k : ℕ} (hk : k ≤ J) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) : Finset (Fin (suffixStage J (512*h) k)) → ℤ :=
  leafWeight (block_fit hk) (leftSource pMod B b q) (rightSource pMod shift C c q)
    (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))

































































end ThreeSum.LightReportingSuffixBoxes

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixLower


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual global-to-local suffix-mask conversion

The program constructs powers once, tests each suffix coordinate using the
verified mask-bit procedure, and accumulates its local power. Runtime is
quadratic in the width, independent of the numeric mask value.
-/

namespace ThreeSum.LightReportingSuffixLower

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase

variable {lim : Limits} {P : Program}

def scanMask {V : ℕ} (S : Finset (Fin V)) (j : ℕ) : ℕ :=
  subsetMask (S.filter fun i => i.val < j)






























def roundBody (pErase : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pErase [v 0, (Light.Expr.op Light.Op.add) (v 2) (v 7), v 3, v 0, v 4]
      8)
    (.ite (Light.Cond.eq (v 8) (v 3)) .skip
      (.set 6
        ((Light.Expr.op Light.Op.add) (v 6)
          (M ((Light.Expr.op Light.Op.add) (v 4) (v 7)))))))

def body (pPowers pErase : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 4, (Light.Expr.op Light.Op.add) (v 0) (k 1), k 2] 5)
    (Light.Stmt.seq (.set 6 (k 0))
      (Light.Stmt.seq (.for 7 (v 1) (roundBody pErase)) (.set 0 (v 6)))))

def time (W V : ℕ) : ℕ := powTableTime (W+1)+V*(LightMaskErase.time W+100)+100

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V))
    (μ : ℕ → ℤ) (powers : ℕ) (ret : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [W,V,offset,subsetMask (liftSet hfit S),powers,ret,scanMask S j,j,r],μ⟩





























































































end ThreeSum.LightReportingSuffixLower

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixSum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Explicit local suffix leaves evaluated by actual global source reads -/

namespace ThreeSum.LightReportingSuffixSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits} {P : Program}

def term {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (U : Finset (Fin V)) : ℤ := leafWeight hfit f g stage preL preR (Q \ U)

def partialSum {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) (j : ℕ) : ℤ :=
  ((missing.map (term hfit Q preL preR f g stage)).take j).sum



















def roundBody (pLeaf : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 19
      ((Light.Expr.op Light.Op.mul)
        ((Light.Expr.op Light.Op.sub) (v 10)
          (M ((Light.Expr.op Light.Op.add) (v 13) (v 18))))
        (v 8)))
    (Light.Stmt.seq
      (.call pLeaf
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6,
          (Light.Expr.op Light.Op.sub) (v 9) (v 11), v 19, v 14, v 15, v 16]
        20)
      (.set 17 ((Light.Expr.op Light.Op.add) (v 17) (v 20)))))

def body (pLeaf : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 17 (k 0))
    (Light.Stmt.seq (.for 18 (v 12) (roundBody pLeaf)) (.set 0 (v 17))))

def time (W n : ℕ) : ℕ := n*(LightSignedLeafGeneral.time W+100)+40

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (Q : Finset (Fin V)) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V)))
    (cut t maskBase baseL baseR work j : ℕ) (σ : State) : Prop :=
  ∃ (mask r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,
      partialSum hfit Q preL preR f g stage missing j,j,mask,r],μ'⟩ ∧ Kept μ μ' work




































































































































end ThreeSum.LightReportingSuffixSum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPrefixMasks


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
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Positional products are the physical masks of the complete shared prefix catalog

Both left and right products use one common tuple list. Every original valid
prefix has a key in that list, and the tuple encodes exactly its original
row-major global masks.
-/

namespace ThreeSum.ReportingHostPrefixMasks

open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators

set_option maxHeartbeats 500000

variable {α : Type*}




























def tuple {h k : ℕ} (p : Prefix h k) : List (Finset (Fin (512*h)) × Finset (Fin (512*h))) :=
  List.ofFn fun i => (p i).val














































def ofTuple {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h))))
    (hlen : xs.length = k) (hmem : ∀ q ∈ xs, q ∈ pairs (512*h) h) : Prefix h k :=
  fun i => ⟨xs[i.val]'(by rw [hlen]; exact i.isLt),
    (pairs_mem _).mp (hmem _ (List.getElem_mem (by rw [hlen]; exact i.isLt)))⟩


































end ThreeSum.ReportingHostPrefixMasks

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingTerminalMasks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
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
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks

open Light Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open QueryCoordinates ReportingHostTerminalChoices ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def choiceAt {h J : ℕ} (q : GlobalOutput h J) (k i : ℕ) : Finset (Coord J (512*h)) :=
  (choices q k)[i]?.getD ∅

def leftAt {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512*h)))) (i : ℕ) : Finset (Coord J (512*h)) :=
  prefixLeft (prefixIndices J k) (prefixRows pre) ∪ choiceAt q k i

def rightAt {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512*h)))) (i : ℕ) : Finset (Coord J (512*h)) :=
  prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
    (remaining (prefixIndices J k) (outputRows q) \ choiceAt q k i)

def count (h J k : ℕ) : ℕ := ((J-k)*(2*h)).choose ((J-k)*h)
def time (h J k : ℕ) : ℕ := LightBlockChildren.time (J*(512*h)) ((J-k)*(2*h)) ((J-k)*h)
def program : Program := LightBlockChildren.program







































variable {lim : Limits} {d : ℕ}















































end ThreeSum.LightReportingTerminalMasks

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostTerminalCosts


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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostBlockBucketTest
end ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Charging actual terminal scans to the original raw prefix mass

The actual independent bucket tester costs `240` per selected physical pair
plus `700` per terminal candidate. This file sums those exact verified costs
over the enumerator's unchanged order. It also proves conservation of raw
mass across the actual positive frontier at any partial depth.
-/

namespace ThreeSum.ReportingHostTerminalCosts

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open ReportingHostTerminalChoices ReportingHostBlockBucketTest BlockSourceEncoding LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000







variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def actualTestWork {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  ((choices q k).map fun S =>
    LightReportingBucketTest.time
      (fun i => key p (modulus h J) 0 (left i)) (fun j => key p (modulus h J) shift (right j)) NL NR
      (leftResidue (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightResidue (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S)))
      (leftFlag (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightFlag (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S)))).sum













































end ThreeSum.ReportingHostTerminalCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverBuild


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
# A complete local-cover construction from the initialized parameters

The enumerated local vertices and their Boolean coordinate rows are built
inside this program. It then constructs all candidate tables, executes the
original greedy schedule, and gathers the exact occurrence coefficient
rows. There are no supplied mask, coefficient, histogram, or matrix tables.
-/

namespace ThreeSum.LightLocalCoverBuild

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

set_option maxHeartbeats 1500000
set_option maxRecDepth 6000

def body (pEnum pBits pHost : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnum [v 0, v 1, v 6, v 14] 17)
    (Light.Stmt.seq (.call pBits [v 0, v 6, v 7, v 4, v 14] 17)
      (.call pHost
        [v 0, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
          v 14, v 15, v 16]
        0)))

def time (h : ℕ) : ℕ := LightSubsetEnumerationSetup.time (512*h) h+
  LightMaskBitTable.time (512*h) (LocalMaskGraph.vertexCount (512*h) h)+
  LightLocalCoverHost.time h+200

def word (h : ℕ) : ℕ := LightLocalCoverHost.word h+2^(512*h+1)

structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pEnumRec : ℕ
  pBits : ℕ
  pOneBits : ℕ
  pErase : ℕ
  pHost : ℕ
  enum : P[pEnum]? = some (LightSubsetEnumerationSetup.body pPowers pEnumRec)
  powers : P[pPowers]? = some powTableBody
  enumRec : P[pEnumRec]? = some (LightSubsetEnumeration.body pEnumRec)
  bits : P[pBits]? = some (LightMaskBitTable.body pOneBits)
  oneBits : P[pOneBits]? = some (LightMaskBits.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  host : LightLocalCoverHost.Procs P pHost
  main : P[pMain]? = some (body pEnum pBits pHost)

variable {lim : Limits} {P : Program} {d : ℕ}














































































































end ThreeSum.LightLocalCoverBuild

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceBatchStep


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
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# One actual retained source bank and its two pointer headers

The program computes the bank's addresses, constructs both original source
stage families from the shared histograms, and writes their two pointers.
Every earlier bank and every input before the header array is retained.
-/

namespace ThreeSum.LightBlockSourceBatchStep

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

/-- The first fourteen arguments are the original retained-host controls and
inputs. The remaining arguments are header base, compact capacity, bank count,
bank base, bank stride, shared scratch addresses, and the current bank index. -/
def body (pSource : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 24
      ((Light.Expr.op Light.Op.add) (v 17)
        ((Light.Expr.op Light.Op.mul) (v 23) (v 18))))
    (Light.Stmt.seq (.set 25 ((Light.Expr.op Light.Op.add) (v 24) (v 15)))
      (Light.Stmt.seq
        (.set 26
          ((Light.Expr.op Light.Op.add) (v 25)
            ((Light.Expr.op Light.Op.mul) (v 0) (v 1))))
        (Light.Stmt.seq
          (.set 27
            ((Light.Expr.op Light.Op.add) (v 26)
              ((Light.Expr.op Light.Op.mul) (v 0) (v 1))))
          (Light.Stmt.seq (.set 28 ((Light.Expr.op Light.Op.add) (v 27) (v 15)))
            (Light.Stmt.seq (.set 29 ((Light.Expr.op Light.Op.add) (v 28) (v 15)))
              (Light.Stmt.seq
                (.set 30
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v 29)
                      ((Light.Expr.op Light.Op.mul) (k 2) (v 15)))
                    (k 2)))
                (Light.Stmt.seq
                  (.set 31
                    ((Light.Expr.op Light.Op.add) (v 30)
                      ((Light.Expr.op Light.Op.mul)
                        ((Light.Expr.op Light.Op.add)
                          ((Light.Expr.op Light.Op.mul) (v 0) (v 1)) (k 1))
                        (v 15))))
                  (Light.Stmt.seq
                    (.call pSource
                      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10,
                        v 11, v 12, v 13, v 24, v 25, v 26, v 27, v 28, v 29,
                        v 30, v 31, v 19, v 20, v 21, v 22]
                      32)
                    (Light.Stmt.seq
                      (.store
                        ((Light.Expr.op Light.Op.add) (v 14)
                          ((Light.Expr.op Light.Op.mul) (k 2) (v 23)))
                        (v 30))
                      (.store
                        ((Light.Expr.op Light.Op.add)
                          ((Light.Expr.op Light.Op.add) (v 14)
                            ((Light.Expr.op Light.Op.mul) (k 2) (v 23)))
                          (k 1))
                        (v 31))))))))))))

def time (h J cut : ℕ) : ℕ := LightBlockSourceRetainedHost.time h J cut+500

structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  source : LightBlockSourceRetainedHost.Procs P pSource
  main : P[pMain]? = some (body pSource)

variable {lim : Limits} {P : Program} {d : ℕ}





























































































































































end ThreeSum.LightBlockSourceBatchStep

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceRetainedProgram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightBlockSourceRetainedHost
end ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Literal efficient program for original source-stage construction

The 41 procedures construct all occurrence-dependent data and reuse the
original band histograms. The cost has no factor proportional to the number
of original input incidences or the dense global modulus in this inner loop.
-/

namespace ThreeSum.LightBlockSourceRetainedProgram

open Light LightPascal LightSubsetAddress LightBlockSourceRetainedHost
open LocalCoverBounds SubsetAddress BlockSourceEncoding LightBlockSourceBuild

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def program : Program :=
  [LightBlockSourceRetainedHost.body 1 5 22,
    LightDownsetEnumerationSetup.body 2 3,powTableBody,
    LightDownsetEnumeration.body 4,LightSubsetEnumeration.body 4,
    LightSourcePreparation.body 6 12,LightBlockSourceHashes.body 7 10,
    LightBlockCoefficients.body 8 9,powTableBody,LightScaleArray.body,
    LightMaskHashes.body 8 11,LightOneHot.body 11,
    LightSourceFlagArray.body 13,LightSourceMaskFlags.body 14 17,
    LightMaskBits.body 15 16,powTableBody,LightMaskErase.body 16,
    LightSourceTrim.body 18,LightSourceRowFlag.body 19 20 21,
    LightSourceRowScan.body,emodBody,LightSourceFlagTest.body,
    LightSourceRetainedStages.body 23 25,LightSourceGather.body 24,emodBody,
    LightZetaStages.body 26 27,LightDownsetSize.body 31 38,
    LightZetaPass.body 28 29,LightSubsetEnumerationSetup.body 36 40,
    LightZetaBatch.body 30,LightZetaCell.body 31 38 39 37,
    LightSubsetSetup.body 32 36 37,buildBody 33 34,fillBody,rowBody 35,
    LightArray.linearBody,powTableBody,rankBody 37,LightSubsetOffset.body,
    LightMaskErase.body 39,LightSubsetEnumeration.body 40]

























def factor (h J : ℕ) : ℕ :=
  1200*(J*(512*h)+1)^2+300*(J+1)*(512*h+1)+600*(J*(512*h)+1)+
  (300*(J*(512*h)+1)^2+J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400)+
  314*(Nat.log 2 (endpointBound h J+1)+1)+12000*(J*(512*h)+1)^4+1122















end ThreeSum.LightBlockSourceRetainedProgram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandBanksCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts

open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress


























































































def storageFactor (n : ℕ) : ℕ :=
  (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)+mu n+256*mu n+3+
    LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))




















































end ThreeSum.SourceBandBanksCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandPrimeConstruction


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction

open Light BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def modulus (y nA nB nC g : ℕ) (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) : ℕ :=
  BandPrimeChoice.modulus (LightPrimePool.prime y) (LightPrimePool.size y)
    nA nB nC g A B C rs levels




































def time (maxMod g R y U levels : ℕ) : ℕ :=
  LightPrimePool.time y+
    LightBandPrimeChain.time maxMod g R (LightPrimePool.size y) U levels+140









variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



















































































end ThreeSum.LightBandPrimeConstruction

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorPrimeCore


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.EncodedColorPrimeData
end ThreeSum.EncodedColorPrimeData


/-!
# Actual common-prime construction with its reusable metadata retained

The verified depth, prime-pool and common-chain programs each run once.
Six header cells retain their controls before the pool and prefix arrays;
all temporary scoring memory follows the exact returned next-free pointer.
-/

namespace ThreeSum.LightEncodedColorPrimeCore

open Light BandCandidateRows EncodedColorPrimeData

set_option maxHeartbeats 2600000
set_option maxRecDepth 13000

def body (pDepth pPool pChain : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDepth [v 9, v 10] 12)
    (Light.Stmt.seq (.set 13 ((Light.Expr.op Light.Op.add) (v 11) (k 6)))
      (Light.Stmt.seq (.call pPool [v 10, v 13] 14)
        (Light.Stmt.seq
          (.set 15
            ((Light.Expr.op Light.Op.add) (v 13)
              ((Light.Expr.op Light.Op.mul) (k 3) (v 10))))
          (Light.Stmt.seq
            (.call pChain
              [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 13, v 14, v 12,
                v 15]
              16)
            (Light.Stmt.seq
              (.set 17
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) (v 15) (v 12)) (k 1)))
              (Light.Stmt.seq (.store (v 11) (v 16))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 11) (k 1)) (v 12))
                  (Light.Stmt.seq
                    (.store ((Light.Expr.op Light.Op.add) (v 11) (k 2)) (v 17))
                    (Light.Stmt.seq
                      (.store ((Light.Expr.op Light.Op.add) (v 11) (k 3)) (v 13))
                      (Light.Stmt.seq
                        (.store ((Light.Expr.op Light.Op.add) (v 11) (k 4))
                          (v 14))
                        (Light.Stmt.seq
                          (.store ((Light.Expr.op Light.Op.add) (v 11) (k 5))
                            (v 15))
                          (.set 0 (v 16))))))))))))))

def poolProgram : Program := ReportingHostRelocation.program LightBandPrimeDepth.program LightPrimePool.program
def joinedProgram : Program := ReportingHostRelocation.program poolProgram LightBandPrimeChain.program
def program : Program := joinedProgram ++ [body 0 1 22]



def time (maxMod g count M y U : ℕ) : ℕ :=
  LightBandPrimeDepth.time M y+LightPrimePool.time y+
    LightBandPrimeChain.time maxMod g count (LightPrimePool.size y) U (LightBandPrimeDepth.depth M y)+1000

def space (free maxMod g M y U : ℕ) : ℕ :=
  max (LightPrimePool.space (poolBase free) y)
    (LightBandPrimeChain.space (prefixBase free y) maxMod g U (LightBandPrimeDepth.depth M y))

def word (maxMod nA nB nC g count M y U : ℕ) : ℕ :=
  max (LightBandPrimeDepth.word M y)
    (max (LightPrimePool.word y)
      (LightBandWeightedScore.word maxMod nA nB nC g count (LightPrimePool.size y) U))

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}























































































































end ThreeSum.LightEncodedColorPrimeCore

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPositiveBatch


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
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-! # Exact ordered accumulation for the actual multi-parent reporting loop -/

namespace ThreeSum.ReportingHostPositiveBatch

open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive

set_option linter.unusedSectionVars false











variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def parentAt {h : ℕ} (pres : List (List (Finset (Fin (512*h))))) (i : ℕ) := pres[i]?.getD []




def through {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) (j : ℕ) :
    List (List (Finset (Fin (512*h)))) :=
  (pres.take j).flatMap (fun pre => positiveChildren I w pre hk)





























end ThreeSum.ReportingHostPositiveBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_DenseGuard


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout


/-!
# Sound cumulative dense stopping on visited wanted labels

Distinct wanted labels have disjoint raw-incidence fibers. Therefore any
visited prefix already exceeding the exact representation-times-false-score
threshold certifies an original equation, before proportional traversal.
-/

namespace ThreeSum.DenseGuard

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def mass {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) : ℕ := (visited.map (rootMass I)).sum




















































end ThreeSum.DenseGuard

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
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
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout


/-!
# A reusable finite scratch layout for every wanted slot

The capacity uses the original physical input counts and the retained
representation cap. Its memory bound does not charge any traversal time:
only the actual retained frontier cells are visited. A mask span of `2^W`
also bounds every partial-depth terminal candidate array.
-/

namespace ThreeSum.ReportingHostWantedLayout

open Finset GlobalEncoding RawIncidences RawReporting LocalCoverBounds
open ReportingHostFrontierLayout LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

def massBound (N NB NC cap : ℕ) : ℕ := N*NB*NC*cap
def capacityBound (N NB NC cap G : ℕ) : ℕ := (massBound N NB NC cap+1)*G

structure Layout where
  root : ℕ
  masks : ℕ
  childL : ℕ
  childR : ℕ
  counts : ℕ
  selected : ℕ
  maskBase : ℕ
  terminalMasks : ℕ
  masksL : ℕ
  masksR : ℕ
  base : ℕ
  bitBase : ℕ
  rowOut : ℕ
  work : ℕ

def make (root K W G T cap : ℕ) : Layout :=
  let masks := slot root cap (K+1)
  let childL := masks+G
  let childR := childL+G
  let counts := childR+G
  let selected := counts+G
  let maskBase := selected+G
  let terminalMasks := maskBase+T
  let masksL := terminalMasks+T
  let masksR := masksL+T
  let base := masksR+T
  let bitBase := base+2*(2*W+4*T+2)
  let rowOut := bitBase+W
  ⟨root,masks,childL,childR,counts,selected,maskBase,terminalMasks,masksL,masksR,base,bitBase,rowOut,rowOut+2⟩

def values (L : Layout) : List ℕ :=
  [L.root,L.masks,L.childL,L.childR,L.counts,L.selected,L.maskBase,L.terminalMasks,
    L.masksL,L.masksR,L.base,L.bitBase,L.rowOut,L.work]



def decoded (dst : ℕ) : ℕ := dst+14
def access (dst J : ℕ) : ℕ := decoded dst+4+J+J
def packed (dst J : ℕ) : ℕ := access dst J+20
def root (dst J : ℕ) : ℕ := packed dst J+J





structure Bounds (L : Layout) (root K W G T cap : ℕ) : Prop where
  root_eq : L.root=root
  frontier : slot root cap (K+1)≤L.masks
  masks : L.masks+G≤L.childL
  childL : L.childL+G≤L.childR
  childR : L.childR+G≤L.counts
  counts : L.counts+G≤L.selected
  selected : L.selected+G≤L.maskBase
  queryMasks : L.maskBase+T≤L.work
  terminalFrontier : slot root cap (K+1)≤L.terminalMasks
  terminalMasks : L.terminalMasks+T≤L.masksL
  masksL : L.masksL+T≤L.masksR
  masksR : L.masksR+T≤L.base
  stop : LightReportingTerminalPreparation.stop L.base W T≤L.bitBase
  bits : L.bitBase+W≤L.rowOut
  rowOut : L.rowOut+2≤L.work























section Mass

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



































end Mass

end ThreeSum.ReportingHostWantedLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixTable


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
# Concrete box-leaf preprocessing over the shrinking suffix ground set

Each local cardinality layer is actually enumerated at width V and evaluated
against the width-W source transforms. The exponentially sized storage and
enumeration are downsetCap V boxCut; W occurs only in polynomial overhead.
-/

namespace ThreeSum.LightReportingSuffixTable

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostSuffix

variable {lim : Limits} {P : Program}

def enumBudget (V cut : ℕ) : ℕ := 800*(V+1)*(downsetCap V cut+1)
def batchBudget (W V cut : ℕ) : ℕ := 9400*(W+1)^2*(downsetCap V cut+1)
def roundBudget (W V cut : ℕ) : ℕ := enumBudget V cut+batchBudget W V cut+90

def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnumSetup [v 8, v 15, v 13, v 14] 16)
    (.call pBatch
      [v 0, v 1, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 15, v 16, v 13, v 10, v 11,
        v 12, v 14]
      17))

def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 15 (((Light.Expr.op Light.Op.add) (v 2) (k 1))) (roundBody pEnumSetup pBatch)

def time (W V cut : ℕ) : ℕ := (cut+1)*(roundBudget W V cut+20)+20

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage baseL baseR dst maskBase work : ℕ)
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,baseL,baseR,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap V boxCut) ∧
    TableAt μ' dst boxCut (LightSignedLeafTable.stageValues μ dst j (leafWeight hfit f g stage preL preR))























































































































def program : Program := LightSignedBoxSetup.program ++
  [LightReportingSuffixCell.body 6 10,LightReportingSuffixBatch.body 25,body 3 26]













































end ThreeSum.LightReportingSuffixTable

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixExplicit


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
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Actual output-sensitive enumeration and evaluation of explicit local suffix leaves -/

namespace ThreeSum.LightReportingSuffixExplicit

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostSuffix

variable {lim : Limits} {P : Program}

structure Procs (P : Program) (pEnum pSum : ℕ) where
  (pWeights pCore pLeaf pAddress : ℕ)
  leafProcs : LightSignedLeafCell.Procs P pLeaf pAddress
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body leafProcs.pPowers leafProcs.pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightReportingSuffixSum.body pLeaf)

def roundBody (pEnum pSum : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnum [v 7, v 10, v 17, v 14, v 15] 18)
    (Light.Stmt.seq
      (.call pSum
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 17, v 18, v 14,
          v 12, v 13, v 15]
        19)
      (.set 16 ((Light.Expr.op Light.Op.add) (v 16) (v 19)))))

def body (pEnum pSum : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 16 (k 0))
    (Light.Stmt.seq (.for 17 (v 11) (roundBody pEnum pSum)) (.set 0 (v 16))))

def roundTime (W c t : ℕ) : ℕ := 10500*(W+1)^2*(layerOffset c t+1)
def time (W c t : ℕ) : ℕ := t*(roundTime W c t+30)+40

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage cut t baseL baseR maskBase work j : ℕ) (σ : State) : Prop :=
  ∃ (count r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,
      ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) j,j,count,r],μ'⟩ ∧
      KeptBut μ μ' work maskBase (layerOffset Q.card t)














































































































































end ThreeSum.LightReportingSuffixExplicit

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPrefixOrder


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixMasks
end ThreeSum.ReportingHostPrefixMasks
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Complete shared prefix records in the physical product-constructor order

The semantic list is obtained from the actual tuple list, without filtering,
reordering, or coalescing equal left/right projections. It connects both
constructed integer arrays to every exact global prefix-mask pair.
-/

namespace ThreeSum.ReportingHostPrefixOrder

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments

set_option maxHeartbeats 600000

/-- The exact record order shared by both physical positional products. -/
def prefixes (h k : ℕ) : List (Prefix h k) :=
  (RadixKeyLists.tuples (pairs (512*h) h) k).attach.map fun t =>
    ofTuple t.val ((RadixKeyLists.mem_tuples _ _ _).mp t.property).1
      ((RadixKeyLists.mem_tuples _ _ _).mp t.property).2























def leftSets (h J k : ℕ) : List (Finset (Fin (J*(512*h)))) :=
  (prefixes h k).map (leftSet (J := J))

def rightSets (h J k : ℕ) : List (Finset (Fin (J*(512*h)))) :=
  (prefixes h k).map (rightSet (J := J))

def preL (h J k i : ℕ) : Finset (Fin (J*(512*h))) := ((leftSets h J k)[i]?).getD ∅
def preR (h J k i : ℕ) : Finset (Fin (J*(512*h))) := ((rightSets h J k)[i]?).getD ∅












































end ThreeSum.ReportingHostPrefixOrder

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostTerminalBatch


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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostBlockBucketTest
end ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Exact original-encoding semantics and cost of the executed terminal batch

This is the specialization of the actual seven-procedure batch to the full
endpoint masks emitted at a valid partial prefix. The precise ordered
candidate sum is charged to raw prefix mass plus the terminal cube term.
-/

namespace ThreeSum.ReportingHostTerminalBatch

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open ReportingHostTerminalChoices ReportingHostBlockBucketTest BlockSourceEncoding LightSourceResidues
open LightReportingTerminalMasks LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

def endpointsLeft {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℤ :=
  fun i => endpointLeft (outputOccurrences q) (leftAt q k pre i)
def endpointsRight {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℤ :=
  fun i => endpointRight (outputOccurrences q) (rightAt q k pre i)
def flagsLeft {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℕ :=
  fun i => leftFlag (outputOccurrences q) (leftAt q k pre i)
def flagsRight {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℕ :=
  fun i => rightFlag (outputOccurrences q) (rightAt q k pre i)

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  LightReportingLeafBatch.time
    (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i))
    (flagsLeft q k pre) (flagsRight q k pre) NL NR (modulus h J) (endpointBound h J)
    (endpointsLeft q k pre) (endpointsRight q k pre) (count h J k)

def Hit {h J : ℕ} (a : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : Prop :=
  LightReportingLeafBatch.Hit a (endpointsLeft q k pre) (endpointsRight q k pre) left right
    (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i))
    (flagsLeft q k pre) (flagsRight q k pre) NL NR (modulus h J) (count h J k)








































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]






















































end ThreeSum.ReportingHostTerminalBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# The complete local cover from four scalar graph parameters

Only `h`, the selected prime, the vertex count, the bucket cap, and one
starting address are arguments. The candidate count, original schedule
length, and every table address are computed by this fixed program before
it invokes the fully checked local-cover builder.
-/

namespace ThreeSum.LightLocalCoverSetup

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 6500

def body (pPower pLog pBuild : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.mul) (k 512) (v 0)))
    (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.mul) (k 2) (v 5)))
      (Light.Stmt.seq (.call pPower [v 1, v 6] 7)
        (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.mul) (v 1) (v 1)))
          (Light.Stmt.seq (.call pLog [v 8] 9)
            (Light.Stmt.seq
              (.set 10
                ((Light.Expr.op Light.Op.mul)
                  ((Light.Expr.op Light.Op.mul) (k 320)
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.mul) (k 2) (v 0)) (k 1)))
                  ((Light.Expr.op Light.Op.add) (v 9) (k 1))))
              (Light.Stmt.seq (.set 11 ((Light.Expr.op Light.Op.add) (v 4) (v 2)))
                (Light.Stmt.seq
                  (.set 12
                    ((Light.Expr.op Light.Op.add) (v 11)
                      ((Light.Expr.op Light.Op.mul) (v 2) (v 5))))
                  (Light.Stmt.seq
                    (.set 13
                      ((Light.Expr.op Light.Op.add) (v 12)
                        ((Light.Expr.op Light.Op.mul) (v 7) (v 6))))
                    (Light.Stmt.seq
                      (.set 14
                        ((Light.Expr.op Light.Op.add) (v 13)
                          ((Light.Expr.op Light.Op.mul) (k 2) (v 2))))
                      (Light.Stmt.seq
                        (.set 15
                          ((Light.Expr.op Light.Op.add) (v 14)
                            ((Light.Expr.op Light.Op.mul) (k 2) (v 2))))
                        (Light.Stmt.seq
                          (.set 16
                            ((Light.Expr.op Light.Op.add) (v 15)
                              ((Light.Expr.op Light.Op.mul) (v 7) (v 1))))
                          (Light.Stmt.seq
                            (.set 17
                              ((Light.Expr.op Light.Op.add) (v 16)
                                ((Light.Expr.op Light.Op.mul) (v 7) (v 1))))
                            (Light.Stmt.seq
                              (.set 18
                                ((Light.Expr.op Light.Op.add) (v 17)
                                  ((Light.Expr.op Light.Op.mul) (v 7) (v 8))))
                              (Light.Stmt.seq
                                (.set 19
                                  ((Light.Expr.op Light.Op.add)
                                    ((Light.Expr.op Light.Op.add)
                                      ((Light.Expr.op Light.Op.add) (v 18) (v 8))
                                      (v 7))
                                    (v 10)))
                                (.call pBuild
                                  [v 5, v 0, v 1, v 7, v 2, v 3, v 4, v 11, v 12,
                                    v 13, v 14, v 15, v 16, v 17, v 18, v 10,
                                    v 19]
                                  0))))))))))))))))

def time (h : ℕ) : ℕ := LightNatPower.time (2*(512*h))+log2Time (cols h)+
  LightLocalCoverBuild.time h+500

def word (h : ℕ) : ℕ := LightLocalCoverBuild.word h+1024+scheduleSize h+rows h+2*cols h+512*h

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pLog : ℕ
  pBuild : ℕ
  power : P[pPower]? = some LightNatPower.body
  log : P[pLog]? = some log2Body
  build : LightLocalCoverBuild.Procs P pBuild
  main : P[pMain]? = some (body pPower pLog pBuild)

variable {lim : Limits} {P : Program} {d : ℕ}





























































































































































def program : Program :=
  [body 1 2 3,LightNatPower.body,log2Body,LightLocalCoverBuild.body 31 33 4,
    LightLocalCoverHost.body 5 24 29,LightLocalCoverMatrix.body 6,
    LightLocalCoverCandidate.body 7 12 19,LightWeightDecode.body 8 9,powTableBody,
    LightWeightRow.body 10,LightRadixDigit.body 11,LightSmallDivide.body,
    LightHashHistogram.body 13 15 17,LightMaskHashes.body 8 14,LightOneHot.body 14,
    LightResidues.residuesBody 16,emodBody,LightHistogram.histogramBody 18,fillBody,
    LightLocalCoverRow.body 20 23,LightPairFlags.body 11 21 22,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 18,LightCoverGreedy.body 18 25 28,
    LightCoverSelect.body 26 27,LightCoverScores.body 21,LightMinimum.body,LightCoverUpdate.body,
    LightWeightGather.body 30,copyBody,LightSubsetEnumerationSetup.body 8 32,
    LightSubsetEnumeration.body 32,LightMaskBitTable.body 34,LightMaskBits.body 8 35,
    LightMaskErase.body 35]








end ThreeSum.LightLocalCoverSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceBatch


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
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual shared source-stage catalog over occurrence vectors

One loop iteration constructs one retained bank and its two header pointers.
The original-band histograms and local-cover data are read throughout and
preserved. The semantic occurrence-row contract labels an ordinary physical
array; it does not assume any source-stage computation or output-subset loop.
-/

namespace ThreeSum.LightBlockSourceBatch

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

structure BankAt {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J : ℕ} (μ : ℕ → ℤ) (base count cut i : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) (q : GlobalOutput h J) : Prop where
  left : LightZetaStages.StoredThrough μ (leftBase base count (J*(512*h)) cut i) cut
    (BlockIndexedQuery.leftSource P B b q) (J*(512*h))
  right : LightZetaStages.StoredThrough μ (rightBase base count (J*(512*h)) cut i) cut
    (BlockIndexedQuery.rightSource P shift A a q) (J*(512*h))
  headerLeft : μ (base+2*i) = (leftBase base count (J*(512*h)) cut i : ℤ)
  headerRight : μ (base+2*i+1) = (rightBase base count (J*(512*h)) cut i : ℤ)





























def body (pStep : ℕ) : Stmt :=
  .for 23 (v 16) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,((Light.Expr.op Light.Op.add) (v 7) ((Light.Expr.op Light.Op.mul) (v 23) (v 0))),
      v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23] 24)

def time (count h J cut : ℕ) : ℕ := count*(LightBlockSourceBatchStep.time h J cut+200)+20

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightBlockSourceBatchStep.Procs P pStep
  main : P[pMain]? = some (body pStep)

def Inv {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J cut occ maps candidates histL histR sourceHistL sourceHistR base count : ℕ)
    (p shift : ℤ) (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : ℕ → GlobalOutput h J) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
      histL,histR,sourceHistL,sourceHistR,base,downsetCap (J*(512*h)) cut,count,
      banks base count,stride (J*(512*h)) cut,maskBase base count (J*(512*h)) cut,
      bitBase base count (J*(512*h)) cut,rowOut base count (J*(512*h)) cut,
      work base count (J*(512*h)) cut,i,r],ν⟩ ∧
    (∀ j < i, BankAt ν base count cut j p shift B b A a (q j)) ∧ Kept μ ν base

variable {lim : Limits} {P : Program} {d : ℕ}


































































































end ThreeSum.LightBlockSourceBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BandPrimeScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales

open BandCandidateRows Scales BandScales CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

def modulus (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  LightBandPrimeConstruction.modulus (primeWindow n) nA nB nC (bandSize n)
    A B C rs (primeDepth radix n)

def score (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  BandWeightedScore.score (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) q nA nB nC (bandSize n) A B C rs








































































































end ThreeSum.BandPrimeScales

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandPrimeSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows


/-!
# Compute the chain depth and construct the common owner modulus

Only the original arrays, candidate records, radix and prime window are
inputs. The host computes the prescribed depth, generates its own prime
pool and executes the common minimum chain, retaining all prefix moduli.
-/

namespace ThreeSum.LightBandPrimeSetup

open Light BandCandidateRows

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000










def time (maxMod g count M y U : ℕ) : ℕ := LightBandPrimeDepth.time M y+
  LightBandPrimeConstruction.time maxMod g count y U (LightBandPrimeDepth.depth M y)+100








variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}












































end ThreeSum.LightBandPrimeSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorPrime


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
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs


/-! # Read the actual normalized band headers and construct one common prime -/

namespace ThreeSum.LightEncodedColorPrime

open Light BandPartition BandCandidateRows BandRawA SourceFiniteInputs

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def count (nA nB nC g : ℕ) : ℕ :=
  size nB g*size nC g+size nA g*size nB g+size nA g*size nC g

def moduli (A B C : List ℤ) (g : ℕ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) (y : ℕ) : ℕ → ℕ :=
  LightBandPrimeConstruction.modulus y A.length B.length C.length g
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (sortedRecords A B C g hg hsA hsB hsC)

def body (pCore : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 11 (M (v 1)))
    (Light.Stmt.seq (.set 12 (M (v 3)))
      (Light.Stmt.seq (.set 13 (M (v 5)))
        (Light.Stmt.seq (.set 14 (M ((Light.Expr.op Light.Op.add) (v 1) (k 1))))
          (Light.Stmt.seq (.set 15 (M ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
            (Light.Stmt.seq
              (.set 16 (M ((Light.Expr.op Light.Op.add) (v 5) (k 1))))
              (Light.Stmt.seq
                (.set 17
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.mul) (v 15) (v 16))
                      ((Light.Expr.op Light.Op.mul) (v 14) (v 15)))
                    ((Light.Expr.op Light.Op.mul) (v 14) (v 16))))
                (.call pCore
                  [v 0, v 2, v 4, v 11, v 12, v 13, v 6, v 7, v 17, v 8, v 9,
                    v 10]
                  0))))))))

def program : Program := LightEncodedColorPrimeCore.program ++ [body 23]



def time (maxMod nA nB nC g M y U : ℕ) : ℕ :=
  LightEncodedColorPrimeCore.time maxMod g (count nA nB nC g) M y U+400

def word (maxMod nA nB nC g M y U : ℕ) : ℕ :=
  LightEncodedColorPrimeCore.word maxMod nA nB nC g (count nA nB nC g) M y U+
    nA+nB+nC+count nA nB nC g+100

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}



























































































end ThreeSum.LightEncodedColorPrime

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout


/-!
# Compute the reusable reporting scratch pointers

The two retained scalar headers supply G and the representation cap.
One real power loop computes the mask span. Scalar arithmetic then lays out
all decoded, selected, packed, frontier, query and terminal buffers; no
buffer is initialized or scanned merely because it was reserved.
-/

namespace ThreeSum.LightReportingWantedLayout

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostFrontierLayout
open ReportingHostWantedLayout

set_option maxHeartbeats 4500000
set_option maxRecDepth 20000
set_option linter.unusedVariables false

def layout (dst h J K N NB NC : ℕ) : Layout :=
  make (ReportingHostWantedLayout.root dst J) K (width h J) (groupSize h) (2^(width h J))
    (capacityBound N NB NC (representationCap h J) (groupSize h))





def numericExtra (h J K N NB NC : ℕ) : ℕ :=
  N*NB+N*NB*NC+massBound N NB NC (representationCap h J)+
    J+512*h+K+N+NB+NC+representationCap h J+groupSize h+1024

/-- Each absolute address is bounded independently. This is invariant under
translating the pre-existing memory prefix. -/
def relativeSpace (dst cover counter h J K N NB NC : ℕ) : ℕ :=
  max ((layout dst h J K N NB NC).work+numericExtra h J K N NB NC)
    (max (cover+4) (counter+3))






def body (pPower : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 9
      ((Light.Expr.op Light.Op.mul) (v 0)
        ((Light.Expr.op Light.Op.mul) (k 512) (v 1))))
    (Light.Stmt.seq (.set 10 (M ((Light.Expr.op Light.Op.add) (v 3) (k 3))))
      (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 4) (k 2))))
        (Light.Stmt.seq (.call pPower [k 2, v 9] 12)
          (Light.Stmt.seq
            (.set 13
              ((Light.Expr.op Light.Op.mul)
                ((Light.Expr.op Light.Op.mul)
                  ((Light.Expr.op Light.Op.mul) (v 5) (v 6)) (v 7))
                (v 11)))
            (Light.Stmt.seq
              (.set 14
                ((Light.Expr.op Light.Op.mul)
                  ((Light.Expr.op Light.Op.add) (v 13) (k 1)) (v 10)))
              (Light.Stmt.seq
                (.set 15
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v 8) (k 38))
                    ((Light.Expr.op Light.Op.mul) (k 3) (v 0))))
                (Light.Stmt.seq
                  (.set 16
                    ((Light.Expr.op Light.Op.add) (v 15)
                      ((Light.Expr.op Light.Op.mul)
                        ((Light.Expr.op Light.Op.add) (v 2) (k 1))
                        ((Light.Expr.op Light.Op.add) (k 4)
                          ((Light.Expr.op Light.Op.mul) (k 2) (v 14))))))
                  (Light.Stmt.seq
                    (.set 17 ((Light.Expr.op Light.Op.add) (v 16) (v 10)))
                    (Light.Stmt.seq
                      (.set 18 ((Light.Expr.op Light.Op.add) (v 17) (v 10)))
                      (Light.Stmt.seq
                        (.set 19 ((Light.Expr.op Light.Op.add) (v 18) (v 10)))
                        (Light.Stmt.seq
                          (.set 20 ((Light.Expr.op Light.Op.add) (v 19) (v 10)))
                          (Light.Stmt.seq
                            (.set 21 ((Light.Expr.op Light.Op.add) (v 20) (v 10)))
                            (Light.Stmt.seq
                              (.set 22
                                ((Light.Expr.op Light.Op.add) (v 21) (v 12)))
                              (Light.Stmt.seq
                                (.set 23
                                  ((Light.Expr.op Light.Op.add) (v 22) (v 12)))
                                (Light.Stmt.seq
                                  (.set 24
                                    ((Light.Expr.op Light.Op.add) (v 23) (v 12)))
                                  (Light.Stmt.seq
                                    (.set 25
                                      ((Light.Expr.op Light.Op.add) (v 24)
                                        (v 12)))
                                    (Light.Stmt.seq
                                      (.set 26
                                        ((Light.Expr.op Light.Op.add) (v 25)
                                          ((Light.Expr.op Light.Op.mul) (k 2)
                                            ((Light.Expr.op Light.Op.add)
                                              ((Light.Expr.op Light.Op.add)
                                                ((Light.Expr.op Light.Op.mul)
                                                  (k 2) (v 9))
                                                ((Light.Expr.op Light.Op.mul)
                                                  (k 4) (v 12)))
                                              (k 2)))))
                                      (Light.Stmt.seq
                                        (.set 27
                                          ((Light.Expr.op Light.Op.add) (v 26)
                                            (v 9)))
                                        (Light.Stmt.seq
                                          (.set 28
                                            ((Light.Expr.op Light.Op.add) (v 27)
                                              (k 2)))
                                          (Light.Stmt.seq (.store (v 8) (v 15))
                                            (Light.Stmt.seq
                                              (.store
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 8) (k 1))
                                                (v 16))
                                              (Light.Stmt.seq
                                                (.store
                                                  ((Light.Expr.op Light.Op.add)
                                                    (v 8) (k 2))
                                                  (v 17))
                                                (Light.Stmt.seq
                                                  (.store
                                                    ((Light.Expr.op Light.Op.add)
                                                      (v 8) (k 3))
                                                    (v 18))
                                                  (Light.Stmt.seq
                                                    (.store
                                                      ((Light.Expr.op
                                                          Light.Op.add)
                                                        (v 8) (k 4))
                                                      (v 19))
                                                    (Light.Stmt.seq
                                                      (.store
                                                        ((Light.Expr.op
                                                            Light.Op.add)
                                                          (v 8) (k 5))
                                                        (v 20))
                                                      (Light.Stmt.seq
                                                        (.store
                                                          ((Light.Expr.op
                                                              Light.Op.add)
                                                            (v 8) (k 6))
                                                          (v 21))
                                                        (Light.Stmt.seq
                                                          (.store
                                                            ((Light.Expr.op
                                                                Light.Op.add)
                                                              (v 8) (k 7))
                                                            (v 22))
                                                          (Light.Stmt.seq
                                                            (.store
                                                              ((Light.Expr.op
                                                                  Light.Op.add)
                                                                (v 8) (k 8))
                                                              (v 23))
                                                            (Light.Stmt.seq
                                                              (.store
                                                                ((Light.Expr.op
                                                                    Light.Op.add)
                                                                  (v 8) (k 9))
                                                                (v 24))
                                                              (Light.Stmt.seq
                                                                (.store
                                                                  ((Light.Expr.op
                                                                      Light.Op.add)
                                                                    (v 8) (k 10))
                                                                  (v 25))
                                                                (Light.Stmt.seq
                                                                  (.store
                                                                    ((Light.Expr.op
                                                                        Light.Op.add)
                                                                      (v 8)
                                                                      (k 11))
                                                                    (v 26))
                                                                  (Light.Stmt.seq
                                                                    (.store
                                                                      ((Light.Expr.op
                                                                          Light.Op.add)
                                                                        (v 8)
                                                                        (k 12))
                                                                      (v 27))
                                                                    (Light.Stmt.seq
                                                                      (.store
                                                                        ((Light.Expr.op
                                                                            Light.Op.add)
                                                                          (v 8)
                                                                          (k 13))
                                                                        (v 28))
                                                                      (.set 0
                                                                        (v
                                                                          28))))))))))))))))))))))))))))))))))))

def program : Program := LightNatPower.program++[body 0]
def time (h J : ℕ) : ℕ := LightNatPower.time (width h J)+2500

















































































































































































end ThreeSum.LightReportingWantedLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Complete suffix-local box preprocessing, including its own shift factor

The program constructs the mask-lifting power, fills every local compact leaf
through the original global source reads, and builds every local prefix-zeta
stage. Its exponentially sized domain is the residual width V.
-/

namespace ThreeSum.LightReportingSuffixSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits}

def coreBody (pTable pStages : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pTable
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
        v 14]
      15)
    (.call pStages [v 8, v 2, v 12, v 13, v 14] 0))

def body (pPowers pCore : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPowers [v 14, (Light.Expr.op Light.Op.add) (v 9) (k 1), k 2] 15)
    (Light.Stmt.seq (.set 16 (M ((Light.Expr.op Light.Op.add) (v 14) (v 9))))
      (.call pCore
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 16, v 10, v 11, v 12,
          v 13, v 14]
        0)))

def program : Program := LightReportingSuffixTable.program ++ [coreBody 27 2,body 14 28]

def procs : LightSignedLeafCell.Procs program 6 10 where
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

def coreTime (W V cut : ℕ) : ℕ := LightReportingSuffixTable.time W V cut+LightBoxStages.time V cut+70
def time (W V cut offset : ℕ) : ℕ := powTableTime (offset+1)+coreTime W V cut+100



















































































































































end ThreeSum.LightReportingSuffixSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixQuery


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# The complete sparse query consumes suffix-local box tables

Explicit leaves use local output-sensitive enumeration and global source
reads; canonical boxes use only local-width compact addresses. The exact
finite partition yields the same global source Möbius value.
-/

namespace ThreeSum.LightReportingSuffixQuery

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
open scoped BigOperators

variable {lim : Limits}

def body (pExplicit pBoxes pSign : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pExplicit
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
        v 16, v 17]
      18)
    (Light.Stmt.seq
      (.call pBoxes [v 7, v 14, v 9, v 10, v 11, v 15, v 16, v 17] 19)
      (Light.Stmt.seq (.set 20 ((Light.Expr.op Light.Op.add) (v 18) (v 19)))
        (.call pSign [v 20, v 9] 0))))

def program : Program := LightSparseQuery.program ++
  [LightMaskUnion.body 17 20,LightSignedLeafGeneral.body 24 10 22,
    LightReportingSuffixSum.body 25,LightReportingSuffixExplicit.body 3 26,body 27 2 22]

def leafProcs : LightSignedLeafCell.Procs program 25 13 where
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

def explicitProcs : LightReportingSuffixExplicit.Procs program 3 26 :=
  ⟨4,5,25,13,leafProcs,rfl,rfl,rfl,rfl⟩

def boxProcs : LightCanonicalBoxSum.Procs program 3 7 where
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

def time (W V c t : ℕ) : ℕ :=
  LightReportingSuffixExplicit.time W c t+LightCanonicalBoxSum.time V c t+LightSign.time V+90



































































































































end ThreeSum.LightReportingSuffixQuery

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostPackedCatalog


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder

set_option maxHeartbeats 600000

def pairKey (radix left right : ℕ) : ℕ := left+radix*right

def packed (key : ℕ → ℕ) (n i : ℕ) : ℕ := key i*(n+1)+i

def codes (key : ℕ → ℕ) (n : ℕ) : List ℤ := List.ofFn fun i : Fin n => (packed key n i.val : ℤ)































































































def prefixKey (h J k i : ℕ) : ℕ :=
  pairKey (2^(J*(512*h))) (subsetMask (preL h J k i)) (subsetMask (preR h J k i))




























end ThreeSum.ReportingHostPackedCatalog

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingTerminalPrepared


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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets


/-!
# Executed terminal preparation followed by the exact original-value batch

The closed program constructs both endpoint and independent flag arrays
from the retained selected maps, then scans only their selected physical
bucket products. Every library call is an exact relocation of an already
verified implementation.
-/

namespace ThreeSum.LightReportingTerminalPrepared

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open LightReportingTerminalMasks LightBlockSourceBuild

set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def body (pPrepare pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPrepare
      [v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21,
        v 22, v 23, v 24, v 25, v 26]
      27)
    (Light.Stmt.seq (.set 28 ((Light.Expr.op Light.Op.mul) (v 10) (v 11)))
      (Light.Stmt.seq
        (.set 29
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 28))
              ((Light.Expr.op Light.Op.mul) (k 4) (v 22)))
            (k 2)))
        (Light.Stmt.seq
          (.set 30
            ((Light.Expr.op Light.Op.add) (v 23)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 28))))
          (Light.Stmt.seq
            (.set 31
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) (v 23) (v 29))
                  ((Light.Expr.op Light.Op.mul) (k 2) (v 28)))
                (v 22)))
            (Light.Stmt.seq
              (.set 32
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) (v 23)
                    ((Light.Expr.op Light.Op.mul) (k 2) (v 28)))
                  ((Light.Expr.op Light.Op.mul) (k 2) (v 22))))
              (Light.Stmt.seq
                (.set 33
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add) (v 23) (v 29))
                      ((Light.Expr.op Light.Op.mul) (k 2) (v 28)))
                    ((Light.Expr.op Light.Op.mul) (k 3) (v 22))))
                (.call pBatch
                  [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 30, v 31,
                    v 32, v 33, v 22, v 26]
                  0))))))))

def libraries : Program := ReportingHostRelocation.program
  LightReportingTerminalPreparation.program LightReportingLeafBatch.program
def program : Program := libraries ++ [body 17 24]

def space (work h J : ℕ) : ℕ :=
  max (LightSourcePreparation.space work J (512*h) (localPrime h))
    (work+4+(Nat.log 2 (endpointBound h J+1)+2))
def word (h J : ℕ) : ℕ :=
  LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
    ((512*h).choose h) (localBucketCap h)+4*endpointBound h J+4*modulus h J+16
def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  LightReportingTerminalPreparation.time h J (count h J k)+
    ReportingHostTerminalBatch.time p shift left right NL NR q k pre+700

variable {lim : Limits}















































































































end ThreeSum.LightReportingTerminalPrepared

end


