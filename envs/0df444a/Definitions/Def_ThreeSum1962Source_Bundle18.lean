-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle18
-- name    : ThreeSum1962Source_Bundle18
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:31:50.247846+00:00
-- url     : https://prove2.me/theorems/8ae6a47d-8850-4e60-a3e0-8b2e8b7b8751
-- title:
--   Physical wanted scanning and the complete fast and hybrid program assemblies
-- statement:
--   This bundle defines the ascending wanted-slot scan, its counter predicate, retained consumer data, and the concrete selected-color, fast-driver, and hybrid programs. For natural slot masses $m_i$, hit predicates $H_i$, threshold $\tau$, and prefix length $N$, acceptance is defined by
--   $$\operatorname{Accepted}(N)\iff\tau<\sum_{i<N}m_i\ \lor\ \exists i<N,\ H_i.$$
--   The scan body returns immediately after a successful prefix; its counter contract records the first accepted prefix on success. For input length $n$, value bound $U$, fixed magnitude exponent $\kappa$, and the chosen cutoff $c_\kappa$, the hybrid assembly selects the original-triple fallback when $n<c_\kappa$ or $U>n^\kappa$, and the composed fast driver otherwise. Resource and time functions accompany these assemblies.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorWantedConsumerData.lean#L19-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorWantedConsumerEnds.lean#L18-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedScan.lean#L20-L72
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumColor.lean#L23-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumConcreteFast.lean#L20-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumHybrid.lean#L23-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumWantedHostDefs.lean#L21-L67
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedConsumerData.lean#L25-L80
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedConsumerScanData.lean#L16-L40
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumFastResourcesColor.lean#L19-L22
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumFastResourcesDriver.lean#L18-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumFastResourcesHybrid.lean#L20-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumFastResourcesHybridPolynomial.lean#L38-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumWantedHostData.lean#L12-L70

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
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumFastResourcesColor


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData


/-! # One affine allocation for a complete selected color

The prelude retains its source and reporting catalogs, ending with the dense
counter. The wanted scan reuses scratch beginning four cells after that
counter. The two exact resource records are combined without bounding the
absolute starting address.
-/

namespace ThreeSum.ThreeSumFastResourcesColor

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

def need (n U : ℕ) : Light.Need :=
  ⟨(EncodedColorReportingResources.need n U).word+(ThreeSumFastResources.need n U).word,
    (EncodedColorReportingResources.need n U).cells+(ThreeSumFastResources.need n U).cells,
    (EncodedColorReportingResources.need n U).depth+(ThreeSumFastResources.need n U).depth+3⟩































































noncomputable section























end
end ThreeSum.ThreeSumFastResourcesColor

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorWantedConsumerEnds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData


/-!
# All persistent wanted-consumer inputs precede the mutable counter

The bounds use the actual packed source and wanted extents. In particular,
the pair-array endpoint is the source-control base, and the occurrence rows
end exactly at the shared source-bank header.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

structure PersistentEnds (cfg : LightReportingWantedDispatch.Config)
    (positions occ g cut rowCount wantedCount : ℕ) : Prop where
  values : cfg.vals+cfg.N≤cfg.counter
  owners : cfg.owners+cfg.N≤cfg.counter
  positions : positions+cfg.N≤cfg.counter
  records : cfg.records+4*rowCount≤cfg.counter
  srcB : cfg.srcB+cfg.NB≤cfg.counter
  srcC : cfg.srcC+cfg.NC≤cfg.counter
  pair : SourceBandPairData.next cfg.pair cfg.NB cfg.NC g
    (BlockSourceEncoding.modulus cfg.h cfg.J)≤cfg.counter
  bank : SourceBandBankData.finish cfg.bank cfg.NB cfg.NC g cfg.h cfg.J cut≤cfg.report
  occurrence : occ+LightBlockSourceCatalog.count cfg.h cfg.J*cfg.J≤cfg.bank
  cover : LightCoverKeyData.keyEnd cfg.cover cfg.h cfg.J≤cfg.counter
  report : SharedReportingBankHeader.finish cfg.report cfg.h cfg.J cfg.NB cfg.NC g≤cfg.counter
  pairs : cfg.pairs+2*wantedCount≤cfg.counter
  masks : cfg.masks+cfg.layerCount≤cfg.counter
  reportBeforeCounter : cfg.report+9≤cfg.counter

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
































































































end ThreeSum.EncodedColorWantedConsumerData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedScan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightReportingWantedDispatch
end ThreeSum.LightReportingWantedDispatch
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts


/-!
# Ascending physical wanted scan with immediate successful return

The recursive prefix runs before slot n-1. A positive prefix result returns
immediately; otherwise exactly the next physical slot is dispatched. The
counter is the exact mass of the executed prefix, including the first slot
whose guard or original-value test succeeds.
-/

namespace ThreeSum.LightReportingWantedScan

open Light Finset SharedTraversalCosts LightReportingWantedDispatch

set_option maxHeartbeats 2600000
set_option maxRecDepth 24000

def Accepted (mass : ℕ→ℕ) (hit : ℕ→Prop) (threshold n : ℕ) : Prop :=
  threshold<prefixMass mass n ∨ ∃ i<n, hit i






























def Counter (mass : ℕ→ℕ) (hit : ℕ→Prop) (threshold count counter : ℕ)
    (result : ℤ) (μ : ℕ→ℤ) : Prop :=
  ∃ k≤count, μ counter=(prefixMass mass k : ℤ) ∧
    (result=0 → k=count) ∧
    (result=1 → Accepted mass hit threshold k ∧ ∀ i<k, ¬Accepted mass hit threshold i)

def time (stepTime : ℕ→ℕ) : ℕ→ℕ
  | 0 => 30
  | n+1 => time stepTime n+stepTime n+300

def body (pSelf pDispatch : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 0)))
    ((Light.Stmt.seq
       (.call pSelf
         [(Light.Expr.op Light.Op.sub) (v 0) (k 1), v 1, v 2, v 3, v 4, v 5, v 6,
           v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19,
           v 20, v 21, v 22]
         23)
       (.ite (Light.Cond.lt (k 0) (v 23)) (.set 0 (k 1))
         (.call pDispatch
           [(Light.Expr.op Light.Op.sub) (v 0) (k 1), v 1, v 2, v 3, v 4, v 5, v 6,
             v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18,
             v 19, v 20, v 21, v 22]
           0))))
    (.set 0 (k 0))

def program : Program := LightReportingWantedDispatch.program++[body 152 151]



































































end ThreeSum.LightReportingWantedScan

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumWantedHostData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData


/-! # The wanted consumer's configuration from the actual retained color payload -/

namespace ThreeSum.ThreeSumWantedHostData

open Light Scales BandScales ThreeSumReportingSetupData EncodedColorNormalizedData



def recordCount (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length

def count (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  WantedResidueKeys.total (radix n)
    (LightGuardedWanted.left (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC))
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (shift n A B C hsA hsB hsC)

def config (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightReportingWantedDispatch.Config where
  layoutHeader := counter free n A B C hsA hsB hsC+4
  J := blockCount (inputBits n)
  h := microHalf (inputBits n)
  K := LightSwitchDepth.depth (blockCount (inputBits n))
  N := (incidences n A B C hsA hsB hsC).length
  NB := B.length
  NC := C.length
  cover := EncodedColorPipelineData.coverBase free n
  counter := counter free n A B C hsA hsB hsC
  pairs := LightWantedSetup.pairBase
    (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n))) (radix n)
  layerCount := OutputDecodeRecords.layerCount (microHalf (inputBits n))
  scheduleSize := GlobalEncoding.scheduleSize (microHalf (inputBits n))
  masks := LightCoverKeys.afterCover (EncodedColorPipelineData.coverBase free n) (microHalf (inputBits n))
  vals := EncodedColorLayout.vals free n (bandSize n)
  owners := LightBandRawA.ownerBase (EncodedColorLayout.vals free n (bandSize n))
    (recordCount n A B C hsA hsB hsC) (bandSize n)
  records := EncodedColorLayout.rec free n (bandSize n)
  pair := EncodedColorPipelineData.controls free n A B C hsA hsB hsC+3
  bank := EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  srcB := EncodedColorLayout.bv free n
  srcC := EncodedColorLayout.cv free n
  report := reportBase free n A B C hsA hsB hsC
  modulus := radix n










theorem count_read {μ : ℕ→ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)=
      (count n A B C hsA hsB hsC : ℤ) := H.wanted.1








end ThreeSum.ThreeSumWantedHostData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumFastResourcesDriver


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # Concrete resources for the complete537-procedure fast driver

The nineteen parameter cells and six reusable color-row cells precede the
selected-color allocation. Parameter-initialization scratch is reclaimed.
The original free address has coefficient one in every memory premise.
-/

namespace ThreeSum.ThreeSumFastResourcesDriver

open Light Scales

set_option maxHeartbeats 1700000
set_option maxRecDepth 15000

def need : ℕ→ℕ→Light.Need :=
  ThreeSumColorDriverResources.fullNeed ThreeSumFastResourcesColor.need

























































noncomputable section




end
end ThreeSum.ThreeSumFastResourcesDriver

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumWantedHostDefs


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData


/-!
# Load the retained color headers and execute the actual wanted scan

All controls passed to the fixed153 scan are read from the initialized
parameter, normalization, encoding and reporting headers. The raw-owner
array is located using the actual three band counts stored by normalization.
-/

namespace ThreeSum.LightThreeSumWantedHost

open Light Scales BandScales ThreeSumReportingSetupData ThreeSumWantedHostData
open BandPartition EncodedColorNormalizedData

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000



/-- n, parameter header, normalized header, encoded result header, counter. -/
def body (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.add) (v 4) (k 4)))
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 1) (k 3))))
      (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 1) (k 1))))
        (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 3) (k 8)))
          (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 8) (k 2))))
            (Light.Stmt.seq (.set 10 ((Light.Expr.op Light.Op.sub) (v 9) (k 1)))
              (Light.Stmt.seq
                (.set 11 (M ((Light.Expr.op Light.Op.add) (v 3) (k 6))))
                (Light.Stmt.seq
                  (.set 12 (M ((Light.Expr.op Light.Op.add) (v 2) (k 1))))
                  (Light.Stmt.seq
                    (.set 13 (M ((Light.Expr.op Light.Op.add) (v 2) (k 3))))
                    (Light.Stmt.seq
                      (.set 14 (M ((Light.Expr.op Light.Op.add) (v 2) (k 5))))
                      (Light.Stmt.seq (.set 15 (M (v 13)))
                        (Light.Stmt.seq (.set 16 (M (v 14)))
                          (Light.Stmt.seq
                            (.set 17
                              (M ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                            (Light.Stmt.seq
                              (.set 18
                                (M ((Light.Expr.op Light.Op.add) (v 3) (k 2))))
                              (Light.Stmt.seq (.set 19 (M (v 18)))
                                (Light.Stmt.seq
                                  (.set 20
                                    (M
                                      ((Light.Expr.op Light.Op.add) (v 18)
                                        (k 1))))
                                  (Light.Stmt.seq (.set 21 (M (v 17)))
                                    (Light.Stmt.seq
                                      (.set 22
                                        (M
                                          ((Light.Expr.op Light.Op.add) (v 17)
                                            (k 10))))
                                      (Light.Stmt.seq
                                        (.set 23
                                          (M
                                            ((Light.Expr.op Light.Op.add) (v 17)
                                              (k 18))))
                                        (Light.Stmt.seq
                                          (.set 24
                                            (M
                                              ((Light.Expr.op Light.Op.add) (v 2)
                                                (k 7))))
                                          (Light.Stmt.seq
                                            (.set 25
                                              (M
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 2) (k 6))))
                                            (Light.Stmt.seq
                                              (.set 26
                                                (M
                                                  ((Light.Expr.op Light.Op.add)
                                                    (v 3) (k 3))))
                                              (Light.Stmt.seq
                                                (.set 27
                                                  ((Light.Expr.op Light.Op.add)
                                                    (v 26) (k 3)))
                                                (Light.Stmt.seq
                                                  (.set 28
                                                    (M
                                                      ((Light.Expr.op
                                                          Light.Op.add)
                                                        (v 3) (k 4))))
                                                  (Light.Stmt.seq
                                                    (.set 29
                                                      (M
                                                        ((Light.Expr.op
                                                            Light.Op.add)
                                                          (v 2) (k 2))))
                                                    (Light.Stmt.seq
                                                      (.set 30
                                                        (M
                                                          ((Light.Expr.op
                                                              Light.Op.add)
                                                            (v 2) (k 4))))
                                                      (Light.Stmt.seq
                                                        (.set 31
                                                          (M
                                                            ((Light.Expr.op
                                                                Light.Op.add)
                                                              (v 1) (k 14))))
                                                        (Light.Stmt.seq
                                                          (.set 32
                                                            (M
                                                              ((Light.Expr.op
                                                                  Light.Op.add)
                                                                (v 1) (k 17))))
                                                          (Light.Stmt.seq
                                                            (.set 33
                                                              (M
                                                                ((Light.Expr.op
                                                                    Light.Op.add)
                                                                  (v 12) (k 1))))
                                                            (Light.Stmt.seq
                                                              (.set 34
                                                                (M
                                                                  ((Light.Expr.op
                                                                      Light.Op.add)
                                                                    (v 13)
                                                                    (k 1))))
                                                              (Light.Stmt.seq
                                                                (.set 35
                                                                  (M
                                                                    ((Light.Expr.op
                                                                        Light.Op.add)
                                                                      (v 14)
                                                                      (k 1))))
                                                                (Light.Stmt.seq
                                                                  (.set 36
                                                                    ((Light.Expr.op
                                                                        Light.Op.add)
                                                                      ((Light.Expr.op
                                                                          Light.Op.add)
                                                                        ((Light.Expr.op
                                                                            Light.Op.mul)
                                                                          (v 34)
                                                                          (v 35))
                                                                        ((Light.Expr.op
                                                                            Light.Op.mul)
                                                                          (v 33)
                                                                          (v 34)))
                                                                      ((Light.Expr.op
                                                                          Light.Op.mul)
                                                                        (v 33)
                                                                        (v 35))))
                                                                  (Light.Stmt.seq
                                                                    (.set 37
                                                                      ((Light.Expr.op
                                                                          Light.Op.add)
                                                                        (v 24)
                                                                        ((Light.Expr.op
                                                                            Light.Op.mul)
                                                                          (v 32)
                                                                          (v
                                                                            36))))
                                                                    (.call pScan
                                                                      [v 19, v 5,
                                                                        v 6, v 7,
                                                                        v 10,
                                                                        v 11,
                                                                        v 15,
                                                                        v 16,
                                                                        v 17, v 4,
                                                                        v 20,
                                                                        v 21,
                                                                        v 22,
                                                                        v 23,
                                                                        v 24,
                                                                        v 37,
                                                                        v 25,
                                                                        v 27,
                                                                        v 28,
                                                                        v 29,
                                                                        v 30, v 8,
                                                                        v 31]
                                                                      0))))))))))))))))))))))))))))))))))

def program : Program := LightReportingWantedScan.program++[body 152]



def word (n : ℕ) : ℕ := n+blockCount (inputBits n)+microHalf (inputBits n)+
  LightSwitchDepth.depth (blockCount (inputBits n))+bandSize n+radix n+
  OutputDecodeRecords.layerCount (microHalf (inputBits n))+
  GlobalEncoding.scheduleSize (microHalf (inputBits n))+
  ColorBandBounds.count n (bandSize n)+bandSize n*ColorBandBounds.count n (bandSize n)+50

end ThreeSum.LightThreeSumWantedHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorWantedConsumerData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData


/-!
# The actual retained inputs of the physical wanted consumer

These are projections and finite bounds for the same normalized witnesses
retained by the selected-color pipeline. Physical A incidences preserve
their owner labels even when their integer values are equal.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

abbrev records (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :=
  BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC

def positions (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightBandRawA.positionBase (config free n A B C hsA hsB hsC).vals
    (recordCount n A B C hsA hsB hsC) (bandSize n)

def occurrence (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightSourceBandHost.occurrenceBase (config free n A B C hsA hsB hsC).pair
    B.length C.length (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n))

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}





























































































end ThreeSum.EncodedColorWantedConsumerData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumFastResourcesHybrid


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Affine resources for the actual finite-cutoff hybrid

The fast branch uses the computed magnitude `n^κ`; the fallback retains
the supplied magnitude `U`. Both branches reuse the same free address.
The fixed cutoff and exponent are included among the actual scalar word
controls, together with every intermediate integer power.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid

open Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 16000

def controls (κ cutoff n : ℕ) : ℕ := n+κ+cutoff+(n+1)^(κ+1)+10

def need (κ cutoff n U : ℕ) : Light.Need :=
  ⟨(ThreeSumFastResourcesDriver.need n (n^κ)).word+(LightBruteThreeSum.need n U).word+controls κ cutoff n,
    max (ThreeSumFastResourcesDriver.need n (n^κ)).cells (LightBruteThreeSum.need n U).cells,
    max (ThreeSumFastResourcesDriver.need n (n^κ)).depth (LightBruteThreeSum.need n U).depth+3⟩

































































end ThreeSum.ThreeSumFastResourcesHybrid

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumFastResourcesHybridPolynomial


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Polynomial hybrid limits with the computed magnitude substituted

The exponent and cutoff are fixed program parameters. The polynomial
bound is valid for every input size and supplied magnitude, including
zero, and does not rely on eventual growth to justify substitution.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid

open Light StageBounds ArithmeticStageBounds

set_option maxHeartbeats 300000
set_option maxRecDepth 16000






















def poweredDriverNeed (κ n _U : ℕ) : Light.Need := ThreeSumFastResourcesDriver.need n (n^κ)

noncomputable section


















































end
end ThreeSum.ThreeSumFastResourcesHybrid

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumColor


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions


/-!
# Execute a complete selected color of the original input

The fixed355 prelude prepares the actual encoding and shared source bank.
The fixed154 header caller then executes the physical wanted scan. Their
verified semantic and time connections yield the original color witness.
-/

namespace ThreeSum.LightThreeSumColor

open Light Scales BandScales ThreeSumReportingSetupData
open ThreeSumWantedHostConditions SharedTraversalCosts

set_option maxHeartbeats 2800000
set_option maxRecDepth 18000

def body (pPrelude pWanted : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pPrelude [v 0, v 1, v 2, v 3, v 4] 5)
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 5) (k 14))))
      (.call pWanted [v 1, v 2, v 4, v 5, v 6] 0)))

def joined : Program := ReportingHostRelocation.program
  LightEncodedColorReportingPipeline.program LightThreeSumWantedHost.program

def program : Program := joined++[body 354 508]























































end ThreeSum.LightThreeSumColor

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedConsumerData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData


/-! # Physical labels and original-fiber semantics for the retained consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedOriginal ReportingHostWantedPhysical SharedReportingBankResourceBounds
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 16000









abbrev Label (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :=
  Wanted (half n) (blocks n) (AType A.length (bandSize n) (records n A B C hsA hsB hsC))

def fiber (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) :=
  localItems (half n) (blocks n) A.length B.length C.length (bandSize n)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (records n A B C hsA hsB hsC)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w

def labelMass (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) : ℕ := rootMass (fiber n A B C hsA hsB hsC w) w

def labelHit (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) : Prop :=
  Terminal (half n) (blocks n) A.length B.length C.length (bandSize n)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (records n A B C hsA hsB hsC)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w (LightSwitchDepth.depth (blocks n))

def recordTime (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) (output old threshold : ℕ) : ℕ :=
  LightReportingWanted.time (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)
    (left (records n A B C hsA hsB hsC) (fun j => B.getD j 0) w)
    (right (records n A B C hsA hsB hsC) (fun j => C.getD j 0) w)
    (leftCount (records n A B C hsA hsB hsC) B.length w)
    (rightCount (records n A B C hsA hsB hsC) C.length w) old threshold
    (fiber n A B C hsA hsB hsC w) w
    (ReportingHostWantedRecordData.catalogs A.length B.length C.length (bandSize n)
      (config free n A B C hsA hsB hsC).report (half n) (blocks n)
      (records n A B C hsA hsB hsC) w output) (LightSwitchDepth.depth (blocks n))

def rawIndex (μ : ℕ→ℤ) (cfg : LightReportingWantedDispatch.Config) (slot : ℕ) : ℕ :=
  (μ (cfg.pairs+2*slot)).toNat

def outputIndex (μ : ℕ→ℤ) (cfg : LightReportingWantedDispatch.Config) (slot : ℕ) : ℕ :=
  (μ (cfg.pairs+2*slot+1)).toNat

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

def slot (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    Fin (μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)).toNat :=
  ⟨s.val,by rw [count_read H,Int.toNat_natCast]; exact s.isLt⟩

def label (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) : Label n A B C hsA hsB hsC :=
  wantedAt H.wanted (slot H s)

















































end ThreeSum.ReportingHostWantedConsumerData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumConcreteFast


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions


/-!
# The concrete537-procedure fast solver

The actual selected-color executable supplies the color law of the closed
driver. The parameter header is built once, followed by one reusable color
row and the reusable selected-color allocation.
-/

namespace ThreeSum.LightThreeSumConcreteFast

open Light Scales StageBounds ThreeSumWantedHostConditions SharedTraversalCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

def program : Program :=
  LightThreeSumFastDriver.program LightThreeSumColor.program 509

def need : ℕ→ℕ→Need := ThreeSumFastResourcesDriver.need

def time (k n : ℕ) : ℕ :=
  LightThreeSumFastDriver.time (colorBudget k n) n


































noncomputable section














end
end ThreeSum.LightThreeSumConcreteFast

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedConsumerScanData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData


/-! # Frozen physical order and the exact cost of the ascending consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open SharedReportingBankResourceBounds SharedTraversalCosts

set_option maxHeartbeats 2200000
set_option maxRecDepth 17000

def threshold (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)*ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC

variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

def mass (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ→ℕ :=
  ReportingHostWantedPrefix.slotMass H.wanted (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length

def hit (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ→Prop :=
  ReportingHostWantedDecision.slotHit H.wanted (fun j => B.getD j 0) (fun j => C.getD j 0)
    B.length C.length (LightSwitchDepth.depth (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))

def stepTime (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (i : ℕ) : ℕ :=
  if hi : i<count n A B C hsA hsB hsC then
    LightReportingWantedDispatch.time (config free n A B C hsA hsB hsC) (wantedDecodeV n)
      (recordTime free n A B C hsA hsB hsC (label H ⟨i,hi⟩)
        (outputIndex μ (config free n A B C hsA hsB hsC) i)
        (prefixMass (mass H) i) (threshold n A B C hsA hsB hsC))
  else 0

def scanTime (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ :=
  LightReportingWantedScan.time (stepTime H) (count n A B C hsA hsB hsC)





























































end ThreeSum.ReportingHostWantedConsumerData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumHybrid


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The complete543-procedure original-input solver

For each fixed magnitude exponent, the cutoff is chosen from the proved
uniform parameter conditions. The program tests that cutoff, computes the
integer power, and uses the exact original-triple fallback whenever needed.
Every branch returns the original distinct-position decision and preserves
all memory before the supplied free address.
-/

namespace ThreeSum.LightThreeSumHybrid

open Light ThreeSumApsp.Spec

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

noncomputable section

def program (κ : ℕ) : Program :=
  LightThreeSumHybridCore.program LightThreeSumConcreteFast.program κ
    (ThreeSumWantedHostConditions.cutoff κ)

def need (κ : ℕ) : ℕ→ℕ→Need :=
  ThreeSumFastResourcesHybrid.need κ (ThreeSumWantedHostConditions.cutoff κ)

def time (κ : ℕ) : ℕ→ℕ→ℕ :=
  ThreeSumHybridCosts.time κ (ThreeSumWantedHostConditions.cutoff κ)

























































end
end ThreeSum.LightThreeSumHybrid

end


