-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle15
-- name    : ThreeSum1962Source_Bundle15
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:25:51.482098+00:00
-- url     : https://prove2.me/theorems/acb98eb6-ed4d-4e7d-bd5d-88dfe709a01a
-- title:
--   Shared reporting cells, level layouts, and wanted-query initialization
-- statement:
--   This bundle defines shared reporting-bank cells, their metadata and table predicates, and the per-level switch and box cutoff. For half-size $h$, block count $J$, and width $W=512hJ$, the common query spans are
--   $$\operatorname{maskSpan}=2^W,\qquad\operatorname{workSpan}=(W+1)^2+8(W+1)+8.$$
--   Program bodies assemble source-band hosts and control records, guarded wanted-pair construction, catalog batches, level queries, initialization, and child expansion. Original wanted labels retain incidence position, lift, and complete output identity. Source-normalization predicates and finite cost expressions connect these layouts to the selected-color inputs and the larger shared-bank construction.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorWantedCosts.lean#L11-L33
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightGuardedWanted.lean#L22-L59
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingCatalogBatch.lean#L26-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingCatalogExpand.lean#L28-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingCatalogLevel.lean#L20-L28
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingInitialize.lean#L25-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingInitializeStored.lean#L23-L36
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedInitialize.lean#L26-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingCell.lean#L23-L51
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingEntry.lean#L21-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingLevels.lean#L22-L66
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandBanksProgram.lean#L10-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandHost.lean#L20-L56
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandHostProgram.lean#L9-L14
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceControlsHost.lean#L20-L51
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceControlsHostProgram.lean#L9-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceFinitePrepared.lean#L9-L12
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedOriginal.lean#L23-L57
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankCosts.lean#L22-L28
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankData.lean#L14-L29
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankLayout.lean#L20-L133
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankLevels.lean#L13-L23
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsQuery.lean#L20-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingCosts.lean#L23-L34
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedTraversalDispatchCosts.lean#L22-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedTraversalScales.lean#L23-L56
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceFiniteCosts.lean#L9-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceFiniteData.lean#L10-L62
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WantedRecordCoverage.lean#L45-L63
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WantedRecordOrder.lean#L20-L118

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightGuardedWanted


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

def left (P : ℕ) (xs : List ℤ) : ℕ → ℤ := fun i => (RawAKeyLists.keys P xs).getD i 0
def right (h J : ℕ) : ℕ → ℤ := fun j => (globalKeys h J).getD j 0
def totalKeys (h J : ℕ) : ℕ := LightGlobalKeys.localCount h^J
def keyBound (P h J : ℕ) : ℕ := 2*P+(512*h*localPrime h)*(localPrime h+1)^J
def wantedFree (free h J n : ℕ) : ℕ := LightCoverKeyData.keyEnd free h J+3*n

/-- h, block count, A-incidence array and length, arithmetic modulus,
guarded modulus, and first free address. -/
def body (pCover pLifts pWanted : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCover [v 0, v 1, v 6] 7)
    (Light.Stmt.seq (.set 8 (M (v 7)))
      (Light.Stmt.seq (.set 9 ((Light.Expr.op Light.Op.add) (v 7) (k 1)))
        (Light.Stmt.seq (.set 10 ((Light.Expr.op Light.Op.add) (v 9) (v 8)))
          (Light.Stmt.seq (.set 11 ((Light.Expr.op Light.Op.mul) (k 3) (v 3)))
            (Light.Stmt.seq (.set 12 ((Light.Expr.op Light.Op.add) (v 10) (v 11)))
              (Light.Stmt.seq (.call pLifts [v 2, v 3, v 4, v 10] 13)
                (.call pWanted [v 10, v 9, v 11, v 8, v 5, v 12] 0))))))))

def liftProgram : Program := ReportingHostRelocation.program LightCoverKeys.program LightRawAKeys.program
def program : Program := ReportingHostRelocation.program liftProgram LightBalancedWanted.program ++
  [body 67 68 97]



def time (P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightCoverKeys.time h J+LightRawAKeys.time xs.length U+
    LightBalancedWanted.time M (left P xs) (right h J) (3*xs.length) (totalKeys h J)
      (keyBound P h J)+300

def space (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (LightCoverKeys.space free h J)
    (max (LightRawAKeys.space (LightCoverKeyData.keyEnd free h J) xs.length U)
      (LightBalancedWanted.space (wantedFree free h J xs.length) M (left P xs) (right h J)
        (3*xs.length) (totalKeys h J) (keyBound P h J)))

def word (P M h J U n : ℕ) : ℕ :=
  max (LightCoverKeys.word h J) (max (LightRawAKeys.word P U)
    (LightBalancedWanted.word M (3*n) (totalKeys h J) (keyBound P h J)))





























variable {lim : Limits}






















































































end ThreeSum.LightGuardedWanted

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandBanksProgram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Closed program for one shared occurrence table and all original source banks -/

namespace ThreeSum.LightSourceBandBanksProgram

open Light

def program : Program := LightBlockSourceBatchProgram.program ++
  [LightSourceBandHistSelect.body,LightSourceBandBankStep.body 43 42,
    LightSourceBandBankBatch.body 44,LightSourceOccurrenceArray.body 47,
    LightOutputDecodeDigits.body 48,LightOutputDecodeDivide.body,LightSourceBandBanks.body 46 45]

















end ThreeSum.LightSourceBandBanksProgram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandHost


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
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Original normalized source arrays to the complete shared source-bank host

The first call reads physical normalized headers and the selected offset,
and constructs the retained histograms and original-position buckets once.
The second call constructs one occurrence table and all common-band source
banks. The complete host assumes no precomputed source histogram or stage.
-/

namespace ThreeSum.LightSourceBandHost

open Light GlobalEncoding BlockSourceEncoding LocalCoverBounds SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def occurrenceBase (base NL NR g h J : ℕ) : ℕ :=
  SourceBandPairData.next base NL NR g (modulus h J)

def bankHeader (base NL NR g h J : ℕ) : ℕ :=
  occurrenceBase base NL NR g h J+LightBlockSourceCatalog.count h J*J

def finish (base NL NR g h J cut : ℕ) : ℕ :=
  SourceBandBankData.finish (bankHeader base NL NR g h J) NL NR g h J cut

def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceBandPair.space base NL NR g p (modulus h J) U D)
    (LightSourceBandBanks.space (bankHeader base NL NR g h J) NL NR g h J cut)

def word (NL NR g p h J U D : ℕ) : ℕ :=
  max (LightSourceBandPair.word NL NR g p (modulus h J) U D)
    (LightSourceBandBanks.word NL NR h J)

def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  LightSourceBandPair.time NL NR g p (modulus h J) U D+
    LightSourceBandBanks.time NL NR g h J cut+500

/-- J,L,h,local prime/cap,cut,modulus,cover arrays, original source value and
endpoint pointers,g,selected original prime,offset cell,free pointer,and
the ordinary compact-capacity/occurrence-count/schedule-size/band-stride controls. -/
def body (pPair pBanks : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPair [v 11, v 12, v 13, v 14, v 15, v 16, v 6, v 17, v 18] 23)
    (Light.Stmt.seq
      (.set 24
        ((Light.Expr.op Light.Op.add) (v 23)
          ((Light.Expr.op Light.Op.mul) (v 20) (v 0))))
      (Light.Stmt.seq
        (.call pBanks
          [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 23, v 7, v 8, v 9, v 10, v 18,
            v 24, v 19, v 20, v 21, v 22]
          25)
        (.set 0 (v 25)))))

structure Procs (P : Program) (pMain : ℕ) where
  pPair : ℕ
  pBanks : ℕ
  pair : LightSourceBandPair.Procs P pPair
  banks : LightSourceBandBanks.Procs P pBanks
  main : P[pMain]?=some (body pPair pBanks)

variable {lim : Limits} {P : Program} {d : ℕ}
















































































end ThreeSum.LightSourceBandHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingEntry


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Load two retained source pointers and construct one shared catalog record

The two sources may come from independent B and C bands. The occurrence
code is already represented by the supplied physical pointer cells. This
program loads those cells, runs the complete existing catalog constructor,
reads its computed prefix count, and writes the five-cell level record.
-/

namespace ThreeSum.LightSharedReportingEntry

open Light SubsetAddress LightPascal ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
open SharedReportingBankData

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

/-- The catalog's twenty-one arguments, with arguments 6 and 7 now source
pointer cells, followed by the exact switch and record destination. -/
def body (pCatalog : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 23 (M (v 6)))
    (Light.Stmt.seq (.set 24 (M (v 7)))
      (Light.Stmt.seq
        (.call pCatalog
          [v 0, v 1, v 2, v 3, v 4, v 5, v 23, v 24, v 8, v 9, v 10, v 11, v 12,
            v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20]
          25)
        (Light.Stmt.seq (.set 26 (M (v 25)))
          (Light.Stmt.seq (.store (v 22) (v 21))
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 22) (k 1)) (v 2))
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 22) (k 2)) (v 20))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 22) (k 3)) (v 16))
                  (Light.Stmt.seq
                    (.store ((Light.Expr.op Light.Op.add) (v 22) (k 4)) (v 26))
                    (.set 0 (v 26)))))))))))

def program : Program := LightReportingCatalogIndex.program ++ [body 51]

def time (h J k boxCut : ℕ) : ℕ := LightReportingCatalogIndex.time h J k boxCut+500












































































































end ThreeSum.LightSharedReportingEntry

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts

open Scales CostLedger ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def localWidth (n : ℕ) : ℕ := 512*half n
def width (n : ℕ) : ℕ := blocks n*localWidth n
def localCount (n : ℕ) : ℕ := LightReportingPrefixArrays.localCount (localWidth n) (half n)

def overhead (n : ℕ) : ℕ :=
  100000*(width n+1)^5+5000*(localWidth n+1)^2*(localSearch 257 n+1)+
    1200*(blocks n+1)+2000*(width n+1)+1050

def time (n k : ℕ) : ℕ := LightReportingCatalogIndex.time (half n) (blocks n) k
  (Switch.residualSize n k-Switch.actualSwitch n k)






































































































end ThreeSum.SharedReportingCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingCatalogBatch


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
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual raw-count batching through the physical suffix-box catalog

Each candidate supplies only its two constructed prefix masks. A real sorted
lookup chooses its cached suffix box, and the actual sparse query stores the
original raw prefix count. The catalog is shared and preserved by all calls.
-/

namespace ThreeSum.LightReportingCatalogBatch

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def roundBody (pQuery : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 23 (M ((Light.Expr.op Light.Op.add) (v 16) (v 22))))
    (Light.Stmt.seq (.set 24 (M ((Light.Expr.op Light.Op.add) (v 17) (v 22))))
      (Light.Stmt.seq
        (.call pQuery
          [v 0, v 1, v 2, v 3, v 23, v 4, v 24, v 5, v 6, v 7, v 8, v 9, v 10,
            v 11, v 12, v 13, v 14, v 15, v 20, v 21]
          25)
        (.store ((Light.Expr.op Light.Op.add) (v 19) (v 22)) (v 25)))))

def body (pQuery : ℕ) : Stmt := .for 22 (v 18) (roundBody pQuery)

def program : Program := LightReportingCatalogQuery.program ++ [body 35]

def time (h J k t n : ℕ) : ℕ := n*(LightReportingCatalogQuery.time h J k t+180)+30

def Inv (μ : ℕ → ℤ) (counts : ℕ → ℕ)
    (h J k t Qmask baseL baseR boxCut indexBase ptrBase inL inR n dst maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
      suffixStage J (512*h) k,k*(512*h),residualSize h J k,Qmask,t,baseL,baseR,
      boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work,j,a,b,r],μ'⟩ ∧
    (∀ i < j, μ' (dst+i) = (counts i : ℤ)) ∧ KeptBut μ μ' maskBase dst n





















































































































































end ThreeSum.LightReportingCatalogBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingInitialize


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
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual root query and frontier initialization

The machine executes the exact catalog-backed empty-prefix query, computes
its capacity from the returned raw mass, and writes the root frontier and
its two aligned zero masks. No supplied root count or capacity is used.
-/

namespace ThreeSum.LightReportingInitialize

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- Query arguments, destination root slot, and local child count. -/
def body (pQuery : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pQuery
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
        v 14, v 15, v 16, v 17, v 18, v 19]
      22)
    (Light.Stmt.seq
      (.set 23
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 22) (k 1))
          (v 21)))
      (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 20) (k 2)) (v 22))
        (Light.Stmt.seq
          (.store ((Light.Expr.op Light.Op.add) (v 20) (k 3)) (v 23))
          (Light.Stmt.seq
            (.store ((Light.Expr.op Light.Op.add) (v 20) (k 1)) (v 10))
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 20) (k 4)) (k 0))
              (Light.Stmt.seq
                (.store
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) (v 20) (k 4)) (v 23))
                  (k 0))
                (.ite (Light.Cond.lt (k 0) (v 22))
                  (Light.Stmt.seq (.store (v 20) (k 1)) (.set 0 (k 1)))
                  (Light.Stmt.seq (.store (v 20) (k 0)) (.set 0 (k 0)))))))))))

def program : Program := LightReportingCatalogQuery.program ++ [body 35]
def time (h J t : ℕ) : ℕ := LightReportingCatalogQuery.time h J 0 t+400

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]














































































































end ThreeSum.LightReportingInitialize

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Exact retained cells of one shared reporting catalog -/

namespace ThreeSum.SharedReportingBankData

open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1500000
set_option maxRecDepth 9000

structure Tables {h J k : ℕ} (μ : ℕ → ℤ) (D : Catalog) (hk : k ≤ J)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop where
  index : ∃ S : List ℤ, Seg μ D.indexBase S ∧
    S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
    S.Pairwise (· ≤ ·)
  pointers : SegN μ D.ptrBase (List.ofFn fun i : Fin (count h k) =>
    D.boxBase+i.val*stride ((J-k)*(512*h)) D.boxCut)
  boxes : ∀ i < count h k, LightBoxStages.StoredThrough μ
    (D.boxBase+i*stride ((J-k)*(512*h)) D.boxCut) D.boxCut
    (leafWeight (block_fit hk) f g ((J-k)*(512*h)) (preL h J k i) (preR h J k i))
    ((J-k)*(512*h))

structure Entry {h J k : ℕ} (μ : ℕ → ℤ) (record : ℕ) (D : Catalog) (hk : k ≤ J)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop where
  header : SegN μ record (D.record h k)
  tables : Tables μ D hk f g























































end ThreeSum.SharedReportingBankData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout

open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

def localWidth (h : ℕ) : ℕ := 512*h
def width (h J : ℕ) : ℕ := J*localWidth h
def suffixWidth (h J k : ℕ) : ℕ := (J-k)*localWidth h
def localChoose (h : ℕ) : ℕ := (localWidth h).choose h
def localPairs (h : ℕ) : ℕ := LightReportingPrefixArrays.localCount (localWidth h) h
def prefixSpan (h k : ℕ) : ℕ := LightRadixKeys.offset (localPairs h) k+1+count h k
def cap (h J k boxCut : ℕ) : ℕ := downsetCap (suffixWidth h J k) boxCut

def pairL (base h : ℕ) : ℕ := base+localChoose h
def pairR (base h : ℕ) : ℕ := pairL base h+localPairs h
def stageL (base h : ℕ) : ℕ := pairR base h+localPairs h
def stageR (base h k : ℕ) : ℕ := stageL base h+prefixSpan h k
def pointers (base h k : ℕ) : ℕ := stageR base h k+prefixSpan h k
def boxes (base h k : ℕ) : ℕ := pointers base h k+count h k
def masks (base h J k boxCut : ℕ) : ℕ :=
  boxes base h k+count h k*stride (suffixWidth h J k) boxCut
def index (base h J k boxCut : ℕ) : ℕ := masks base h J k boxCut
def work (base h J k boxCut : ℕ) : ℕ := masks base h J k boxCut+cap h J k boxCut+count h k
def finish (base h J k boxCut : ℕ) : ℕ :=
  work base h J k boxCut+2*localWidth h+2+1+tableSize (width h J)+(width h J+1)+count h k
def cellSize (h J k boxCut : ℕ) : ℕ := finish 0 h J k boxCut

def catalog (base h J k boxCut t : ℕ) : ReportingHostLevelData.Catalog :=
  ⟨t,boxCut,boxes base h k,index base h J k boxCut,pointers base h k⟩























































































def levelOffset (h J : ℕ) (boxCut : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => levelOffset h J boxCut k+cellSize h J k (boxCut k)















end ThreeSum.SharedReportingBankLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedTraversalScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Scales LocalCoverBounds LightBlockQuery ReportingHostLevelData
open StageBounds CostLedger
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def scaledOverhead (n : ℕ) : ℕ := overhead (half n) (blocks n)





























def CatalogScales (n : ℕ) (D : ℕ → Catalog) : Prop :=
  ∀ k ≤ Switch.terminalDepth n, (D k).t=Switch.actualSwitch n k






























































































open Filter Real Parameters
open scoped Topology

noncomputable section












































end
end ThreeSum.SharedTraversalCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorWantedCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys


/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts

open Light WantedResidueKeys

set_option maxHeartbeats 1800000

def time (P M h J U len : ℕ) : ℕ :=
  LightCoverKeys.time h J+LightRawAKeys.time len U+
    LightOriginalOffset.time M (3*len) (LightGuardedWanted.totalKeys h J)
      (LightGuardedWanted.keyBound P h J)+
    2000*(3*len+LightGuardedWanted.totalKeys h J+M+
      3*len*LightGuardedWanted.totalKeys h J/M+1)*
      (Nat.log 2 (LightGuardedWanted.keyBound P h J+1)+Nat.log 2 (M+M+1)+1)+400

def sourceBase (free M h J len : ℕ) : ℕ :=
  LightWantedSetup.pairBase (LightGuardedWanted.wantedFree free h J len)
    (3*len) (LightGuardedWanted.totalKeys h J) M+
    2*(3*len*LightGuardedWanted.totalKeys h J/M)

def space (free P M h J U len : ℕ) : ℕ :=
  max (LightCoverKeys.space free h J)
    (max (LightRawAKeys.space (LightCoverKeyData.keyEnd free h J) len U)
      (max (LightOriginalOffset.space (LightGuardedWanted.wantedFree free h J len)
        M (3*len+LightGuardedWanted.totalKeys h J) (LightGuardedWanted.keyBound P h J))
        (max (LightSourceResidues.space
          (LightWantedSetup.pairBase (LightGuardedWanted.wantedFree free h J len)
            (3*len) (LightGuardedWanted.totalKeys h J) M)
          M (LightGuardedWanted.keyBound P h J) M)
          (sourceBase free M h J len))))





































































end ThreeSum.EncodedColorWantedCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceFinitePrepared


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
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs


/-! # Actual source construction from the retained prepared outputs -/

namespace ThreeSum.LightSourceFinitePrepared

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs

def args (free base bv be cv ce g p h J cut len : ℕ) : List ℤ :=
  [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,
    maps free h,candidates free h,leftCounts free h,rightCounts free h,
    bv,be,cv,ce,g,p,LightGuardedWanted.wantedFree free h J len+3,base,scheduleSize h]

variable {lim : Limits} {P : Program} {d : ℕ}











































end ThreeSum.LightSourceFinitePrepared

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedOriginal


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical


/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000

abbrev AType (n g : ℕ) (rs : List Record) := Fin (items n g rs).length

def owner {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) : ℕ :=
  (BandRawA.labelAt n g rs w.1.val).owner

def left {h J n g : ℕ} (rs : List Record) (fB : ℕ→ℤ)
    (w : Wanted h J (AType n g rs)) (j : ℕ) : ℤ :=
  fB (BandPartition.start g (ownerRecord n g rs w.1.val).b+j)

def right {h J n g : ℕ} (rs : List Record) (fC : ℕ→ℤ)
    (w : Wanted h J (AType n g rs)) (j : ℕ) : ℤ :=
  fC (BandPartition.start g (ownerRecord n g rs w.1.val).c+j)

def leftCount {h J n g : ℕ} (rs : List Record) (NB : ℕ)
    (w : Wanted h J (AType n g rs)) : ℕ := bandLength NB g (ownerRecord n g rs w.1.val).b

def rightCount {h J n g : ℕ} (rs : List Record) (NC : ℕ)
    (w : Wanted h J (AType n g rs)) : ℕ := bandLength NC g (ownerRecord n g rs w.1.val).c

def globalItems (h J n NB NC g p : ℕ) (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) : Finset (RawItem h J (AType n g rs) (Fin NB) (Fin NC)) :=
  rawOn h J (p : ℤ) shift (finiteAllProducts n NB NC g rs)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)

def localItems (h J n NB NC g p : ℕ) (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    Finset (RawItem h J (AType n g rs) (Fin NB) (Fin NC)) :=
  rawOn h J (p : ℤ) shift (finiteOwnerProduct n NB NC g rs (owner rs w))
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)

def Terminal (h J n NB NC g p : ℕ) (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) (k : ℕ) : Prop :=
  ∃ pre∈ReportingHostFrontier.frontier (localItems h J n NB NC g p rs fA fB fC shift w) w k,
    ReportingHostTerminalBatch.Hit (valueAt n g rs fA w.1.val) p shift
      (left rs fB w) (right rs fC w) (leftCount rs NB w) (rightCount rs NC w) w.2.2 k pre

































































section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)
























end Actual

end ThreeSum.ReportingHostWantedOriginal

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_WantedRecordOrder


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences


/-!
# Original wanted labels behind the interleaved pair indices

Left indices recover the A-incidence position and its lift. Right indices
recover the unchanged global output record. The maps retain distinct source
positions even when their integer key values coincide.
-/

namespace ThreeSum.WantedRecordOrder

open GlobalEncoding GlobalKeyEnumeration RawIncidences RawAKeyLists
open OutputDecodeOrder

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

theorem input_length_pos {xs : List ℤ} {i : ℕ} (hi : i < 3*xs.length) : 0 < xs.length := by omega

theorem records_getD {xs : List ℤ} {i : ℕ} (hi : i < 3*xs.length) :
    (RawAKeyLists.records xs).getD i (0,⟨0,input_length_pos hi⟩) =
      (⟨i/xs.length,(Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi⟩,
        ⟨i%xs.length,Nat.mod_lt _ (input_length_pos hi)⟩) := by
  have hN : 0 < xs.length := input_length_pos hi
  change (RawAKeyLists.records xs).getD i (0,⟨0,hN⟩)=_
  have hq : i/xs.length < 3 := (Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi
  have hr : i%xs.length < xs.length := Nat.mod_lt _ (input_length_pos hi)
  have he : i/xs.length*xs.length+i%xs.length=i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i xs.length
  unfold RawAKeyLists.records List.product
  conv_lhs => rw [← he]
  rw [getD_flatMap_uniform _ _ xs.length (by simp) (0 : Fin 3)
    ((0,⟨0,hN⟩) : RawAKeyLists.Record xs)
    (by simpa only [List.length_finRange] using hq) hr]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_finRange] using hr),
    List.getElem_map]
  congr 1
  · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_finRange] using hq)]
    apply Fin.ext
    simp
  · apply Fin.ext
    simp

theorem key_getD {P : ℤ} {xs : List ℤ} {i : ℕ} (hi : i < 3*xs.length) :
    (RawAKeyLists.keys P xs).getD i 0=
      xs.getD (i%xs.length) 0%P+
        lift ⟨i/xs.length,(Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi⟩*P := by
  unfold RawAKeyLists.keys
  rw [List.getD_map_of_lt _ (by rwa [RawAKeyLists.records_length])
    ((0,⟨0,input_length_pos hi⟩) : RawAKeyLists.Record xs) 0,records_getD hi]
  rfl

def label {xs : List ℤ} (h J i j : ℕ) (hi : i < 3*xs.length) :
    RawReporting.Wanted h J (Fin xs.length) :=
  (⟨i%xs.length,Nat.mod_lt _ (input_length_pos hi)⟩,
    (⟨i/xs.length,(Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi⟩,
      LightOutputDecodeOriginal.output h J j))

theorem mem_wanted_iff {M h J i j : ℕ} {P shift : ℤ} {xs : List ℤ}
    (hi : i < 3*xs.length) (hj : j < LightGuardedWanted.totalKeys h J) :
    label h J i j hi ∈ RawAKeyLists.wanted M P xs h J shift ↔
      (M : ℤ) ∣ (RawAKeyLists.keys P xs).getD i 0+shift-(globalKeys h J).getD j 0 := by
  rw [RawAKeyLists.mem_wanted,key_getD hi,
    OutputDecodeRecords.original_global_key (show j < OutputDecodeRecords.localCount h^J from hj)]
  rfl






















theorem cells_getD_left (ps : List (ℕ × ℕ)) (k : ℕ) :
    (WantedPairs.cells ps).getD (2*k) 0=((ps.getD k (0,0)).1 : ℤ) := by
  induction ps generalizing k with
  | nil => simp [WantedPairs.cells]
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k => simpa [WantedPairs.cells,Nat.mul_succ,Nat.add_assoc] using ih k

theorem cells_getD_right (ps : List (ℕ × ℕ)) (k : ℕ) :
    (WantedPairs.cells ps).getD (2*k+1) 0=((ps.getD k (0,0)).2 : ℤ) := by
  induction ps generalizing k with
  | nil => simp [WantedPairs.cells]
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k => simpa [WantedPairs.cells,Nat.mul_succ,Nat.add_assoc] using ih k

theorem segment_pair {μ : ℕ → ℤ} {base k : ℕ} {ps : List (ℕ × ℕ)}
    (H : Light.Seg μ base (WantedPairs.cells ps)) (hk : k < ps.length) :
    μ (base+2*k)=((ps.getD k (0,0)).1 : ℤ) ∧
      μ (base+2*k+1)=((ps.getD k (0,0)).2 : ℤ) := by
  have h0 : 2*k < (WantedPairs.cells ps).length := by rw [WantedPairs.cells_length]; omega
  have h1 : 2*k+1 < (WantedPairs.cells ps).length := by rw [WantedPairs.cells_length]; omega
  constructor
  · rw [← cells_getD_left, List.getD_eq_getElem _ _ h0]
    exact H _ h0
  · rw [← cells_getD_right,List.getD_eq_getElem _ _ h1, Nat.add_assoc]
    exact H _ h1

end ThreeSum.WantedRecordOrder

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandHostProgram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Closed original-array-to-shared-source-bank program -/

namespace ThreeSum.LightSourceBandHostProgram

open Light

def program : Program := LightSourceBandBanksProgram.program ++
  [LightSourceBucketOriginal.body 51 56,LightSourceHistogram.body 52 54,
    LightSourceResidues.body 53,emodBody,LightHistogram.histogramBody 55,fillBody,
    LightSourceBucketFromHistogram.body 57 58,LightSourceBucketOffsets.body,LightSourceBucketScatter.body,
    LightSourceBandStep.body 50,LightSourceBandBatch.body 59,LightSmallDivide.body,
    LightSourceBandSetup.body 61 60,LightSourceBandPair.body 62 55,LightSourceBandHost.body 63 49]


























end ThreeSum.LightSourceBandHostProgram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceControlsHost


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
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Shared source construction with its size controls computed by the program

Three persistent control cells precede the complete source host. The
capacity initializer's polynomial scratch is reclaimed by the source host.
Occurrence count, compact capacity, and bank stride are read from the
constructed cells or the initializer result, never supplied as arguments.
-/

namespace ThreeSum.LightSourceControlsHost

open Light GlobalEncoding BlockSourceEncoding LocalCoverBounds SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def sourceBase (base : ℕ) : ℕ := base+3

def finish (base NL NR g h J cut : ℕ) : ℕ :=
  LightSourceBandHost.finish (sourceBase base) NL NR g h J cut

def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceControls.space (sourceBase base) h J)
    (LightSourceBandHost.space (sourceBase base) NL NR g p h J cut U D)

def word (NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceControls.word h J cut) (LightSourceBandHost.word NL NR g p h J U D)

def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  LightSourceControls.time h J+LightSourceBandHost.time NL NR g p h J cut U D+500

/-- The source host's original inputs and local schedule size; none of
the occurrence count, compact capacity, or bank span is an input. -/
def body (pControls pSource : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 20 ((Light.Expr.op Light.Op.add) (v 18) (k 3)))
    (Light.Stmt.seq
      (.call pControls [v 0, v 1, v 3, v 5, v 19, v 6, v 18, v 20] 21)
      (Light.Stmt.seq (.set 22 (M (v 18)))
        (Light.Stmt.seq (.set 23 (M ((Light.Expr.op Light.Op.add) (v 18) (k 1))))
          (Light.Stmt.seq
            (.call pSource
              [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12,
                v 13, v 14, v 15, v 16, v 17, v 20, v 22, v 23, v 19, v 21]
              24)
            (.set 0 (v 24)))))))

structure Procs (P : Program) (pMain : ℕ) where
  pControls : ℕ
  pSource : ℕ
  controls : LightSourceControls.Procs P pControls
  source : LightSourceBandHost.Procs P pSource
  main : P[pMain]?=some (body pControls pSource)

variable {lim : Limits} {P : Program} {d : ℕ}





























































































end ThreeSum.LightSourceControlsHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingCell


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Compute a suffix capacity and every address before constructing a catalog

The local binomial counts and current prefix count/span are scalar state
maintained by the surrounding bank loops. The compact suffix capacity is
computed here by the actual Pascal/downset routine. All remaining addresses
are computed arithmetically, and the existing entry constructor is called
exactly once. The return value is the next free payload address.
-/

namespace ThreeSum.LightSharedReportingCell

open Light SubsetAddress LightPascal ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog SharedReportingBankData
open SharedReportingBankLayout

set_option maxHeartbeats 2900000
set_option maxRecDepth 15000

/-- h,J,k,source pointer cells,t,boxCut,local choose/pair counts,current
prefix count/span,record destination,and first free payload cell. -/
def body (pSize pEntry : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 13 ((Light.Expr.op Light.Op.mul) (k 512) (v 0)))
    (Light.Stmt.seq (.set 14 ((Light.Expr.op Light.Op.mul) (v 1) (v 13)))
      (Light.Stmt.seq
        (.set 15
          ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.sub) (v 1) (v 2))
            (v 13)))
        (Light.Stmt.seq (.call pSize [v 15, v 6, v 12] 16)
          (Light.Stmt.seq (.set 17 ((Light.Expr.op Light.Op.add) (v 12) (v 7)))
            (Light.Stmt.seq (.set 18 ((Light.Expr.op Light.Op.add) (v 17) (v 8)))
              (Light.Stmt.seq
                (.set 19 ((Light.Expr.op Light.Op.add) (v 18) (v 8)))
                (Light.Stmt.seq
                  (.set 20 ((Light.Expr.op Light.Op.add) (v 19) (v 10)))
                  (Light.Stmt.seq
                    (.set 21 ((Light.Expr.op Light.Op.add) (v 20) (v 10)))
                    (Light.Stmt.seq
                      (.set 22 ((Light.Expr.op Light.Op.add) (v 21) (v 9)))
                      (Light.Stmt.seq
                        (.set 23
                          ((Light.Expr.op Light.Op.mul)
                            ((Light.Expr.op Light.Op.add) (v 15) (k 1)) (v 16)))
                        (Light.Stmt.seq
                          (.set 24
                            ((Light.Expr.op Light.Op.add) (v 22)
                              ((Light.Expr.op Light.Op.mul) (v 9) (v 23))))
                          (Light.Stmt.seq
                            (.set 25
                              ((Light.Expr.op Light.Op.add)
                                ((Light.Expr.op Light.Op.add) (v 24) (v 16))
                                (v 9)))
                            (Light.Stmt.seq
                              (.set 26
                                ((Light.Expr.op Light.Op.add)
                                  ((Light.Expr.op Light.Op.add)
                                    ((Light.Expr.op Light.Op.add)
                                      ((Light.Expr.op Light.Op.add)
                                        ((Light.Expr.op Light.Op.add)
                                          ((Light.Expr.op Light.Op.add) (v 25)
                                            ((Light.Expr.op Light.Op.mul) (k 2)
                                              (v 13)))
                                          (k 2))
                                        (k 1))
                                      ((Light.Expr.op Light.Op.mul)
                                        ((Light.Expr.op Light.Op.add) (v 14)
                                          (k 1))
                                        ((Light.Expr.op Light.Op.add) (v 14)
                                          (k 1))))
                                    ((Light.Expr.op Light.Op.add) (v 14) (k 1)))
                                  (v 9)))
                              (Light.Stmt.seq
                                (.set 27
                                  ((Light.Expr.op Light.Op.mul)
                                    ((Light.Expr.op Light.Op.mul) (k 2) (v 0))
                                    (v 1)))
                                (Light.Stmt.seq
                                  (.call pEntry
                                    [v 14, v 27, v 6, v 15, v 15,
                                      (Light.Expr.op Light.Op.mul) (v 2) (v 13),
                                      v 3, v 4, v 13, v 0, v 2, v 12, v 17, v 18,
                                      v 19, v 20, v 21, v 22, v 24, v 25, v 24,
                                      v 5, v 11]
                                    28)
                                  (.set 0 (v 26))))))))))))))))))

def program : Program :=
  ReportingHostRelocation.program LightSharedReportingEntry.program LightDownsetSize.program ++
    [body 53 52]

def time (h J k boxCut : ℕ) : ℕ :=
  LightDownsetSize.time ((J-k)*(512*h))+LightSharedReportingEntry.time h J k boxCut+1500























































































































































end ThreeSum.LightSharedReportingCell

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# Charge the executed shared catalog bank, including every surrounding loop

The exact sum of level costs is preserved. Actual switch evaluation,
downset sizing, address arithmetic, row iteration, and the one-time depth
and Pascal initializers add only a factor of exponent zero to the existing
shared-box ledger. The bank is indexed by occurrence and two bands alone.
-/

namespace ThreeSum.SharedReportingBankCosts

open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def roundExtra (n : ℕ) : ℕ :=
  LightSwitchCosts.timeBudget n+1400*(width n+1)^2+2808
def roundOverhead (n : ℕ) : ℕ := SharedReportingCosts.overhead n+roundExtra n
def setup (n : ℕ) : ℕ :=
  LightSwitchCosts.depthBudget n+1500*(localWidth n+1)^2+3300
def overhead (n : ℕ) : ℕ := roundOverhead n+1600+setup n
def budget (n : ℕ) : ℕ := overhead n*(boxCount n+1)
























































































noncomputable section

































end
end ThreeSum.SharedReportingBankCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingCatalogLevel


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
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Actual shared-catalog queries followed by stable positive compaction -/

namespace ThreeSum.LightReportingCatalogLevel

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pBatch pFilter : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pBatch
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
        v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21]
      23)
    (.call pFilter [v 18, v 19, v 22] 0))

def suffix : Program := [LightReportingFilter.body,body 36 37]
def program : Program := LightReportingCatalogBatch.program ++ suffix

def time (h J k t n : ℕ) : ℕ := LightReportingCatalogBatch.time h J k t n+LightReportingFilter.time n+100

























































































end ThreeSum.LightReportingCatalogLevel

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingInitializeStored


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
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Root initialization from retained catalog and cover headers

The root query reads its sorted-catalog controls and the selected cover's
actual group-size cell. The empty-prefix dimensions are computed directly
from the common source width and cut; root mass and capacity are returned
by the executed query and initializer.
-/

namespace ThreeSum.LightReportingInitializeStored

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

/-- Width, source cut, source stages, catalog bank, packed query mask,
retained cover, root output, mask scratch, and work. -/
def body (pInit : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 10 (M ((Light.Expr.op Light.Op.add) (v 6) (k 3))))
    (Light.Stmt.seq (.set 11 (M (v 4)))
      (Light.Stmt.seq (.set 12 (M ((Light.Expr.op Light.Op.add) (v 4) (k 1))))
        (Light.Stmt.seq (.set 13 (M ((Light.Expr.op Light.Op.add) (v 4) (k 2))))
          (Light.Stmt.seq (.set 14 (M ((Light.Expr.op Light.Op.add) (v 4) (k 3))))
            (Light.Stmt.seq
              (.set 15 (M ((Light.Expr.op Light.Op.add) (v 4) (k 4))))
              (.call pInit
                [v 0, v 1, v 0, k 0, k 0, k 0, k 0, v 0, k 0, v 1, v 5, v 11, v 2,
                  v 3, v 12, v 13, v 14, v 15, v 8, v 9, v 7, v 10]
                0)))))))

def program : Program := LightReportingInitialize.program ++ [body 36]
def time (h J t : ℕ) : ℕ := LightReportingInitialize.time h J t+500

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]








































































end ThreeSum.LightReportingInitializeStored

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankLevels


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000

def residual (h J k : ℕ) : ℕ := 2*h*(J-k)
def switch (h J k : ℕ) : ℕ := Switch.switchIndex J k (residual h J k)
def boxCut (h J k : ℕ) : ℕ := residual h J k-switch h J k
def offset (h J : ℕ) : ℕ → ℕ := levelOffset h J (boxCut h J)
def baseAt (base h J k : ℕ) : ℕ := base+offset h J k
def catalogAt (base h J k : ℕ) : ReportingHostLevelData.Catalog :=
  catalog (baseAt base h J k) h J k (boxCut h J k) (switch h J k)

def Built (μ : ℕ → ℤ) (record base h J K : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop :=
  ∀ k < K, ∃ hk : k ≤ J, Entry μ (record+5*k) (catalogAt base h J k) hk f g
















































































































end ThreeSum.SharedReportingBankLevels

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsQuery


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Concrete scratch limits for queries into the retained shared catalog bank

One mask span of `2^W` works for every prescribed level. The remaining
workspace is polynomial in W, including the exact packed-key remainder
workspace. Both source cardinalities are bounded independently by the
physical band size, and the switch and cut are the executed bank values.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def queryMaskSpan (h J : ℕ) : ℕ := 2^(width h J)
def queryWorkSpan (h J : ℕ) : ℕ := (width h J+1)^2+8*(width h J+1)+8
def queryWord (h J g : ℕ) : ℕ :=
  (width h J+1)*2^(width h J+1)+
    LightReportingCatalogLookup.word (width h J) (2^(2*width h J))+
    (2^(width h J)+1)*(2^(width h J)*((2^(width h J)*g)*(2^(width h J)*g)))








































































































end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedTraversalDispatchCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts

open Scales StageBounds CostLedger LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def scalarOverhead (c n : ℕ) : ℕ :=
  800*(blocks n+1)*(8192*(inputBits n+1)+3)+8300+
    20*width (half n) (blocks n)+2520+c














def totalOverhead (c n : ℕ) : ℕ := scaledOverhead n+scalarOverhead c n

def dispatchBudget (c k n : ℕ) : ℕ := 30+totalOverhead c n*
  (initialCount UniformStageBounds.wantedBudget n+
    activeCount (UniformStageBounds.falseBudget k) n+
    terminalCount (UniformStageBounds.falseBudget k) n)











































open Filter Real Parameters
open scoped Topology

noncomputable section



































end
end ThreeSum.SharedTraversalCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_WantedRecordCoverage


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder


/-!
# Completeness of the physical wanted-record array

The pair array produced by the selected-offset join covers every original
guarded wanted label. Conversely every stored pair selects such a label.
These statements concern the actual emitted array, including duplicate
integer keys at different source positions.
-/

namespace ThreeSum.WantedRecordCoverage

open Light GlobalEncoding GlobalKeyEnumeration WantedRecordOrder

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



























theorem output_pair {μ : ℕ → ℤ} {free M P h J slot : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (hk : slot < (μ free).toNat) :
    ∃ i j, ∃ hi : i < 3*xs.length,
      j < LightGuardedWanted.totalKeys h J ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot)=(i : ℤ) ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot+1)=(j : ℤ) ∧
      label h J i j hi ∈ RawAKeyLists.wanted M P xs h J shift := by
  rcases H with ⟨hcount,_,_,_,ps,hlen,_,hmem,hseg⟩
  have hk' : slot < ps.length := by rw [hlen]; simpa only [hcount,Int.toNat_natCast] using hk
  let p := ps.getD slot (0,0)
  have hp : p ∈ ps := by
    rw [show p=ps[slot] from List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  have hb := (hmem p.1 p.2).mp hp
  have hread := segment_pair hseg hk'
  refine ⟨p.1,p.2,hb.1,hb.2.1,hread.1,hread.2,?_⟩
  exact (mem_wanted_iff hb.1 hb.2.1).mpr hb.2.2
























end ThreeSum.WantedRecordCoverage

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceControlsHostProgram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Closed original source program with computed bank dimensions -/

namespace ThreeSum.LightSourceControlsHostProgram

open Light

def program : Program := LightSourceBandHostProgram.program ++
  [LightDownsetSize.body 66 73,LightSubsetSetup.body 67 71 72,
    LightPascal.buildBody 68 69,fillBody,LightPascal.rowBody 70,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 72,LightSubsetOffset.body,
    LightNatPower.body,log2Body,LightSourceControlsMax.body,
    LightSourceControlsSpan.body 76,LightSourceControls.body 74 65 75 77,
    LightSourceControlsHost.body 78 64]

def retainedProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩

def batchProcs : LightBlockSourceBatch.Procs program 42 := ⟨41,⟨0,retainedProcs,rfl⟩,rfl⟩

def banksProcs : LightSourceBandBanks.Procs program 49 :=
  ⟨46,47,48,45,rfl,rfl,rfl,⟨44,⟨43,42,rfl,batchProcs,rfl⟩,rfl⟩,rfl⟩

def originalProcs : LightSourceBucketOriginal.Procs program 50 :=
  ⟨51,56,⟨52,53,54,55,rfl,rfl,rfl,rfl,rfl⟩,⟨57,58,rfl,rfl,rfl⟩,rfl⟩

def setupProcs : LightSourceBandSetup.Procs program 62 :=
  ⟨61,60,rfl,⟨59,⟨50,originalProcs,rfl⟩,rfl⟩,rfl⟩

def pairProcs : LightSourceBandPair.Procs program 63 := ⟨62,55,setupProcs,rfl,rfl⟩

def sourceProcs : LightSourceBandHost.Procs program 64 := ⟨63,49,pairProcs,banksProcs,rfl⟩

def controlProcs : LightSourceControls.Procs program 78 :=
  ⟨74,65,75,77,76,66,67,68,69,70,71,72,73,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩

def programProcs : LightSourceControlsHost.Procs program 79 := ⟨78,64,controlProcs,sourceProcs,rfl⟩



end ThreeSum.LightSourceControlsHostProgram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceFiniteCosts


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
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts

open Scales TrimScales StageBounds CostLedger BandScales

def time (n p U D : ℕ) : ℕ :=
  (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
    2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
    SourceControlCosts.factor (microHalf (inputBits n)) (blockCount (inputBits n))+5705)*encoderCount n+4859

def space (base n p U D : ℕ) : ℕ :=
  base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n+
      (256*mu n+1)^2+(256*mu n+1))*encoderCount n+
    Nat.log 2 (scheduleCount n+1)+
    max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19

def finish (base n : ℕ) : ℕ :=
  base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17

def word (n p U D : ℕ) : ℕ :=
  LightSourceControlsHost.word n n (bandSize n) p
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D





























end ThreeSum.SourceFiniteCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceFiniteData


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
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords


/-! # Retained source banks for the concrete normalized finite arrays -/

namespace ThreeSum.SourceFiniteData

open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA

structure Stored (μ : ℕ → ℤ) (base g p h J cut : ℕ) (B C : List ℤ) (shift r : ℤ) : Prop where
  returned : r=(LightSourceControlsHost.finish base B.length C.length g h J cut : ℤ)
  controls : Seg μ base (SourceControlLayout.values h J cut)
  buckets : SourceBandPairData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0)
    (LightSourceControlsHost.sourceBase base) B.length C.length g p (BlockSourceEncoding.modulus h J) shift
  banks : SourceBandBankData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0)
    (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J)
    B.length C.length g h J cut
    (LightSourceBandHost.occurrenceBase (LightSourceControlsHost.sourceBase base) B.length C.length g h J)
    (p : ℤ) shift


























/-- The actual color/band payload with its normalized lists exposed, so
the owner records and finite source banks use the very same B/C witnesses. -/
def Normalized (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g)
    (originalA originalB originalC A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) (r : ℤ) : Prop :=
  let rs := sortedRecords A B C g hg hsA hsB hsC
  r=((items A.length g rs).length : ℤ) ∧
    LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
    LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
    LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
    LightBandEnumeration.Tables μ tables
      (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
      (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
      (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)) ∧
    Seg μ rec (cells rs) ∧
    BandRawA.Stored μ vals (LightBandRawA.ownerBase vals rs.length g)
      (LightBandRawA.positionBase vals rs.length g) (fun i => A.getD i 0) (items A.length g rs)















end ThreeSum.SourceFiniteData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingCatalogExpand


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
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Complete parent expansion through an actual shared shrinking-suffix catalog

This program constructs every ordered child mask pair, locates its own cached
box through the physical sorted index, runs the exact original raw-count
query, and stably compacts positive child positions. It requires no supplied
per-child box addresses and retains the complete source/catalog storage.
-/

namespace ThreeSum.LightReportingCatalogExpand

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pChildren pLevel : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pChildren [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 26)
    (.call pLevel
      [v 0, v 10, v 11, v 12, v 12, v 11, v 25, v 13, v 26, v 14, v 15, v 16,
        v 17, v 18, v 19, v 20, v 7, v 8, v 21, v 22, v 24, v 9, v 23]
      0))

def program : Program :=
  ReportingHostRelocation.program LightBlockChildren.program LightReportingCatalogLevel.program ++
    [body 0 45]

def time (h J k t : ℕ) : ℕ :=
  LightBlockChildren.time (width h J) (2*h) h+
    LightReportingCatalogLevel.time h J (k+1) t (groupSize h)+150



















































































































































end ThreeSum.LightReportingCatalogExpand

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedInitialize


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
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
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
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Executed wanted-mask packing, root query, and cumulative guard

The program packs the decoded original query rows, initializes the actual
root frontier using persistent catalogs, and updates the running mass
counter before any proportional traversal. Its Boolean result is exactly
the actual threshold comparison. The global guard-soundness theorem can
therefore certify this early branch on the original owner domain.
-/

namespace ThreeSum.LightReportingWantedInitialize

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

/-- Width, cut, J, L, source stages, catalog bank, raw/packed query rows,
retained cover, dense counter/header, root output, and query scratch. -/
def body (pPack pInit pGuard : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 14 (M ((Light.Expr.op Light.Op.add) (v 10) (k 1))))
    (Light.Stmt.seq (.call pPack [v 2, v 3, v 7, v 8, v 13] 15)
      (Light.Stmt.seq
        (.call pInit [v 0, v 1, v 4, v 5, v 6, v 15, v 9, v 11, v 12, v 13] 16)
        (.call pGuard [v 10, v 11, v 14] 0))))

def initialLibraries : Program := ReportingHostRelocation.program
  LightBlockMasks.program LightReportingInitializeStored.program
def libraries : Program := ReportingHostRelocation.program initialLibraries LightDenseGuard.program
def program : Program := libraries ++ [body 0 39 40]
def time (h J t : ℕ) : ℕ :=
  LightBlockMasks.time J (512*h)+LightReportingInitializeStored.time h J t+LightDenseGuard.time+600

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







































































































end ThreeSum.LightReportingWantedInitialize

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingLevels


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Construct every level once for one occurrence and independent source bands

The loop executes the cubic switch, maintains the exact prefix count and
prefix-array span, and appends one compact catalog per level. Its budget is
the sum of the actual level budgets. Five-cell metadata records are
contiguous; completed payloads remain immutable.
-/

namespace ThreeSum.LightSharedReportingLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData SharedReportingBankLevels

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

/-- h,J,level count,source pointer cells,local choose/pair counts,record and
payload destinations. The surrounding initializer computes the level count. -/
def body (pSwitch pCell : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 9 (k 1))
    (Light.Stmt.seq (.set 10 (k 2))
      (Light.Stmt.seq (.set 11 (v 8))
        (Light.Stmt.seq
          (.for 12 (v 2)
            (Light.Stmt.seq
              (.set 13
                ((Light.Expr.op Light.Op.mul)
                  ((Light.Expr.op Light.Op.mul) (k 2) (v 0))
                  ((Light.Expr.op Light.Op.sub) (v 1) (v 12))))
              (Light.Stmt.seq (.call pSwitch [v 1, v 12, v 13] 14)
                (Light.Stmt.seq
                  (.set 15 ((Light.Expr.op Light.Op.sub) (v 13) (v 14)))
                  (Light.Stmt.seq
                    (.call pCell
                      [v 0, v 1, v 12, v 3, v 4, v 14, v 15, v 5, v 6, v 9, v 10,
                        (Light.Expr.op Light.Op.add) (v 7)
                          ((Light.Expr.op Light.Op.mul) (k 5) (v 12)),
                        v 11]
                      11)
                    (Light.Stmt.seq
                      (.set 9 ((Light.Expr.op Light.Op.mul) (v 9) (v 6)))
                      (.set 10
                        ((Light.Expr.op Light.Op.add)
                          ((Light.Expr.op Light.Op.add) (v 10) (k 1))
                          (v 9)))))))))
          (.set 0 (v 11))))))

def roundTime (h J i : ℕ) : ℕ :=
  LightSwitch.time (residual h J i)+LightSharedReportingCell.time h J i (boxCut h J i)+800
def time (h J K : ℕ) : ℕ := (∑ i ∈ Finset.range K, (roundTime h J i+8))+100

def program : Program :=
  ReportingHostRelocation.program LightSharedReportingCell.program LightSwitch.program ++ [body 63 62]



structure Resources (lim : Limits) (base h J K B D d : ℕ) : Prop where
  state : ((J+K+512+prefixSpan h K+count h K : ℕ) : ℤ) ≤ lim.word
  space : baseAt base h J K ≤ lim.space
  powers : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word
  keys : ∀ i < K, (LightRadixKeys.word (2^(512*h)) (2^(512*h)) i : ℤ) ≤ lim.word
  width : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word
  index : ∀ i < K, (LightReportingSortedCatalog.word (J*(512*h)) (count h i) : ℤ) ≤ lim.word
  values : ∀ i < K, (((2^((J-i)*(512*h))*
    ((2^((J-i)*(512*h))*B)*(2^((J-i)*(512*h))*D))) : ℕ) : ℤ) ≤ lim.word
  switch : ∀ i < K, (LightSwitch.word J (residual h J i) : ℤ) ≤ lim.word
  pairDepth : d+512*h+K+8 ≤ lim.depth
  widthDepth : d+J*(512*h)+18 ≤ lim.depth
  sortDepth : ∀ i < K, d+Nat.clog 2 (count h i)+6 ≤ lim.depth

def Inv (μ : ℕ → ℤ) (record base h J K cellL cellR i : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) (σ : State) : Prop :=
  ∃ (r t cut : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base,
      count h i,prefixSpan h i,baseAt base h J i,i,r,t,cut],ν⟩ ∧
    Built ν record base h J i f g ∧ Kept μ ν record ∧ KeptBut μ ν base record (5*K)





































































































































end ThreeSum.LightSharedReportingLevels

end


