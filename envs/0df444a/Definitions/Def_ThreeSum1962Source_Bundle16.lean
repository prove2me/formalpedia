-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle16
-- name    : ThreeSum1962Source_Bundle16
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:27:51.215151+00:00
-- url     : https://prove2.me/theorems/d390f931-e58c-4227-8202-b0e4f99cad64
-- title:
--   Complete shared-bank rows, retained color data, and frontier traversal
-- statement:
--   This bundle defines the physical order of shared reporting rows. With $n_B,n_C$ source-band counts, occurrence index $s$, and band indices $i,j$, the row rank is
--   $$\operatorname{rank}(s,i,j)=(s n_B+i)n_C+j.$$
--   The completed-row predicate requires all valid rows below a processed rank to contain their level catalogs. Header and access definitions locate the full metadata slab and payloads. Retained pipeline records connect normalized color inputs, chosen primes, cover data, wanted pairs, and source banks. Program bodies compose complete bank construction, positive-frontier expansion, level traversal, and reporting setup; accompanying definitions specify traversal costs and finite resource envelopes.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/DenseGuardWanted.lean#L17-L71
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorNormalizedData.lean#L11-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorPipelineData.lean#L11-L80
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorPrimeReadyData.lean#L9-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorSourcesCosts.lean#L10-L11
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorStageCosts.lean#L10-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorFiniteSources.lean#L10-L16
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorSources.lean#L22-L48
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorWantedSources.lean#L12-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingFrontierStep.lean#L29-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingLevels.lean#L24-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingPositiveExpand.lean#L26-L40
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingStoredStep.lean#L25-L52
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedAccess.lean#L24-L54
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingBank.lean#L21-L62
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingHost.lean#L24-L72
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingPair.lean#L14-L23
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumReportingSetupBank.lean#L14-L28
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedDecision.lean#L29-L32
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedPhysical.lean#L20-L60
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedPrefix.lean#L30-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankAccess.lean#L14-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankHeader.lean#L13-L67
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBounds.lean#L21-L40
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean#L13-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsWanted.lean#L23-L85
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankRows.lean#L14-L123
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedTraversalCosts.lean#L24-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumColorBudgets.lean#L96-L102
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumReportingSetupData.lean#L11-L41

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankRows


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels


/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1800000

def pairs (S nb nc : ℕ) : ℕ := S*nb*nc
def rank (nb nc s i j : ℕ) : ℕ := (s*nb+i)*nc+j
def total (h J NB NC g : ℕ) : ℕ :=
  pairs (LightBlockSourceCatalog.count h J) (BandPartition.size NB g) (BandPartition.size NC g)
def rowRecord (record K q : ℕ) : ℕ := record+5*K*q
def rowBase (base h J K q : ℕ) : ℕ := base+q*offset h J K































































































def Done (μ : ℕ → ℤ) (record base h J K NB NC g processed : ℕ)
    (fB fC : ℕ → ℤ) (p shift : ℤ) : Prop :=
  ∀ s < LightBlockSourceCatalog.count h J, ∀ i < BandPartition.size NB g,
    ∀ j < BandPartition.size NC g,
    rank (BandPartition.size NB g) (BandPartition.size NC g) s i j < processed →
    Built μ (rowRecord record K (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      (rowBase base h J K (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j)) h J K
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s))




































end ThreeSum.SharedReportingBankRows

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsWanted


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout


/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostWantedLayout ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

def wantedWork (h J K N NB NC : ℕ) : ℕ :=
  (LightReportingWantedLayout.layout 0 h J K N NB NC).work

def wantedNumeric (h J K N NB NC : ℕ) : ℕ :=
  N*NB+N*NB*NC+massBound N NB NC (representationCap h J)+
    J+512*h+K+N+NB+NC+representationCap h J+groupSize h+
    LightBlockQuery.sourceCut h J+1024

def wantedScratch (h J V : ℕ) : ℕ :=
  LightReportingTerminal.space 0 h J+queryWorkSpan h J+
    (Nat.log 2 (V+1)+2)+(512*h+1)+20

def wantedCells (h J K N NB NC V : ℕ) : ℕ :=
  wantedWork h J K N NB NC+wantedNumeric h J K N NB NC+wantedScratch h J V

def wantedDepth (h J K N NB NC : ℕ) : ℕ :=
  K+2*LightBlockQuery.width h J+massBound N NB NC (representationCap h J)+
    2^(LightBlockQuery.width h J)+50
































structure WantedBuffers (lim : Limits) (dst h J K N NB NC V : ℕ) : Prop where
  numeric : (LightReportingWantedLayout.layout dst h J K N NB NC).work+
    wantedNumeric h J K N NB NC≤lim.space
  terminal : LightReportingTerminal.space
    (LightReportingWantedLayout.layout dst h J K N NB NC).work h J≤lim.space
  query : (LightReportingWantedLayout.layout dst h J K N NB NC).work+
    queryWorkSpan h J≤lim.space
  decoder : LightWantedDecode.space
    (LightReportingWantedLayout.layout dst h J K N NB NC).work V≤lim.space
  pack : (LightReportingWantedLayout.layout dst h J K N NB NC).work+(512*h+1)≤lim.space
  parameters : J+512*h+groupSize h+LightBlockQuery.sourceCut h J≤lim.space
  values : ∀ x∈ReportingHostWantedLayout.values
    (LightReportingWantedLayout.layout dst h J K N NB NC), x≤lim.space




































section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







































end Raw
end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_DenseGuardWanted


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder


/-!
# Distinct wanted labels in the actual emitted array

The join's physical slots decode injectively, even when original integer
values or key values repeat. Consequently every prefix of the actual
array is a valid distinct-label input to the cumulative dense guard.
-/

namespace ThreeSum.DenseGuardWanted

open Light WantedRecordOrder

def leftIndex (μ : ℕ → ℤ) (free NL NR M slot : ℕ) : ℕ :=
  (μ (LightWantedSetup.pairBase free NL NR M+2*slot)).toNat

def rightIndex (μ : ℕ → ℤ) (free NL NR M slot : ℕ) : ℕ :=
  (μ (LightWantedSetup.pairBase free NL NR M+2*slot+1)).toNat



















theorem output_bounds {μ : ℕ → ℤ} {free M P h J slot : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (hk : slot < (μ free).toNat) :
    leftIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot < 3*xs.length ∧
      rightIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot <
        LightGuardedWanted.totalKeys h J := by
  obtain ⟨i,j,hi,hj,hL,hR,_⟩ := WantedRecordCoverage.output_pair H hk
  simpa only [leftIndex,rightIndex,hL,hR,Int.toNat_natCast] using And.intro hi hj

def labelAt {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (slot : Fin (μ free).toNat) : RawReporting.Wanted h J (Fin xs.length) :=
  label h J (leftIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot.val)
    (rightIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot.val)
    (output_bounds H slot.isLt).1










def labels {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift) :
    List (RawReporting.Wanted h J (Fin xs.length)) := List.ofFn (labelAt H)





































end ThreeSum.DenseGuardWanted

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorSources


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


/-!
# Source banks from the actual cover and wanted output headers

The program reads its reusable destination from wanted+2, reads all local
source controls and pointers from the constructed cover header, computes
localPrime^J with the existing scalar-power procedure, and invokes the
complete shared source host. No source dimension or cover pointer is an
externally supplied control.
-/

namespace ThreeSum.LightEncodedColorSources

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

def sourceBase (free p M h J : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
    (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J) (3*xs.length)
    (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J : ℤ)

/-- h,J,cut,B value/header,C value/header,g,P,wanted header,cover header. -/
def body (pPower pSource : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 9) (k 2))))
    (Light.Stmt.seq (.set 12 ((Light.Expr.op Light.Op.add) (v 9) (k 3)))
      (Light.Stmt.seq (.set 13 (M ((Light.Expr.op Light.Op.add) (v 10) (k 6))))
        (Light.Stmt.seq (.call pPower [v 13, v 1] 14)
          (Light.Stmt.seq
            (.set 15 (M ((Light.Expr.op Light.Op.add) (v 10) (k 8))))
            (Light.Stmt.seq
              (.set 16 (M ((Light.Expr.op Light.Op.add) (v 10) (k 7))))
              (Light.Stmt.seq
                (.set 17 (M ((Light.Expr.op Light.Op.add) (v 10) (k 10))))
                (Light.Stmt.seq
                  (.set 18 (M ((Light.Expr.op Light.Op.add) (v 10) (k 12))))
                  (Light.Stmt.seq
                    (.set 19 (M ((Light.Expr.op Light.Op.add) (v 10) (k 13))))
                    (Light.Stmt.seq
                      (.set 20 (M ((Light.Expr.op Light.Op.add) (v 10) (k 14))))
                      (Light.Stmt.seq
                        (.set 21 (M ((Light.Expr.op Light.Op.add) (v 10) (k 15))))
                        (.call pSource
                          [v 1, v 15, v 0, v 13, v 16, v 2, v 14, v 18, v 19,
                            v 20, v 21, v 3, v 4, v 5, v 6, v 7, v 8, v 12, v 11,
                            v 17]
                          0))))))))))))

def program : Program := LightSourceControlsHostProgram.program ++ [body 74 79]



def time (NL NR g p h J cut U M : ℕ) : ℕ :=
  LightNatPower.time J+LightSourceControlsHost.time NL NR g p h J cut U M+1000

variable {lim : Limits} {d : ℕ}














































































































end ThreeSum.LightEncodedColorSources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorSourcesCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-! # Original-size resource envelope for the actual source-header adapter -/

namespace ThreeSum.EncodedColorSourcesCosts

open Scales TrimScales BandScales

def time (n p U M : ℕ) : ℕ :=
  LightNatPower.time (blockCount (inputBits n))+SourceFiniteCosts.time n p U M+1000













end ThreeSum.EncodedColorSourcesCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorNormalizedData


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
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData

open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout

def incidences (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List ℤ :=
  values (fun j => A.getD j 0)
    (items A.length (bandSize n) (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) : Prop :=
  Seg μ free (normalizedHeads free n (bandSize n)) ∧
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    μ (normalizedEnd free n (bandSize n))=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    SourceFiniteData.Normalized μ (av free n) (ae free n) (bv free n) (be free n) (cv free n) (ce free n)
      (tables free n) (rec free n (bandSize n)) (vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
      (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
      A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ)










































end ThreeSum.EncodedColorNormalizedData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingPositiveExpand


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
namespace ThreeSum.LightReportingPositiveMasks
end ThreeSum.LightReportingPositiveMasks
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
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual parent expansion returning compact positive-prefix mask arrays

All child construction, physical catalog lookup, exact querying, positive
selection, and aligned mask gathering are executed by this closed program.
Only the actual positive output intervals may change below child scratch.
-/

namespace ThreeSum.LightReportingPositiveExpand

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive LightReportingPositiveMasks

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pExpand pGather : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pExpand
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
        v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25]
      28)
    (Light.Stmt.seq (.call pGather [v 23, v 7, v 8, v 28, v 21, v 26, v 27] 29)
      (.set 0 (v 28))))

def program : Program :=
  ReportingHostRelocation.program LightReportingCatalogExpand.program LightReportingGatherPair.program ++
    [body 46 48]

def time (h J k t : ℕ) : ℕ :=
  LightReportingCatalogExpand.time h J k t+LightReportingGatherPair.time (groupSize h)+120

abbrev KeptOutputs (μ ν : ℕ → ℤ) (bound outL outR n : ℕ) : Prop :=
  SameOn (fun i => i < bound ∧ Outside outL n i ∧ Outside outR n i) μ ν











































































































end ThreeSum.LightReportingPositiveExpand

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingPair


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources


/-! # Load the two independent source-band pointer cells for one shared pair -/

namespace ThreeSum.LightSharedReportingPair

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankLayout SharedReportingBankLevels SharedReportingBankSources

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000

/-- h,J,level count,first source bank,source-bank span,occurrence,B band,C
band,local choose/pair counts,metadata row,and first free payload. -/
def body (pLevels : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 12
      ((Light.Expr.op Light.Op.add)
        ((Light.Expr.op Light.Op.add) (v 3)
          ((Light.Expr.op Light.Op.mul) (v 6) (v 4)))
        ((Light.Expr.op Light.Op.mul) (k 2) (v 5))))
    (Light.Stmt.seq
      (.set 13
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v 3)
              ((Light.Expr.op Light.Op.mul) (v 7) (v 4)))
            ((Light.Expr.op Light.Op.mul) (k 2) (v 5)))
          (k 1)))
      (Light.Stmt.seq
        (.call pLevels [v 0, v 1, v 2, v 12, v 13, v 8, v 9, v 10, v 11] 14)
        (.set 0 (v 14)))))

def time (h J K : ℕ) : ℕ := LightSharedReportingLevels.time h J K+500
def program : Program := LightSharedReportingLevels.program ++ [body 64]























































end ThreeSum.LightSharedReportingPair

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankHeader


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows


/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader

open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1900000

def levels (J : ℕ) : ℕ := LightSwitchDepth.depth J+1
def records (free : ℕ) : ℕ := free+9
def payload (free h J NB NC g : ℕ) : ℕ :=
  records free+5*levels J*total h J NB NC g
def finish (free h J NB NC g : ℕ) : ℕ :=
  rowBase (payload free h J NB NC g) h J (levels J) (total h J NB NC g)
def header (free h J NB NC g : ℕ) : List ℕ :=
  [records free,payload free h J NB NC g,levels J,LightBlockSourceCatalog.count h J,
    BandPartition.size NB g,BandPartition.size NC g,finish free h J NB NC g,
    localChoose h,localPairs h]









































structure Stored (μ : ℕ → ℤ) (free h J NB NC g : ℕ) (fB fC : ℕ → ℤ) (p shift : ℤ) : Prop where
  heads : SegN μ free (header free h J NB NC g)
  rows : Done μ (records free) (payload free h J NB NC g) h J (levels J) NB NC g
    (total h J NB NC g) fB fC p shift





































end ThreeSum.SharedReportingBankHeader

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedPhysical


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


/-!
# The actual wanted array on physical owner-incidence indices

The key constructor uses the mapped A-value list. The reporter and dense
owner domains use physical positions in the incidence-label list. Their
length-preserving transport keeps every physical position, lift and full
output record, including positions holding equal integer values.
-/

namespace ThreeSum.ReportingHostWantedPhysical

open Light BandRawA BandCandidateRows RawIncidences GlobalEncoding

set_option maxHeartbeats 2100000
set_option maxRecDepth 10000

/-- The exact, value-preserving finite index transport; no sorting or
identification of equal values occurs. -/
def incidenceIndices (f : ℕ→ℤ) (n g : ℕ) (rs : List Record) :
    Fin (values f (items n g rs)).length ≃ Fin (items n g rs).length where
  toFun i := ⟨i.val,by simpa only [values_length] using i.isLt⟩
  invFun i := ⟨i.val,by simpa only [values_length] using i.isLt⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl









def transport {α β : Type*} {h J : ℕ} (e : α≃β)
    (w : RawReporting.Wanted h J α) : RawReporting.Wanted h J β := (e w.1,w.2)












section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P (values f (items n g rs)))
    (LightGuardedWanted.right h J) (3*(values f (items n g rs)).length)
    (LightGuardedWanted.totalKeys h J) shift)

def wantedAt (slot : Fin (μ free).toNat) : RawReporting.Wanted h J (Fin (items n g rs).length) :=
  transport (incidenceIndices f n g rs) (DenseGuardWanted.labelAt H slot)




































































end Actual

end ThreeSum.ReportingHostWantedPhysical

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorFiniteSources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-! # Retained finite normalization and actual source controls in one contract -/

namespace ThreeSum.LightEncodedColorFiniteSources

open Light Scales TrimScales BandScales

def base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightEncodedColorSources.sourceBase free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) xs

def args (free bv be cv ce n p len : ℕ) : List ℤ :=
  [microHalf (inputBits n),blockCount (inputBits n),mu n,bv,be,cv,ce,bandSize n,p,
    LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) len,free]













variable {lim : Limits} {d : ℕ}































































end ThreeSum.LightEncodedColorFiniteSources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorPrimeReadyData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # The same normalized finite witnesses and their actually selected prime -/

namespace ThreeSum.EncodedColorPrimeReadyData

open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData

def moduli (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ → ℕ :=
  LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)

def selected (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  moduli n A B C hsA hsB hsC (LightBandPrimeDepth.depth (radix n) (primeWindow n))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) : Prop :=
  Seg μ free (normalizedHeads free n (bandSize n)) ∧
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    μ (normalizedEnd free n (bandSize n))=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    SourceFiniteData.Normalized μ (av free n) (ae free n) (bv free n) (be free n) (cv free n) (ce free n)
      (tables free n) (rec free n (bandSize n)) (vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
      (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
      A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    EncodedColorPrimeData.Stored μ (prime free n (bandSize n)) (radix n) (primeWindow n)
      (moduli n A B C hsA hsB hsC)











end ThreeSum.EncodedColorPrimeReadyData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingFrontierStep


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
namespace ThreeSum.LightReportingPositiveExpand
end ThreeSum.LightReportingPositiveExpand
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
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.ReportingHostPositiveBatch
end ThreeSum.ReportingHostPositiveBatch
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual multi-parent reporting frontier step

The loop reads each stored parent mask pair, executes the complete positive
expansion, and appends only the returned positive masks to aligned output
arrays. The accumulated output is the literal ordered concatenation used by
the original raw-incidence reporting frontier.
-/

namespace ThreeSum.LightReportingFrontierStep

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive ReportingHostPositiveBatch
open LightReportingPositiveExpand

set_option maxHeartbeats 3500000
set_option maxRecDepth 10000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def roundBody (pExpand : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 31 (M ((Light.Expr.op Light.Op.add) (v 24) (v 30))))
    (Light.Stmt.seq (.set 32 (M ((Light.Expr.op Light.Op.add) (v 25) (v 30))))
      (Light.Stmt.seq
        (.call pExpand
          [v 0, v 1, v 2, v 31, v 32, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10,
            v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21,
            v 22, v 23, (Light.Expr.op Light.Op.add) (v 27) (v 29),
            (Light.Expr.op Light.Op.add) (v 28) (v 29)]
          33)
        (.set 29 ((Light.Expr.op Light.Op.add) (v 29) (v 33))))))

def body (pExpand : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 29 (k 0))
    (Light.Stmt.seq (.for 30 (v 26) (roundBody pExpand)) (.set 0 (v 29))))

def program : Program := LightReportingPositiveExpand.program ++ [body 49]
def time (h J k t n : ℕ) : ℕ := n*(LightReportingPositiveExpand.time h J k t+200)+100

def Inv {h J k : ℕ} (μ : ℕ → ℤ) (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J)
    (t baseL baseR boxCut indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame (([width h J,h,rowMask (outputRows w.2.2) ⟨k,hk⟩,subsetMask (querySet k (outputRows w.2.2)),
      masks,dstL,dstR,work,sourceCut h J,suffixStage J (512*h) (k+1),(k+1)*h,residualSize h J (k+1),
      t,baseL,baseR,boxCut,indexBase,ptrBase,count h (k+1),groupSize h,dst,selected,maskBase,(k+1)*(512*h),
      inL,inR,pres.length,outL,outR,(through I w pres hk j).length,j] : List ℕ).map
      (fun n => (n : ℤ)) ++ [a,b,r]),ν⟩ ∧
    SegN ν outL ((through I w pres hk j).map fun pre => subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))) ∧
    SegN ν outR ((through I w pres hk j).map fun pre =>
      subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))) ∧
    KeptOutputs μ ν masks outL outR (through I w pres hk j).length










































































































































































































end ThreeSum.LightReportingFrontierStep

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedTraversalCosts


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
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData


/-!
# Cost of the executed positive-frontier traversal

The expensive expansion remains multiplied by the number of actual positive
parents. Empty frontiers pay only the fixed level overhead. The terminal
scan is charged to the exact original bucket products, and the dense guard
removes this proportional charge from the branch which has already exceeded
the threshold.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostLevelData
open ReportingHostFrontierLayout
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

def levelUnit (h J : ℕ) (D : ℕ → Catalog) (K : ℕ) : ℕ :=
  ∑ k ∈ range K, (LightReportingPositiveExpand.time h J k (D (k+1)).t+200)

def searchUnit (h J : ℕ) (D : ℕ → Catalog) (K : ℕ) : ℕ :=
  levelUnit h J D K+ReportingHostTerminalFrontier.charge h J K+240

def initialUnit (h J : ℕ) (D : ℕ → Catalog) (K : ℕ) : ℕ :=
  LightReportingWantedInitialize.time h J (D 0).t+1300*K+1860

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]








































































































end ThreeSum.SharedTraversalCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingBank


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows


/-!
# One actual shared catalog bank in occurrence, B-band, C-band order

One flat loop has exactly S*nb*nc rounds. Three scalar carry counters give
the occurrence and two independent bands, with C varying fastest. No
quotient, output-subset, lift, or A-incidence loop is used to enumerate
these shared rows. All earlier metadata and payloads remain retained.
-/

namespace ThreeSum.LightSharedReportingBank

open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankRows

set_option maxHeartbeats 3800000
set_option maxRecDepth 16000

/-- h,J,K,source first/span,S,nb,nc,H,E,metadata base,payload base. -/
def body (pPair : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.set 17
      ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (v 5) (v 6))
        (v 7)))
    (Light.Stmt.seq (.set 12 (k 0))
      (Light.Stmt.seq (.set 13 (k 0))
        (Light.Stmt.seq (.set 14 (k 0))
          (Light.Stmt.seq (.set 15 (v 10))
            (Light.Stmt.seq (.set 16 (v 11))
              (Light.Stmt.seq
                (.for 18 (v 17)
                  (Light.Stmt.seq
                    (.call pPair
                      [v 0, v 1, v 2, v 3, v 4, v 12, v 13, v 14, v 8, v 9, v 15,
                        v 16]
                      16)
                    (Light.Stmt.seq (.set 16 (v 16))
                      (Light.Stmt.seq
                        (.set 15
                          ((Light.Expr.op Light.Op.add) (v 15)
                            ((Light.Expr.op Light.Op.mul) (k 5) (v 2))))
                        (.ite
                          (Light.Cond.lt
                            ((Light.Expr.op Light.Op.add) (v 14) (k 1)) (v 7))
                          (.set 14 ((Light.Expr.op Light.Op.add) (v 14) (k 1)))
                          (Light.Stmt.seq (.set 14 (k 0))
                            (.ite
                              (Light.Cond.lt
                                ((Light.Expr.op Light.Op.add) (v 13) (k 1)) (v 6))
                              (.set 13
                                ((Light.Expr.op Light.Op.add) (v 13) (k 1)))
                              (Light.Stmt.seq (.set 13 (k 0))
                                (.set 12
                                  ((Light.Expr.op Light.Op.add) (v 12)
                                    (k 1)))))))))))
                (.set 0 (v 16)))))))))

def time (h J K NB NC g : ℕ) : ℕ :=
  total h J NB NC g*(LightSharedReportingPair.time h J K+1000)+300

def controlWord (h J K NB NC g : ℕ) : ℕ :=
  LightBlockSourceCatalog.count h J*BandPartition.size NB g+
  LightBlockSourceCatalog.count h J+BandPartition.size NB g+BandPartition.size NC g+J+K+512

def program : Program := LightSharedReportingPair.program ++ [body 65]


def Inv (μ : ℕ → ℤ) (fB fC : ℕ → ℤ) (p shift : ℤ)
    (header record base h J K NB NC g q : ℕ) (σ : State) : Prop :=
  ∃ (s i j : ℕ) (ν : ℕ → ℤ),
    σ=⟨frame [h,J,K,SourceBandBankData.first header,SourceBandBankLayout.span h J (2*h*J),
      LightBlockSourceCatalog.count h J,BandPartition.size NB g,BandPartition.size NC g,
      localChoose h,localPairs h,record,base,s,i,j,rowRecord record K q,rowBase base h J K q,
      total h J NB NC g,q],ν⟩ ∧
    q=rank (BandPartition.size NB g) (BandPartition.size NC g) s i j ∧
    s ≤ LightBlockSourceCatalog.count h J ∧ i ≤ BandPartition.size NB g ∧ j ≤ BandPartition.size NC g ∧
    (0 < total h J NB NC g → i < BandPartition.size NB g ∧ j < BandPartition.size NC g) ∧
    Done ν record base h J K NB NC g q fB fC p shift ∧ Kept μ ν record ∧
    KeptBut μ ν base record (5*K*total h J NB NC g)











































































































































end ThreeSum.LightSharedReportingBank

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankAccess


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources


/-! # Constant-time row addresses and original-output reporting interfaces -/

namespace ThreeSum.SharedReportingBankAccess

open Light GlobalEncoding BlockIndexedQuery OutputDecodeRecords
open SharedReportingBankRows SharedReportingBankHeader SharedReportingBankLevels
open SharedReportingBankData SharedReportingBankSources

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def slot (NB NC g s i j : ℕ) : ℕ :=
  rank (BandPartition.size NB g) (BandPartition.size NC g) s i j
def recordAt (free J NB NC g s i j : ℕ) : ℕ :=
  rowRecord (records free) (levels J) (slot NB NC g s i j)
def payloadAt (free h J NB NC g s i j : ℕ) : ℕ :=
  rowBase (payload free h J NB NC g) h J (levels J) (slot NB NC g s i j)
def levelCatalog (free h J NB NC g s i j k : ℕ) : ReportingHostLevelData.Catalog :=
  catalogAt (payloadAt free h J NB NC g s i j) h J k





































































































end ThreeSum.SharedReportingBankAccess

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Explicit finite resource envelopes for the executed shared reporting bank

The envelopes below include the entire header and metadata slab, every
compact payload and construction scratch region, all prefix/local counts,
packed keys, switch intermediates, and both independent source lengths.
They are derived from the actual finite host contract.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000

def prefixCount (h J : ℕ) : ℕ := 2^(2*((J+1)*(512*h)))
def prefixStorage (h J : ℕ) : ℕ := (levels J+1)*(prefixCount h J+1)
def cellBound (h J : ℕ) : ℕ :=
  2^(512*h)+2*2^(2*(512*h))+2*prefixStorage h J+3*prefixCount h J+
    prefixCount h J*(width h J+1)*2^(width h J)+2^(width h J)+2*(512*h)+3+
    (width h J+1)^2+(width h J+1)
def extent (h J n : ℕ) : ℕ :=
  9+(512*h+1)^2+LightBlockSourceCatalog.count h J*n*n*
    (5*levels J+levels J*cellBound h J)
def depth (h J : ℕ) : ℕ := 512*h+levels J+2*width h J+30
def control (h J n : ℕ) : ℕ :=
  LightBlockSourceCatalog.count h J*n+LightBlockSourceCatalog.count h J+n+n+J+levels J+512
def stateWord (h J : ℕ) : ℕ := J+levels J+512+prefixStorage h J+prefixCount h J
def word (h J n g : ℕ) : ℕ :=
  control h J n+SourceBandBankLayout.span h J (2*h*J)+2^(512*h+1)+2^(2*(512*h))+
    LightSwitchDepth.word J+stateWord h J+LightRadixKeys.word (2^(512*h)) (2^(512*h)) J+
    (width h J+1)*2^(width h J+1)+
    LightReportingSortedCatalog.word (width h J) (2^(2*width h J))+
    2^(width h J)*((2^(width h J)*g)*(2^(width h J)*g))+
    (J+2*h*J+1001)^64




































































































































































end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedDecision


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
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedPrefix
end ThreeSum.ReportingHostWantedPrefix
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts


/-!
# Exact whole-scan YES and NO for the original physical domain

Every emitted slot has its own original owner bands. Prefix threshold
crossings are sound by distinct physical labels; if no crossing occurs,
the terminal tests cover every original zero through an actual emitted slot.
-/

namespace ThreeSum.ReportingHostWantedDecision

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting GlobalEncoding
open ReportingHostWantedPhysical ReportingHostWantedOriginal ReportingHostWantedPrefix
open LightReportingWantedScan SharedTraversalCosts

set_option maxHeartbeats 2100000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)

def slotHit (fB fC : ℕ→ℤ) (NB NC K i : ℕ) : Prop :=
  if hi : i<(μ free).toNat then
    Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H ⟨i,hi⟩) K
  else False






















































end Actual

end ThreeSum.ReportingHostWantedDecision

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedPrefix


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
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts


/-!
# The exact dense counter of the physical ascending wanted scan

The finite physical labels are injective even when input values repeat.
The sum of the queried owner masses in any prefix is consequently the
mass of a distinct-label prefix in the complete original domain.
-/

namespace ThreeSum.ReportingHostWantedPrefix

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical ReportingHostWantedOriginal
open ReportingHostFrontierLayout SharedTraversalCosts

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)

def labels : List (Wanted h J (AType n g rs)) := List.ofFn (wantedAt H)












def slotMass (fB fC : ℕ→ℤ) (NB NC i : ℕ) : ℕ :=
  if hi : i<(μ free).toNat then
    rootMass (localItems h J n NB NC g P rs fA fB fC shift (wantedAt H ⟨i,hi⟩))
      (wantedAt H ⟨i,hi⟩)
  else 0








































end Actual

end ThreeSum.ReportingHostWantedPrefix

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorWantedSources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-! # Execute wanted records and shared original source banks consecutively -/

namespace ThreeSum.LightEncodedColorWantedSources

open Light Scales TrimScales BandScales

set_option maxHeartbeats 2500000
set_option maxRecDepth 13000

/-- h,J,cut,A-incidences,length,P,M,cover base,B value/header,C value/header,g. -/
def body (pWanted pSources : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pWanted [v 0, v 1, v 3, v 4, v 5, v 6, v 7] 13)
    (.call pSources [v 0, v 1, v 2, v 8, v 9, v 10, v 11, v 12, v 5, v 13, v 7] 0))

def joined : Program := ReportingHostRelocation.program LightGuardedWanted.program LightEncodedColorSources.program
def program : Program := joined ++ [body 98 179]



def args (a free bv be cv ce n p M len : ℕ) : List ℤ :=
  [microHalf (inputBits n),blockCount (inputBits n),mu n,a,len,p,M,free,bv,be,cv,ce,bandSize n]

def time (n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightGuardedWanted.time p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs+
    EncodedColorSourcesCosts.time n p U M+400

def space (free n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (LightGuardedWanted.space free p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs)
    (SourceFiniteCosts.space (LightEncodedColorFiniteSources.base free n p M xs) n p U M)

def word (n p M U len : ℕ) : ℕ :=
  max (LightGuardedWanted.word p M (microHalf (inputBits n)) (blockCount (inputBits n)) U len)
    (SourceFiniteCosts.word n p U M)

def depth (n M len : ℕ) : ℕ :=
  max (512*microHalf (inputBits n)+blockCount (inputBits n)+Nat.clog 2 M+3*len+13)
    (256*mu n+18)

variable {lim : Limits} {d : ℕ}













































































end ThreeSum.LightEncodedColorWantedSources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorPipelineData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # One retained selected-color payload, from original input to shared sources -/

namespace ThreeSum.EncodedColorPipelineData

open Light Scales BandScales ColorClassLists EncodedColorNormalizedData

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

def coverBase (free n : ℕ) : ℕ :=
  EncodedColorLayout.cover free n (bandSize n) (radix n) (primeWindow n)

def wantedHeader (free n len : ℕ) : ℕ :=
  LightGuardedWanted.wantedFree (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n)) len

def controls (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightEncodedColorFiniteSources.base (coverBase free n) n
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (radix n) (incidences n A B C hsA hsB hsC)

def bankHeader (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase (controls free n A B C hsA hsB hsC))
    B.length C.length (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n))

def finish (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightSourceControlsHost.finish (controls free n A B C hsA hsB hsC) B.length C.length (bandSize n)
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)

def values (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List ℤ :=
  LightEncodedColorResult.values (EncodedColorLayout.prime free n (bandSize n)) (coverBase free n)
    (wantedHeader free n (incidences n A B C hsA hsB hsC).length) (controls free n A B C hsA hsB hsC)
    (bankHeader free n A B C hsA hsB hsC) (finish free n A B C hsA hsB hsC)
    (incidences n A B C hsA hsB hsC).length (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)

structure Stored (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (A B C : List ℤ) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop where
  heads : Seg μ (finish free n A B C hsA hsB hsC) (values free n A B C hsA hsB hsC)
  normalizedHeads : Seg μ free (EncodedColorLayout.normalizedHeads free n (bandSize n))
  countCell : μ (EncodedColorLayout.normalizedEnd free n (bandSize n))=
    ((incidences n A B C hsA hsB hsC).length : ℤ)
  normalized : SourceFiniteData.Normalized μ
    (EncodedColorLayout.av free n) (EncodedColorLayout.ae free n)
    (EncodedColorLayout.bv free n) (EncodedColorLayout.be free n)
    (EncodedColorLayout.cv free n) (EncodedColorLayout.ce free n)
    (EncodedColorLayout.tables free n) (EncodedColorLayout.rec free n (bandSize n))
    (EncodedColorLayout.vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
    (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
    A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ)
  primes : EncodedColorPrimeData.Stored μ (EncodedColorLayout.prime free n (bandSize n))
    (radix n) (primeWindow n) (EncodedColorPrimeReadyData.moduli n A B C hsA hsB hsC)
  cover : LightCoverKeyData.Stored μ (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n))
  wanted : LightWantedSetup.Output μ (wantedHeader free n (incidences n A B C hsA hsB hsC).length) (radix n)
    (LightGuardedWanted.left (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (incidences n A B C hsA hsB hsC))
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n)))
  sources : SourceFiniteData.Stored μ (controls free n A B C hsA hsB hsC) (bandSize n)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) B C
    (RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
    (finish free n A B C hsA hsB hsC : ℤ)
  countBound : radix n*(μ (wantedHeader free n (incidences n A B C hsA hsB hsC).length)).toNat ≤
    3*(incidences n A B C hsA hsB hsC).length*
      LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n))
  lifts : Seg μ (LightCoverKeyData.keyEnd (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.keys (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (incidences n A B C hsA hsB hsC))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    r=(finish free n A B C hsA hsB hsC : ℤ) ∧ Stored μ free n color x A B C hsA hsB hsC




























end ThreeSum.EncodedColorPipelineData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumColorBudgets


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales


/-!
# Actual encoding-output masses fit the uniform reporting budgets

Both inequalities come from the retained pipeline payload. The wanted
count includes all physical A occurrences and all three lifts; the false
score uses the very common modulus selected from the original normalized
arrays. No input-dependent counting or prime-quality premise is assumed.
The explicit numerical divisor premise is discharged eventually, uniformly
before the input arrays are quantified.
-/

namespace ThreeSum.ThreeSumColorBudgets

open Light Scales BandScales CostLedger GlobalEncoding LocalCoverBounds
open ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000


















variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}




















































def falseScore (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightDenseSetup.falseScore (LightPrimePool.prime (primeWindow n)) (LightPrimePool.size (primeWindow n))
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    A.length B.length C.length (bandSize n)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC)





































open Filter













end ThreeSum.ThreeSumColorBudgets

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingStoredStep


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
# One actual reporting level from persistent physical headers

The host reads the previously computed capacity and frontier count, the
packed next output row, and the shared five-cell catalog record. It invokes
the complete multi-parent expansion and writes the new physical header.
-/

namespace ThreeSum.LightReportingStoredStep

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout ReportingHostMasks

set_option maxHeartbeats 3500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def body (pStep : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 19 (M ((Light.Expr.op Light.Op.add) (v 8) (k 3))))
    (Light.Stmt.seq
      (.set 20
        ((Light.Expr.op Light.Op.add) (k 4)
          ((Light.Expr.op Light.Op.mul) (k 2) (v 19))))
      (Light.Stmt.seq
        (.set 21
          ((Light.Expr.op Light.Op.add) (v 8)
            ((Light.Expr.op Light.Op.mul)
              ((Light.Expr.op Light.Op.sub) (v 3) (k 1)) (v 20))))
        (Light.Stmt.seq
          (.set 22
            ((Light.Expr.op Light.Op.add) (v 8)
              ((Light.Expr.op Light.Op.mul) (v 3) (v 20))))
          (Light.Stmt.seq
            (.set 23
              (M
                ((Light.Expr.op Light.Op.sub)
                  ((Light.Expr.op Light.Op.add) (v 7) (v 3)) (k 1))))
            (Light.Stmt.seq
              (.set 24 (M ((Light.Expr.op Light.Op.add) (v 21) (k 1))))
              (Light.Stmt.seq
                (.set 25
                  ((Light.Expr.op Light.Op.add) (v 6)
                    ((Light.Expr.op Light.Op.mul) (k 5) (v 3))))
                (Light.Stmt.seq (.set 26 (M (v 25)))
                  (Light.Stmt.seq
                    (.set 27 (M ((Light.Expr.op Light.Op.add) (v 25) (k 1))))
                    (Light.Stmt.seq
                      (.set 28 (M ((Light.Expr.op Light.Op.add) (v 25) (k 2))))
                      (Light.Stmt.seq
                        (.set 29 (M ((Light.Expr.op Light.Op.add) (v 25) (k 3))))
                        (Light.Stmt.seq
                          (.set 30
                            (M ((Light.Expr.op Light.Op.add) (v 25) (k 4))))
                          (Light.Stmt.seq
                            (.set 31
                              ((Light.Expr.op Light.Op.mul)
                                ((Light.Expr.op Light.Op.sub) (v 2) (v 3))
                                (v 18)))
                            (Light.Stmt.seq
                              (.set 32 ((Light.Expr.op Light.Op.mul) (v 3) (v 1)))
                              (Light.Stmt.seq
                                (.set 33
                                  ((Light.Expr.op Light.Op.mul)
                                    ((Light.Expr.op Light.Op.sub) (v 2) (v 3))
                                    ((Light.Expr.op Light.Op.mul) (k 2) (v 1))))
                                (Light.Stmt.seq
                                  (.set 34
                                    ((Light.Expr.op Light.Op.mul) (v 3) (v 18)))
                                  (Light.Stmt.seq (.set 35 (M (v 21)))
                                    (Light.Stmt.seq
                                      (.call pStep
                                        [v 0, v 1, v 23, v 24, v 9, v 10, v 11,
                                          v 15, v 17, v 31, v 32, v 33, v 26, v 4,
                                          v 5, v 27, v 28, v 29, v 30, v 16, v 12,
                                          v 13, v 14, v 34,
                                          (Light.Expr.op Light.Op.add) (v 21)
                                            (k 4),
                                          (Light.Expr.op Light.Op.add)
                                            ((Light.Expr.op Light.Op.add) (v 21)
                                              (k 4))
                                            (v 19),
                                          v 35,
                                          (Light.Expr.op Light.Op.add) (v 22)
                                            (k 4),
                                          (Light.Expr.op Light.Op.add)
                                            ((Light.Expr.op Light.Op.add) (v 22)
                                              (k 4))
                                            (v 19)]
                                        36)
                                      (Light.Stmt.seq
                                        (.set 37
                                          ((Light.Expr.op Light.Op.sub) (v 24)
                                            (v 23)))
                                        (Light.Stmt.seq (.store (v 22) (v 36))
                                          (Light.Stmt.seq
                                            (.store
                                              ((Light.Expr.op Light.Op.add) (v 22)
                                                (k 1))
                                              (v 37))
                                            (.set 0 (v 36)))))))))))))))))))))))

def program : Program := LightReportingFrontierStep.program ++ [body 50]
def time (h J k t n : ℕ) : ℕ := LightReportingFrontierStep.time h J k t n+1000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
















































































































































































































end ThreeSum.LightReportingStoredStep

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingHost


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows


/-!
# Execute the shared reporting bank from retained source headers

The inclusive terminal level count and both local combinatorial counts
are computed by actual programs. Occurrence count, band counts, and the
source-bank first pointer and stride are loaded from their retained
headers. The nine-cell result header precedes all five-cell level records
and compact catalog payloads.
-/

namespace ThreeSum.LightSharedReportingHost

open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankRows
open SharedReportingBankHeader

set_option maxHeartbeats 3900000
set_option maxRecDepth 16000

/-- h,J,source controls header,source pair header,source bank header,free. -/
def body (pDepth pCounts pBank : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 2) (k 1))))
    (Light.Stmt.seq (.set 8 (M ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
      (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 3) (k 3))))
        (Light.Stmt.seq (.set 10 (M (v 4)))
          (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 4) (k 2))))
            (Light.Stmt.seq (.call pDepth [v 1] 6)
              (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 6) (k 1)))
                (Light.Stmt.seq
                  (.set 12 ((Light.Expr.op Light.Op.add) (v 5) (k 9)))
                  (Light.Stmt.seq
                    (.call pCounts
                      [v 0, (Light.Expr.op Light.Op.add) (v 5) (k 7), v 12] 13)
                    (Light.Stmt.seq
                      (.set 14 (M ((Light.Expr.op Light.Op.add) (v 5) (k 7))))
                      (Light.Stmt.seq
                        (.set 15
                          ((Light.Expr.op Light.Op.mul)
                            ((Light.Expr.op Light.Op.mul) (v 7) (v 8)) (v 9)))
                        (Light.Stmt.seq
                          (.set 16
                            ((Light.Expr.op Light.Op.add) (v 12)
                              ((Light.Expr.op Light.Op.mul)
                                ((Light.Expr.op Light.Op.mul) (k 5) (v 6))
                                (v 15))))
                          (Light.Stmt.seq
                            (.call pBank
                              [v 0, v 1, v 6, v 10, v 11, v 7, v 8, v 9, v 14,
                                v 13, v 12, v 16]
                              17)
                            (Light.Stmt.seq (.set 17 (v 17))
                              (Light.Stmt.seq (.store (v 5) (v 12))
                                (Light.Stmt.seq
                                  (.store
                                    ((Light.Expr.op Light.Op.add) (v 5) (k 1))
                                    (v 16))
                                  (Light.Stmt.seq
                                    (.store
                                      ((Light.Expr.op Light.Op.add) (v 5) (k 2))
                                      (v 6))
                                    (Light.Stmt.seq
                                      (.store
                                        ((Light.Expr.op Light.Op.add) (v 5) (k 3))
                                        (v 7))
                                      (Light.Stmt.seq
                                        (.store
                                          ((Light.Expr.op Light.Op.add) (v 5)
                                            (k 4))
                                          (v 8))
                                        (Light.Stmt.seq
                                          (.store
                                            ((Light.Expr.op Light.Op.add) (v 5)
                                              (k 5))
                                            (v 9))
                                          (Light.Stmt.seq
                                            (.store
                                              ((Light.Expr.op Light.Op.add) (v 5)
                                                (k 6))
                                              (v 17))
                                            (.set 0 (v 17)))))))))))))))))))))))

def depthPrefix : Program := LightSharedReportingBank.program ++
  LightSwitchDepth.program.map (ReportingHostRelocation.relocate LightSharedReportingBank.program.length)
def countMap : Program :=
  LightSharedReportingCounts.program.map (ReportingHostRelocation.relocate depthPrefix.length)
def program : Program := depthPrefix ++ countMap ++ [body 67 69 66]


def time (h J NB NC g : ℕ) : ℕ :=
  LightSwitchDepth.time J+LightSharedReportingCounts.time h+
    LightSharedReportingBank.time h J (levels J) NB NC g+3000
def space (free h J NB NC g : ℕ) : ℕ :=
  max (records free+LightPascal.tableSize (512*h)) (finish free h J NB NC g)

structure Resources (lim : Limits) (free h J NB NC g d : ℕ) : Prop where
  space : space free h J NB NC g ≤ lim.space
  control : (LightSharedReportingBank.controlWord h J (levels J) NB NC g : ℤ) ≤ lim.word
  span : (SourceBandBankLayout.span h J (2*h*J) : ℤ) ≤ lim.word
  powers : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word
  pairs : (localPairs h : ℤ) ≤ lim.word
  depthWord : (LightSwitchDepth.word J : ℤ) ≤ lim.word
  depth : d+512*h+4 ≤ lim.depth
  bank : ∀ q < total h J NB NC g,
    LightSharedReportingLevels.Resources lim
      (rowBase (payload free h J NB NC g) h J (levels J) q) h J (levels J) g g (d+3)














































































































































end ThreeSum.LightSharedReportingHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedAccess


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored


/-!
# Actual owner, independent sources and shared reporting-row access

A physical A incidence selects its owner and original value. The owner
selects both original bands, the decoded occurrence selects their retained
source families, and one constant-time lookup selects the shared catalog
row. The resulting twenty-cell record is ready for the guarded reporter.
-/

namespace ThreeSum.LightReportingWantedAccess

open Light BandRawA BandCandidateRows BlockSourceEncoding
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 3300000
set_option maxRecDepth 15000
set_option linter.unusedVariables false

def selection (n g : ℕ) (rs : List Record) (idx pair bank cover NB NC h J cut occ code : ℕ) : Pointers :=
  retained pair bank cover NB NC g h J cut occ
    (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c code

def catalog (n g : ℕ) (rs : List Record) (idx report J NB NC code : ℕ) : ℕ :=
  SharedReportingBankAccess.recordAt report J NB NC g code
    (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c

def record (f : ℕ→ℤ) (n g : ℕ) (rs : List Record)
    (idx pair bank cover NB NC h J cut occ code srcB srcC report : ℕ) : List ℤ :=
  LightReportingOwnerSelect.row f n g rs idx ++
    (catalog n g rs idx report J NB NC code : ℤ)::
      (ReportingHostSourceSelection.values (selection n g rs idx pair bank cover NB NC h J cut occ code)
        srcB srcC code J).map (fun t => (t : ℤ))

/-- Packed A values and owner labels, owner records, incidence, source pair,
source banks, cover, original B/C, occurrence code, J, reporting banks, dst. -/
def body (pOwner pSource pLookup : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pOwner [v 0, v 1, v 2, v 3, v 12] 13)
    (Light.Stmt.seq (.set 14 (M ((Light.Expr.op Light.Op.add) (v 12) (k 2))))
      (Light.Stmt.seq (.set 15 (M ((Light.Expr.op Light.Op.add) (v 12) (k 3))))
        (Light.Stmt.seq (.set 16 ((Light.Expr.op Light.Op.add) (v 12) (k 5)))
          (Light.Stmt.seq
            (.call pSource [v 4, v 5, v 6, v 7, v 8, v 14, v 15, v 9, v 10, v 16]
              17)
            (Light.Stmt.seq (.call pLookup [v 11, v 9, v 14, v 15] 18)
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 12) (k 4)) (v 18))
                (.set 0 (v 12)))))))))

def initialLibraries : Program := ReportingHostRelocation.program
  LightReportingOwnerSelect.program LightReportingSourceSelect.program
def libraries : Program := ReportingHostRelocation.program initialLibraries LightSharedReportingLookup.program
def program : Program := libraries ++ [body 0 1 2]



































































































































end ThreeSum.LightReportingWantedAccess

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def magnitude (n : ℕ) : ℕ := 2^(2048*(inputBits n+1))
def polynomialPart (n : ℕ) : ℕ := 5000*(magnitude n+1)^5*(n+1)^2
def envelope (n : ℕ) : ℕ := polynomialPart n+(magnitude n)^64
def scaledWord (n : ℕ) : ℕ := word (half n) (blocks n) n (BandScales.bandSize n)
def scaledExtent (n : ℕ) : ℕ := extent (half n) (blocks n) n
def scaledDepth (n : ℕ) : ℕ := depth (half n) (blocks n)

structure Components (n : ℕ) : Prop where
  positive : 1 ≤ magnitude n
  localWidthBound : 512*half n+1 ≤ magnitude n
  blocksBound : blocks n+1 ≤ magnitude n
  levelsBound : levels (blocks n)+1 ≤ magnitude n
  widthBound : width (half n) (blocks n)+1 ≤ magnitude n
  prefixBound : prefixCount (half n) (blocks n) ≤ magnitude n
  localPower : 2^(512*half n+1) ≤ magnitude n
  pairsPower : 2^(2*(512*half n)) ≤ magnitude n
  widthPower : 2^(width (half n) (blocks n)+1) ≤ magnitude n
  indexPower : 2^(2*width (half n) (blocks n)) ≤ magnitude n
  occurrence : LightBlockSourceCatalog.count (half n) (blocks n) ≤ magnitude n
  prime : LocalCoverBounds.localPrime (half n) ≤ magnitude n
  primePower : LocalCoverBounds.localPrime (half n)^(blocks n)*LocalCoverBounds.localPrime (half n) ≤ magnitude n
  radixPower : (2^(512*half n)+1)^(blocks n) ≤ magnitude n
  switchBase : blocks n+2*half n*blocks n+1001 ≤ magnitude n
  depthWord : LightSwitchDepth.word (blocks n) ≤ magnitude n





























































































































































































































































end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorStageCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # Uniform budgets for wanted records followed by the shared source banks -/

namespace ThreeSum.EncodedColorStageCosts

open Scales BandScales ArithmeticStageBounds

def incidenceCap (n : ℕ) : ℕ := bandSize n*ColorBandBounds.count n (bandSize n)

def sourceBase (free n M len : ℕ) : ℕ :=
  EncodedColorWantedCosts.sourceBase free M (microHalf (inputBits n)) (blockCount (inputBits n)) len

def time (n P M U len : ℕ) : ℕ :=
  EncodedColorWantedCosts.time P M (microHalf (inputBits n)) (blockCount (inputBits n)) U len+
    EncodedColorSourcesCosts.time n P U M+400

def space (free n P M U len : ℕ) : ℕ :=
  max (EncodedColorWantedCosts.space free P M (microHalf (inputBits n)) (blockCount (inputBits n)) U len)
    (SourceFiniteCosts.space (sourceBase free n M len) n P U M)

def word (n P M U len : ℕ) : ℕ :=
  LightEncodedColorWantedSources.word n P M U len

def depth (n M len : ℕ) : ℕ := LightEncodedColorWantedSources.depth n M len


































































end ThreeSum.EncodedColorStageCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumReportingSetupData


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


/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData

open Light Scales BandScales EncodedColorNormalizedData

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

def reportBase (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8

def counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  SharedReportingBankHeader.finish (reportBase free n A B C hsA hsB hsC)
    (microHalf (inputBits n)) (blockCount (inputBits n)) B.length C.length (bandSize n)

def shift (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℤ :=
  RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n))

def Catalog (μ : ℕ → ℤ) (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop :=
  SharedReportingBankHeader.Stored μ (reportBase free n A B C hsA hsB hsC)
    (microHalf (inputBits n)) (blockCount (inputBits n)) B.length C.length (bandSize n)
    (fun j => B.getD j 0) (fun j => C.getD j 0)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (shift n A B C hsA hsB hsC)

structure Stored (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1))
    (x : Fin n → ℤ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop where
  encoded : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC
  catalog : Catalog μ free n A B C hsA hsB hsC
  dense : LightDenseSetup.Stored μ (counter free n A B C hsA hsB hsC)
    (GlobalEncoding.representationCap (microHalf (inputBits n)) (blockCount (inputBits n)))
    (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC)




































end ThreeSum.ThreeSumReportingSetupData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingLevels


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
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
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
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual bounded sequence of reporting levels

The recursive host executes only the requested number of levels, loading
all catalogs from persistent records. Its exact cost is the sum of the
actual level costs, with no multiplication by a worst-level query bound.
-/

namespace ThreeSum.LightReportingLevels

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix LightReportingPrefixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def body (pSelf pStep : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 3)))
    ((Light.Stmt.seq
       (.call pSelf
         [v 0, v 1, v 2, (Light.Expr.op Light.Op.sub) (v 3) (k 1), v 4, v 5, v 6,
           v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18]
         19)
       (.call pStep
         [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
           v 14, v 15, v 16, v 17, v 18]
         0)))
    (.set 0 (M (v 8)))

def program : Program := LightReportingStoredStep.program ++ [body 52 51]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (D : ℕ→Catalog) : ℕ→ℕ
  | 0 => 30
  | k+1 => time I w D k+
    LightReportingStoredStep.time h J k (D (k+1)).t (ReportingHostFrontier.frontier I w k).length+200

variable {lim : Limits}











































































































end ThreeSum.LightReportingLevels

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumReportingSetupBank


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


/-! # Run shared reporting precomputation from the encoded color header -/

namespace ThreeSum.LightThreeSumReportingSetupBank

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 2100000
set_option maxRecDepth 14000



/-- Input length, parameter header, normalized header, encoded result header. -/
def body (pBank : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 4 (M ((Light.Expr.op Light.Op.add) (v 1) (k 1))))
    (Light.Stmt.seq (.set 5 (M ((Light.Expr.op Light.Op.add) (v 1) (k 3))))
      (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 3) (k 3))))
        (Light.Stmt.seq (.set 7 ((Light.Expr.op Light.Op.add) (v 6) (k 3)))
          (Light.Stmt.seq (.set 8 (M ((Light.Expr.op Light.Op.add) (v 3) (k 4))))
            (Light.Stmt.seq
              (.set 9 (M ((Light.Expr.op Light.Op.add) (v 3) (k 5))))
              (.call pBank [v 4, v 5, v 6, v 7, v 8, v 9] 0)))))))

def program : Program := LightSharedReportingHost.program++[body 74]



def time (n : ℕ) : ℕ := SharedReportingBankCosts.budget n+400

















































































end ThreeSum.LightThreeSumReportingSetupBank

end


