-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle17
-- name    : ThreeSum1962Source_Bundle17
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:29:05.208743+00:00
-- url     : https://prove2.me/theorems/5d1c627a-7470-4ba1-9567-d86128aa0d5e
-- title:
--   Wanted-slot dispatch, composed color pipelines, and machine resource budgets
-- statement:
--   This bundle defines wanted-slot configurations and the program calls for layout construction, decoding, source selection, and guarded reporting. It composes the selected-color pipeline with shared reporting setup and assigns word, space, and depth requirements to parameter initialization, preprocessing, dense counters, scans, and drivers. For natural input size $n$, set $M=2^{2048(\operatorname{log2}(n)+1)}$, with $\operatorname{log2}(0)=0$. The defined query and wanted envelopes are
--   $$E_{\mathrm{query}}=100(M+1)^6,\qquad E_{\mathrm{wanted}}=10000(M+1)^{10}.$$
--   Additional cost functions specify preprocessing, per-color work, and the hybrid branch selected by size and input-magnitude guards.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorPipelineResources.lean#L65-L68
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorPipelineTime.lean#L24-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorReportingCosts.lean#L16-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorReportingData.lean#L21-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorReportingResources.lean#L13-L16
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/EncodedColorResourceScale.lean#L15-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawAResourcesScales.lean#L14-L15
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorPipeline.lean#L18-L70
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorReportingPipeline.lean#L20-L33
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWanted.lean#L25-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedDecodeAccess.lean#L22-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedDispatch.lean#L18-L75
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedRecordCall.lean#L21-L73
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedSearch.lean#L25-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightThreeSumReportingSetup.lean#L19-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedControls.lean#L10-L61
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostWantedRecordData.lean#L24-L33
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsDense.lean#L117-L125
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsDenseScales.lean#L12-L15
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsPolynomial.lean#L66-L66
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsQueryScales.lean#L12-L12
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsWantedScales.lean#L13-L16
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankResourceBoundsWantedScan.lean#L16-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedTraversalScanCosts.lean#L22-L87
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L19-L70
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumFastResources.lean#L20-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumHybridCosts.lean#L22-L31
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumParameterResources.lean#L17-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumParameterResourcesTime.lean#L18-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumReportingSetupResources.lean#L13-L16

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedDecodeAccess


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
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightReportingWantedAccess
end ThreeSum.LightReportingWantedAccess
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection


/-!
# Decode and select one physical wanted slot

The actual emitted pair is decoded before selecting the physical A owner,
both original bands, the retained occurrence sources and the shared catalog
row. The original decoded Q rows survive the selection for mask packing.
-/

namespace ThreeSum.LightReportingWantedDecodeAccess

open Light BandRawA BandCandidateRows BlockSourceEncoding GlobalEncoding
open OutputDecodeRecords
open ReportingHostSourceSelection LightReportingWantedAccess

set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
set_option linter.unusedVariables false

def body (pDecode pAccess : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDecode [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8] 19)
    (Light.Stmt.seq (.set 20 (M (v 7)))
      (.call pAccess
        [v 9, v 10, v 11, v 20, v 12, v 13, v 14, v 15, v 16, v 19, v 3, v 17,
          v 18]
        0)))

def libraries : Program := ReportingHostRelocation.program
  LightWantedDecode.program LightReportingWantedAccess.program
def program : Program := libraries ++ [body 4 8]
def time (J V : ℕ) : ℕ := LightWantedDecode.time J V+8300






















































































































































end ThreeSum.LightReportingWantedDecodeAccess

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedControls


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
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout


/-! # Typed contents of the executed wanted access and scratch records -/

namespace ThreeSum.ReportingHostWantedControls

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostWantedLayout

structure Selection where
  av : ℤ
  owner : ℕ
  bandB : ℕ
  bandC : ℕ
  catalog : ℕ
  srcL : ℕ
  srcR : ℕ
  offsetsL : ℕ
  flatL : ℕ
  offsetsR : ℕ
  flatR : ℕ
  NL : ℕ
  NR : ℕ
  baseL : ℕ
  baseR : ℕ
  occ : ℕ
  maps : ℕ
  candidates : ℕ
  histL : ℕ
  histR : ℕ

def record (S : Selection) : List ℤ :=
  [S.av,S.owner,S.bandB,S.bandC,S.catalog,S.srcL,S.srcR,S.offsetsL,S.flatL,S.offsetsR,S.flatR,
    S.NL,S.NR,S.baseL,S.baseR,S.occ,S.maps,S.candidates,S.histL,S.histR]



def ofAccess (f : ℕ→ℤ) (n g : ℕ) (rs : List BandCandidateRows.Record)
    (idx pair bank cover NB NC h J cut occ code srcB srcC report : ℕ) : Selection :=
  let X := LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code
  ⟨f (BandRawA.labelAt n g rs idx).position,(BandRawA.labelAt n g rs idx).owner,
    (BandRawA.ownerRecord n g rs idx).b,(BandRawA.ownerRecord n g rs idx).c,
    LightReportingWantedAccess.catalog n g rs idx report J NB NC code,
    srcB+X.startL,srcC+X.startR,X.offsetsL,X.flatL,X.offsetsR,X.flatR,X.sizeL,X.sizeR,
    X.stagesL,X.stagesR,ReportingHostSourceSelection.occurrenceRow X code J,
    X.maps,X.candidates,X.histL,X.histR⟩






def rawRows (layoutHeader J : ℕ) : ℕ := decoded layoutHeader+4+J

def arguments (S : Selection) (L : Layout) (layoutHeader cover counter h J K : ℕ) : List ℤ :=
  [S.av,S.srcL,S.srcR,S.offsetsL,S.flatL,S.offsetsR,S.flatR,S.NL,S.NR,
    BlockSourceEncoding.modulus h J,J,512*h,h,localPrime h,localBucketCap h,
    S.occ,S.maps,S.candidates,S.histL,S.histR,K,L.root,S.catalog,packed layoutHeader J,
    S.baseL,S.baseR,L.masks,L.childL,L.childR,L.counts,L.selected,L.maskBase,L.work,
    0,sourceCut h J,L.terminalMasks,L.masksL,L.masksR,L.base,L.bitBase,L.rowOut,
    rawRows layoutHeader J,cover,counter]













end ThreeSum.ReportingHostWantedControls

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorResourceScale


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def width (n : ℕ) : ℕ := blocks n*(512*half n)
def localEnvelope (n : ℕ) : ℕ := LightLocalCoverInitResources.envelope (half n)
def scale (n : ℕ) : ℕ := SharedReportingBankResourceBounds.magnitude n+localEnvelope n+
  maxMod n+primeWindow n+n+100

































































































noncomputable section


















end
end ThreeSum.EncodedColorResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandRawAResourcesScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Proved polynomial limits for original-input band and incidence preprocessing -/

namespace ThreeSum.LightBandRawAResources

open Light Scales BandScales StageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def base (n : ℕ) : ℕ := (SharedReportingBankResourceBounds.magnitude n+1)*(n+1)^2
def envelope (n : ℕ) : ℕ := 1000*base n

































































noncomputable section























end
end ThreeSum.LightBandRawAResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsDense


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # Exact finite resources for constructing the dense-stop counter

The power-loop bound includes its actual `(base+1)^(J+1)` intermediate.
The modular scoring workspace remains affine in an arbitrary destination.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales ArithmeticStageBounds GlobalEncoding LocalCoverBounds
open KaratsubaInterface

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000




































































































/-- Exactly the word reservation of the physical twenty-one-procedure setup. -/
def denseWord (n U : ℕ) : ℕ :=
  LightDenseSetup.word (maxMod n) n n n (bandSize n) (ColorBandBounds.count n (bandSize n))
    (LightPrimePool.size (primeWindow n)) U (half n) (blocks n)+
    n+bandSize n+blocks n+ColorBandBounds.count n (bandSize n)+maxMod n+
    LightPrimePool.size (primeWindow n)+20

def denseCells (n U : ℕ) : ℕ := 4+LightWeightedScore.space 0 (maxMod n) (bandSize n) U
def denseDepth (n : ℕ) : ℕ := Nat.clog 2 (maxMod n)+8














































end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsPolynomial


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales StageBounds Filter Light
open scoped Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section














































def need (n _U : ℕ) : Light.Need := ⟨scaledWord n,scaledExtent n,scaledDepth n⟩













end
end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsQueryScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Polynomial resources for every wanted query into the shared bank -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light StageBounds SharedReportingBankLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

def queryEnvelope (n : ℕ) : ℕ := 100*(magnitude n+1)^6










































































noncomputable section











































end
end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsWantedScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000

def wantedEnvelope (n : ℕ) : ℕ := 10000*(magnitude n+1)^10

def wantedNeed (n U : ℕ) : Light.Need :=
  ⟨wantedEnvelope n*(U+1),wantedEnvelope n,wantedEnvelope n⟩















































































































































noncomputable section









































end
end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorPipeline


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
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


/-! # Execute one original color through the retained shared source bank -/

namespace ThreeSum.LightEncodedColorPipeline

open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout
open EncodedColorNormalizedData

set_option maxHeartbeats 4200000
set_option maxRecDepth 17000



/-- Original array, length, parameter header, selected color row, free address. -/
def body (pPrime pSources pHeader pResult : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pPrime [v 0, v 1, v 2, v 3, v 4] 5)
    (Light.Stmt.seq (.set 6 (M (v 5)))
      (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 5) (k 2))))
        (Light.Stmt.seq (.set 8 (M ((Light.Expr.op Light.Op.sub) (v 5) (k 1))))
          (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 4) (k 7))))
            (Light.Stmt.seq
              (.set 10 (M ((Light.Expr.op Light.Op.add) (v 4) (k 2))))
              (Light.Stmt.seq
                (.set 11 (M ((Light.Expr.op Light.Op.add) (v 4) (k 3))))
                (Light.Stmt.seq
                  (.set 12 (M ((Light.Expr.op Light.Op.add) (v 4) (k 4))))
                  (Light.Stmt.seq
                    (.set 13 (M ((Light.Expr.op Light.Op.add) (v 4) (k 5))))
                    (Light.Stmt.seq
                      (.set 14 (M ((Light.Expr.op Light.Op.add) (v 2) (k 1))))
                      (Light.Stmt.seq
                        (.set 15 (M ((Light.Expr.op Light.Op.add) (v 2) (k 3))))
                        (Light.Stmt.seq
                          (.set 16 (M ((Light.Expr.op Light.Op.add) (v 2) (k 4))))
                          (Light.Stmt.seq
                            (.set 17
                              (M ((Light.Expr.op Light.Op.add) (v 2) (k 14))))
                            (Light.Stmt.seq
                              (.set 18
                                (M ((Light.Expr.op Light.Op.add) (v 2) (k 17))))
                              (Light.Stmt.seq
                                (.call pSources
                                  [v 14, v 15, v 16, v 9, v 8, v 6, v 17, v 7,
                                    v 10, v 11, v 12, v 13, v 18]
                                  19)
                                (Light.Stmt.seq
                                  (.call pHeader [v 7, v 15, v 8] 20)
                                  (Light.Stmt.seq
                                    (.set 21
                                      (M
                                        ((Light.Expr.op Light.Op.add) (v 20)
                                          (k 2))))
                                    (Light.Stmt.seq
                                      (.set 22
                                        (M
                                          ((Light.Expr.op Light.Op.add) (v 21)
                                            (k 8))))
                                      (Light.Stmt.seq
                                        (.set 23
                                          (M
                                            ((Light.Expr.op Light.Op.add) (v 21)
                                              (k 1))))
                                        (Light.Stmt.seq
                                          (.set 24
                                            ((Light.Expr.op Light.Op.add) (v 22)
                                              ((Light.Expr.op Light.Op.mul) (v 23)
                                                (v 15))))
                                          (.call pResult
                                            [v 5, v 7, v 20, v 21, v 24, v 19,
                                              v 8, v 6]
                                            0)))))))))))))))))))))

def joined : Program := ReportingHostRelocation.program
  LightEncodedColorPrimeHost.program LightEncodedColorWantedSources.program

def program : Program := joined ++
  [LightEncodedColorWantedHeader.body,LightEncodedColorResult.body,body 71 252 253 254]



def sourceBound (free n : ℕ) : ℕ := EncodedColorStageCosts.sourceBase
  (EncodedColorPipelineData.coverBase free n) n (radix n) (EncodedColorStageCosts.incidenceCap n)

def finishBound (free n : ℕ) : ℕ := SourceFiniteCosts.finish (sourceBound free n) n

def time (n U : ℕ) : ℕ := LightEncodedColorPrimeHost.inputTime n U+
  EncodedColorStageCosts.time n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n)+
  LightEncodedColorWantedHeader.time (blockCount (inputBits n))+1600

def space (free n U : ℕ) : ℕ := max (LightEncodedColorPrimeHost.inputSpace free n U)
  (max (EncodedColorStageCosts.space (EncodedColorPipelineData.coverBase free n) n (maxMod n)
    (radix n) U (EncodedColorStageCosts.incidenceCap n)) (finishBound free n+8))

def word (n U : ℕ) : ℕ := max (LightEncodedColorPrimeHost.inputWord n U)
  (EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n))+
    EncodedColorStageCosts.incidenceCap n+maxMod n+radix n+bandSize n+
    microHalf (inputBits n)+blockCount (inputBits n)+mu n+
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))+100

def depth (n : ℕ) : ℕ := max (LightEncodedColorPrimeHost.depth n)
  (EncodedColorStageCosts.depth n (radix n) (EncodedColorStageCosts.incidenceCap n))+1

variable {lim : Limits} {d : ℕ}













































































































































































































end ThreeSum.LightEncodedColorPipeline

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorReportingData


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


/-!
# The original source header after shared reporting and dense initialization

The prelude returns the source header unchanged. The reporting header starts
eight cells later, and its field six contains the initialized dense counter.
All contracts retain the same normalized A, B and C witnesses.
-/

namespace ThreeSum.EncodedColorReportingData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000



def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1))
    (x : Fin n → ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    r=(EncodedColorPipelineData.finish free n A B C hsA hsB hsC : ℤ) ∧
      ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC






















































end ThreeSum.EncodedColorReportingData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedSearch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
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
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Executed partial-depth traversal followed by terminal reporting

This is the expensive branch of a wanted-record query. Its caller executes
the cumulative root-mass guard first. Catalogs and sources remain persistent;
the branch walks the prescribed levels, reads the retained terminal slot,
and tests its exact original physical bucket products.
-/

namespace ThreeSum.LightReportingWantedSearch

open Light Finset BlockRows BlockIndex BlockMaskLayout BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostLevelData ReportingHostFrontierLayout
open RawIncidences RawReporting

set_option maxHeartbeats 4400000
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

/-- Original terminal controls (20), requested depth and root, the shared
catalog/packed-row/source pointers, level scratch, group and cut, terminal
scratch, and work. -/
def body (pLevels pTerminal : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 41 ((Light.Expr.op Light.Op.mul) (v 10) (v 11)))
    (Light.Stmt.seq
      (.call pLevels
        [v 41, v 12, v 10, v 20, v 24, v 25, v 22, v 23, v 21, v 26, v 27, v 28,
          v 29, v 30, v 31, v 32, v 33, v 34, v 11]
        42)
      (.call pTerminal
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
          v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 35, v 36, v 37, v 38,
          v 39, v 40, v 32]
        0)))

def libraries : Program := ReportingHostRelocation.program
  LightReportingLevels.program LightReportingTerminalStored.program
def program : Program := libraries ++ [body 52 93]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (D : ℕ→Catalog) (K : ℕ) : ℕ :=
  LightReportingLevels.time I w D K+LightReportingTerminalStored.time p shift left right NL NR I w K+500








































































































end ThreeSum.LightReportingWantedSearch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightThreeSumReportingSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData


/-!
# Execute both reporting preparations from the original encoded-color payload

The shared catalog bank is constructed once. Its returned free pointer is
passed directly to dense initialization, which reads the original arrays,
actual candidate records, selected modulus and prime pool from memory.
-/

namespace ThreeSum.LightThreeSumReportingSetup

open Light Scales BandScales ArithmeticStageBounds ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

def body (pBank pDense : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pBank [v 0, v 1, v 2, v 3] 4)
    (.call pDense [v 0, v 1, v 2, v 3, v 4] 0))

def joined : Program := ReportingHostRelocation.program
  LightThreeSumReportingSetupBank.program LightThreeSumReportingSetupDense.program

def program : Program := joined++[body 75 96]



def time (n U R : ℕ) : ℕ := LightThreeSumReportingSetupBank.time n+
  LightThreeSumReportingSetupDense.time n U R+200



























































end ThreeSum.LightThreeSumReportingSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostWantedRecordData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal


/-!
# Original-domain facts carried by the two actual wanted records

All source stages, buckets, occurrence rows, and per-level catalogs below
come from the retained concrete constructors. The decoder supplies the
unaltered original Q masks used by the guarded reporter.
-/

namespace ThreeSum.ReportingHostWantedRecordData

open Light Finset BandRawA BandCandidateRows GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting BlockEncoding BlockForced BlockMaskLayout BlockCoefficientRows
open ReportingHostWantedOriginal ReportingHostWantedControls ReportingHostWantedLayout
open ReportingHostSourceSelectionStored OutputDecodeRecords

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

def selected (fA : ℕ→ℤ) (n NB NC g pair bank cover h J occ srcB srcC report : ℕ)
    (rs : List Record) (w : Wanted h J (AType n g rs)) (output : ℕ) : Selection :=
  ofAccess fA n g rs w.1.val pair bank cover NB NC h J (LightBlockQuery.sourceCut h J) occ
    (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output) srcB srcC report

def catalogs (n NB NC g report h J : ℕ) (rs : List Record)
    (w : Wanted h J (AType n g rs)) (output k : ℕ) : ReportingHostLevelData.Catalog :=
  SharedReportingBankAccess.levelCatalog report h J NB NC g
    (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)
    (ownerRecord n g rs w.1.val).b (ownerRecord n g rs w.1.val).c k






















section Stored

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
  {n NB NC g pair bank cover h J p occ srcB srcC report output : ℕ}
  {rs : List Record} {shift : ℤ} (w : Wanted h J (AType n g rs))



















































































end Stored


















end ThreeSum.ReportingHostWantedRecordData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumParameterResources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Exact polynomial resources for the executed parameter initializer

The nineteen-cell output starts at an arbitrary destination. Scratch begins
immediately after that header; its reservation is translated only once.
-/

namespace ThreeSum.ThreeSumParameterResources

open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 14000

def work (dst : ℕ) : ℕ := dst+19
def cells (n : ℕ) : ℕ := 19+LightParameterInit.space 0 n
def depth (n : ℕ) : ℕ := 512*LightParameterInit.half n+6
def envelope (n : ℕ) : ℕ := 20000*scale n
def need (n _U : ℕ) : Light.Need := ⟨LightParameterInit.word n,cells n,depth n⟩








































































noncomputable section











end
























end ThreeSum.ThreeSumParameterResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumParameterResourcesTime


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Charge the executed parameter initialization

The actual square-root and quotient loops are bounded by the band root and
divisor. Polynomial storage envelopes do not replace these time bounds.
-/

namespace ThreeSum.ThreeSumParameterResources

open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
open Filter Parameters ArithmeticStageBounds

set_option maxHeartbeats 1900000
set_option maxRecDepth 14000

def timeBudget (n : ℕ) : ℕ :=
  10000*(inputBits n+1+blocks n+mu n+bandRoot n+bandDivisor n+localEnvelope n)














noncomputable section


























end
end ThreeSum.ThreeSumParameterResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsDenseScales


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Polynomial limits for the exact dense initialization resources -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds ArithmeticStageBounds

set_option maxHeartbeats 1600000
set_option maxRecDepth 14000

def denseEnvelope (n : ℕ) : ℕ := 20000*(EncodedColorResources.scale n)^8

/-- Exact word, relative cell extent, and depth of the physical dense setup. -/
def denseNeed (n U : ℕ) : Light.Need := ⟨denseWord n U,denseCells n U,denseDepth n⟩

































noncomputable section













end

















end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankResourceBoundsWantedScan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Polynomial call depth for scanning every physical wanted record

The scan retains the exact word and cell reservations of one wanted
dispatcher. Only its depth includes the number of physical records.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds

set_option maxHeartbeats 1700000
set_option maxRecDepth 14000

def wantedScanCount (n : ℕ) : ℕ := 9*(magnitude n)^5

def wantedScanNeed (n U : ℕ) : Light.Need :=
  ⟨(wantedNeed n U).word,(wantedNeed n U).cells,(wantedNeed n U).depth+wantedScanCount n+4⟩



































noncomputable section


















end
end ThreeSum.SharedReportingBankResourceBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorPipelineResources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Polynomial Need for the exact closed selected-color pipeline -/

namespace ThreeSum.EncodedColorResources

open Light Scales BandScales ArithmeticStageBounds StageBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000





















































def need (n U : ℕ) : Light.Need :=
  ⟨LightEncodedColorPipeline.word n U,3000*(scale n)^5+U,LightEncodedColorPipeline.depth n⟩

def envelope (n : ℕ) : ℕ := 1000000*(scale n)^10





















noncomputable section











end
























end ThreeSum.EncodedColorResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorPipelineTime


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# The executed selected-color preprocessing fits the final time exponent

This charges the actual fixed256 program's complete time expression:
normalization and incidence construction, common-prime selection, local
cover and global keys, balanced wanted rows, shared source banks and the
retained result-header computation. Reporting and the outer color loop
remain separate composition obligations.
-/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def preprocessingTime (k n : ℕ) : ℕ := LightEncodedColorPipeline.time n (n^k)

noncomputable section














































end
end ThreeSum.EncodedColorTime

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorReportingCosts


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


/-! # Actual time of the source, shared reporting and dense prelude -/

namespace ThreeSum.EncodedColorReportingCosts

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open CostLedger
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def setupTime (n U : ℕ) : ℕ := LightThreeSumReportingSetupBank.time n+
  LightThreeSumReportingSetupDense.time n U (ColorBandBounds.count n (bandSize n))+200

def time (n U : ℕ) : ℕ := LightEncodedColorPipeline.time n U+setupTime n U+1000

def preprocessingTime (k n : ℕ) : ℕ := time n (n^k)















noncomputable section





































end
end ThreeSum.EncodedColorReportingCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWanted


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
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
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Complete guarded reporting for one actual wanted record

Decoded query masks are packed, the root mass is queried and added to the
running counter, and the actual comparison controls the expensive branch.
Only a zero guard result executes partial-depth traversal and terminal
original-value testing. Every source and catalog is retained and reused.
-/

namespace ThreeSum.LightReportingWanted

open Light Finset BlockRows BlockIndex BlockMaskLayout BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostLevelData ReportingHostFrontierLayout
open RawIncidences RawReporting

set_option maxHeartbeats 5000000
set_option maxRecDepth 18000
set_option linter.unusedSectionVars false

/-- The search controls, with a zero placeholder for the group count, then
decoded raw Q rows, retained cover, and the dense counter/header. -/
def body (pInit pSearch : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 44 ((Light.Expr.op Light.Op.mul) (v 10) (v 11)))
    (Light.Stmt.seq (.set 33 (M ((Light.Expr.op Light.Op.add) (v 42) (k 3))))
      (Light.Stmt.seq
        (.call pInit
          [v 44, v 34, v 10, v 11, v 24, v 25, v 22, v 41, v 23, v 42, v 43, v 21,
            v 31, v 32]
          45)
        (.ite (Light.Cond.lt (k 0) (v 45)) (.set 0 (k 1))
          (.call pSearch
            [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12,
              v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23,
              v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, v 34,
              v 35, v 36, v 37, v 38, v 39, v 40]
            0)))))

def libraries : Program := ReportingHostRelocation.program
  LightReportingWantedInitialize.program LightReportingWantedSearch.program
def program : Program := libraries ++ [body 41 136]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR old threshold : ℕ)
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (D : ℕ→Catalog) (K : ℕ) : ℕ :=
  LightReportingWantedInitialize.time h J (D 0).t+
    (if threshold<old+rootMass I w then 0 else LightReportingWantedSearch.time p shift left right NL NR I w D K)+700



































































































































































end ThreeSum.LightReportingWanted

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumColorDriverResources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# Affine resources for a color scan and its single parameter initialization

Per-color storage is reused after one six-cell color row. The full driver
uses nineteen persistent parameter cells and reclaims the initializer's
scratch before the scan. Both allocations have coefficient one on free.
-/

namespace ThreeSum.ThreeSumColorDriverResources

open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

def overhead (n _U : ℕ) : Need :=
  ⟨LightColorScanHost.word n,6,count (width n)+4⟩

def need (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  ⟨(colorNeed n U).word+(overhead n U).word,
    (colorNeed n U).cells+(overhead n U).cells,
    (colorNeed n U).depth+(overhead n U).depth⟩

def fullNeed (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  ⟨(ThreeSumParameterResources.need n U).word+(need colorNeed n U).word,
    max (ThreeSumParameterResources.need n U).cells (19+(need colorNeed n U).cells),
    (ThreeSumParameterResources.need n U).depth+(need colorNeed n U).depth+2⟩







































def overheadEnvelope (n : ℕ) : ℕ := 200*(n+1)^2











noncomputable section
























































end
end ThreeSum.ThreeSumColorDriverResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumReportingSetupResources


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


/-! # Compose the two actual reporting allocations at an arbitrary free pointer -/

namespace ThreeSum.ThreeSumReportingSetupResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def need (n U : ℕ) : Light.Need :=
  ⟨(SharedReportingBankResourceBounds.need n U).word+(SharedReportingBankResourceBounds.denseNeed n U).word,
    (SharedReportingBankResourceBounds.need n U).cells+(SharedReportingBankResourceBounds.denseNeed n U).cells,
    (SharedReportingBankResourceBounds.need n U).depth+(SharedReportingBankResourceBounds.denseNeed n U).depth+3⟩























noncomputable section























end
end ThreeSum.ThreeSumReportingSetupResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumFastResources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-! # Relative limits for the complete wanted-header loader and scan

All numeric controls come from the input size. The loader starts its reusable
scratch at `counter+4`; every retained absolute pointer is handled by its
individual allocation end rather than being included in a numeric envelope.
-/

namespace ThreeSum.ThreeSumFastResources

open Light Scales BandScales StageBounds SharedReportingBankResourceBounds

set_option maxHeartbeats 2100000
set_option maxRecDepth 15000

def headerWord (n : ℕ) : ℕ :=
  n+blocks n+half n+LightSwitchDepth.depth (blocks n)+bandSize n+radix n+
    OutputDecodeRecords.layerCount (half n)+GlobalEncoding.scheduleSize (half n)+
    ColorBandBounds.count n (bandSize n)+EncodedColorStageCosts.incidenceCap n+50

/-- Two outer call levels above the actual whole-wanted scan. -/
def need (n U : ℕ) : Light.Need :=
  ⟨(wantedScanNeed n U).word,(wantedScanNeed n U).cells,(wantedScanNeed n U).depth+2⟩







































































noncomputable section



















end
end ThreeSum.ThreeSumFastResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorReportingPipeline


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


/-!
# Original selected color through the shared reporting and dense prelude

The literal355-procedure program runs the existing source pipeline and then
the reporting setup. It returns the original source header; all normalized
lists and occurrence-shared catalogs are retained in the same payload.
-/

namespace ThreeSum.LightEncodedColorReportingPipeline

open Light Scales BandScales ThreeSumReportingSetupData EncodedColorNormalizedData

set_option maxHeartbeats 2600000
set_option maxRecDepth 17000

/-- Original array, length, parameter header, selected color row, free address. -/
def body (pSource pReporting : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSource [v 0, v 1, v 2, v 3, v 4] 5)
    (Light.Stmt.seq (.call pReporting [v 1, v 2, v 4, v 5] 6) (.set 0 (v 5))))

def joined : Program := ReportingHostRelocation.program
  LightEncodedColorPipeline.program LightThreeSumReportingSetup.program

def program : Program := joined++[body 255 353]



def time (n U : ℕ) : ℕ := EncodedColorReportingCosts.time n U




















































end ThreeSum.LightEncodedColorReportingPipeline

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedTraversalScanCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# Charge the actual fixed153 wanted scan and fixed154 header caller

The concrete dispatcher contributes4500 operations, and the ascending
recursion contributes300 per slot. The exact active-branch mass remains
inside the cumulative guard until the original reporting ledger is applied.
-/

namespace ThreeSum.SharedTraversalCosts

open Light Finset Scales BandScales GlobalEncoding RawIncidences RawReporting
open ReportingHostLevelData StageBounds CostLedger
open ReportingHostFrontierLayout Parameters

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def slotEnvelope (n threshold : ℕ) (mass : ℕ→ℕ) (i : ℕ) : ℕ :=
  scaledOverhead n*queryTerms n 0+scalarOverhead 4800 n+
    if threshold<prefixMass mass i+mass i then 0 else
      mass i*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n))

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

























































def colorBudget (k n : ℕ) : ℕ :=
  EncodedColorReportingCosts.time n (n^k)+dispatchBudget 4800 k n+5000











noncomputable section














end
end ThreeSum.SharedTraversalCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedRecordCall


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
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout


/-!
# Execute the guarded reporter from the two concrete packed records

This procedure loads the twenty-cell owner/source selection and fourteen
computed scratch pointers, reads the retained prime and trim cap, and
passes exactly the verified guarded reporter's forty-four arguments.
Its compositional law retains the supplied reporter postcondition unchanged.
-/

namespace ThreeSum.LightReportingWantedRecordCall

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostWantedLayout
open ReportingHostWantedControls

set_option maxHeartbeats 5500000
set_option maxRecDepth 24000
set_option linter.unusedVariables false

def body (pWanted : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 8 (M ((Light.Expr.op Light.Op.add) (v 0) (k 0))))
    (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 0) (k 1))))
      (Light.Stmt.seq (.set 10 (M ((Light.Expr.op Light.Op.add) (v 0) (k 2))))
        (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 0) (k 3))))
          (Light.Stmt.seq (.set 12 (M ((Light.Expr.op Light.Op.add) (v 0) (k 4))))
            (Light.Stmt.seq
              (.set 13 (M ((Light.Expr.op Light.Op.add) (v 0) (k 5))))
              (Light.Stmt.seq
                (.set 14 (M ((Light.Expr.op Light.Op.add) (v 0) (k 6))))
                (Light.Stmt.seq
                  (.set 15 (M ((Light.Expr.op Light.Op.add) (v 0) (k 7))))
                  (Light.Stmt.seq
                    (.set 16 (M ((Light.Expr.op Light.Op.add) (v 0) (k 8))))
                    (Light.Stmt.seq
                      (.set 17 (M ((Light.Expr.op Light.Op.add) (v 0) (k 9))))
                      (Light.Stmt.seq
                        (.set 18 (M ((Light.Expr.op Light.Op.add) (v 0) (k 10))))
                        (Light.Stmt.seq
                          (.set 19
                            (M ((Light.Expr.op Light.Op.add) (v 0) (k 11))))
                          (Light.Stmt.seq
                            (.set 20
                              (M ((Light.Expr.op Light.Op.add) (v 0) (k 12))))
                            (Light.Stmt.seq
                              (.set 21
                                (M ((Light.Expr.op Light.Op.add) (v 0) (k 13))))
                              (Light.Stmt.seq
                                (.set 22
                                  (M ((Light.Expr.op Light.Op.add) (v 0) (k 14))))
                                (Light.Stmt.seq
                                  (.set 23
                                    (M
                                      ((Light.Expr.op Light.Op.add) (v 0)
                                        (k 15))))
                                  (Light.Stmt.seq
                                    (.set 24
                                      (M
                                        ((Light.Expr.op Light.Op.add) (v 0)
                                          (k 16))))
                                    (Light.Stmt.seq
                                      (.set 25
                                        (M
                                          ((Light.Expr.op Light.Op.add) (v 0)
                                            (k 17))))
                                      (Light.Stmt.seq
                                        (.set 26
                                          (M
                                            ((Light.Expr.op Light.Op.add) (v 0)
                                              (k 18))))
                                        (Light.Stmt.seq
                                          (.set 27
                                            (M
                                              ((Light.Expr.op Light.Op.add) (v 0)
                                                (k 19))))
                                          (Light.Stmt.seq
                                            (.set 28
                                              (M
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 1) (k 0))))
                                            (Light.Stmt.seq
                                              (.set 29
                                                (M
                                                  ((Light.Expr.op Light.Op.add)
                                                    (v 1) (k 1))))
                                              (Light.Stmt.seq
                                                (.set 30
                                                  (M
                                                    ((Light.Expr.op Light.Op.add)
                                                      (v 1) (k 2))))
                                                (Light.Stmt.seq
                                                  (.set 31
                                                    (M
                                                      ((Light.Expr.op
                                                          Light.Op.add)
                                                        (v 1) (k 3))))
                                                  (Light.Stmt.seq
                                                    (.set 32
                                                      (M
                                                        ((Light.Expr.op
                                                            Light.Op.add)
                                                          (v 1) (k 4))))
                                                    (Light.Stmt.seq
                                                      (.set 33
                                                        (M
                                                          ((Light.Expr.op
                                                              Light.Op.add)
                                                            (v 1) (k 5))))
                                                      (Light.Stmt.seq
                                                        (.set 34
                                                          (M
                                                            ((Light.Expr.op
                                                                Light.Op.add)
                                                              (v 1) (k 6))))
                                                        (Light.Stmt.seq
                                                          (.set 35
                                                            (M
                                                              ((Light.Expr.op
                                                                  Light.Op.add)
                                                                (v 1) (k 7))))
                                                          (Light.Stmt.seq
                                                            (.set 36
                                                              (M
                                                                ((Light.Expr.op
                                                                    Light.Op.add)
                                                                  (v 1) (k 8))))
                                                            (Light.Stmt.seq
                                                              (.set 37
                                                                (M
                                                                  ((Light.Expr.op
                                                                      Light.Op.add)
                                                                    (v 1) (k 9))))
                                                              (Light.Stmt.seq
                                                                (.set 38
                                                                  (M
                                                                    ((Light.Expr.op
                                                                        Light.Op.add)
                                                                      (v 1)
                                                                      (k 10))))
                                                                (Light.Stmt.seq
                                                                  (.set 39
                                                                    (M
                                                                      ((Light.Expr.op
                                                                          Light.Op.add)
                                                                        (v 1)
                                                                        (k 11))))
                                                                  (Light.Stmt.seq
                                                                    (.set 40
                                                                      (M
                                                                        ((Light.Expr.op
                                                                            Light.Op.add)
                                                                          (v 1)
                                                                          (k
                                                                            12))))
                                                                    (Light.Stmt.seq
                                                                      (.set 41
                                                                        (M
                                                                          ((Light.Expr.op
                                                                              Light.Op.add)
                                                                            (v 1)
                                                                            (k
                                                                              13))))
                                                                      (Light.Stmt.seq
                                                                        (.set 42
                                                                          (M
                                                                            ((Light.Expr.op
                                                                                Light.Op.add)
                                                                              (v
                                                                                6)
                                                                              (k
                                                                                6))))
                                                                        (Light.Stmt.seq
                                                                          (.set 43
                                                                            (M
                                                                              ((Light.Expr.op
                                                                                  Light.Op.add)
                                                                                (v
                                                                                  6)
                                                                                (k
                                                                                  7))))
                                                                          (Light.Stmt.seq
                                                                            (.set
                                                                              44
                                                                              ((Light.Expr.op
                                                                                  Light.Op.mul)
                                                                                (k
                                                                                  512)
                                                                                (v
                                                                                  2)))
                                                                            (Light.Stmt.seq
                                                                              (.set
                                                                                45
                                                                                ((Light.Expr.op
                                                                                    Light.Op.mul)
                                                                                  (v
                                                                                    3)
                                                                                  ((Light.Expr.op
                                                                                      Light.Op.mul)
                                                                                    (k
                                                                                      2)
                                                                                    (v
                                                                                      2))))
                                                                              (Light.Stmt.seq
                                                                                (.set
                                                                                  46
                                                                                  ((Light.Expr.op
                                                                                      Light.Op.add)
                                                                                    ((Light.Expr.op
                                                                                        Light.Op.add)
                                                                                      (v
                                                                                        1)
                                                                                      (k
                                                                                        18))
                                                                                    (v
                                                                                      3)))
                                                                                (Light.Stmt.seq
                                                                                  (.set
                                                                                    47
                                                                                    ((Light.Expr.op
                                                                                        Light.Op.add)
                                                                                      ((Light.Expr.op
                                                                                          Light.Op.add)
                                                                                        (v
                                                                                          1)
                                                                                        (k
                                                                                          38))
                                                                                      ((Light.Expr.op
                                                                                          Light.Op.mul)
                                                                                        (k
                                                                                          2)
                                                                                        (v
                                                                                          3))))
                                                                                  (.call
                                                                                    pWanted
                                                                                    [v
                                                                                        8,
                                                                                      v
                                                                                        13,
                                                                                      v
                                                                                        14,
                                                                                      v
                                                                                        15,
                                                                                      v
                                                                                        16,
                                                                                      v
                                                                                        17,
                                                                                      v
                                                                                        18,
                                                                                      v
                                                                                        19,
                                                                                      v
                                                                                        20,
                                                                                      v
                                                                                        5,
                                                                                      v
                                                                                        3,
                                                                                      v
                                                                                        44,
                                                                                      v
                                                                                        2,
                                                                                      v
                                                                                        42,
                                                                                      v
                                                                                        43,
                                                                                      v
                                                                                        23,
                                                                                      v
                                                                                        24,
                                                                                      v
                                                                                        25,
                                                                                      v
                                                                                        26,
                                                                                      v
                                                                                        27,
                                                                                      v
                                                                                        4,
                                                                                      v
                                                                                        28,
                                                                                      v
                                                                                        12,
                                                                                      v
                                                                                        47,
                                                                                      v
                                                                                        21,
                                                                                      v
                                                                                        22,
                                                                                      v
                                                                                        29,
                                                                                      v
                                                                                        30,
                                                                                      v
                                                                                        31,
                                                                                      v
                                                                                        32,
                                                                                      v
                                                                                        33,
                                                                                      v
                                                                                        34,
                                                                                      v
                                                                                        41,
                                                                                      k
                                                                                        0,
                                                                                      v
                                                                                        45,
                                                                                      v
                                                                                        35,
                                                                                      v
                                                                                        36,
                                                                                      v
                                                                                        37,
                                                                                      v
                                                                                        38,
                                                                                      v
                                                                                        39,
                                                                                      v
                                                                                        40,
                                                                                      v
                                                                                        46,
                                                                                      v
                                                                                        6,
                                                                                      v
                                                                                        7]
                                                                                    0)))))))))))))))))))))))))))))))))))))))))

def program : Program := LightReportingWanted.program++[body 137]

def numericExtra (h J K : ℕ) : ℕ :=
  J+512*h+K+BlockSourceEncoding.modulus h J+sourceCut h J+
    localPrime h+localBucketCap h+1024

/-- Separate translated addresses from the size-only scalar envelope. -/
def space (selectionHeader layoutHeader cover counter h J K : ℕ) : ℕ :=
  max (max (selectionHeader+20) (layoutHeader+38+3*J))
    (max (max (cover+8) (counter+2)) (numericExtra h J K))


























































































































































































































































































end ThreeSum.LightReportingWantedRecordCall


end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_EncodedColorReportingResources


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


/-! # Affine resources for source construction followed by reporting setup -/

namespace ThreeSum.EncodedColorReportingResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def need (n U : ℕ) : Light.Need :=
  ⟨(EncodedColorResources.need n U).word+(ThreeSumReportingSetupResources.need n U).word,
    (EncodedColorResources.need n U).cells+(ThreeSumReportingSetupResources.need n U).cells,
    (EncodedColorResources.need n U).depth+(ThreeSumReportingSetupResources.need n U).depth+2⟩


























noncomputable section























end
end ThreeSum.EncodedColorReportingResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ThreeSumHybridCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds


/-!
# The exact hybrid cost along every fixed input-magnitude exponent

The exceptional-size and excessive-magnitude branches use the original
triple scan. Once the size reaches the fixed cutoff, every bound at most
n^κ selects the same fast cost. The scalar exponentiation and fixed caller
cost fit within the proved gap between the certificate and target exponents.
-/

namespace ThreeSum.ThreeSumHybridCosts

open Light Parameters StageBounds Filter

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def time (κ cutoff n U : ℕ) : ℕ :=
  if n<cutoff ∨ n^κ<U then
    LightBruteThreeSum.time n+LightNatPower.time κ+1000
  else
    LightThreeSumFastDriver.time (SharedTraversalCosts.colorBudget κ n) n+
      LightNatPower.time κ+1000

def fastTime (κ n : ℕ) : ℕ :=
  LightThreeSumFastDriver.time (SharedTraversalCosts.colorBudget κ n) n+
    LightNatPower.time κ+1000





noncomputable section
































































end
end ThreeSum.ThreeSumHybridCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingWantedDispatch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout


/-!
# Execute one physical wanted slot from the reusable retained controls

The actual pointer constructor runs first. Its returned work pointer feeds
the actual wanted decoder and owner/source/catalog selector. The concrete
two-record loader then invokes the guarded original-value reporter.
-/

namespace ThreeSum.LightReportingWantedDispatch

open Light ReportingHostWantedLayout ReportingHostWantedControls

set_option maxHeartbeats 2600000
set_option maxRecDepth 22000

structure Config where
  layoutHeader : ℕ
  J : ℕ
  h : ℕ
  K : ℕ
  N : ℕ
  NB : ℕ
  NC : ℕ
  cover : ℕ
  counter : ℕ
  pairs : ℕ
  layerCount : ℕ
  scheduleSize : ℕ
  masks : ℕ
  vals : ℕ
  owners : ℕ
  records : ℕ
  pair : ℕ
  bank : ℕ
  srcB : ℕ
  srcC : ℕ
  report : ℕ
  modulus : ℕ

def arguments (C : Config) (slot : ℕ) : List ℤ :=
  [slot,C.layoutHeader,C.J,C.h,C.K,C.N,C.NB,C.NC,C.cover,C.counter,C.pairs,
    C.layerCount,C.scheduleSize,C.masks,C.vals,C.owners,C.records,C.pair,C.bank,
    C.srcB,C.srcC,C.report,C.modulus]

def layoutArguments (C : Config) : List ℤ :=
  [C.J,C.h,C.K,C.cover,C.counter,C.N,C.NB,C.NC,C.layoutHeader]

def decodeArguments (C : Config) (slot work : ℕ) : List ℤ :=
  [C.pairs,slot,C.N,C.J,C.scheduleSize,C.layerCount,C.masks,decoded C.layoutHeader,work,
    C.vals,C.owners,C.records,C.pair,C.bank,C.cover,C.srcB,C.srcC,C.report,access C.layoutHeader C.J]

def recordArguments (C : Config) : List ℤ :=
  [access C.layoutHeader C.J,C.layoutHeader,C.h,C.J,C.K,C.modulus,C.cover,C.counter]

def body (pLayout pDecode pRecord : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pLayout [v 2, v 3, v 4, v 8, v 9, v 5, v 6, v 7, v 1] 23)
    (Light.Stmt.seq (.set 24 ((Light.Expr.op Light.Op.add) (v 1) (k 14)))
      (Light.Stmt.seq
        (.set 25
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v 1) (k 18))
            ((Light.Expr.op Light.Op.mul) (k 2) (v 2))))
        (Light.Stmt.seq
          (.call pDecode
            [v 10, v 0, v 5, v 2, v 12, v 11, v 13, v 24, v 23, v 14, v 15, v 16,
              v 17, v 18, v 8, v 19, v 20, v 21, v 25]
            26)
          (.call pRecord [v 25, v 1, v 3, v 2, v 4, v 22, v 8, v 9] 0)))))

def baseLibraries : Program := ReportingHostRelocation.program
  LightReportingWantedLayout.program LightReportingWantedDecodeAccess.program

def libraries : Program := ReportingHostRelocation.program
  baseLibraries LightReportingWantedRecordCall.program

def program : Program := libraries++[body 1 11 150]

def time (C : Config) (V reportTime : ℕ) : ℕ :=
  LightReportingWantedLayout.time C.h C.J+
    LightReportingWantedDecodeAccess.time C.J V+reportTime+4500






































end ThreeSum.LightReportingWantedDispatch

end


