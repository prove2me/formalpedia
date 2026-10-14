-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle14
-- name    : ThreeSum1962Source_Bundle14
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:23:34.010652+00:00
-- url     : https://prove2.me/theorems/f85c9b59-0f7b-43d6-b229-bea40d0de81a
-- title:
--   Persistent cover and source catalogs, level interfaces, and terminal programs
-- statement:
--   This bundle defines retained cover/key data, occurrence-indexed source catalogs, their physical headers, and the programs that construct them. A suffix table of width $V$ and cutoff $c$ has stride
--   $$\operatorname{stride}(V,c)=(V+1)\sum_{a=0}^{\min(V,c)}\binom{V}{a}.$$
--   Reporting interfaces collect five-field catalog descriptors, sorted packed-index storage, pointer arrays, source-stage tables, address bounds, and scratch requirements. Further bodies compose prefix-index construction, catalog queries, suffix-catalog setup, and terminal scans over stored frontiers. Local-cover metadata and source-control layouts provide the concrete addresses and parameters consumed by these programs.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockSourceCatalogCosts.lean#L62-L91
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceBatchProgram.lean#L19-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceCatalog.lean#L23-L57
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceCatalogProgram.lean#L30-L32
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverKeyData.lean#L19-L58
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverKeys.lean#L20-L177
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorPrimeHost.lean#L13-L57
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverInit.lean#L20-L137
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverMetadata.lean#L21-L67
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingCatalogIndex.lean#L23-L38
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingCatalogQuery.lean#L28-L39
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L26-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixCatalog.lean#L22-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixCatalogSetup.lean#L12-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixQueryHost.lean#L19-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingTerminal.lean#L23-L45
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingTerminalFrontier.lean#L22-L36
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingTerminalStored.lean#L24-L45
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandBankBatch.lean#L13-L33
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandBankStep.lean#L14-L37
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandBanks.lean#L23-L66
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceControls.lean#L19-L70
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostLevelData.lean#L23-L74
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostSourceSelectionStored.lean#L21-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostTerminalFrontier.lean#L21-L84
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedReportingBankSources.lean#L11-L23
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandBankData.lean#L9-L22
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBandBankLayout.lean#L11-L77
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceControlLayout.lean#L9-L42
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceFiniteInputs.lean#L11-L14

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverMetadata


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
namespace ThreeSum.LightLocalCoverSetup
end ThreeSum.LightLocalCoverSetup
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Stored dimensions and pointers for the actual local cover

The twelve header fields are: L, 2h, schedule length, candidate count,
schedule coefficients, selected candidate indices, left counts, right
counts, candidate coefficients, cover matrix, first reusable address, p².
All values are computed from h, p, the vertex count, and the layout base.
-/

namespace ThreeSum.LightLocalCoverMetadata

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
open LightLocalCoverSetup (word)

set_option maxHeartbeats 2000000
set_option maxRecDepth 8500

def nextFree (base h : ℕ) : ℕ := scheduleMaps base h+scheduleSize h*(2*(512*h))

def values (base h : ℕ) : List ℤ :=
  [512*h,2*h,scheduleSize h,rows h,scheduleMaps base h,candidates base h,
    hist0 base h,hist1 base h,maps base h,matrixPtr base h,nextFree base h,cols h]

def body (pPower pLog : ℕ) : Stmt :=
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
              (Light.Stmt.seq (.set 11 ((Light.Expr.op Light.Op.add) (v 3) (v 2)))
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
                                (Light.Stmt.seq
                                  (.set 20
                                    ((Light.Expr.op Light.Op.add)
                                      ((Light.Expr.op Light.Op.add) (v 18) (v 8))
                                      (v 7)))
                                  (Light.Stmt.seq
                                    (.set 21
                                      ((Light.Expr.op Light.Op.add) (v 19)
                                        ((Light.Expr.op Light.Op.mul) (v 10)
                                          (v 6))))
                                    (Light.Stmt.seq
                                      (.set 22
                                        ((Light.Expr.op Light.Op.mul) (k 2)
                                          (v 0)))
                                      (Light.Stmt.seq (.store (v 4) (v 5))
                                        (Light.Stmt.seq
                                          (.store
                                            ((Light.Expr.op Light.Op.add) (v 4)
                                              (k 1))
                                            (v 22))
                                          (Light.Stmt.seq
                                            (.store
                                              ((Light.Expr.op Light.Op.add) (v 4)
                                                (k 2))
                                              (v 10))
                                            (Light.Stmt.seq
                                              (.store
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 4) (k 3))
                                                (v 7))
                                              (Light.Stmt.seq
                                                (.store
                                                  ((Light.Expr.op Light.Op.add)
                                                    (v 4) (k 4))
                                                  (v 19))
                                                (Light.Stmt.seq
                                                  (.store
                                                    ((Light.Expr.op Light.Op.add)
                                                      (v 4) (k 5))
                                                    (v 20))
                                                  (Light.Stmt.seq
                                                    (.store
                                                      ((Light.Expr.op
                                                          Light.Op.add)
                                                        (v 4) (k 6))
                                                      (v 15))
                                                    (Light.Stmt.seq
                                                      (.store
                                                        ((Light.Expr.op
                                                            Light.Op.add)
                                                          (v 4) (k 7))
                                                        (v 16))
                                                      (Light.Stmt.seq
                                                        (.store
                                                          ((Light.Expr.op
                                                              Light.Op.add)
                                                            (v 4) (k 8))
                                                          (v 12))
                                                        (Light.Stmt.seq
                                                          (.store
                                                            ((Light.Expr.op
                                                                Light.Op.add)
                                                              (v 4) (k 9))
                                                            (v 17))
                                                          (Light.Stmt.seq
                                                            (.store
                                                              ((Light.Expr.op
                                                                  Light.Op.add)
                                                                (v 4) (k 10))
                                                              (v 21))
                                                            (Light.Stmt.seq
                                                              (.store
                                                                ((Light.Expr.op
                                                                    Light.Op.add)
                                                                  (v 4) (k 11))
                                                                (v 8))
                                                              (.set 0
                                                                (v
                                                                  21))))))))))))))))))))))))))))))))

def time (h : ℕ) : ℕ := LightNatPower.time (2*(512*h))+log2Time (cols h)+1000

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pLog : ℕ
  power : P[pPower]? = some LightNatPower.body
  log : P[pLog]? = some log2Body
  main : P[pMain]? = some (body pPower pLog)

variable {lim : Limits} {P : Program} {d : ℕ}



















































































































































































































end ThreeSum.LightLocalCoverMetadata

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceBatchProgram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Closed actual source-bank catalog program

The existing 41-procedure library is retained unchanged. Two host procedures
are appended with their actual call indices, giving a fixed 43-procedure
program. The table contains no source-function oracle and no Q enumeration.
-/

namespace ThreeSum.LightBlockSourceBatchProgram

open Light SubsetAddress

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def program : Program := LightBlockSourceRetainedProgram.program ++
  [LightBlockSourceBatchStep.body 0,LightBlockSourceBatch.body 41]







































end ThreeSum.LightBlockSourceBatchProgram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceCatalog


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
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Constructed occurrence rows and their shared source banks

The first call constructs every big-endian occurrence row from its physical
bank index. The second call builds the two retained original source-stage
families once for that row. Original-band histograms and selected cover data
remain available throughout. No array of complete output records is read.
-/

namespace ThreeSum.LightBlockSourceCatalog

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
open BlockSourceOccurrenceOrder OutputDecodeOrder OutputDecodeRecords

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def count (h J : ℕ) : ℕ := scheduleSize h^J






def time (h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (count h J) J+
    LightBlockSourceBatch.time (count h J) h J cut+400




















def Stored {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J base cut : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) : Prop :=
  ∀ i < count h J, LightBlockSourceBatch.BankAt μ base (count h J) cut i P shift B b A a
    (representative h J i)










variable {lim : Limits} {P : Program} {d : ℕ}

















































































end ThreeSum.LightBlockSourceCatalog

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorPrimeHost


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
namespace ThreeSum.Scales
end ThreeSum.Scales


/-! # Original selected color to its retained common prime and physical arrays -/

namespace ThreeSum.LightEncodedColorPrimeHost

open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 15000

def body (pNormalize pPrime : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pNormalize [v 0, v 1, v 2, v 3, v 4] 5)
    (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 5) (k 1)))
      (Light.Stmt.seq (.set 7 (M (v 4)))
        (Light.Stmt.seq (.set 8 (M ((Light.Expr.op Light.Op.add) (v 4) (k 1))))
          (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 4) (k 2))))
            (Light.Stmt.seq
              (.set 10 (M ((Light.Expr.op Light.Op.add) (v 4) (k 3))))
              (Light.Stmt.seq
                (.set 11 (M ((Light.Expr.op Light.Op.add) (v 4) (k 4))))
                (Light.Stmt.seq
                  (.set 12 (M ((Light.Expr.op Light.Op.add) (v 4) (k 5))))
                  (Light.Stmt.seq
                    (.set 13 (M ((Light.Expr.op Light.Op.add) (v 4) (k 6))))
                    (Light.Stmt.seq
                      (.set 14 (M ((Light.Expr.op Light.Op.add) (v 2) (k 17))))
                      (Light.Stmt.seq
                        (.set 15 (M ((Light.Expr.op Light.Op.add) (v 2) (k 14))))
                        (Light.Stmt.seq
                          (.set 16
                            (M ((Light.Expr.op Light.Op.add) (v 2) (k 18))))
                          (Light.Stmt.seq
                            (.call pPrime
                              [v 7, v 8, v 9, v 10, v 11, v 12, v 14, v 13, v 15,
                                v 16, v 6]
                              17)
                            (.set 0 (v 6)))))))))))))))

def joined : Program := ReportingHostRelocation.program LightEncodedColorNormalize.program LightEncodedColorPrime.program
def program : Program := joined ++ [body 45 70]













def depth (n : ℕ) : ℕ := max
  (LightBandRawAColor.depth (inputBits n+1) n (bandSize n)+3)
  (Nat.clog 2 (maxMod n)+11)

def inputTime (n U : ℕ) : ℕ := LightEncodedColorNormalize.time n+
  LightEncodedColorPrime.time (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U+600

def inputSpace (free n U : ℕ) : ℕ := max (LightEncodedColorNormalize.space free n)
  (LightEncodedColorPrimeCore.space (prime free n (bandSize n)) (maxMod n) (bandSize n)
    (radix n) (primeWindow n) U)

def inputWord (n U : ℕ) : ℕ := max (LightEncodedColorNormalize.word n U)
  (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U)+
    bandSize n+radix n+primeWindow n+100

variable {lim : Limits} {d : ℕ}





















































































































end ThreeSum.LightEncodedColorPrimeHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixCatalog


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostQueryBounds
end ThreeSum.ReportingHostQueryBounds
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual construction of a contiguous suffix-box catalog

Each input record is a physical pair of global prefix masks. The host invokes
complete suffix-local setup for every record, writes the corresponding table
pointer, and retains every previous table. The table stride is the exact
local-width storage size; the following setup host computes it explicitly.
-/

namespace ThreeSum.LightReportingSuffixCatalog

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix ReportingHostQueryBounds

set_option maxHeartbeats 1800000

variable {lim : Limits}

def stride (V cut : ℕ) : ℕ := (V+1)*downsetCap V cut

def roundBody (pSetup : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 19 (M ((Light.Expr.op Light.Op.add) (v 10) (v 18))))
    (Light.Stmt.seq (.set 20 (M ((Light.Expr.op Light.Op.add) (v 11) (v 18))))
      (Light.Stmt.seq
        (.set 21
          ((Light.Expr.op Light.Op.add) (v 14)
            ((Light.Expr.op Light.Op.mul) (v 18) (v 15))))
        (Light.Stmt.seq
          (.call pSetup
            [v 0, v 1, v 2, v 3, v 4, v 19, v 5, v 20, v 6, v 7, v 8, v 9, v 21,
              v 16, v 17]
            22)
          (.store ((Light.Expr.op Light.Op.add) (v 13) (v 18)) (v 21))))))

def body (pSetup : ℕ) : Stmt := .for 18 (v 12) (roundBody pSetup)

def program : Program := LightReportingSuffixSetup.program ++ [body 29]

def time (W V cut offset n : ℕ) : ℕ := n*(LightReportingSuffixSetup.time W V cut offset+200)+30

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b addr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
      ptrBase,boxBase,stride V boxCut,maskBase,work,j,a,b,addr,r],μ'⟩ ∧
    (∀ i < j, μ' (ptrBase+i) = (boxBase+i*stride V boxCut : ℤ)) ∧
    (∀ i < j, LightBoxStages.StoredThrough μ' (boxBase+i*stride V boxCut) boxCut
      (leafWeight hfit f g stage (preL i) (preR i)) V) ∧
    Kept μ μ' ptrBase
































































































































end ThreeSum.LightReportingSuffixCatalog

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixQueryHost


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
# Complete suffix-local querying from the physical global query mask

The host computes the local query mask by a bounded bit scan, reads the
lifting factor from its own power table, and executes the complete local-box
sparse query. No local-mask conversion or power table is supplied by a caller.
-/

namespace ThreeSum.LightReportingSuffixQueryHost

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits}

def body (pLower pQuery : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pLower [v 0, v 7, v 8, v 10, v 17] 18)
    (Light.Stmt.seq (.set 19 (M ((Light.Expr.op Light.Op.add) (v 17) (v 8))))
      (.call pQuery
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 19, v 9, v 18, v 11, v 12,
          v 13, v 14, v 15, v 16, v 17]
        0)))

def suffix : Program := [LightReportingSuffixLower.body 17 20,body 29 28]
def program : Program := LightReportingSuffixQuery.program ++ suffix
def time (W V c t : ℕ) : ℕ := LightReportingSuffixLower.time W V+LightReportingSuffixQuery.time W V c t+100











































































end ThreeSum.LightReportingSuffixQueryHost

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingTerminal


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
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Complete single-prefix terminal program

The terminal host computes its balanced candidate count with Pascal,
enumerates both full endpoint mask arrays, constructs their exact endpoint
and independent trimming data, and tests their retained original buckets.
No candidate count, endpoint array, or trimming flag is supplied by an oracle.
-/

namespace ThreeSum.LightReportingTerminal

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000

def body (pCount pMasks pPrepared : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 31 ((Light.Expr.op Light.Op.mul) (v 10) (v 11)))
    (Light.Stmt.seq
      (.set 32
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.sub) (v 10) (v 20))
          ((Light.Expr.op Light.Op.mul) (k 2) (v 12))))
      (Light.Stmt.seq
        (.set 33
          ((Light.Expr.op Light.Op.mul)
            ((Light.Expr.op Light.Op.sub) (v 10) (v 20)) (v 12)))
        (Light.Stmt.seq (.call pCount [v 32, v 33, v 30] 34)
          (Light.Stmt.seq
            (.call pMasks
              [v 31, v 33, v 21, v 22, v 23, v 21, v 24, v 25, v 26, v 30] 35)
            (.call pPrepared
              [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12,
                v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 25, v 26, v 34, v 27,
                v 28, v 29, v 30]
              0))))))

def initialLibraries : Program := ReportingHostRelocation.program
  LightReportingTerminalMasks.program LightReportingBinomial.program
def libraries : Program := ReportingHostRelocation.program
  initialLibraries LightReportingTerminalPrepared.program
def program : Program := libraries ++ [body 11 0 37]

def space (work h J : ℕ) : ℕ :=
  max (LightReportingTerminalPrepared.space work h J)
    (max (work+LightPascal.tableSize (J*(512*h))) (work+2*(J*(512*h))+2))
def word (h J : ℕ) : ℕ := LightReportingTerminalPrepared.word h J+2^(J*(512*h)+1)
def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  LightReportingBinomial.time ((J-k)*(2*h))+LightReportingTerminalMasks.time h J k+
    LightReportingTerminalPrepared.time p shift left right NL NR q k pre+800

variable {lim : Limits}























































































































end ThreeSum.LightReportingTerminal

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverInit


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
# The complete local cover initialized from h and the original free pointer

The first eight header cells are the original local graph counts, prime,
and bucket cap. The next twelve contain computed dimensions and packed
pointers. The cover tables begin immediately after this fixed header.
-/

namespace ThreeSum.LightLocalCoverInit

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def base (free : ℕ) : ℕ := free+20

def values (free h : ℕ) : List ℤ :=
  LightLocalParameters.values h++LightLocalCoverMetadata.values (base free) h

def body (pParameters pMetadata pSetup : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 2 ((Light.Expr.op Light.Op.add) (v 1) (k 20)))
    (Light.Stmt.seq (.call pParameters [v 0, v 1, v 2] 3)
      (Light.Stmt.seq (.set 4 (M ((Light.Expr.op Light.Op.add) (v 1) (k 1))))
        (Light.Stmt.seq (.set 5 (M ((Light.Expr.op Light.Op.add) (v 1) (k 7))))
          (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 1) (k 8)))
            (Light.Stmt.seq (.call pMetadata [v 0, v 3, v 4, v 2, v 6] 7)
              (Light.Stmt.seq (.call pSetup [v 0, v 3, v 4, v 5, v 2] 8)
                (.set 0 (v 7)))))))))

def time (h : ℕ) : ℕ := LightLocalParameters.time h+
  LightLocalCoverMetadata.time h+LightLocalCoverSetup.time h+100

def word (h : ℕ) : ℕ := LightLocalParameters.word h+LightLocalCoverSetup.word h

def space (free h : ℕ) : ℕ :=
  max (LightLocalParameters.space (base free) h) (LightLocalCoverLayout.space (base free) h)

structure Procs (P : Program) (pMain : ℕ) where
  pParameters : ℕ
  pMetadata : ℕ
  pSetup : ℕ
  parameters : LightLocalParameters.Procs P pParameters
  metadata : LightLocalCoverMetadata.Procs P pMetadata
  setup : LightLocalCoverSetup.Procs P pSetup
  main : P[pMain]? = some (body pParameters pMetadata pSetup)

variable {lim : Limits} {P : Program} {d : ℕ}














































































/-- Keep the original 36-procedure cover table at indices 0 through 35. -/
def program : Program := LightLocalCoverSetup.program++
  [LightLocalParameters.body 37 45 50,LightLocalCounts.body 38,LightSubsetSetup.body 39 43 44,
    LightPascal.buildBody 40 41,fillBody,LightPascal.rowBody 42,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 44,LightSelectedPrime.body 46 47,sqrtBody,
    LightPrimePool.body 48,LightPrimality.body 49,emodBody,LightSmallDivide.body,
    LightLocalCoverMetadata.body 1 2,body 36 51 0]













end ThreeSum.LightLocalCoverInit

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockSourceCatalogCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales


/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout













































def work (n : ℕ) : ℕ := bandCount n*LightBlockSourceCatalog.time
  (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)

























/-- Occurrence rows and persistent bank records, excluding reusable scratch. -/
def catalogCells (n : ℕ) : ℕ :=
  bandCount n*scheduleCount n*(blockCount (inputBits n)+stride (256*mu n) (mu n)+2)

























end ThreeSum.BlockSourceCatalogCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceCatalogProgram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightBlockSourceCatalog
end ThreeSum.LightBlockSourceCatalog
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Literal program and finite cost of the constructed source catalog -/

namespace ThreeSum.LightBlockSourceCatalogProgram

open Light SubsetAddress LightBlockSourceCatalog

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000


















def factor (h J : ℕ) : ℕ :=
  LightBlockSourceRetainedProgram.factor h J+1120+
    300*(J+1)*(Nat.log 2 (count h J+1)+2)



























end ThreeSum.LightBlockSourceCatalogProgram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandBankStep


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Construct every occurrence bank for one common original-band index -/

namespace ThreeSum.LightSourceBandBankStep

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress LightBlockSourceBatchLayout BlockSourceOccurrenceOrder

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

/-- The twelve retained-source controls and cover pointers, pair catalog,
output bank base, compact capacity, occurrence count, and common band index. -/
def body (pSelect pBatch : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSelect [v 12, v 16, v 13] 17)
    (Light.Stmt.seq (.set 18 ((Light.Expr.op Light.Op.mul) (v 0) (v 1)))
      (Light.Stmt.seq
        (.set 19
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.mul) (k 5) (v 14))
                ((Light.Expr.op Light.Op.mul) (k 2) (v 18)))
              (k 2))
            ((Light.Expr.op Light.Op.mul)
              ((Light.Expr.op Light.Op.mul) (k 2)
                ((Light.Expr.op Light.Op.add) (v 18) (k 1)))
              (v 14))))
        (Light.Stmt.seq
          (.set 20
            ((Light.Expr.op Light.Op.add) (v 13)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 15))))
          (Light.Stmt.seq
            (.set 21
              ((Light.Expr.op Light.Op.add) (v 20)
                ((Light.Expr.op Light.Op.mul) (v 15) (v 19))))
            (Light.Stmt.seq (.set 22 ((Light.Expr.op Light.Op.add) (v 21) (v 14)))
              (Light.Stmt.seq
                (.set 23 ((Light.Expr.op Light.Op.add) (v 22) (v 18)))
                (Light.Stmt.seq
                  (.set 24 ((Light.Expr.op Light.Op.add) (v 23) (k 2)))
                  (.call pBatch
                    [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11,
                      M (v 13), M ((Light.Expr.op Light.Op.add) (v 13) (k 1)),
                      v 13, v 14, v 15, v 20, v 19, v 21, v 22, v 23, v 24]
                    25)))))))))

def time (h J cut : ℕ) : ℕ := LightBlockSourceBatch.time (LightBlockSourceCatalog.count h J) h J cut+1500

def word (NL NR h J : ℕ) : ℕ := LightBlockSourceRetainedHost.word NL NR h J+2*NL+2*NR+32

structure Procs (P : Program) (pMain : ℕ) where
  pSelect : ℕ
  pBatch : ℕ
  select : P[pSelect]?=some LightSourceBandHistSelect.body
  batch : LightBlockSourceBatch.Procs P pBatch
  main : P[pMain]?=some (body pSelect pBatch)

variable {lim : Limits} {P : Program} {d : ℕ}




























































































































end ThreeSum.LightSourceBandBankStep

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandBankLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout


/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

def span (h J cut : ℕ) : ℕ :=
  LightBlockSourceRetainedHost.space
    (work 0 (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J

def baseAt (base h J cut i : ℕ) : ℕ := base+i*span h J cut


























































def At (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut : ℕ) (p shift : ℤ) (i : ℕ) : Prop :=
  LightBlockSourceCatalog.Stored μ h J (baseAt base h J cut i) cut p shift
    (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
    (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)


















end ThreeSum.SourceBandBankLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSuffixCatalogSetup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Suffix catalog construction computes its own physical table stride -/

namespace ThreeSum.LightReportingSuffixCatalogSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix LightReportingSuffixCatalog

variable {lim : Limits}

def body (pSize pCatalog : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSize [v 6, v 2, v 16] 17)
    (Light.Stmt.seq
      (.set 18
        ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 6) (k 1))
          (v 17)))
      (.call pCatalog
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
          v 14, v 18, v 15, v 16]
        0)))

def program : Program := LightReportingSuffixCatalog.program ++ [body 9 30]

def time (W V cut offset n : ℕ) : ℕ :=
  LightDownsetSize.time V+LightReportingSuffixCatalog.time W V cut offset n+100























































































end ThreeSum.LightReportingSuffixCatalogSetup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingTerminalFrontier


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
namespace ThreeSum.ReportingHostTerminalFrontier
end ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Executed terminal iteration over the retained prefix arrays

The recursion reads the two aligned prefix masks from retained memory and
runs the complete terminal program for each prefix. Its cost is the sum of
the actual prefix costs. Reused scratch never changes the prefix arrays or
the original source buckets, occurrence rows, and selected cover data.
-/

namespace ThreeSum.LightReportingTerminalFrontier

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostTerminalFrontier

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000

/-- The terminal host's 31 arguments, with arguments 22 and 23 now the
retained prefix-array pointers, followed by the number of prefixes. -/
def body (pSelf pTerminal : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 31)))
    ((Light.Stmt.seq
       (.call pSelf
         [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
           v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25,
           v 26, v 27, v 28, v 29, v 30, (Light.Expr.op Light.Op.sub) (v 31) (k 1)]
         32)
       (Light.Stmt.seq (.set 33 ((Light.Expr.op Light.Op.sub) (v 31) (k 1)))
         (Light.Stmt.seq (.set 34 (M ((Light.Expr.op Light.Op.add) (v 22) (v 33))))
           (Light.Stmt.seq (.set 35 (M ((Light.Expr.op Light.Op.add) (v 23) (v 33))))
             (Light.Stmt.seq
               (.call pTerminal
                 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12,
                   v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 34, v 35,
                   v 24, v 25, v 26, v 27, v 28, v 29, v 30]
                 36)
               (.ite
                 (Light.Cond.lt (k 0) ((Light.Expr.op Light.Op.add) (v 32) (v 36)))
                 (.set 0 (k 1)) (.set 0 (k 0)))))))))
    (.set 0 (k 0))

def program : Program := LightReportingTerminal.program ++ [body 39 38]

variable {lim : Limits}


















































































































end ThreeSum.LightReportingTerminalFrontier

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostTerminalFrontier


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Exact terminal-prefix order, summed cost, and original completeness

The prefix batch consumes the actual retained frontier order. Every local
scan keeps its own selected-pair charge; their sum is bounded by the exact
original raw mass at the partial depth.
-/

namespace ThreeSum.ReportingHostTerminalFrontier

open Finset BlockRows BlockEncoding GlobalEncoding RawIncidences RawReporting RawPrefixCounts
open StoredReporting LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

def prefixAt {h : ℕ} (pres : List (List (Finset (Fin (512*h))))) (i : ℕ) : List (Finset (Fin (512*h))) :=
  pres[i]?.getD []




def Hit {h J : ℕ} (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) (n : ℕ) : Prop :=
  ∃ i<n, ReportingHostTerminalBatch.Hit av p shift left right NL NR q k (prefixAt pres i)



























def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) : ℕ→ℕ
  | 0 => 30
  | n+1 => time p shift left right NL NR q k pres n+
      LightReportingTerminal.time p shift left right NL NR q k (prefixAt pres n)+300



















def charge (h J k : ℕ) : ℕ :=
  LightReportingBinomial.time ((J-k)*(2*h))+LightReportingTerminalMasks.time h J k+
    LightReportingTerminalPreparation.time h J (LightReportingTerminalMasks.count h J k)+
    (2*LightResidues.residueBudget (endpointBound h J)+1300)*2^((J-k)*(2*h))+1830

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





































end ThreeSum.ReportingHostTerminalFrontier

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCoverKeys


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# From h to the original local cover and all global output keys

The fixed host obtains every key-constructor parameter from the header
written by the actual local-cover initializer. The original schedule,
candidate histograms, metadata, and input prefix remain available afterwards.
-/

namespace ThreeSum.LightCoverKeys

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- h, global block count, and first free address. -/
def body (pCover pKeys : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCover [v 0, v 2] 3)
    (.call pKeys
      [M ((Light.Expr.op Light.Op.add) (v 2) (k 8)),
        M ((Light.Expr.op Light.Op.add) (v 2) (k 9)),
        M ((Light.Expr.op Light.Op.add) (v 2) (k 10)),
        M ((Light.Expr.op Light.Op.add) (v 2) (k 6)), v 1,
        M ((Light.Expr.op Light.Op.add) (v 2) (k 12)), M (v 2), v 3]
      0))

def afterCover (free h : ℕ) : ℕ :=
  LightLocalCoverMetadata.nextFree (LightLocalCoverInit.base free) h

def keyHeader (free h J : ℕ) : ℕ :=
  LightGlobalKeys.scratch (afterCover free h) h+LightRadixKeys.offset (LightGlobalKeys.localCount h) J

def time (h J : ℕ) : ℕ := LightLocalCoverInit.time h+LightGlobalKeys.time h J+200
def space (free h J : ℕ) : ℕ :=
  max (LightLocalCoverInit.space free h) (LightGlobalKeys.space (afterCover free h) h J)
def word (h J : ℕ) : ℕ := max (LightLocalCoverInit.word h) (LightGlobalKeys.word h J)

structure Procs (P : Program) (pMain : ℕ) where
  pCover : ℕ
  pKeys : ℕ
  cover : LightLocalCoverInit.Procs P pCover
  keys : LightGlobalKeys.Procs P pKeys
  main : P[pMain]? = some (body pCover pKeys)

variable {lim : Limits} {P : Program} {d : ℕ}












































































































/-- Preserve the original initializer's procedure indices, then append
the key constructor and this two-call host. -/
def program : Program := LightLocalCoverInit.program++
  [LightGlobalKeys.body 54 57 64,LightSubsetEnumerationSetup.body 55 56,powTableBody,
    LightSubsetEnumeration.body 56,LightLocalKeys.body 58 63,LightLocalKeyRow.body 59 60 62,
    fillBody,LightMaskHashes.body 55 61,LightOneHot.body 61,LightArray.linearBody,copyBody,
    LightRadixKeys.body 64 65,LightRadixRows.body 66,LightReportingAffine.body,body 52 53]

def keyProcs : LightGlobalKeys.Procs program 53 :=
  ⟨54,55,56,57,64,65,66,rfl,rfl,rfl,rfl,
    ⟨58,63,rfl,⟨59,60,55,61,62,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl,rfl,rfl⟩

def coverSetupProcs : LightLocalCoverSetup.Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨31,8,32,33,34,35,4,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨5,24,29,⟨6,⟨7,12,19,⟨8,9,10,11,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,8,14,15,16,17,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨20,11,21,22,23,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨18,25,28,rfl,⟨26,21,27,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨30,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩

def coverProcs : LightLocalCoverInit.Procs program 52 :=
  ⟨36,51,0,⟨37,45,50,⟨38,39,40,41,42,43,44,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    ⟨46,47,rfl,⟨48,⟨49,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨1,2,rfl,rfl,rfl⟩,coverSetupProcs,rfl⟩

def programProcs : Procs program 67 := ⟨52,53,coverProcs,keyProcs,rfl⟩



end ThreeSum.LightCoverKeys

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceFiniteInputs


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
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

def maps (free h : ℕ) : ℕ := scheduleMaps (LightLocalCoverInit.base free) h
def candidates (free h : ℕ) : ℕ := LightLocalCoverLayout.candidates (LightLocalCoverInit.base free) h
def leftCounts (free h : ℕ) : ℕ := hist0 (LightLocalCoverInit.base free) h
def rightCounts (free h : ℕ) : ℕ := hist1 (LightLocalCoverInit.base free) h






















































end ThreeSum.SourceFiniteInputs

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandBankBatch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Actual source-bank catalog loop over common padded band indices -/

namespace ThreeSum.LightSourceBandBankBatch

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def body (pStep : ℕ) : Stmt :=
  .for 18 (v 16) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
      ((Light.Expr.op Light.Op.add) (v 13) ((Light.Expr.op Light.Op.mul) (v 18) (v 17))),v 14,v 15,v 18] 19)

def time (NL NR g h J cut : ℕ) : ℕ :=
  SourceBandPairSlices.count NL NR g*(LightSourceBandBankStep.time h J cut+200)+20

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightSourceBandBankStep.Procs P pStep
  main : P[pMain]?=some (body pStep)

def Inv (μ : ℕ → ℤ) (fL fR : ℕ → ℤ)
    (pair NL NR g p h J cut occ maps candidates histL histR base : ℕ) (shift : ℤ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
      histL,histR,pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,
      SourceBandPairSlices.count NL NR g,span h J cut,i,r],ν⟩ ∧
    (∀ j < i, At ν fL fR base NL NR g h J cut (p : ℤ) shift j) ∧ Kept μ ν base

variable {lim : Limits} {P : Program} {d : ℕ}




















































































end ThreeSum.LightSourceBandBankBatch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceBandBankData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout


/-! # Retained common-band source catalog with one occurrence table -/

namespace ThreeSum.SourceBandBankData

open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords

def first (base : ℕ) : ℕ := base+5
def finish (base NL NR g h J cut : ℕ) : ℕ :=
  baseAt (first base) h J cut (SourceBandPairSlices.count NL NR g)

def header (base NL NR g h J cut occ : ℕ) : List ℤ :=
  [first base,SourceBandPairSlices.count NL NR g,span h J cut,
    finish base NL NR g h J cut,occ]

structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut occ : ℕ) (p shift : ℤ) : Prop where
  heads : Seg μ base (header base NL NR g h J cut occ)
  banks : ∀ i < SourceBandPairSlices.count NL NR g,
    At μ fL fR (first base) NL NR g h J cut p shift i
  rows : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
    μ (occ+k*J+j)=((OutputDecodeOrder.indices (scheduleSize h) J k).getD j 0 : ℤ)









































end ThreeSum.SourceBandBankData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceControlLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-! # Arithmetic dimensions of the original shared source bank -/

namespace ThreeSum.SourceControlLayout

open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress

def scratch (J W logP logE : ℕ) : ℕ :=
  max (max (max ((W+1)^2+(W+1)) (logE+2)) (logP+5)) (J+1)

def stride (W K : ℕ) : ℕ := 5*K+2*W+4+2*(W+1)*K

def span (J W K S logP logE : ℕ) : ℕ :=
  S*stride W K+K+W+2+scratch J W logP logE

def word (J W K S logP logE : ℕ) : ℕ :=
  span J W K S logP logE+stride W K+J+W+K+S+logP+logE+(W+1)^2+30






















def values (h J cut : ℕ) : List ℤ :=
  [downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,SourceBandBankLayout.span h J cut]

end ThreeSum.SourceControlLayout

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingPrefixCatalog


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}

def count (h k : ℕ) : ℕ := (LightReportingPrefixArrays.localCount (512*h) h)^k

def body (pPrefixes pCatalog : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pPrefixes [v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 19] 20)
    (Light.Stmt.seq (.set 21 (M (v 20)))
      (Light.Stmt.seq (.set 22 ((Light.Expr.op Light.Op.sub) (v 20) (v 14)))
        (Light.Stmt.seq (.set 23 ((Light.Expr.op Light.Op.add) (v 15) (v 22)))
          (Light.Stmt.seq (.set 24 ((Light.Expr.op Light.Op.add) (v 20) (k 1)))
            (Light.Stmt.seq (.set 25 ((Light.Expr.op Light.Op.add) (v 23) (k 1)))
              (Light.Stmt.seq
                (.set 26 ((Light.Expr.op Light.Op.mul) (v 10) (v 9)))
                (Light.Stmt.seq
                  (.call pCatalog
                    [v 0, v 1, v 2, v 3, v 26, v 26, v 4, v 5, v 6, v 7, v 24,
                      v 25, v 21, v 16, v 17, v 18, v 19]
                    27)
                  (.set 0 (v 20))))))))))

def program : Program :=
  ReportingHostRelocation.program LightReportingPrefixArrays.program LightReportingSuffixCatalogSetup.program ++
    [body 10 42]

def time (h J k boxCut : ℕ) : ℕ :=
  LightReportingPrefixArrays.time (512*h) h k+
    LightReportingSuffixCatalogSetup.time (J*(512*h)) ((J-k)*(512*h)) boxCut (k*(512*h)) (count h k)+500






































































































































end ThreeSum.LightReportingPrefixCatalog

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingTerminalStored


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
namespace ThreeSum.ReportingHostTerminalFrontier
end ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting


/-!
# Terminal scanning from the actual frontier header

This adapter reads the capacity produced by root initialization and the
terminal level's retained count, query mask, and two prefix-array pointers.
It then executes the complete terminal scan in the unchanged frontier order.
-/

namespace ThreeSum.LightReportingTerminalStored

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostTerminalFrontier
open RawIncidences RawReporting ReportingHostFrontierLayout

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

/-- The 20 original-source/encoding controls, depth and root pointer, then
the seven terminal scratch pointers. All frontier metadata is loaded. -/
def body (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 29 (M ((Light.Expr.op Light.Op.add) (v 21) (k 3))))
    (Light.Stmt.seq
      (.set 30
        ((Light.Expr.op Light.Op.add) (v 21)
          ((Light.Expr.op Light.Op.mul) (v 20)
            ((Light.Expr.op Light.Op.add) (k 4)
              ((Light.Expr.op Light.Op.mul) (k 2) (v 29))))))
      (Light.Stmt.seq (.set 31 (M (v 30)))
        (Light.Stmt.seq (.set 32 (M ((Light.Expr.op Light.Op.add) (v 30) (k 1))))
          (Light.Stmt.seq (.set 33 ((Light.Expr.op Light.Op.add) (v 30) (k 4)))
            (Light.Stmt.seq (.set 34 ((Light.Expr.op Light.Op.add) (v 33) (v 29)))
              (.call pScan
                [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11,
                  v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 32,
                  v 33, v 34, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 31]
                0)))))))

def program : Program := LightReportingTerminalFrontier.program ++ [body 39]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) : ℕ :=
  ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 k
    (ReportingHostFrontier.frontier I w k) (ReportingHostFrontier.frontier I w k).length+600









































































































end ThreeSum.LightReportingTerminalStored

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCoverKeyData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

def keyEnd (free h J : ℕ) : ℕ :=
  LightCoverKeys.keyHeader free h J+1+LightGlobalKeys.localCount h^J


























structure Stored (μ : ℕ → ℤ) (free h J : ℕ) : Prop where
  count : μ (LightCoverKeys.keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ)
  keys : Seg μ (LightCoverKeys.keyHeader free h J+1) (globalKeys h J)
  header : Seg μ free (LightLocalCoverInit.values free h)
  data : Data μ h (maps (LightLocalCoverInit.base free) h)
    (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
    (matrixPtr (LightLocalCoverInit.base free) h)
  rows : ScheduleRows μ h (scheduleMaps (LightLocalCoverInit.base free) h)
  indices : ∀ s : Occurrence h, μ (candidates (LightLocalCoverInit.base free) h+s.val)=
    (candidateAt h s : ℤ)
  masks : ∀ i < outputCount (512*h) h, μ (LightCoverKeys.afterCover free h+i)=
    (LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)





























end ThreeSum.LightCoverKeyData

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandBanks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SourceBandBankData
end ThreeSum.SourceBandBankData
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# One occurrence catalog reused across all original source bands

The physical B/C band counts determine the loop length. A single radix
decoder loop constructs the occurrence rows. The bank loop then selects
retained histograms and builds exactly two families per common band and
occurrence. The result header stores the first bank base, band count, band
stride, next free address, and occurrence-row pointer.
-/

namespace ThreeSum.LightSourceBandBanks

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout SourceBandBankData

set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

def afterCountBody (pRows pBanks : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 19 ((Light.Expr.op Light.Op.add) (v 13) (k 5)))
    (Light.Stmt.seq
      (.set 20
        ((Light.Expr.op Light.Op.add) (v 19)
          ((Light.Expr.op Light.Op.mul) (v 18) (v 17))))
      (Light.Stmt.seq (.call pRows [v 15, v 0, v 16, v 7, v 20] 21)
        (Light.Stmt.seq (.store (v 13) (v 19))
          (Light.Stmt.seq
            (.store ((Light.Expr.op Light.Op.add) (v 13) (k 1)) (v 18))
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 13) (k 2)) (v 17))
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 13) (k 3)) (v 20))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 13) (k 4)) (v 7))
                  (Light.Stmt.seq
                    (.call pBanks
                      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10,
                        v 11, v 12, v 19, v 14, v 15, v 18, v 17]
                      21)
                    (.set 0 (v 20)))))))))))

def body (pRows pBanks : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 18 (M ((Light.Expr.op Light.Op.add) (v 12) (k 1))))
    (Light.Stmt.seq
      (.ite (Light.Cond.lt (v 18) (M ((Light.Expr.op Light.Op.add) (v 12) (k 3))))
        (.set 18 (M ((Light.Expr.op Light.Op.add) (v 12) (k 3)))) .skip)
      (afterCountBody pRows pBanks)))

def afterTime (NL NR g h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
    LightSourceBandBankBatch.time NL NR g h J cut+1000

def time (NL NR g h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
    LightSourceBandBankBatch.time NL NR g h J cut+1200

def space (base NL NR g h J cut : ℕ) : ℕ :=
  max (LightOutputDecodeDigits.space (finish base NL NR g h J cut) (LightBlockSourceCatalog.count h J))
    (span h J cut)

def word (NL NR h J : ℕ) : ℕ :=
  max (LightSourceBandBankStep.word NL NR h J)
    (LightOutputDecodeDigits.word (LightBlockSourceCatalog.count h J) (scheduleSize h) J)

structure Procs (P : Program) (pMain : ℕ) where
  pRows : ℕ
  pDigits : ℕ
  pDivide : ℕ
  pBanks : ℕ
  rows : P[pRows]?=some (LightSourceOccurrenceArray.body pDigits)
  digits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]?=some LightOutputDecodeDivide.body
  banks : LightSourceBandBankBatch.Procs P pBanks
  main : P[pMain]?=some (body pRows pBanks)

variable {lim : Limits} {P : Program} {d : ℕ}


































































































































































end ThreeSum.LightSourceBandBanks

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostSourceSelectionStored


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection


/-!
# Selected controls from the actual retained original-source catalogs

The selector's concrete header reads follow from the existing band,
occurrence-bank and local-cover constructors. Its two independently chosen
bands supply the unchanged physical buckets and the exact original-output
source stages. No output-subset loop or source reconstruction is involved.
-/

namespace ThreeSum.ReportingHostSourceSelectionStored

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection OutputDecodeRecords BlockCoefficientRows

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000

def retained (pair bank cover NL NR g h J cut occ i j code : ℕ) : Pointers where
  leftHeaders := SourceBandPairData.leftBase pair
  rightHeaders := SourceBandPairData.rightBase pair NL g (modulus h J)
  firstBank := SourceBandBankData.first bank
  bankSpan := SourceBandBankLayout.span h J cut
  occurrenceBase := occ
  startL := BandPartition.start g i
  startR := BandPartition.start g j
  sizeL := SourceBandLayout.len NL g i
  sizeR := SourceBandLayout.len NR g j
  offsetsL := SourceBandLayout.offsets (SourceBandPairData.leftBase pair) NL g (modulus h J) i
  flatL := SourceBandLayout.flat (SourceBandPairData.leftBase pair) NL g (modulus h J) i
  offsetsR := SourceBandLayout.offsets (SourceBandPairData.rightBase pair NL g (modulus h J)) NR g (modulus h J) j
  flatR := SourceBandLayout.flat (SourceBandPairData.rightBase pair NL g (modulus h J)) NR g (modulus h J) j
  stagesL := LightBlockSourceBatchLayout.leftBase
    (SourceBandBankLayout.baseAt (SourceBandBankData.first bank) h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut code
  stagesR := LightBlockSourceBatchLayout.rightBase
    (SourceBandBankLayout.baseAt (SourceBandBankData.first bank) h J cut j)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut code
  maps := LightLocalCoverLayout.scheduleMaps (LightLocalCoverInit.base cover) h
  candidates := LightLocalCoverLayout.candidates (LightLocalCoverInit.base cover) h
  histL := LightLocalCoverLayout.hist0 (LightLocalCoverInit.base cover) h
  histR := LightLocalCoverLayout.hist1 (LightLocalCoverInit.base cover) h



















































































































end ThreeSum.ReportingHostSourceSelectionStored

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SharedReportingBankSources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData


/-! # Independent source bands and exact reuse for every decoded output -/

namespace ThreeSum.SharedReportingBankSources

open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords

def bankBase (base h J cut band : ℕ) : ℕ :=
  SourceBandBankLayout.baseAt (SourceBandBankData.first base) h J cut band

def leftCell (base h J cut band occurrence : ℕ) : ℕ := bankBase base h J cut band+2*occurrence
def rightCell (base h J cut band occurrence : ℕ) : ℕ := bankBase base h J cut band+2*occurrence+1

def leftBase (base h J cut band occurrence : ℕ) : ℕ :=
  LightBlockSourceBatchLayout.leftBase (bankBase base h J cut band)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut occurrence

def rightBase (base h J cut band occurrence : ℕ) : ℕ :=
  LightBlockSourceBatchLayout.rightBase (bankBase base h J cut band)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut occurrence
































































end ThreeSum.SharedReportingBankSources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceControls


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
# Actual occurrence count, compact capacity, and exact bank stride

Only the block dimensions and previously constructed local schedule controls
are supplied. Scalar powering, the compact downset-size program, two actual
logarithms, and exact span arithmetic construct all three source controls.
-/

namespace ThreeSum.LightSourceControls

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def spanWord (h J cut : ℕ) : ℕ :=
  SourceControlLayout.word J (J*(512*h)) (downsetCap (J*(512*h)) cut)
    (LightBlockSourceCatalog.count h J) (Nat.log 2 ((512*h)*localPrime h+1))
    (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1))

def word (h J cut : ℕ) : ℕ :=
  spanWord h J cut+(J*(512*h)+1)*2^(J*(512*h)+1)+(scheduleSize h+1)^(J+1)+
    2*((512*h)*localPrime h+1)+2*(LightBlockSourceBuild.endpointBound h J+1)+
    modulus h J*localPrime h+J+512*h+localPrime h+cut+scheduleSize h+modulus h J+J*(512*h)+50

def space (work h J : ℕ) : ℕ := work+LightPascal.tableSize (J*(512*h))+(J*(512*h)+1)

def time (h J : ℕ) : ℕ :=
  LightNatPower.time J+LightDownsetSize.time (J*(512*h))+
    log2Time ((512*h)*localPrime h+1)+log2Time (LightBlockSourceBuild.endpointBound h J+1)+2000

/-- J, local width, local prime, cutoff, schedule size, original local
prime power, three-cell destination, and polynomial scratch. -/
def body (pPower pDownset pLog pSpan : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pPower [v 4, v 0] 8)
    (Light.Stmt.seq (.set 9 ((Light.Expr.op Light.Op.mul) (v 0) (v 1)))
      (Light.Stmt.seq (.call pDownset [v 9, v 3, v 7] 10)
        (Light.Stmt.seq
          (.call pLog
            [(Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.mul) (v 1) (v 2)) (k 1)]
            11)
          (Light.Stmt.seq
            (.call pLog
              [(Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.mul) (v 9)
                    ((Light.Expr.op Light.Op.mul) (v 5) (v 2)))
                  (k 1)]
              12)
            (Light.Stmt.seq (.call pSpan [v 0, v 9, v 10, v 8, v 11, v 12] 13)
              (Light.Stmt.seq (.store (v 6) (v 10))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 6) (k 1)) (v 8))
                  (Light.Stmt.seq
                    (.store ((Light.Expr.op Light.Op.add) (v 6) (k 2)) (v 13))
                    (.set 0 (v 13)))))))))))

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pDownset : ℕ
  pLog : ℕ
  pSpan : ℕ
  pMax : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  pOffset : ℕ
  power : P[pPower]?=some LightNatPower.body
  downset : P[pDownset]?=some (LightDownsetSize.body pSetup pOffset)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]?=some LightSubsetOffset.body
  log : P[pLog]?=some log2Body
  span : P[pSpan]?=some (LightSourceControlsSpan.body pMax)
  maximum : P[pMax]?=some LightSourceControlsMax.body
  main : P[pMain]?=some (body pPower pDownset pLog pSpan)

variable {lim : Limits} {P : Program} {d : ℕ}



































































































end ThreeSum.LightSourceControls

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingCatalogIndex


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
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Complete actual suffix catalog with a sorted physical lookup index

The returned header and both array addresses are obtained from the previous
actual constructor. The program then constructs the sorted packed index,
retaining every original box pointer and source/table cell.
-/

namespace ThreeSum.LightReportingCatalogIndex

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixOrder ReportingHostSuffix LightReportingSuffixCatalog
open LightReportingPrefixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : Limits}

def body (pCatalog pIndex : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pCatalog
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
        v 14, v 15, v 16, v 17, v 18, v 19]
      21)
    (Light.Stmt.seq (.set 22 (M (v 21)))
      (Light.Stmt.seq (.set 23 ((Light.Expr.op Light.Op.sub) (v 21) (v 14)))
        (Light.Stmt.seq
          (.set 24
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v 15) (v 23)) (k 1)))
          (Light.Stmt.seq (.set 25 ((Light.Expr.op Light.Op.add) (v 21) (k 1)))
            (Light.Stmt.seq (.call pIndex [v 0, v 25, v 24, v 22, v 20, v 19] 26)
              (.set 0 (v 21))))))))

def program : Program :=
  ReportingHostRelocation.program LightReportingPrefixCatalog.program LightReportingSortedCatalog.program ++
    [body 43 50]

def time (h J k boxCut : ℕ) : ℕ := LightReportingPrefixCatalog.time h J k boxCut+
  LightReportingSortedCatalog.time (J*(512*h)) (count h k)+250

















































































































end ThreeSum.LightReportingCatalogIndex

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingCatalogQuery


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
namespace ThreeSum.ReportingHostCatalogSelection
end ThreeSum.ReportingHostCatalogSelection
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Actual indexed suffix-box query with exact original raw-count semantics

The machine recovers the complete-catalog index from the two physical prefix
masks, reads its stored box pointer, and executes the suffix-local sparse
query. The original prefix is used only to state and prove its specification;
neither a catalog position nor a table pointer is supplied to this machine.
-/

namespace ThreeSum.LightReportingCatalogQuery

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostCatalogSelection

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pLookup pQuery : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pLookup [v 0, v 17, v 15, v 4, v 6, v 19] 20)
    (Light.Stmt.seq (.set 21 (M ((Light.Expr.op Light.Op.add) (v 16) (v 20))))
      (.call pQuery
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13,
          v 14, v 21, v 18, v 19]
        0)))

def program : Program :=
  ReportingHostRelocation.program LightReportingCatalogLookup.program LightReportingSuffixQueryHost.program ++
    [body 3 34]

def time (h J k t : ℕ) : ℕ :=
  LightReportingCatalogLookup.time (width h J) (count h k)+
    LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t+100









































































































end ThreeSum.LightReportingCatalogQuery

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostLevelData


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
# Exact retained catalog and scratch interfaces for the level loop

These records collect the memory assertions already produced by the actual
prefix-catalog constructor. They contain no assumed query procedure. The
query adapter below invokes the existing closed, verified catalog program.
-/

namespace ThreeSum.ReportingHostLevelData

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

structure Catalog where
  t : ℕ
  boxCut : ℕ
  boxBase : ℕ
  indexBase : ℕ
  ptrBase : ℕ

/-- The fields actually consumed by the level machine, including the computed
prefix count. The box base remains a semantic ownership bound. -/
def Catalog.record (D : Catalog) (h k : ℕ) : List ℕ :=
  [D.t,D.boxCut,D.indexBase,D.ptrBase,count h k]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

structure Sources {h J : ℕ} (μ : ℕ→ℤ) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (q : GlobalOutput h J) (baseL baseR : ℕ) : Prop where
  left : LightZetaStages.StoredThrough μ baseL (sourceCut h J) (leftSource pMod B b q) (width h J)
  right : LightZetaStages.StoredThrough μ baseR (sourceCut h J) (rightSource pMod shift C c q) (width h J)

structure Stored {h J k : ℕ} (μ : ℕ→ℤ) (D : Catalog) (hk : k≤J)
    (pMod shift : ℤ) (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (q : GlobalOutput h J) : Prop where
  index : ∃ S : List ℤ, Seg μ D.indexBase S ∧
    S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
    S.Pairwise (· ≤ ·)
  pointers : SegN μ D.ptrBase (List.ofFn fun i : Fin (count h k) =>
    D.boxBase+i.val*stride (suffixStage J (512*h) k) D.boxCut)
  boxes : ∀ i<count h k, LightBoxStages.StoredThrough μ
    (D.boxBase+i*stride (suffixStage J (512*h) k) D.boxCut) D.boxCut
    (leafWeight (block_fit hk) (leftSource pMod B b q) (rightSource pMod shift C c q)
      (suffixStage J (512*h) k) (preL h J k i) (preR h J k i)) (suffixStage J (512*h) k)

structure Bounds (h J k : ℕ) (D : Catalog) (baseL baseR stop : ℕ) : Prop where
  left : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J)≤stop
  right : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J)≤stop
  index : D.indexBase+count h k≤stop
  pointers : D.ptrBase+count h k≤stop
  boxes : D.boxBase+count h k*stride (suffixStage J (512*h) k) D.boxCut≤stop

structure Scratch (lim : Limits) (h J k : ℕ) (D : Catalog) (bCard cCard maskBase work : ℕ) : Prop where
  masks : maskBase+LightSparseQuery.queryItems (residualSize h J k) D.t≤work
  space : work+1+tableSize (width h J)+(width h J+1)≤lim.space
  powers : work+(2*width h J+2)≤lim.space
  emod : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h k)+1)+2)≤lim.space
  word : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ)≤lim.word
  lookup : (LightReportingCatalogLookup.word (width h J) (count h k) : ℤ)≤lim.word
  values : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
    (residualSize h J k) D.t bCard cCard : ℤ)≤lim.word
  t : D.t≤residualSize h J k+1
  cut : D.boxCut≤residualSize h J k
  flags : residualSize h J k-D.t≤D.boxCut


























































end ThreeSum.ReportingHostLevelData

end


