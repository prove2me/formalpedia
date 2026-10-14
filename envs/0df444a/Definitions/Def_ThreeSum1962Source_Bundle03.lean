-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle03
-- name    : ThreeSum1962Source_Bundle03
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T06:06:12.026253+00:00
-- url     : https://prove2.me/theorems/5344090c-4de2-45db-85dd-02583d2ee5b3
-- title:
--   Reporting accessors, scalar controls, and source-selection layouts
-- statement:
--   This bundle defines routines for indexed gathering, packed reporting keys, retained-catalog lookup, source-band selection, signed residue conversion, array scaling and signed-leaf evaluation. It includes compact subset-address calculations, support marking, independent trimming flags, and the scalar arithmetic of the reporting switch. For block count \(J\), depth \(j\), residual size \(r\), and candidate \(q\), two switch components are
--   $$
--   L=(291J+1000j)r^3,\qquad C=q\bigl(799r^2+q(72r+24q)\bigr).
--   $$
--   Additional definitions describe ordered radix decoding, modular triple counts, program relocation, source-header pointers and memory-fit conditions. Together they specify how reporting obtains stored data and computes its control values.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingGather.lean#L17-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingPackKeys.lean#L12-L18
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSourceSelect.lean#L19-L65
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightResidues.lean#L19-L52
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightScaleArray.lean#L11-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingLookup.lean#L12-L22
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSign.lean#L11-L17
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSignedLeaf.lean#L20-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSmallDivide.lean#L17-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandHistSelect.lean#L12-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceControlsMax.lean#L9-L9
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceControlsSpan.lean#L13-L22
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceFlagTest.lean#L9-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceRowScan.lean#L21-L79
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetAddress.lean#L20-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetOffset.lean#L19-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSupportMark.lean#L16-L121
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSwitch.lean#L20-L96
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSwitchBounds.lean#L17-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSwitchScalar.lean#L11-L15
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightTrimTest.lean#L9-L28
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWantedRow.lean#L16-L29
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightGather.lean#L17-L35
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalParameterBounds.lean#L18-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ModuloCosts.lean#L16-L16
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ModuloCounts.lean#L17-L24
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/OutputDecodeOccurrenceCode.lean#L11-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/OutputDecodeOrder.lean#L22-L89
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostRelocation.lean#L16-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ReportingHostSourceSelection.lean#L12-L87

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingGather


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Actual indexed gathering of selected reporting masks

The index array and source array can lie on either side of the destination.
This supports reusable high-address child scratch and low-address frontier
storage without scanning discarded children or overwriting retained input.
-/

namespace ThreeSum.LightReportingGather

open Light

variable {lim : Limits} {P : Program}

def body : Stmt := pass 5 (v 3) (v 2) (M (((Light.Expr.op Light.Op.add) (v 1)
                                            (M ((Light.Expr.op Light.Op.add) (v 0) (v 5))))))
def program : Program := [body]
def time (t : ℕ) : ℕ := 40*t+10










































end ThreeSum.LightReportingGather

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingPackKeys


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog


/-! # The actual linear pass that packs prefix keys and original catalog indices -/

namespace ThreeSum.LightReportingPackKeys

open Light LightArray ReportingHostPackedCatalog

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  pass 5 (v 2) (v 4)
    (((Light.Expr.op Light.Op.add)
       ((Light.Expr.op Light.Op.mul)
         ((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v 0) (v 5)))
           ((Light.Expr.op Light.Op.mul) (v 3)
             (M ((Light.Expr.op Light.Op.add) (v 1) (v 5)))))
         ((Light.Expr.op Light.Op.add) (v 2) (k 1)))
       (v 5)))

def time (n : ℕ) : ℕ := 50*n+10

def word (radix n : ℕ) : ℕ := radix^2*(n+1)+n+radix+2




































































end ThreeSum.LightReportingPackKeys

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingSourceSelect


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection


/-!
# Actual constant-time selection of both independent source bands

The procedure reads the retained band, stage-bank and cover headers. It
materializes the fifteen controls consumed by wanted reporting, including
physical bucket pointers and the shared occurrence row, without scanning
any source or reconstructing a transform. All reads precede all writes.
-/

namespace ThreeSum.LightReportingSourceSelect

open Light ReportingHostSourceSelection

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

/-- Pair header, source-bank header, cover, original B/C bases, independent
B/C band indices, decoded occurrence code, J, and the fifteen-cell output. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 10 (M (v 0)))
    (Light.Stmt.seq (.set 11 (M ((Light.Expr.op Light.Op.add) (v 0) (k 2))))
      (Light.Stmt.seq (.set 12 (M (v 1)))
        (Light.Stmt.seq (.set 13 (M ((Light.Expr.op Light.Op.add) (v 1) (k 2))))
          (Light.Stmt.seq (.set 14 (M ((Light.Expr.op Light.Op.add) (v 1) (k 4))))
            (Light.Stmt.seq
              (.set 15
                ((Light.Expr.op Light.Op.add) (v 10)
                  ((Light.Expr.op Light.Op.mul) (k 6) (v 5))))
              (Light.Stmt.seq
                (.set 16
                  ((Light.Expr.op Light.Op.add) (v 11)
                    ((Light.Expr.op Light.Op.mul) (k 6) (v 6))))
                (Light.Stmt.seq (.set 17 (M (v 15)))
                  (Light.Stmt.seq
                    (.set 18 (M ((Light.Expr.op Light.Op.add) (v 15) (k 1))))
                    (Light.Stmt.seq
                      (.set 19 (M ((Light.Expr.op Light.Op.add) (v 15) (k 4))))
                      (Light.Stmt.seq
                        (.set 20 (M ((Light.Expr.op Light.Op.add) (v 15) (k 5))))
                        (Light.Stmt.seq (.set 21 (M (v 16)))
                          (Light.Stmt.seq
                            (.set 22
                              (M ((Light.Expr.op Light.Op.add) (v 16) (k 1))))
                            (Light.Stmt.seq
                              (.set 23
                                (M ((Light.Expr.op Light.Op.add) (v 16) (k 4))))
                              (Light.Stmt.seq
                                (.set 24
                                  (M ((Light.Expr.op Light.Op.add) (v 16) (k 5))))
                                (Light.Stmt.seq
                                  (.set 25
                                    ((Light.Expr.op Light.Op.add) (v 3) (v 17)))
                                  (Light.Stmt.seq
                                    (.set 26
                                      ((Light.Expr.op Light.Op.add) (v 4) (v 21)))
                                    (Light.Stmt.seq
                                      (.set 27
                                        ((Light.Expr.op Light.Op.add)
                                          ((Light.Expr.op Light.Op.add) (v 12)
                                            ((Light.Expr.op Light.Op.mul) (v 5)
                                              (v 13)))
                                          ((Light.Expr.op Light.Op.mul) (k 2)
                                            (v 7))))
                                      (Light.Stmt.seq
                                        (.set 28
                                          ((Light.Expr.op Light.Op.add)
                                            ((Light.Expr.op Light.Op.add)
                                              ((Light.Expr.op Light.Op.add) (v 12)
                                                ((Light.Expr.op Light.Op.mul)
                                                  (v 6) (v 13)))
                                              ((Light.Expr.op Light.Op.mul) (k 2)
                                                (v 7)))
                                            (k 1)))
                                        (Light.Stmt.seq (.set 29 (M (v 27)))
                                          (Light.Stmt.seq (.set 30 (M (v 28)))
                                            (Light.Stmt.seq
                                              (.set 31
                                                ((Light.Expr.op Light.Op.add)
                                                  (v 14)
                                                  ((Light.Expr.op Light.Op.mul)
                                                    (v 7) (v 8))))
                                              (Light.Stmt.seq
                                                (.set 32
                                                  (M
                                                    ((Light.Expr.op Light.Op.add)
                                                      (v 2) (k 12))))
                                                (Light.Stmt.seq
                                                  (.set 33
                                                    (M
                                                      ((Light.Expr.op
                                                          Light.Op.add)
                                                        (v 2) (k 13))))
                                                  (Light.Stmt.seq
                                                    (.set 34
                                                      (M
                                                        ((Light.Expr.op
                                                            Light.Op.add)
                                                          (v 2) (k 14))))
                                                    (Light.Stmt.seq
                                                      (.set 35
                                                        (M
                                                          ((Light.Expr.op
                                                              Light.Op.add)
                                                            (v 2) (k 15))))
                                                      (Light.Stmt.seq
                                                        (.store (v 9) (v 25))
                                                        (Light.Stmt.seq
                                                          (.store
                                                            ((Light.Expr.op
                                                                Light.Op.add)
                                                              (v 9) (k 1))
                                                            (v 26))
                                                          (Light.Stmt.seq
                                                            (.store
                                                              ((Light.Expr.op
                                                                  Light.Op.add)
                                                                (v 9) (k 2))
                                                              (v 19))
                                                            (Light.Stmt.seq
                                                              (.store
                                                                ((Light.Expr.op
                                                                    Light.Op.add)
                                                                  (v 9) (k 3))
                                                                (v 20))
                                                              (Light.Stmt.seq
                                                                (.store
                                                                  ((Light.Expr.op
                                                                      Light.Op.add)
                                                                    (v 9) (k 4))
                                                                  (v 23))
                                                                (Light.Stmt.seq
                                                                  (.store
                                                                    ((Light.Expr.op
                                                                        Light.Op.add)
                                                                      (v 9) (k 5))
                                                                    (v 24))
                                                                  (Light.Stmt.seq
                                                                    (.store
                                                                      ((Light.Expr.op
                                                                          Light.Op.add)
                                                                        (v 9)
                                                                        (k 6))
                                                                      (v 18))
                                                                    (Light.Stmt.seq
                                                                      (.store
                                                                        ((Light.Expr.op
                                                                            Light.Op.add)
                                                                          (v 9)
                                                                          (k 7))
                                                                        (v 22))
                                                                      (Light.Stmt.seq
                                                                        (.store
                                                                          ((Light.Expr.op
                                                                              Light.Op.add)
                                                                            (v 9)
                                                                            (k 8))
                                                                          (v 29))
                                                                        (Light.Stmt.seq
                                                                          (.store
                                                                            ((Light.Expr.op
                                                                                Light.Op.add)
                                                                              (v
                                                                                9)
                                                                              (k
                                                                                9))
                                                                            (v
                                                                              30))
                                                                          (Light.Stmt.seq
                                                                            (.store
                                                                              ((Light.Expr.op
                                                                                  Light.Op.add)
                                                                                (v
                                                                                  9)
                                                                                (k
                                                                                  10))
                                                                              (v
                                                                                31))
                                                                            (Light.Stmt.seq
                                                                              (.store
                                                                                ((Light.Expr.op
                                                                                    Light.Op.add)
                                                                                  (v
                                                                                    9)
                                                                                  (k
                                                                                    11))
                                                                                (v
                                                                                  32))
                                                                              (Light.Stmt.seq
                                                                                (.store
                                                                                  ((Light.Expr.op
                                                                                      Light.Op.add)
                                                                                    (v
                                                                                      9)
                                                                                    (k
                                                                                      12))
                                                                                  (v
                                                                                    33))
                                                                                (Light.Stmt.seq
                                                                                  (.store
                                                                                    ((Light.Expr.op
                                                                                        Light.Op.add)
                                                                                      (v
                                                                                        9)
                                                                                      (k
                                                                                        13))
                                                                                    (v
                                                                                      34))
                                                                                  (Light.Stmt.seq
                                                                                    (.store
                                                                                      ((Light.Expr.op
                                                                                          Light.Op.add)
                                                                                        (v
                                                                                          9)
                                                                                        (k
                                                                                          14))
                                                                                      (v
                                                                                        35))
                                                                                    (.set
                                                                                      0
                                                                                      (v
                                                                                        9)))))))))))))))))))))))))))))))))))))))))))

def program : Program := [body]












































































































































end ThreeSum.LightReportingSourceSelect

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightResidues


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def residue (p : ℕ) (c x : ℤ) : ℕ := ((c * x) % (p : ℤ)).toNat











/-- Arguments are source, destination, count, modulus, scratch, sign.
The last two locals are the loop counter and the returned residue. -/
def residuesBody (pEmod : ℕ) : Stmt :=
  .for 6 (v 2) (
    (Light.Stmt.seq
      (.call pEmod
        [(Light.Expr.op Light.Op.mul) (v 5)
            (M ((Light.Expr.op Light.Op.add) (v 0) (v 6))),
          v 3, v 4]
        7)
      (.store ((Light.Expr.op Light.Op.add) (v 1) (v 6)) (v 7))))

def residueBudget (U : ℕ) : ℕ := 43 * (Nat.log 2 (U + 1) + 1) + 34

def residuesTime (n U : ℕ) : ℕ := n * (residueBudget U + 30) + 6








def Inv (μ : ℕ → ℤ) (src dst n p work : ℕ) (c : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src, dst, n, p, work, c, i, r], μ'⟩ ∧
    (∀ j < i, μ' (dst + j) = (residue p c (μ (src + j)) : ℤ)) ∧
    KeptBut μ μ' work dst n
















































































end ThreeSum.LightResidues

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightScaleArray


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightArray
end ThreeSum.LightArray


/-! # A costed array scaling pass -/

namespace ThreeSum.LightScaleArray

open Light ThreeSum.LightArray

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt := pass 4 (v 2) (v 1) (((Light.Expr.op Light.Op.mul) (v 3)
                                         (M ((Light.Expr.op Light.Op.add) (v 0) (v 4)))))

def time (n : ℕ) : ℕ := 18*n+6



























end ThreeSum.LightScaleArray

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSharedReportingLookup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SharedReportingBankAccess
end ThreeSum.SharedReportingBankAccess
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows


/-! # Actual constant-time lookup of one retained shared catalog row -/

namespace ThreeSum.LightSharedReportingLookup

open Light SharedReportingBankRows SharedReportingBankHeader SharedReportingBankAccess

set_option maxHeartbeats 1900000
set_option maxRecDepth 10000

/-- Bank header, decoded occurrence code, B band, C band. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 4 (M (v 0)))
    (Light.Stmt.seq (.set 5 (M ((Light.Expr.op Light.Op.add) (v 0) (k 2))))
      (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 0) (k 4))))
        (Light.Stmt.seq (.set 7 (M ((Light.Expr.op Light.Op.add) (v 0) (k 5))))
          (Light.Stmt.seq
            (.set 8
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.mul) (v 1) (v 6)) (v 2)))
            (Light.Stmt.seq
              (.set 9
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.mul) (v 8) (v 7)) (v 3)))
              (.set 0
                ((Light.Expr.op Light.Op.add) (v 4)
                  ((Light.Expr.op Light.Op.mul)
                    ((Light.Expr.op Light.Op.mul) (k 5) (v 5)) (v 9))))))))))

def program : Program := [body]

































































end ThreeSum.LightSharedReportingLookup

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSign


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Exact alternating signs by a bounded coordinate-count loop -/

namespace ThreeSum.LightSign

open Light

variable {lim : Limits} {P : Program}

/-- Arguments: signed value and a nonnegative exponent. -/
def body : Stmt := .for 2 (v 1) (.set 0 (((Light.Expr.op Light.Op.sub) (k 0) (v 0))))

def time (e : ℕ) : ℕ := 20*e+20

def Inv (μ : ℕ → ℤ) (x : ℤ) (e j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [(-1 : ℤ)^j*x,e,j],μ⟩








































end ThreeSum.LightSign

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSignedLeaf


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
# Evaluating one signed leaf by actual stored suffix-stage reads

The program forms the two disjoint prefix unions by integer addition,
computes both compact addresses, reads both stored transform cells, takes
their product, and applies the exact alternating sign. All arithmetic
bounds follow from the original histogram bounds.
-/

namespace ThreeSum.LightSignedLeaf

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Width, source cutoff, suffix stage, left prefix cardinality and mask,
right prefix cardinality and mask, leaf cardinality and mask, two source
stage-array bases, polynomial scratch. -/
def body (pLookup pSign : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pLookup
      [v 0, v 1, (Light.Expr.op Light.Op.add) (v 3) (v 7),
        (Light.Expr.op Light.Op.add) (v 4) (v 8), v 2, v 9, v 11]
      12)
    (Light.Stmt.seq
      (.call pLookup
        [v 0, v 1, (Light.Expr.op Light.Op.add) (v 5) (v 7),
          (Light.Expr.op Light.Op.add) (v 6) (v 8), v 2, v 10, v 11]
        13)
      (Light.Stmt.seq (.set 14 ((Light.Expr.op Light.Op.mul) (v 12) (v 13)))
        (.call pSign [v 14, v 7] 0))))























































































































end ThreeSum.LightSignedLeaf

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSmallDivide


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Exact natural quotient by a small counting loop

This helper is used for size parameters whose numerator is logarithmic in
the original input length. Its time is linear in the quotient, explicitly
charged below. A zero divisor returns zero, matching natural division.
-/

namespace ThreeSum.LightSmallDivide

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 1)))
    ((Light.Stmt.seq (.set 2 (k 0))
       (Light.Stmt.seq
         (.while
           (Light.Cond.le
             ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 2) (k 1))
               (v 1))
             (v 0))
           (.set 2 ((Light.Expr.op Light.Op.add) (v 2) (k 1))))
         (.set 0 (v 2)))))
    (.set 0 (k 0))

def time (a b : ℕ) : ℕ := 20*(a/b+1)+20


































































end ThreeSum.LightSmallDivide

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceBandHistSelect


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
end ThreeSum.SourceBandPairSlices


/-! # Actual constant-time retained histogram selection with empty padding -/

namespace ThreeSum.LightSourceBandHistSelect

open Light BandPartition SourceBandPairData SourceBandPairSlices

set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

def finishBody : Stmt := (Light.Stmt.seq (.store (v 2) (v 3))
                           (.store ((Light.Expr.op Light.Op.add) (v 2) (k 1)) (v 4)))

def rightBody : Stmt :=
  (Light.Stmt.seq
    (.ite (Light.Cond.lt (v 1) (M ((Light.Expr.op Light.Op.add) (v 0) (k 3))))
      (.set 4
        (M
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add)
              (M ((Light.Expr.op Light.Op.add) (v 0) (k 2)))
              ((Light.Expr.op Light.Op.mul) (k 6) (v 1)))
            (k 3))))
      .skip)
    finishBody)

/-- The pair-catalog header, common band index, and two temporary cells. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 3 (M ((Light.Expr.op Light.Op.add) (v 0) (k 4))))
    (Light.Stmt.seq (.set 4 (M ((Light.Expr.op Light.Op.add) (v 0) (k 4))))
      (Light.Stmt.seq
        (.ite (Light.Cond.lt (v 1) (M ((Light.Expr.op Light.Op.add) (v 0) (k 1))))
          (.set 3
            (M
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (M (v 0))
                  ((Light.Expr.op Light.Op.mul) (k 6) (v 1)))
                (k 3))))
          .skip)
        rightBody)))

variable {lim : Limits} {P : Program} {d : ℕ}















































































































end ThreeSum.LightSourceBandHistSelect

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceControlsMax


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Scalar maximum for exact shared-bank dimensions -/

namespace ThreeSum.LightSourceControlsMax

open Light

def body : Stmt := .ite ((Light.Cond.lt (v 0) (v 1))) (.set 0 (v 1)) (.set 0 (v 0))

variable {lim : Limits} {P : Program} {d : ℕ}


















end ThreeSum.LightSourceControlsMax

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceControlsSpan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.SourceControlLayout
end ThreeSum.SourceControlLayout


/-! # Actual arithmetic computation of the exact source-bank span -/

namespace ThreeSum.LightSourceControlsSpan

open Light SourceControlLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

/-- J, total width, compact capacity, occurrence count, and the two
logarithms needed by the retained stage workspace. -/
def body (pMax : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.add) (v 1) (k 1)))
    (Light.Stmt.seq
      (.set 7
        ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v 6) (v 6))
          (v 6)))
      (Light.Stmt.seq
        (.call pMax [v 7, (Light.Expr.op Light.Op.add) (v 5) (k 2)] 8)
        (Light.Stmt.seq
          (.call pMax [v 8, (Light.Expr.op Light.Op.add) (v 4) (k 5)] 9)
          (Light.Stmt.seq
            (.call pMax [v 9, (Light.Expr.op Light.Op.add) (v 0) (k 1)] 10)
            (Light.Stmt.seq
              (.set 11
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.mul) (k 5) (v 2))
                      ((Light.Expr.op Light.Op.mul) (k 2) (v 1)))
                    (k 4))
                  ((Light.Expr.op Light.Op.mul)
                    ((Light.Expr.op Light.Op.mul) (k 2) (v 6)) (v 2))))
              (.set 0
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add)
                        ((Light.Expr.op Light.Op.mul) (v 3) (v 11)) (v 2))
                      (v 1))
                    (k 2))
                  (v 10)))))))))

variable {lim : Limits} {P : Program} {d : ℕ}










































































end ThreeSum.LightSourceControlsSpan

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceFlagTest


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Independent cardinality-and-bucket trimming test -/

namespace ThreeSum.LightSourceFlagTest

open Light

def flag (card required count cap : ℕ) : ℕ :=
  if card=required ∧ count≤cap then 1 else 0










def body : Stmt :=
  .ite ((Light.Cond.eq (v 0) (v 1)))
    (.ite ((Light.Cond.le (v 2) (v 3))) (.set 0 (k 1)) (.set 0 (k 0)))
    (.set 0 (k 0))

def time : ℕ := 25

variable {lim : Limits} {P : Program} {d : ℕ}






















end ThreeSum.LightSourceFlagTest

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSourceRowScan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Counting and hashing one physical block row

A single scan of the Boolean row constructs its cardinality and both raw
one-hot hashes. The two orientations are accumulated independently from the
stored unscaled map rows. All arithmetic is explicitly word bounded.
-/

namespace ThreeSum.LightSourceRowScan

open Light Finset
open scoped BigOperators

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def count (bits : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, bits i

def hash (bits w0 w1 : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, if bits i=1 then w1 i else w0 i

































def roundBody : Stmt :=
  (Light.Stmt.seq (.set 9 (M ((Light.Expr.op Light.Op.add) (v 0) (v 8))))
    (Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.add) (v 5) (v 9)))
      (.ite (Light.Cond.eq (v 9) (k 1))
        (Light.Stmt.seq
          (.set 6
            ((Light.Expr.op Light.Op.add) (v 6)
              (M ((Light.Expr.op Light.Op.add) (v 2) (v 8)))))
          (.set 7
            ((Light.Expr.op Light.Op.add) (v 7)
              (M ((Light.Expr.op Light.Op.add) (v 1) (v 8))))))
        (Light.Stmt.seq
          (.set 6
            ((Light.Expr.op Light.Op.add) (v 6)
              (M ((Light.Expr.op Light.Op.add) (v 1) (v 8)))))
          (.set 7
            ((Light.Expr.op Light.Op.add) (v 7)
              (M ((Light.Expr.op Light.Op.add) (v 2) (v 8)))))))))

/-- Arguments: Boolean row, zero coefficients, one coefficients, width,
and three-cell output (cardinality, left hash, right hash). -/
def body : Stmt :=
  (Light.Stmt.seq (.set 5 (k 0))
    (Light.Stmt.seq (.set 6 (k 0))
      (Light.Stmt.seq (.set 7 (k 0))
        (Light.Stmt.seq (.for 8 (v 3) roundBody)
          (Light.Stmt.seq (.store (v 4) (v 5))
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 4) (k 1)) (v 6))
              (.store ((Light.Expr.op Light.Op.add) (v 4) (k 2)) (v 7))))))))

def time (L : ℕ) : ℕ := 150*L+100
def word (L U : ℕ) : ℕ := (L+1)*(U+1)+1

variable {lim : Limits} {P : Program} {d : ℕ}






































































































end ThreeSum.LightSourceRowScan

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSubsetAddress


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal

variable {lim : Limits} {P : Program}

def Powers (μ : ℕ → ℤ) (base W : ℕ) : Prop :=
  ∀ i ≤ W, μ (base+i) = ((2^i : ℕ) : ℤ)













/-- Arguments: remaining width, cardinality, mask, original width,
Pascal table, and power table. The seventh local stores the next bit index.
The return value replaces the first argument. -/
def rankBody (pSelf : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 0)))
    ((Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.sub) (v 0) (k 1)))
       (.ite (Light.Cond.lt (v 2) (M ((Light.Expr.op Light.Op.add) (v 5) (v 6))))
         (.call pSelf [v 6, v 1, v 2, v 3, v 4, v 5] 0)
         (Light.Stmt.seq
           (.call pSelf
             [v 6, (Light.Expr.op Light.Op.sub) (v 1) (k 1),
               (Light.Expr.op Light.Op.sub) (v 2)
                 (M ((Light.Expr.op Light.Op.add) (v 5) (v 6))),
               v 3, v 4, v 5]
             0)
           (.set 0
             ((Light.Expr.op Light.Op.add) (v 0)
               (M
                 ((Light.Expr.op Light.Op.add)
                   ((Light.Expr.op Light.Op.add) (v 4)
                     ((Light.Expr.op Light.Op.mul) (v 6)
                       ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                   (v 1)))))))))
    (.set 0 (k 0))

def rankTime (L : ℕ) : ℕ := 100*L+30





































































































end ThreeSum.LightSubsetAddress

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSubsetOffset


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


/-! # The layer-offset scan for compact downset addresses -/

namespace ThreeSum.LightSubsetOffset

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program} {d : ℕ}









def body : Stmt :=
  (Light.Stmt.seq (.set 5 (k 0))
    (Light.Stmt.seq
      (.for 4 (v 2)
        (.set 5
          ((Light.Expr.op Light.Op.add) (v 5)
            (M
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 0)
                  ((Light.Expr.op Light.Op.mul) (v 1)
                    ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
                (v 4))))))
      (.set 0 (v 5))))

def time (k : ℕ) : ℕ := 30*k+20

























































end ThreeSum.LightSubsetOffset

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSupportMark


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# A Boolean support table with repeated keys

The routine clears the destination, then marks a key only when its validity
flag is one. Repeated retained representations set the same bit; this is
the support operation needed for a local hash-cover row.
-/

namespace ThreeSum.LightSupportMark

open Light Finset

def Hit (key valid : ℕ → ℕ) (r i : ℕ) : Prop :=
  ∃ j ∈ range i, valid j = 1 ∧ key j = r

instance (key valid : ℕ → ℕ) (r i : ℕ) : Decidable (Hit key valid r i) := by
  unfold Hit
  infer_instance

def bit (key valid : ℕ → ℕ) (r i : ℕ) : ℕ := if Hit key valid r i then 1 else 0

































def markBody : Stmt :=
  .for 5 (v 3) (
    .ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v 1) (v 5))) (k 1)))
      (.store (((Light.Expr.op Light.Op.add) (v 2)
                 (M ((Light.Expr.op Light.Op.add) (v 0) (v 5))))) (k 1)) .skip)

def markTime (n : ℕ) : ℕ := 40*n+6

variable {lim : Limits} {P : Program} {d : ℕ}





















































def body (pFill : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pFill [v 2, v 4, k 0] 6) markBody)

def time (n p : ℕ) : ℕ := fillTime p+markTime n+10


































end ThreeSum.LightSupportMark

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSwitch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Execute the exact cubic switch in the benchmark language

The fixed procedure increases q from zero until the first accepted integer.
At every prescribed reporting depth that integer exists, including when
the residual is zero. Memory is unchanged and all scalar intermediates fit
the explicit polynomial word bound.
-/

namespace ThreeSum.LightSwitch

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def test : Cond :=
  (Light.Cond.lt
    ((Light.Expr.op Light.Op.mul)
      ((Light.Expr.op Light.Op.mul) (k 10)
        ((Light.Expr.op Light.Op.sub) (v 0) (v 1)))
      ((Light.Expr.op Light.Op.mul) (v 3)
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.mul)
            ((Light.Expr.op Light.Op.mul) (k 799) (v 2)) (v 2))
          ((Light.Expr.op Light.Op.mul) (v 3)
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.mul) (k 72) (v 2))
              ((Light.Expr.op Light.Op.mul) (k 24) (v 3)))))))
    ((Light.Expr.op Light.Op.mul)
      ((Light.Expr.op Light.Op.mul)
        ((Light.Expr.op Light.Op.mul)
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.mul) (k 291) (v 0))
            ((Light.Expr.op Light.Op.mul) (k 1000) (v 1)))
          (v 2))
        (v 2))
      (v 2)))

def body : Stmt :=
  (Light.Stmt.seq (.set 3 (k 0))
    (Light.Stmt.seq
      (.while test (.set 3 ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
      (.set 0 (v 3))))

def time (r : ℕ) : ℕ := 100*(r+1)+50

variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}































































def program : Program := [body]

















end ThreeSum.LightSwitch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSwitchBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Finite scalar bounds and minimality for the executed cubic switch

These are the exact cleared integer comparisons of `Switch.switchIndex`.
No real arithmetic is executed by the eventual program.
-/

namespace ThreeSum.LightSwitch

open Light

set_option maxHeartbeats 1800000

def left (J j r : ℕ) : ℕ := (291*J+1000*j)*r*r*r
def cubic (r q : ℕ) : ℕ := q*(799*r*r+q*(72*r+24*q))
def factor (J j : ℕ) : ℕ := 10*(J-j)
def word (J r : ℕ) : ℕ := (J+r+1001)^64













































end ThreeSum.LightSwitch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightSwitchScalar


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Structural safety for the fixed scalar expressions of the cubic switch -/

namespace ThreeSum.LightSwitchScalar

open Light

set_option maxHeartbeats 1600000

def Small (B : ℕ) : Expr → Prop
  | .const n => n ≤ B
  | .var _ => True
  | .op _ a b => Small B a ∧ Small B b
  | .load _ => False






























































end ThreeSum.LightSwitchScalar

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightTrimTest


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # The exact local retained-edge test -/

namespace ThreeSum.LightTrimTest

open Light

def flag (overlap leftCount rightCount cap : ℕ) : ℕ :=
  if overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap then 1 else 0










def body : Stmt :=
  .ite ((Light.Cond.eq (v 0) (k 0)))
    (.ite ((Light.Cond.le (v 1) (v 3)))
      (.ite ((Light.Cond.le (v 2) (v 3))) (.set 0 (k 1)) (.set 0 (k 0)))
      (.set 0 (k 0)))
    (.set 0 (k 0))

def time : ℕ := 30

variable {lim : Limits} {P : Program} {d : ℕ}



























end ThreeSum.LightTrimTest

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWantedRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Append an entire matching residue fiber as original-position pairs

The row performs exactly one iteration per matching right index. It writes
interleaved original left/right positions and preserves every earlier row.
-/

namespace ThreeSum.LightWantedRow

open Light

set_option maxHeartbeats 900000

/-- Left position, right-index array, fiber start/length, output base,
and number of pairs already written. -/
def body : Stmt :=
  .for 6 (v 3) (
    (Light.Stmt.seq
      (.store
        ((Light.Expr.op Light.Op.add) (v 4)
          ((Light.Expr.op Light.Op.mul) (k 2)
            ((Light.Expr.op Light.Op.add) (v 5) (v 6))))
        (v 0))
      (.store
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v 4)
            ((Light.Expr.op Light.Op.mul) (k 2)
              ((Light.Expr.op Light.Op.add) (v 5) (v 6))))
          (k 1))
        (M
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 1) (v 2))
            (v 6))))))

def time (n : ℕ) : ℕ := 120*n+20

def Inv (μ : ℕ → ℤ) (left src start n dst previous j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ=⟨frame [left,src,start,n,dst,previous,j],ν⟩ ∧
    (∀ t < j, ν (dst+2*(previous+t))=(left : ℤ) ∧
      ν (dst+2*(previous+t)+1)=μ (src+start+t)) ∧
    SameOutside μ ν (dst+2*previous) (2*n)

variable {lim : Limits} {P : Program} {d : ℕ}






















































end ThreeSum.LightWantedRow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightWeightGather


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Gathering selected coefficient rows

The selection array contains ordinary candidate indices. This fixed program
reads each selected index and copies its whole coefficient row into the
corresponding schedule occurrence. Repeated selections are retained.
-/

namespace ThreeSum.LightWeightGather

open Light

set_option maxHeartbeats 1000000

def body (pCopy : ℕ) : Stmt :=
  .for 5 (v 3) (
    (Light.Stmt.seq (.set 6 (M ((Light.Expr.op Light.Op.add) (v 0) (v 5))))
      (.call pCopy
        [(Light.Expr.op Light.Op.add) (v 1)
            ((Light.Expr.op Light.Op.mul) (v 6) (v 4)),
          (Light.Expr.op Light.Op.add) (v 2)
            ((Light.Expr.op Light.Op.mul) (v 5) (v 4)),
          v 4]
        7)))

def time (rows width : ℕ) : ℕ := rows*(copyTime width+100)+6
def word (N rows width : ℕ) : ℕ := N+rows+width+1

def Inv (μ : ℕ → ℤ) (indices src dst rows width : ℕ) (select : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (x r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [indices,src,dst,rows,width,i,x,r],μ'⟩ ∧
    (∀ j < i, ∀ a < width, μ' (dst+j*width+a) = μ (src+select j*width+a)) ∧
    SameOutside μ μ' dst (rows*width)

structure Procs (P : Program) (pMain : ℕ) where
  pCopy : ℕ
  copy : P[pCopy]? = some copyBody
  main : P[pMain]? = some (body pCopy)

variable {lim : Limits} {P : Program} {d : ℕ}














































































end ThreeSum.LightWeightGather

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LocalParameterBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds

open LocalCoverBounds

set_option maxHeartbeats 1000000

def base (h : ℕ) : ℕ := 2^(2048*(h+1))
def envelope (h : ℕ) : ℕ := 2^(2048*(h+1)+2)



















































































































































































end ThreeSum.LocalParameterBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ModuloCosts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface


/-!
# Finite arithmetic-operation bounds for the complete counting backend

The only input-size dependence outside the Karatsuba term is the number of
original elements times their remainder bit budget. Histogram initialization,
capacity computation and folding are included in the displayed constant.
-/

namespace ThreeSum.ModuloCosts

open KaratsubaInterface

def roundedPower (p : ℕ) : ℕ := 3 ^ Nat.clog 2 p













































end ThreeSum.ModuloCosts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ModuloCounts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram


/-!
# Modular triple counts from the original integer arrays

This interface identifies the executable histogram/correlation lookup with
the exact `Arithmetic.modCount` used in the weighted false-triple argument.
The three indices retain their multiplicities even when input values repeat.
-/

namespace ThreeSum.ModuloCounts

open Finset LightResidueHistogram
open scoped BigOperators

def triples (nA nB nC : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  range nA ×ˢ (range nB ×ˢ range nC)

def difference (a b c : ℕ → ℤ) (t : ℕ × ℕ × ℕ) : ℤ :=
  c t.2.2 - b t.2.1 - a t.1

def count (p nA nB nC : ℕ) (a b c : ℕ → ℤ) : ℕ :=
  Arithmetic.modCount (triples nA nB nC) (difference a b c) (p : ℤ)


























































end ThreeSum.ModuloCounts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_OutputDecodeOccurrenceCode


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords


/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode

open OutputDecodeOrder OutputDecodeRecords GlobalEncoding

set_option maxHeartbeats 1500000

def code (T M : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | J+1,k => (k%(T*M))/M+T*code T M J (k/(T*M))
























































end ThreeSum.OutputDecodeOccurrenceCode

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_OutputDecodeOrder


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists


/-!
# Exact physical tuple indices for output decoding

The product enumerator is lexicographic: its first block is the outermost
choice. Repeated integer key values have no role in these index equations.
The recursive decoder takes the final coordinate by division and remainder.
-/

namespace ThreeSum.OutputDecodeOrder

open RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 6000

variable {α β : Type*}

theorem getD_flatMap_uniform (xs : List α) (f : α → List β) (q : ℕ)
    (hf : ∀ x ∈ xs, (f x).length=q) (da : α) (db : β)
    {z r : ℕ} (hz : z < xs.length) (hr : r < q) :
    (xs.flatMap f).getD (z*q+r) db = (f (xs.getD z da)).getD r db := by
  induction xs generalizing z with
  | nil => simp at hz
  | cons x xs ih =>
    have hlen : (f x).length=q := hf x (by simp)
    have htail : ∀ a ∈ xs, (f a).length=q := fun a ha => hf a (by simp [ha])
    cases z with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.getD_cons_zero,List.flatMap_cons]
      exact List.getD_append _ _ _ _ (by omega)
    | succ z =>
      have hz' : z < xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hz
      have hoff : (z+1)*q+r-q=z*q+r := by simp only [Nat.add_mul,one_mul]; omega
      rw [List.flatMap_cons,List.getD_append_right _ _ _ _ (by
        rw [hlen]
        simp only [Nat.succ_eq_add_one,Nat.add_mul,one_mul]
        omega),hlen]
      rw [hoff,List.getD_cons_succ]
      exact ih htail hz'





















def indices (m : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | J+1,k => indices m J (k/m)++[k%m]

theorem indices_length (m J k : ℕ) : (indices m J k).length=J := by
  induction J generalizing k with
  | zero => rfl
  | succ J ih => simp [indices,ih]

theorem indices_lt {m : ℕ} (hm : 0 < m) (J k : ℕ) :
    ∀ a ∈ indices m J k, a < m := by
  induction J generalizing k with
  | zero => simp [indices]
  | succ J ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ih _ a ha
    · have he : a=k%m := by simpa using ha
      subst a
      exact Nat.mod_lt _ hm

theorem indices_getD_lt {m J k j : ℕ} (hm : 0 < m) (hj : j < J) :
    (indices m J k).getD j 0 < m := by
  rw [List.getD_eq_getElem _ _ (by rw [indices_length]; exact hj)]
  exact indices_lt hm J k _ (List.getElem_mem _)








































end ThreeSum.OutputDecodeOrder

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostRelocation


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation

open Light

@[simp] def relocate (offset : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (relocate offset s) (relocate offset t)
  | .ite c s t => .ite c (relocate offset s) (relocate offset t)
  | .while c s => .while c (relocate offset s)
  | .call p args x => .call (offset+p) args x

def program (prefixProgram P : Program) : Program := prefixProgram ++ P.map (relocate prefixProgram.length)

































end ThreeSum.ReportingHostRelocation

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_ReportingHostSourceSelection


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Fifteen retained controls selected for one owner and occurrence -/

namespace ThreeSum.ReportingHostSourceSelection

open Light

set_option maxHeartbeats 1600000

structure Pointers where
  leftHeaders : ℕ
  rightHeaders : ℕ
  firstBank : ℕ
  bankSpan : ℕ
  occurrenceBase : ℕ
  startL : ℕ
  startR : ℕ
  sizeL : ℕ
  sizeR : ℕ
  offsetsL : ℕ
  flatL : ℕ
  offsetsR : ℕ
  flatR : ℕ
  stagesL : ℕ
  stagesR : ℕ
  maps : ℕ
  candidates : ℕ
  histL : ℕ
  histR : ℕ

def leftHead (X : Pointers) (i : ℕ) : ℕ := X.leftHeaders+6*i
def rightHead (X : Pointers) (j : ℕ) : ℕ := X.rightHeaders+6*j
def leftStageCell (X : Pointers) (i code : ℕ) : ℕ := X.firstBank+i*X.bankSpan+2*code
def rightStageCell (X : Pointers) (j code : ℕ) : ℕ := X.firstBank+j*X.bankSpan+2*code+1
def occurrenceRow (X : Pointers) (code J : ℕ) : ℕ := X.occurrenceBase+code*J

def values (X : Pointers) (srcB srcC code J : ℕ) : List ℕ :=
  [srcB+X.startL,srcC+X.startR,X.offsetsL,X.flatL,X.offsetsR,X.flatR,
    X.sizeL,X.sizeR,X.stagesL,X.stagesR,occurrenceRow X code J,
    X.maps,X.candidates,X.histL,X.histR]

structure HeaderReads (μ : ℕ→ℤ) (X : Pointers) (pair bank cover i j code : ℕ) : Prop where
  leftHeaders : μ pair=(X.leftHeaders : ℤ)
  rightHeaders : μ (pair+2)=(X.rightHeaders : ℤ)
  firstBank : μ bank=(X.firstBank : ℤ)
  bankSpan : μ (bank+2)=(X.bankSpan : ℤ)
  occurrenceBase : μ (bank+4)=(X.occurrenceBase : ℤ)
  startL : μ (leftHead X i)=(X.startL : ℤ)
  sizeL : μ (leftHead X i+1)=(X.sizeL : ℤ)
  offsetsL : μ (leftHead X i+4)=(X.offsetsL : ℤ)
  flatL : μ (leftHead X i+5)=(X.flatL : ℤ)
  startR : μ (rightHead X j)=(X.startR : ℤ)
  sizeR : μ (rightHead X j+1)=(X.sizeR : ℤ)
  offsetsR : μ (rightHead X j+4)=(X.offsetsR : ℤ)
  flatR : μ (rightHead X j+5)=(X.flatR : ℤ)
  stagesL : μ (leftStageCell X i code)=(X.stagesL : ℤ)
  stagesR : μ (rightStageCell X j code)=(X.stagesR : ℤ)
  maps : μ (cover+12)=(X.maps : ℤ)
  candidates : μ (cover+13)=(X.candidates : ℤ)
  histL : μ (cover+14)=(X.histL : ℤ)
  histR : μ (cover+15)=(X.histR : ℤ)









/-- Individual address and scalar bounds for the fixed selector. Each translated
pointer occurs in its own bound, so an arbitrary already occupied prefix is
charged only once by callers. -/
structure Fits (X : Pointers) (pair bank cover srcB srcC i j code J dst stop : ℕ) : Prop where
  pair : pair+3≤stop
  bank : bank+5≤stop
  cover : cover+16≤stop
  output : dst+15≤stop
  leftHead : leftHead X i+6≤stop
  rightHead : rightHead X j+6≤stop
  leftStage : leftStageCell X i code+1≤stop
  rightStage : rightStageCell X j code+1≤stop
  occurrence : occurrenceRow X code J≤stop
  scalars : J+X.bankSpan+20≤stop
  values : ∀ v∈values X srcB srcC code J, v≤stop

















end ThreeSum.ReportingHostSourceSelection

end


