-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle02
-- name    : ThreeSum1962Source_Bundle02
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T05:33:45.044099+00:00
-- url     : https://prove2.me/theorems/ed6c744e-8eb4-4023-bdcc-72f80812a948
-- title:
--   Array scans, reporting primitives, and resource parameters
-- statement:
--   This bundle defines Light program bodies for array arithmetic, Boolean dot products, histogram construction, table-lookup sums, minimum selection, natural powers, mask operations and one-hot hash evaluation. Its reporting routines include affine scans, original-value bucket tests, positive-count filtering and color-class extraction. For a natural count array \(c\), the selected-index list is
--   $$
--   [i\mid 0\le i<n,\ c(i)>0],
--   $$
--   in increasing index order. The definitions also specify argument and scratch layouts, loop invariants, time expressions, retained-memory conditions, source widths and endpoint bounds, and local-cover resource envelopes. These supply concrete bodies and specifications for subsequent execution contracts.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/KaratsubaInterface.lean#L17-L17
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightArray.lean#L17-L32
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandPrimeDepth.lean#L19-L107
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawARow.lean#L18-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandWeightedScoreSlice.lean#L11-L17
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockQuery.lean#L21-L23
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceBuild.lean#L20-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBooleanDot.lean#L17-L44
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCapacity.lean#L17-L25
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightClassFilter.lean#L17-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorParameters.lean#L22-L41
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverUpdate.lean#L9-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightDenseGuard.lean#L16-L47
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorResult.lean#L9-L27
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorWantedHeader.lean#L12-L26
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightExplicitSum.lean#L50-L60
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightHistogram.lean#L19-L101
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLeafSum.lean#L40-L51
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverHashHistogram.lean#L16-L17
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverInitResources.lean#L13-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverResources.lean#L20-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLookupSum.lean#L17-L46
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMaskErase.lean#L17-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMinimum.lean#L15-L61
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightNatPower.lean#L17-L71
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOneHot.lean#L22-L36
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightRadixDigit.lean#L9-L15
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingAffine.lean#L11-L14
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingBucketRow.lean#L19-L52
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingFilter.lean#L17-L57

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
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_KaratsubaInterface


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba


/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface

open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial

def capacity (p : ℕ) : ℕ := 2 ^ Nat.clog 2 p

























































































end ThreeSum.KaratsubaInterface

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightArray


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Reading a source in place is safe because each pass writes only earlier
indices.  Disjoint sources are safe as well. -/
def SourceSafe (src dst n : ℕ) : Prop := src = dst ∨ Apart src n dst n








/-- linear(srcA, srcB, dst, n, c): dst[i] := srcA[i] + c*srcB[i]. -/
def linearBody : Stmt :=
  pass 5 (v 3) (v 2) (((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v 0) (v 5)))
                        ((Light.Expr.op Light.Op.mul) (v 4)
                          (M ((Light.Expr.op Light.Op.add) (v 1) (v 5))))))

def linearTime (n : ℕ) : ℕ := 23 * n + 6


























































end ThreeSum.LightArray

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandPrimeDepth


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Compute the prescribed common-prime depth without division

The loop compares successive `4*(4*y)^(i+1)` with the radix. It returns
exactly `Nat.log (4*y) (R/4)`, including the zero-depth case. Only local
variables change, and the number of iterations is that logarithm.
-/

namespace ThreeSum.LightBandPrimeDepth

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

def depth (R y : ℕ) : ℕ := Nat.log (4*y) (R/4)

def body : Stmt :=
  (Light.Stmt.seq (.set 2 (k 0))
    (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.mul) (k 16) (v 1)))
      (Light.Stmt.seq
        (.while (Light.Cond.le (v 3) (v 0))
          (Light.Stmt.seq
            (.set 3
              ((Light.Expr.op Light.Op.mul)
                ((Light.Expr.op Light.Op.mul) (k 4) (v 1)) (v 3)))
            (.set 2 ((Light.Expr.op Light.Op.add) (v 2) (k 1)))))
        (.set 0 (v 2)))))

def time (R y : ℕ) : ℕ := 30*depth R y+30
def word (R y : ℕ) : ℕ := 4*y*(R+4)+R+8

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}










































































def program : Program := [body]








end ThreeSum.LightBandPrimeDepth

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandRawARow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# One actual A-band incidence row

Values are copied from the retained sorted A segment. Parallel arrays
receive the physical owner slot and the sorted-array coordinate.
-/

namespace ThreeSum.LightBandRawARow

open Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

/-- Source, value output, owner output, position output, length, owner, start. -/
def body (pCopy pFill : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCopy [v 0, v 1, v 4] 7)
    (Light.Stmt.seq (.call pFill [v 2, v 4, v 5] 7)
      (pass 8 (v 4) (v 3) ((Light.Expr.op Light.Op.add) (v 6) (v 8)))))

def time (n : ℕ) : ℕ := copyTime n+fillTime n+30*n+100

def KeptOthers (μ ν : ℕ → ℤ) (values owners positions n : ℕ) : Prop :=
  SameOn (fun a => Outside values n a ∧ Outside owners n a ∧ Outside positions n a) μ ν

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src values owners positions n owner start : ℕ}






































end ThreeSum.LightBandRawARow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBandWeightedScoreSlice


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Constant-time exact truncated band lengths for weighted-score calls -/

namespace ThreeSum.LightBandWeightedScoreSlice

open Light

set_option maxHeartbeats 900000

def body : Stmt :=
  (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.mul) (v 2) (v 1)))
    (Light.Stmt.seq (.set 4 ((Light.Expr.op Light.Op.sub) (v 0) (v 3)))
      (Light.Stmt.seq (.ite (Light.Cond.lt (v 1) (v 4)) (.set 4 (v 1)) .skip)
        (.set 0 (v 4)))))

def time : ℕ := 80

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}































end ThreeSum.LightBandWeightedScoreSlice

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockQuery


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
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# The actual sparse-query machine returns the original raw prefix mass

All coordinate transport, prefix sizes, source bounds, and cutoff facts
are discharged for the concrete block histograms. The remaining storage
premises are precisely the arrays produced by source and box preprocessing.
-/

namespace ThreeSum.LightBlockQuery

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts

variable {lim : Limits} {P : Program}

abbrev width (h J : ℕ) : ℕ := J*(512*h)
abbrev sourceCut (h J : ℕ) : ℕ := 2*h*J
abbrev residualSize (h J k : ℕ) : ℕ := (J-k)*(2*h)





section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]






























































































































end OriginalIndices

end ThreeSum.LightBlockQuery

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBlockSourceBuild


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
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Original block-source multiplicities from the costed constructor

These contracts specialize the actual histogram-and-gather program to the
unchanged block encoding. Endpoint bounds follow from the constructed
coefficient rows; they are not extra semantic assumptions about the encoder.
The original input enumeration explicitly retains individual incidences.
-/

namespace ThreeSum.LightBlockSourceBuild

open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds

set_option maxHeartbeats 1500000

def endpointBound (h J : ℕ) : ℕ := J*(512*h)*(localPrime h^J*localPrime h)
















































variable {lim : Limits} {P : Program} {d : ℕ}
































































end ThreeSum.LightBlockSourceBuild

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightBooleanDot


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# A checked Boolean inner product

The local-cover search uses this literal memory scan to count targets
covered by a candidate and still active. No set-cardinality oracle is an
instruction of the program.
-/

namespace ThreeSum.LightBooleanDot

open Light Finset
open scoped BigOperators

def dot (f g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, f i * g i


















def loopBody : Stmt :=
  .set 3 (((Light.Expr.op Light.Op.add) (v 3)
            ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v 0) (v 4)))
              (M ((Light.Expr.op Light.Op.add) (v 1) (v 4))))))

def body : Stmt :=
  (Light.Stmt.seq (.set 3 (k 0))
    (Light.Stmt.seq (.for 4 (v 2) loopBody) (.set 0 (v 3))))

def time (n : ℕ) : ℕ := 32*n+20

variable {lim : Limits} {P : Program} {d : ℕ}



























































end ThreeSum.LightBooleanDot

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCapacity


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface


/-!
# Computing the polynomial capacity in the benchmark language

This is the doubling loop used by the upstream `clog2` procedure, with its
power returned instead of its exponent. The actual machine therefore computes
the requested power-of-two capacity; the capacity is not supplied as advice.
-/

namespace ThreeSum.LightCapacity

open Light ThreeSum.KaratsubaInterface

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  (Light.Stmt.seq (.set 1 (k 0))
    (Light.Stmt.seq (.set 2 (k 1))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v 2) (v 0))
          (Light.Stmt.seq (.set 2 ((Light.Expr.op Light.Op.add) (v 2) (v 2)))
            (.set 1 ((Light.Expr.op Light.Op.add) (v 1) (k 1)))))
        (.set 0 (v 2)))))

def time (p : ℕ) : ℕ := 12 * Nat.clog 2 p + 10










































end ThreeSum.LightCapacity

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightClassFilter


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000

def items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) : List ℤ :=
  ((List.range n).filter fun i => decide (color i = want)).map fun i => scale*x i


















def roundBody : Stmt :=
  .ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v 1) (v 7))) (v 4)))
    ((Light.Stmt.seq
       (.store
         ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v 2) (k 1))
           (v 6))
         ((Light.Expr.op Light.Op.mul) (v 5)
           (M ((Light.Expr.op Light.Op.add) (v 0) (v 7)))))
       (.set 6 ((Light.Expr.op Light.Op.add) (v 6) (k 1))))) .skip

/-- Source, color array, output header, input length, desired color, sign. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 6 (k 0))
    (Light.Stmt.seq (.for 7 (v 3) roundBody)
      (Light.Stmt.seq (.store (v 2) (v 6)) (.set 0 (v 6)))))

def time (n : ℕ) : ℕ := 100*n+100

def Inv (μ : ℕ → ℤ) (x : ℕ → ℤ) (color : ℕ → ℕ)
    (src colors dst n want : ℕ) (scale : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ,
    σ = ⟨frame [src,colors,dst,n,want,scale,(items x color want scale j).length,j],ν⟩ ∧
    Seg ν (dst+1) (items x color want scale j) ∧ SameOutside μ ν dst (n+1)

variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightColorParameters


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters


/-!
# Execute one coloring-parameter slot

Five exact scalar divisions recover the two binary coordinates and four
ternary colors. Only six output cells are written, so the outer color loop
can reuse this record. The complete family has only polynomially many slots
in the binary index width.
-/

namespace ThreeSum.LightColorParameters

open Light ColorParameters

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

def body (pDivide : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDivide [v 1, k 3] 3)
    (Light.Stmt.seq (.call pDivide [v 3, k 3] 4)
      (Light.Stmt.seq (.call pDivide [v 4, k 3] 5)
        (Light.Stmt.seq (.call pDivide [v 5, k 3] 6)
          (Light.Stmt.seq (.call pDivide [v 6, v 0] 7)
            (Light.Stmt.seq
              (.set 8
                ((Light.Expr.op Light.Op.sub) (v 6)
                  ((Light.Expr.op Light.Op.mul) (v 7) (v 0))))
              (Light.Stmt.seq
                (.set 9
                  ((Light.Expr.op Light.Op.sub) (v 5)
                    ((Light.Expr.op Light.Op.mul) (v 6) (k 3))))
                (Light.Stmt.seq
                  (.set 10
                    ((Light.Expr.op Light.Op.sub) (v 4)
                      ((Light.Expr.op Light.Op.mul) (v 5) (k 3))))
                  (Light.Stmt.seq
                    (.set 11
                      ((Light.Expr.op Light.Op.sub) (v 3)
                        ((Light.Expr.op Light.Op.mul) (v 4) (k 3))))
                    (Light.Stmt.seq
                      (.set 12
                        ((Light.Expr.op Light.Op.sub) (v 1)
                          ((Light.Expr.op Light.Op.mul) (v 3) (k 3))))
                      (Light.Stmt.seq (.store (v 2) (v 7))
                        (Light.Stmt.seq
                          (.store ((Light.Expr.op Light.Op.add) (v 2) (k 1))
                            (v 8))
                          (Light.Stmt.seq
                            (.store ((Light.Expr.op Light.Op.add) (v 2) (k 2))
                              (v 9))
                            (Light.Stmt.seq
                              (.store ((Light.Expr.op Light.Op.add) (v 2) (k 3))
                                (v 10))
                              (Light.Stmt.seq
                                (.store ((Light.Expr.op Light.Op.add) (v 2) (k 4))
                                  (v 11))
                                (Light.Stmt.seq
                                  (.store
                                    ((Light.Expr.op Light.Op.add) (v 2) (k 5))
                                    (v 12))
                                  (.set 0 (v 2))))))))))))))))))

def time (t : ℕ) : ℕ := 100*t+2000







variable {lim : Limits} {P : Program} {d W t free : ℕ} {μ : ℕ → ℤ}
































































































end ThreeSum.LightColorParameters

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightCoverUpdate


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Removing the targets covered by the selected candidate -/

namespace ThreeSum.LightCoverUpdate

open Light

def body : Stmt :=
  pass 3 (v 2) (v 1)
    (((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v 1) (v 3)))
       ((Light.Expr.op Light.Op.sub) (k 1)
         (M ((Light.Expr.op Light.Op.add) (v 0) (v 3))))))

def time (n : ℕ) : ℕ := 26*n+6

variable {lim : Limits} {P : Program} {d : ℕ}






















































end ThreeSum.LightCoverUpdate

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightDenseGuard


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Actual cumulative mass guard before expensive reporting

The root header is the actual Initialize output, whose third cell contains
the queried raw mass. This procedure adds that cell to the retained running
counter and returns one exactly when the computed threshold is exceeded.
It changes only the counter cell.
-/

namespace ThreeSum.LightDenseGuard

open Light

def body : Stmt :=
  (Light.Stmt.seq
    (.set 3
      ((Light.Expr.op Light.Op.add) (M (v 0))
        (M ((Light.Expr.op Light.Op.add) (v 1) (k 2)))))
    (Light.Stmt.seq (.store (v 0) (v 3))
      (.ite (Light.Cond.lt (v 2) (v 3)) (.set 0 (k 1)) (.set 0 (k 0)))))

def time : ℕ := 60

variable {lim : Limits} {P : Program} {μ : ℕ→ℤ}
  {counter root old mass threshold d : ℕ}






















def program : Program := [body]










end ThreeSum.LightDenseGuard

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorResult


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # Write the compact selected-color result after all retained source data -/

namespace ThreeSum.LightEncodedColorResult

open Light

def values (prime cover wanted controls bank out len p : ℕ) : List ℤ :=
  [prime,cover,wanted,controls,bank,out+8,len,p]

def body : Stmt :=
  (Light.Stmt.seq (.set 8 ((Light.Expr.op Light.Op.add) (v 5) (k 8)))
    (Light.Stmt.seq (.store (v 5) (v 0))
      (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 5) (k 1)) (v 1))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 5) (k 2)) (v 2))
          (Light.Stmt.seq
            (.store ((Light.Expr.op Light.Op.add) (v 5) (k 3)) (v 3))
            (Light.Stmt.seq
              (.store ((Light.Expr.op Light.Op.add) (v 5) (k 4)) (v 4))
              (Light.Stmt.seq
                (.store ((Light.Expr.op Light.Op.add) (v 5) (k 5)) (v 8))
                (Light.Stmt.seq
                  (.store ((Light.Expr.op Light.Op.add) (v 5) (k 6)) (v 6))
                  (Light.Stmt.seq
                    (.store ((Light.Expr.op Light.Op.add) (v 5) (k 7)) (v 7))
                    (.set 0 (v 5)))))))))))

def memory (μ : ℕ → ℤ) (prime cover wanted controls bank out len p : ℕ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update μ out (prime : ℤ))
      (out+1) cover) (out+2) wanted) (out+3) controls) (out+4) bank) (out+5) (out+8)) (out+6) len) (out+7) p


















variable {lim : Limits} {P : Program} {d : ℕ}
































end ThreeSum.LightEncodedColorResult

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightEncodedColorWantedHeader


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-! # Recover the wanted-header address from the retained cover controls -/

namespace ThreeSum.LightEncodedColorWantedHeader

open Light GlobalEncoding LocalCoverBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Cover header, block count, and original incidence count. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 3 (M ((Light.Expr.op Light.Op.add) (v 0) (k 18))))
    (Light.Stmt.seq (.set 4 (M (v 0)))
      (Light.Stmt.seq (.set 5 (M ((Light.Expr.op Light.Op.add) (v 0) (k 10))))
        (Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.mul) (v 5) (v 4)))
          (Light.Stmt.seq
            (.set 7
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v 3) (v 4)) (v 6)))
            (Light.Stmt.seq (.set 8 (k 1))
              (Light.Stmt.seq
                (.for 9 (v 1)
                  (Light.Stmt.seq
                    (.set 7
                      ((Light.Expr.op Light.Op.add)
                        ((Light.Expr.op Light.Op.add) (v 7) (k 1)) (v 8)))
                    (.set 8 ((Light.Expr.op Light.Op.mul) (v 8) (v 6)))))
                (Light.Stmt.seq
                  (.set 7
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add) (v 7) (k 1)) (v 8)))
                  (.set 0
                    ((Light.Expr.op Light.Op.add) (v 7)
                      ((Light.Expr.op Light.Op.mul) (k 3) (v 2))))))))))))

def time (J : ℕ) : ℕ := 100*J+1000




















variable {lim : Limits} {P : Program} {d : ℕ}

























































































end ThreeSum.LightEncodedColorWantedHeader

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightExplicitSum


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
# Complete execution of the explicit leaves of a sparse query

The loop visits only missing-set cardinalities below the threshold. Each
layer is enumerated inside the actual query mask and immediately evaluated.
One reusable mask buffer is sufficient; all source stages are preserved.
-/

namespace ThreeSum.LightExplicitSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}































def roundBody (pEnum pSum : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pEnum [v 0, v 8, v 15, v 12, v 13] 16)
    (Light.Stmt.seq
      (.call pSum
        [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 15, v 16, v 12, v 10,
          v 11, v 13]
        17)
      (.set 14 ((Light.Expr.op Light.Op.add) (v 14) (v 17)))))

/-- Width, source cutoff, suffix stage, two prefixes, query cardinality and
mask, missing threshold, two source bases, reusable mask buffer and scratch. -/
def body (pEnum pSum : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 14 (k 0))
    (Light.Stmt.seq (.for 15 (v 9) (roundBody pEnum pSum)) (.set 0 (v 14))))






















































































































































































































end ThreeSum.LightExplicitSum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightHistogram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}

def count (key : ℕ → ℕ) (r i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => key j = r).card
















/-- The address is deliberately recomputed instead of stored in a temporary:
this makes the loop preserve all locals apart from its counter. -/
def countBody : Stmt :=
  .for 4 (v 2) (.store (((Light.Expr.op Light.Op.add) (v 1)
                          (M ((Light.Expr.op Light.Op.add) (v 0) (v 4)))))
    (((Light.Expr.op Light.Op.add)
       (M
         ((Light.Expr.op Light.Op.add) (v 1)
           (M ((Light.Expr.op Light.Op.add) (v 0) (v 4)))))
       (k 1))))

def countTime (n : ℕ) : ℕ := 24 * n + 6






















































def histogramBody (pFill : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pFill [v 1, v 3, k 0] 5) countBody)

def histogramTime (n p : ℕ) : ℕ := fillTime p + countTime n + 5



























end ThreeSum.LightHistogram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLeafSum


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
# Summing a cardinality layer of explicit signed leaves

Missing masks are read from actual memory. Each complementary leaf is
formed by exact subtraction and evaluated from the two stored source
transforms. The source cutoff is independent of the smaller box cutoff.
-/

namespace ThreeSum.LightLeafSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
























def roundBody (pLeaf : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pLeaf
      [v 0, v 1, v 2, v 3, v 4, v 5, v 6,
        (Light.Expr.op Light.Op.sub) (v 7) (v 9),
        (Light.Expr.op Light.Op.sub) (v 8)
          (M ((Light.Expr.op Light.Op.add) (v 11) (v 16))),
        v 12, v 13, v 14]
      17)
    (.set 15 ((Light.Expr.op Light.Op.add) (v 15) (v 17))))

/-- Width, source cutoff, suffix stage, two prefixes (cardinality and mask),
query cardinality and mask, missing cardinality, mask count, mask buffer,
two source-stage bases and scratch. -/
def body (pLeaf : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 15 (k 0))
    (Light.Stmt.seq (.for 16 (v 10) (roundBody pLeaf)) (.set 0 (v 15))))












































































































































































end ThreeSum.LightLeafSum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverHashHistogram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightHashHistogram
end ThreeSum.LightHashHistogram


/-!
# Preserving completed candidate tables during local hash construction

This proves a stronger preservation conclusion for the existing actual
hash/residue/histogram program, with its original input and resource
conditions. It lets successive local candidates retain earlier coefficient,
histogram, and cover-matrix rows above the temporary raw/code arrays.
-/

namespace ThreeSum.LightLocalCoverHashHistogram

open Light LightHashHistogram

def Preserved (μ ν : ℕ → ℤ) (work raw codes hist n p : ℕ) : Prop :=
  ∀ a, a < work → Outside raw n a → Outside codes n a → Outside hist p a → ν a = μ a

variable {lim : Limits} {P : Program} {d : ℕ}














































































end ThreeSum.LightLocalCoverHashHistogram

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverInitResources


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


/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 1500000

def envelope (h : ℕ) : ℕ := 2^(5000000*(h+1)^2)




























































































































end ThreeSum.LightLocalCoverInitResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLocalCoverResources


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude

set_option maxHeartbeats 1800000

def envelope (h : ℕ) : ℕ := 2^(4000000*(h+1)^2)











































































































































































































end ThreeSum.LightLocalCoverResources

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightLookupSum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Summing an array of indirect nonnegative table lookups

The program reads each key once and adds its table entry to a word-sized
accumulator. The contract counts the loop, address arithmetic, both loads,
and additions. It does not change memory.
-/

namespace ThreeSum.LightLookupSum

open Light Finset
open scoped BigOperators

def prefixSum (f : ℕ → ℕ) (key : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, f (key i)


















def loopBody : Stmt :=
  .set 4 (((Light.Expr.op Light.Op.add) (v 4)
            (M
              ((Light.Expr.op Light.Op.add) (v 1)
                (M ((Light.Expr.op Light.Op.add) (v 0) (v 5)))))))

/-- Arguments: key array, value table, number of keys, table length. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 4 (k 0))
    (Light.Stmt.seq (.for 5 (v 2) loopBody) (.set 0 (v 4))))

def time (n : ℕ) : ℕ := 24*n+20

variable {lim : Limits} {P : Program} {d : ℕ}




























































end ThreeSum.LightLookupSum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightMaskErase


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase


/-!
# Machine deletion of one mask coordinate

Each call decreases the remaining width. Powers of two are table reads;
there is no division, advice, or loop proportional to the mask value.
-/

namespace ThreeSum.LightMaskErase

open Light ThreeSum.MaskErase ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments are remaining width, coordinate, mask, original width, power
base. Local 5 retains the next bit index across the recursive call. -/
def body (pSelf : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 0)))
    ((Light.Stmt.seq (.set 5 ((Light.Expr.op Light.Op.sub) (v 0) (k 1)))
       (.ite (Light.Cond.lt (v 2) (M ((Light.Expr.op Light.Op.add) (v 4) (v 5))))
         (.call pSelf [v 5, v 1, v 2, v 3, v 4] 0)
         (.ite (Light.Cond.eq (v 1) (v 5))
           (.set 0
             ((Light.Expr.op Light.Op.sub) (v 2)
               (M ((Light.Expr.op Light.Op.add) (v 4) (v 5)))))
           (Light.Stmt.seq
             (.call pSelf
               [v 5, v 1,
                 (Light.Expr.op Light.Op.sub) (v 2)
                   (M ((Light.Expr.op Light.Op.add) (v 4) (v 5))),
                 v 3, v 4]
               0)
             (.set 0
               ((Light.Expr.op Light.Op.add)
                 (M ((Light.Expr.op Light.Op.add) (v 4) (v 5))) (v 0))))))))
    (.set 0 (k 0))

def time (L : ℕ) : ℕ := 100*L+30
















































































end ThreeSum.LightMaskErase

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightMinimum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light

def least (f : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if f n < f (least f n) then n else least f n



































def scanBody : Stmt :=
  .ite ((Light.Cond.lt (M ((Light.Expr.op Light.Op.add) (v 0) (v 3)))
          (M ((Light.Expr.op Light.Op.add) (v 0) (v 2))))) (.set 2 (v 3)) .skip

def body : Stmt :=
  (Light.Stmt.seq (.set 2 (k 0))
    (Light.Stmt.seq (.for 3 (v 1) scanBody) (.set 0 (v 2))))

def time (n : ℕ) : ℕ := 32*n + 20

variable {lim : Limits} {P : Program} {d : ℕ}





































end ThreeSum.LightMinimum

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightNatPower


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Scalar integer powers in the benchmark language

The exponent is a size parameter, so a loop of that many multiplications
has polynomial-logarithmic cost in the applications below. No power table
or auxiliary memory is required.
-/

namespace ThreeSum.LightNatPower

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  (Light.Stmt.seq (.set 2 (k 1))
    (Light.Stmt.seq
      (.for 3 (v 1) (.set 2 ((Light.Expr.op Light.Op.mul) (v 2) (v 0))))
      (.set 0 (v 2))))

def time (e : ℕ) : ℕ := 20*e+20
















































def program : Program := [body]








end ThreeSum.LightNatPower

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightOneHot


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask


/-!
# A fixed word-RAM one-hot hash evaluator

The recursive procedure visits the mask's bit positions in decreasing order,
reads the selected coefficient, and adds it. Its time is linear in the width,
independent of the mask's numeric magnitude. The public wrapper constructs
its own powers-of-two table and preserves both coefficient arrays.
-/

namespace ThreeSum.LightOneHot

open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}

/-- Arguments are current width, mask, original width, power table, and the
two coefficient arrays. Local 6 retains the current coordinate. -/
def body (pSelf : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v 0)))
    ((Light.Stmt.seq (.set 6 ((Light.Expr.op Light.Op.sub) (v 0) (k 1)))
       (.ite (Light.Cond.lt (v 1) (M ((Light.Expr.op Light.Op.add) (v 3) (v 6))))
         (Light.Stmt.seq (.call pSelf [v 6, v 1, v 2, v 3, v 4, v 5] 0)
           (.set 0
             ((Light.Expr.op Light.Op.add) (v 0)
               (M ((Light.Expr.op Light.Op.add) (v 4) (v 6))))))
         (Light.Stmt.seq
           (.call pSelf
             [v 6,
               (Light.Expr.op Light.Op.sub) (v 1)
                 (M ((Light.Expr.op Light.Op.add) (v 3) (v 6))),
               v 2, v 3, v 4, v 5]
             0)
           (.set 0
             ((Light.Expr.op Light.Op.add) (v 0)
               (M ((Light.Expr.op Light.Op.add) (v 5) (v 6)))))))))
    (.set 0 (k 0))

def time (L : ℕ) : ℕ := 100*L+30

def word (W U : ℕ) : ℕ := 2^(W+1)+(W+1)*U






























































































































































end ThreeSum.LightOneHot

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightRadixDigit


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-! # An actual radix digit using two local counting divisions -/

namespace ThreeSum.LightRadixDigit

open Light

def body (pDivide : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDivide [v 0, v 1] 3)
    (Light.Stmt.seq (.call pDivide [v 3, v 2] 4)
      (.set 0
        ((Light.Expr.op Light.Op.sub) (v 3)
          ((Light.Expr.op Light.Op.mul) (v 4) (v 2))))))

def time (k : ℕ) : ℕ := 40*(k+1)+100
def word (k b p : ℕ) : ℕ := 4*(k+b+p+2)

variable {lim : Limits} {P : Program} {d : ℕ}










































































end ThreeSum.LightRadixDigit

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingAffine


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light
namespace ThreeSum.LightArray
end ThreeSum.LightArray


/-! # Costed affine scans used to form reporting child-prefix masks -/

namespace ThreeSum.LightReportingAffine

open Light ThreeSum.LightArray

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  pass 5 (v 2) (v 1) (((Light.Expr.op Light.Op.add) (v 3)
                        ((Light.Expr.op Light.Op.mul) (v 4)
                          (M ((Light.Expr.op Light.Op.add) (v 0) (v 5))))))

def time (n : ℕ) : ℕ := 23*n+6






























end ThreeSum.LightReportingAffine

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingBucketRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Exact original-value testing of one retained physical bucket

The procedure visits the bucket's physical index array and reads the original
value at each index. It counts exact integer equalities with the supplied
target and preserves every memory cell. Equal values at distinct original
indices remain separate tests.
-/

namespace ThreeSum.LightReportingBucketRow

open Light Finset

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

def count (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((range n).filter fun j => value (index j)=target).card






















def roundBody : Stmt :=
  .ite ((Light.Cond.eq
          (M
            ((Light.Expr.op Light.Op.add) (v 1)
              (M ((Light.Expr.op Light.Op.add) (v 2) (v 6)))))
          (v 0)))
    (.set 5 (((Light.Expr.op Light.Op.add) (v 5) (k 1)))) .skip

/-- Target value, original value array, retained physical indices, bucket
length, original value-array length. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 5 (k 0))
    (Light.Stmt.seq (.for 6 (v 3) roundBody) (.set 0 (v 5))))

def time (n : ℕ) : ℕ := 60*n+30


variable {lim : Limits} {P : Program} {d : ℕ}




























































end ThreeSum.LightReportingBucketRow

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LightReportingFilter


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Light
end Light


/-!
# Actual positive-query filtering for a reporting frontier

The scan writes exactly the indices of positive stored query counts, in input
order. Its cost is linear in the candidate count, and original input arrays
are preserved. It does not recompute or assume the query implementation.
-/

namespace ThreeSum.LightReportingFilter

open Light

variable {lim : Limits} {P : Program}

def selected (count : ℕ → ℕ) (j : ℕ) : List ℕ :=
  (List.range j).filter fun i => 0 < count i






















def roundBody : Stmt :=
  .ite ((Light.Cond.lt (k 0) (M ((Light.Expr.op Light.Op.add) (v 1) (v 4)))))
    ((Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v 2) (v 3)) (v 4))
       (.set 3 ((Light.Expr.op Light.Op.add) (v 3) (k 1)))))
    .skip

/-- Number of candidates, stored query counts, selected-index output. -/
def body : Stmt :=
  (Light.Stmt.seq (.set 3 (k 0))
    (Light.Stmt.seq (.for 4 (v 0) roundBody) (.set 0 (v 3))))

def time (n : ℕ) : ℕ := 100*n+40

def Inv (μ : ℕ → ℤ) (count : ℕ → ℕ) (n src dst j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [n,src,dst,(selected count j).length,j],μ'⟩ ∧
    SegN μ' dst (selected count j) ∧ SameOutside μ μ' dst n



































































end ThreeSum.LightReportingFilter

end


