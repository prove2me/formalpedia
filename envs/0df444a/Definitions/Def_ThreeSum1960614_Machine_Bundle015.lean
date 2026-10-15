-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle015
-- name    : ThreeSum1960614_Machine_Bundle015
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:35:30.028091+00:00
-- url     : https://prove2.me/theorems/8c863d94-d7ee-4926-8492-eeff72a95384
-- title:
--   Mask processing, weighted modular scores, and compact zeta updates
-- statement:
--   These finite Light programs inspect individual bits of a width-$L$ subset mask using constructed powers and the checked coordinate-deletion routine. They produce Boolean coordinate rows, evaluate lists of one-hot weighted hashes, find a nonempty mask's least coordinate, form a union and its cardinality, and list the powers corresponding to a query subset. Their loop invariants record the partial mask or row and preservation of the required memory regions.
--
--   The original-offset wrapper constructs two signed-key histograms, a power-of-two capacity, and their correlation, then chooses the least minimizing offset; repeated keys remain distinct incidences. Paired gathering aligns the two reporting-prefix mask arrays. Prime selection computes the integer square-root threshold and scans a primality-tested pool, taking its first prime. Source-bucket construction computes prefix offsets and scatters every physical index once while retaining the original code and count arrays. Subset enumeration builds its own power table, and ordered-weight decoding builds its own radix powers before splitting even and odd digits into two coefficient rows.
--
--   For positive base modulus $q$, auxiliary primes $p_0,\ldots,p_{s-1}$, and three integer arrays, write $C(m)$ for the number of their modular zero-sum triples modulo $m$. The weighted-score procedure computes
--
--   $$sC(q)-\sum_{i=0}^{s-1}C(\operatorname{joint}(q,p_i)),$$
--
--   where the joint modulus is $q$ when $p_i$ divides $q$, and $qp_i$ otherwise. The fixed fourteen-procedure program includes the concrete modular-counting and arithmetic implementations; its invariant records the remaining partial score and preservation below the free pointer. The switch compatibility interface delegates to the integer quartic procedure.
--
--   Finally, a compact zeta-cell program constructs its own Pascal and power tables, obtains the compact address of a valid mask $S$, and tests a coordinate $i$. It writes the old value at $S$ plus the old value at $S\setminus\{i\}$ when $i\in S$, and simply copies the old value when $i\notin S$. Its destination stores only the compact downset data.
--
--   These components implement the hash-family evaluation, deterministic choices, modular score, and subset-transform operations appearing in the complete deterministic integer 3SUM runtime proof. In particular their interfaces expose constructed data and explicit procedure closure rather than counting any of these operations as a machine oracle.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskBits.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskHashes.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskMinimum.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskUnion.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOriginalOffset.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightQueryWeights.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingGatherPair.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSelectedPrime.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketFromHistogram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSubsetEnumerationSetup.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSwitch.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWeightDecode.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWeightedScore.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightZetaCell.lean

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
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
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightMaskHashes
end ThreeSum.LightMaskHashes
namespace ThreeSum.LightMaskMinimum
end ThreeSum.LightMaskMinimum
namespace ThreeSum.LightMaskUnion
end ThreeSum.LightMaskUnion
namespace ThreeSum.LightOriginalOffset
end ThreeSum.LightOriginalOffset
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightQueryWeights
end ThreeSum.LightQueryWeights
namespace ThreeSum.LightReportingGatherPair
end ThreeSum.LightReportingGatherPair
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSelectedPrime
end ThreeSum.LightSelectedPrime
namespace ThreeSum.LightSourceBucketFromHistogram
end ThreeSum.LightSourceBucketFromHistogram
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumerationSetup
end ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum.LightSwitch
end ThreeSum.LightSwitch
namespace ThreeSum.LightWeightDecode
end ThreeSum.LightWeightDecode
namespace ThreeSum.LightWeightedScore
end ThreeSum.LightWeightedScore
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.MaskUnion
end ThreeSum.MaskUnion
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskUnion
end ThreeSum1960614.Machine.ThreeSum.LightMaskUnion
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
end ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
end ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair
end ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime
end ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitch
end ThreeSum1960614.Machine.ThreeSum.LightSwitch
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightDecode
end ThreeSum1960614.Machine.ThreeSum.LightWeightDecode
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightedScore
end ThreeSum1960614.Machine.ThreeSum.LightWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.MaskUnion
end ThreeSum1960614.Machine.ThreeSum.MaskUnion
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.WeightedModuli
end ThreeSum1960614.Machine.ThreeSum.WeightedModuli
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore

namespace ThreeSum1960614.Machine

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits
open _root_.ThreeSum.LightMaskBits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase









def loopBody (pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 4 (_root_.ThreeSum1960614.Machine.Light.v 0) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pErase [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3] 5) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.k 1)))))

def body (pPowers pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 3, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 5) (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.loopBody pErase))



def Inv (μ : ℕ → ℤ) (L m dst work i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨_root_.Light.frame [L,m,dst,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (_root_.ThreeSum.LightMaskBits.bit L m j : ℤ)) ∧ _root_.ThreeSum.LightSubsetAddress.Powers μ' work L ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst L

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightMaskBits

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes
open _root_.ThreeSum.LightMaskHashes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 1000000

def loopBody (pHash : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.for 7 (_root_.ThreeSum1960614.Machine.Light.v 3) (
    (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHash [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 7)), _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.v 8))))

def body (pPowers pHash : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 6, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 8) (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.loopBody pHash))



def Inv (μ : ℕ → ℤ) (mask w0 w1 : ℕ → ℕ)
    (L masks dst n src0 src1 work i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [L,masks,dst,n,src0,src1,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (_root_.ThreeSum.OneHotMask.eval w0 w1 L (mask j) : ℤ)) ∧
    _root_.ThreeSum.LightSubsetAddress.Powers μ' work L ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst n

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightMaskHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing the least coordinate of a nonempty mask

The program constructs its own powers table, scans the bit positions,
and uses the verified mask-deletion test. Its work is quadratic in the
width and its scratch is linear. It never scans mask values.
-/

namespace ThreeSum.LightMaskMinimum
open _root_.ThreeSum.LightMaskMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



def roundBody (pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pErase [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 4)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.v 5)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip) _root_.ThreeSum1960614.Machine.Light.Stmt.skip))

/-- Arguments: width, nonempty mask, scratch base. -/
def body (pPowers pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 2, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 4 (_root_.ThreeSum1960614.Machine.Light.v 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 5 (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum.roundBody pErase)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 4)))))



def Inv {L : ℕ} (μ : ℕ → ℤ) (S : Finset (Fin L)) (hS : S.Nonempty)
    (work : ℕ) (powRet : ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ r : ℤ, σ = ⟨_root_.Light.frame [L,_root_.ThreeSum.SubsetAddress.subsetMask S,work,powRet,_root_.ThreeSum.LightMaskMinimum.best S hS j,j,r],μ⟩









end ThreeSum.LightMaskMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# General mask union and its cardinality on the bounded-word machine

The program tests each coordinate using the checked bit-deletion routine.
It constructs its own powers table, adds each new bit once, and writes the
union cardinality to one output cell. It never visits an ambient cube.
-/

namespace ThreeSum.LightMaskUnion
open _root_.ThreeSum.LightMaskUnion


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskUnion
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskUnion

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def roundBody (pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pErase [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 5] 10) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pErase [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 5] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 10) (_root_.ThreeSum1960614.Machine.Light.v 3)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 2)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 9))))))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip)))

/-- Width, first cardinality and mask, second mask, cardinality output,
power-table scratch. The return value is the union mask. -/
def body (pPowers pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 5, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 7 (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 9 (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskUnion.roundBody pErase)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 7)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 8)))))))



def Inv {W : ℕ} (μ : ℕ → ℤ) (A B : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ eB eA : ℤ,
    σ = ⟨_root_.Light.frame [W,A.card,_root_.ThreeSum.SubsetAddress.subsetMask A,_root_.ThreeSum.SubsetAddress.subsetMask B,dst,work,powRet,
      (_root_.ThreeSum.MaskUnion.scanSet A B j).card,_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.MaskUnion.scanSet A B j),j,eB,eA],μ⟩









end ThreeSum.LightMaskUnion

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset
open _root_.ThreeSum.LightOriginalOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000







/-- Left and right signed key arrays, their lengths, modulus, maximum
length, and first free address. -/
def body (pCapacity pHist pOffset : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCapacity [_root_.ThreeSum1960614.Machine.Light.v 4] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 8 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) (_root_.ThreeSum1960614.Machine.Light.v 7))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 3) (_root_.ThreeSum1960614.Machine.Light.v 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 11 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 5) (_root_.ThreeSum1960614.Machine.Light.v 7)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 5))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHist [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.k 1)] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pHist [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.k 1] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pOffset [_root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 8, _root_.ThreeSum1960614.Machine.Light.v 9, _root_.ThreeSum1960614.Machine.Light.v 10, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 12, _root_.ThreeSum1960614.Machine.Light.v 4] 0)))))))))





structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pFill : ℕ
  pOffset : ℕ
  pCyclic : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pMinimum : ℕ
  capacityProc : P[pCapacity]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.body
  histogram : P[pHist]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody pEmod)
  emod : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody
  count : P[pHistogram]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody pFill)
  offset : P[pOffset]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.body pCyclic pMinimum)
  cyclic : P[pCyclic]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body pMultiply pLinear)
  karatsuba : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  minimum : P[pMinimum]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.body
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.body pCapacity pHist pOffset)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.body 1 2 7,_root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.body 3 5,_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody 4,
    _root_.ThreeSum1960614.Machine.Light.emodBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody 6,_root_.ThreeSum1960614.Machine.Light.fillBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.body 8 12,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body 9 11,_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.body 9 10 11 6,_root_.ThreeSum1960614.Machine.Light.halfBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.body]

def programProcs : _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.program 0 :=
  ⟨1,2,3,4,5,6,7,8,9,10,11,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩







end ThreeSum.LightOriginalOffset

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights
open _root_.ThreeSum.LightQueryWeights


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def roundBody (pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pErase [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.v 5)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 6)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1)))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip))

/-- Arguments: ambient width, query mask, output base, power scratch base. -/
def body (pPowers pErase : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 3, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 6 (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.roundBody pErase)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 5)))))



def Inv {W : ℕ} (μ : ℕ → ℤ) (Q : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [W,_root_.ThreeSum.SubsetAddress.subsetMask Q,dst,work,powRet,(_root_.ThreeSum.QueryCoordinates.positions Q j).length,j,r],μ'⟩ ∧
    _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.QueryCoordinates.selectedPowers Q j) ∧ _root_.ThreeSum.LightSubsetAddress.Powers μ' work W ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst W











end ThreeSum.LightQueryWeights

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual aligned gathering of both selected reporting-prefix mask arrays -/

namespace ThreeSum.LightReportingGatherPair
open _root_.ThreeSum.LightReportingGatherPair


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

def body (pGather : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pGather [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pGather [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4] 0))

def program : _root_.ThreeSum1960614.Machine.Light.Program := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGather.program ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.body 0]






end ThreeSum.LightReportingGatherPair

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the deterministic square-root prime selection

The candidate pool is scanned by the verified primality program. Its first
entry is exactly the minimum used by `LocalCoverBounds.selectedPrime`.
The input threshold is positive; the routine has no primality oracle or
externally supplied list of candidates.
-/

namespace ThreeSum.LightSelectedPrime
open _root_.ThreeSum.LightSelectedPrime


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues

set_option maxHeartbeats 1000000



def body (pSqrt pPool : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSqrt [(_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)] 2) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 3 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPool [_root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 1] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.v 1))))))





structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pSqrt : ℕ
  pPool : ℕ
  sqrt : P[pSqrt]? = some _root_.ThreeSum1960614.Machine.Light.sqrtBody
  pool : _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.Procs P pPool
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.body pSqrt pPool)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightSelectedPrime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Retained code/count arrays to exact contiguous original-index buckets

This actual three-procedure program is generic in the residue code function.
It constructs prefix offsets and scatters every physical index exactly once.
The code and count arrays are retained for source stages and later joins.
-/

namespace ThreeSum.LightSourceBucketFromHistogram
open _root_.ThreeSum.LightSourceBucketFromHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: code array, histogram, offsets, cursor scratch, flat index
output, input count, residue count. -/
def body (pOffsets pScatter : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pOffsets [_root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 5] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pScatter [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6] 7))



structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pOffsets : ℕ
  pScatter : ℕ
  offsets : P[pOffsets]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets.body
  scatter : P[pScatter]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketScatter.body
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram.body pOffsets pScatter)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightSourceBucketFromHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup
open _root_.ThreeSum.LightSubsetEnumerationSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

def body (pPowers pEnum : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 3, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.k 2] 4) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEnum [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3] 0))











end ThreeSum.LightSubsetEnumerationSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! Compatibility interface consumed by the full reporting driver.
It delegates to the proved degree-four Light procedure. No cubic test or
separate callback implementation remains in this execution path. -/

namespace ThreeSum.LightSwitch
open _root_.ThreeSum.LightSwitch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
abbrev word := _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.word

abbrev body := _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.body
def time (r : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.time r
def program : _root_.ThreeSum1960614.Machine.Light.Program := [_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.body]















end ThreeSum.LightSwitch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual decoding of the unchanged ordered hash-weight enumeration

The five-procedure program constructs its own power table, then decodes
the even and odd coordinates into two contiguous coefficient rows. The
digits are exactly those of `WeightEnumeration.decodedWeight`, which is
already proved equal to the original `allWeights` enumeration in order.
-/

namespace ThreeSum.LightWeightDecode
open _root_.ThreeSum.LightWeightDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

def body (pPowers pRow : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 5 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pPowers [_root_.ThreeSum1960614.Machine.Light.v 4, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 1] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRow [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.k 0, _root_.ThreeSum1960614.Machine.Light.k 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 0] 6) (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRow [_root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.k 1, _root_.ThreeSum1960614.Machine.Light.k 2, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 0), _root_.ThreeSum1960614.Machine.Light.v 0] 6))))




def Rows (μ : ℕ → ℤ) (dst L p k : ℕ) : Prop :=
  ∀ i < L,
    μ (dst+i) = (_root_.ThreeSum.WeightEnumeration.digit p (2*L) k (2*i) : ℤ) ∧
    μ (dst+L+i) = (_root_.ThreeSum.WeightEnumeration.digit p (2*L) k (2*i+1) : ℤ)

structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pPowers : ℕ
  pRow : ℕ
  pDigit : ℕ
  pDivide : ℕ
  powers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody
  row : P[pRow]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightRow.body pDigit)
  digit : P[pDigit]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.body pDivide)
  divide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightDecode.body pPowers pRow)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightWeightDecode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the weighted modular score

The joint-modulus helper uses the verified division-free remainder routine.
The score loop computes a base count, then visits the auxiliary-prime array
once.  All calls reuse the same scratch region and preserve the original
arrays.  Its intermediate scores are proved nonnegative.

The generic loop theorem exposes the modular-counting execution contract.
The concrete wrapper instantiates that contract with the checked fixed
modular-counting program; no counting operation is added to the machine.
-/

namespace ThreeSum.LightWeightedScore
open _root_.ThreeSum.LightWeightedScore


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WeightedModuli
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedModuli
open _root_.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Arguments: positive base modulus, positive auxiliary modulus, scratch. -/
def jointBody (pEmod : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pEmod [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2] 3) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.k 0)) _root_.ThreeSum1960614.Machine.Light.Stmt.skip (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 1)))))





/-- Arguments: A, B, C, their lengths, base modulus, maximum array length,
auxiliary-prime array, number of primes, and scratch.
Locals 11 and 12 hold the base count and remaining score; 13 is the loop
counter, and 14 and 15 hold the joint modulus and its count. -/
def body (pCount pJoint : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCount [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 10] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.v 11))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.for 13 (_root_.ThreeSum1960614.Machine.Light.v 9) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pJoint [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 8) (_root_.ThreeSum1960614.Machine.Light.v 13)), _root_.ThreeSum1960614.Machine.Light.v 10] 14) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pCount [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 4, _root_.ThreeSum1960614.Machine.Light.v 5, _root_.ThreeSum1960614.Machine.Light.v 14, _root_.ThreeSum1960614.Machine.Light.v 7, _root_.ThreeSum1960614.Machine.Light.v 10] 15) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 12 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 15)))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set 0 (_root_.ThreeSum1960614.Machine.Light.v 12)))))



def Inv (μ : ℕ → ℤ) (primes : ℕ → ℕ)
    (a b c nA nB nC q N aux s free : ℕ) (i : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (jval cval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨_root_.Light.frame [(a : ℤ),b,c,nA,nB,nC,q,N,aux,s,free,
      _root_.ThreeSum.ModuloCounts.count q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)),
      _root_.ThreeSum.WeightedScore.remaining primes s q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j))
        (fun j => μ (c+j)) i,i,jval,cval],ν⟩ ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free









/-- Syntax-only closure for a weighted-score procedure and its concrete
modular-counting, joint-modulus, and arithmetic procedures. -/
structure Procs (P : _root_.ThreeSum1960614.Machine.Light.Program) (pMain : ℕ) where
  pCount : ℕ
  pJoint : ℕ
  count : _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.Procs P pCount
  main : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.body pCount pJoint)
  joint : P[pJoint]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.jointBody count.pEmod)



/-- A fixed fourteen-procedure program. All recursive and nonrecursive calls
refer to members of this list; no modular-counting oracle is assumed. -/
def program : _root_.ThreeSum1960614.Machine.Light.Program :=
  [_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.body 2 1, _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.jointBody 6, _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.body 3 4 8 5 13,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.body, _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.body 5 7, _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody 6,
    _root_.ThreeSum1960614.Machine.Light.emodBody, _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody 12, _root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body 9 11,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.body 9 10 11 12, _root_.ThreeSum1960614.Machine.Light.halfBody, _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody, _root_.ThreeSum1960614.Machine.Light.fillBody,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLookupSum.body]







end ThreeSum.LightWeightedScore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# An actual compact-table zeta-cell update

The fixed procedure builds its own Pascal and power tables, ranks the input
mask, deletes the requested coordinate, ranks the smaller mask if necessary,
and writes the zeta addition at the compact downset address. The scratch area
is polynomial in the width. Neither addresses nor table values are supplied
by an oracle.
-/

namespace ThreeSum.LightZetaCell
open _root_.ThreeSum.LightZetaCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





/-- Arguments: width, cardinality, mask, coordinate, source, destination,
and scratch. The destination contains only `downsetCap` data cells. -/
def body (pSetup pOffset pErase pRank : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 10 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 6) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.k 1))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pSetup [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 6] 7) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pOffset [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 1, _root_.ThreeSum1960614.Machine.Light.v 0] 8) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 9 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 7) (_root_.ThreeSum1960614.Machine.Light.v 8))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pErase [_root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 3, _root_.ThreeSum1960614.Machine.Light.v 2, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 10] 11) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v 11) (_root_.ThreeSum1960614.Machine.Light.v 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pRank [_root_.ThreeSum1960614.Machine.Light.v 0, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 11, _root_.ThreeSum1960614.Machine.Light.v 0, _root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 10] 12) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call pOffset [_root_.ThreeSum1960614.Machine.Light.v 6, _root_.ThreeSum1960614.Machine.Light.v 0, (_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.k 1), _root_.ThreeSum1960614.Machine.Light.v 0] 13) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set 14 ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 12) (_root_.ThreeSum1960614.Machine.Light.v 13))) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 9)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 9))) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 14)))))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 5) (_root_.ThreeSum1960614.Machine.Light.v 9)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.v 9))))))))))















end ThreeSum.LightZetaCell

end ThreeSum1960614.Machine


