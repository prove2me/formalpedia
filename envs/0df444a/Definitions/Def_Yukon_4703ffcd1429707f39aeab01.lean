-- Prove2me | Definitions.Def_Yukon_4703ffcd1429707f39aeab01
-- name    : Yukon_4703ffcd1429707f39aeab01
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T17:25:19.441624+00:00
-- url     : https://prove2.me/theorems/71356757-93bc-404e-b927-26ebcb0cda5d
-- title:
--   LowerFoundation source module 1/2
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-split-Yukon_4703ffcd1429707f39aeab01
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzFhODdkNGRjY2FkZDAzMTYxZjEzNTQzM2ZkY2ViMzlhZDlhODkyYmFjOWJjYjRjYmNmM2MzZDliMWRlMWZmMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tc3BsaXQtWXVrb25fNDcwM2ZmY2QxNDI5NzA3ZjM5YWVhYjAxIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNDcwM2ZmY2QxNDI5NzA3ZjM5YWVhYjAxIiwidiI6Mn0]

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.GradedMulAction
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Int.Associated
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Real.Embedding
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.GroupTheory.Submonoid.Inverses
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.GameAdd
import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.NormalClosure
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.ZMod
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyConstant.Basic
import Definitions.Def_Yukon_ca34dce12d256cc8e344ef5f



import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Log
import Init.Data.Vector.OfFn
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Aesop
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Basic
import Init.Data.List.FinRange
import Mathlib.Data.Matrix.Reflection
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Batteries.Tactic.Lint
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Batteries.Control.Lemmas
import Mathlib.Data.Vector.Defs
import Batteries.Control.OptionT
import Batteries.Control.AlternativeMonad
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Init.Data.UInt.Lemmas
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.List.Sym
import Mathlib.Order.Basic
import Mathlib.Control.Monad.Writer
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Set.Card
import Init.Data.Vector.Lemmas
import Mathlib.Control.Lawful
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Logic.Equiv.Sum
import Std.Tactic.Do
import Std.Internal.Do.Assertion
import Mathlib.Algebra.Order.Monoid.Defs
import Init.Data.String.Lemmas.Iterate
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Iterate
import Init.Data.String.Defs
import Init.Omega
import Init.Data.Slice.Lemmas
import Init.Data.Nat.Mod
import Init.Data.List.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Range
import Init.Data.Iterators.Lemmas
import Init.Data.Range
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Std.Do.Triple.SpecLemmas
import Init.Data.Slice.Array
import Init.Data.Range.Polymorphic
import Init.Data.Range.Polymorphic.Iterators
import Init.While
import Init.Syntax
import Lean.Meta.Sym.Pattern
import Lean.Meta.Tactic.Simp
import Lean.Meta.Match.MatcherApp
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Do.Attr
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Sym.Apply
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finsupp.Order
import Std.Data.HashMap.Lemmas
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Use
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Attr.Register
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Vector.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.AdjoinRoot
import Lean.Compiler.IR
import Definitions.Def_Yukon_259e1f66095e57d2601bc351
import Definitions.Def_Yukon_01ccec4dda453f6e2e78a73a
import Definitions.Def_Yukon_ba7304588491aaabedef2404
import Definitions.Def_Yukon_5bec250b841ba6aa1175dc48
import Definitions.Def_Yukon_df15ca12ddf2d8e2d1b3970a
import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
set_option backward.isDefEq.respectTransparency.types false
/-! Compact lower-bound proof; prior work is credited in the enclosed components. -/

-- Mathlib's linters run interpreted after every declaration; they only warn.
set_option linter.all false

section Compact_KernelEval
/-
Optional submission helper. Not part of the challenge; copy it into your
submission root and edit it freely.
-/

-- Only Mathlib: this file is identical for the lower and upper tracks.
/-!
# Kernel-cheap evaluation helpers

`by decide` hands the goal to the **kernel**, which discharges it by unfolding
definitions. It never runs `simp`. So no closed-form lemma -- yours, ours, or
Mathlib's -- can make a `decide` cheaper; only the definition it unfolds can.

`Finset.range n` is a `Multiset`, hence a `Quot` of a `List`, and `Finset.sum` is
`Multiset.foldr`, so every summand costs the kernel a `Quot.lift`/`List.rec`
traversal where a `Nat` recursion costs one addition. That is what `sumRange`
below avoids, and what the closed forms remove entirely.
-/

namespace KernelEval

/-- `∑ i ∈ Finset.range n, f i`, by structural recursion on `ℕ`.

Write this where you would write `∑ i ∈ Finset.range n, f i` inside a definition
that a `decide` has to evaluate. -/
def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n

@[simp] theorem sumRange_zero (f : ℕ → ℕ) : sumRange f 0 = 0 := rfl

@[simp] theorem sumRange_succ (f : ℕ → ℕ) (n : ℕ) :
    sumRange f (n + 1) = sumRange f n + f n := rfl

/-- Stated in this direction on purpose: it rewrites *your* definition into the
`Finset` form, so every existing Mathlib lemma about `Finset.sum` still applies.
The kernel speedup comes from the definition; this lemma preserves your proofs. -/
theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => rw [sumRange_succ, ih, Finset.sum_range_succ]

/-! ### Closed forms

`sumRange` is cheaper per element than `Finset.sum`, but still linear in the
number of elements. When the body is affine the sum has a closed form and the
cost drops to O(1), which is a much larger difference than the one above. -/

/-- Division-free form of `∑_{r=0}^{m} (a - r)`: holds in `ℕ` with no division
and no side condition beyond `m ≤ a`. -/
theorem sum_range_sub_add (a m : ℕ) (h : m ≤ a) :
    (∑ r ∈ Finset.range (m + 1), (a - r)) + (∑ r ∈ Finset.range (m + 1), r)
      = (m + 1) * a := by
  rw [← Finset.sum_add_distrib]
  have hpt : ∀ r ∈ Finset.range (m + 1), (a - r) + r = a := by
    intro r hr
    have : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

/-- Closed form of `∑_{r=0}^{m} (a - r)`. `m ≤ a` is exactly the condition under
which the truncated subtraction is honest. -/
theorem sum_range_sub (a m : ℕ) (h : m ≤ a) :
    ∑ r ∈ Finset.range (m + 1), (a - r) = (m + 1) * a - (m + 1) * m / 2 := by
  have hadd := sum_range_sub_add a m h
  have hgauss : (∑ r ∈ Finset.range (m + 1), r) * 2 = (m + 1) * m :=
    Finset.sum_range_id_mul_two (m + 1)
  omega

/-! ### Nested sums: close the inner one

A nested `Finset.range` sum is the worst case, because the inner traversal runs
once per outer element. You do not need a closed form for the whole thing to get
most of the win -- closing only the inner sum takes the work from `O(outer *
inner)` to `O(outer)`, and where the inner body is affine that is just
`sum_range_sub` applied pointwise.

Given

```lean
def f (T YS S : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (min T YS + 1),
    ∑ r ∈ Finset.range (min S (min (T-y) (YS-y)) + 1), (T+1-y-r)
```

define it with the inner sum already closed, and recover the original statement
as a lemma so existing proofs still apply:

```lean
def f (T YS S : ℕ) : ℕ :=
  sumRange (fun y =>
    let M := min S (min (T-y) (YS-y))
    (M+1) * (T+1-y) - (M+1) * M / 2) (min T YS + 1)

theorem f_eq (T YS S : ℕ) :
    f T YS S = ∑ y ∈ Finset.range (min T YS + 1),
      ∑ r ∈ Finset.range (min S (min (T-y) (YS-y)) + 1), (T+1-y-r) := by
  rw [f, sumRange_eq]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have h : min S (min (T-y) (YS-y)) ≤ T+1-y := by
    have : min S (min (T-y) (YS-y)) ≤ T - y :=
      le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    omega
  exact (sum_range_sub (T+1-y) _ h).symm
```

Anything that previously unfolded `f` should be pointed at `f_eq` instead --
typically one `simp` argument or one `rw` per site.

Closing the outer sum too would need a case split on where `min` changes branch;
that is a much larger proof for a much smaller further gain. -/

end KernelEval

end Compact_KernelEval

section Compact_PackedLegacyCore0
/-! Packed from ProximityPrize.SubmissionLower.I5. -/
section PackedLegacy_I5
namespace ProximityPrize.SubmissionLower.RCN072
noncomputable section
variable (K:Type) [Field K]
abbrev Poly3:=MvPolynomial (Fin 3) K
def freezeCoordinates (v:Fin 3 → K) (n:ℕ):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (fun i => if i.val < n then MvPolynomial.C (v i) else MvPolynomial.X i)
def freezeKernel (v:Fin 3 → K) (n:ℕ):Ideal (Poly3 K):=
 RingHom.ker (freezeCoordinates K v n).toRingHom
instance freezeKernel_isPrime (v:Fin 3 → K) (n:ℕ):
   (freezeKernel K v n).IsPrime:=
 RingHom.ker_isPrime (freezeCoordinates K v n).toRingHom
theorem freeze_comp (v:Fin 3 → K) (n m:ℕ) (hnm:n ≤ m):
   (freezeCoordinates K v m).comp (freezeCoordinates K v n)=
     freezeCoordinates K v m:=by
 ext i
 by_cases hi:i.val < n
 · simp [freezeCoordinates,hi,lt_of_lt_of_le hi hnm]
 · simp [freezeCoordinates,hi]
theorem freezeKernel_mono (v:Fin 3 → K) (n m:ℕ) (hnm:n ≤ m):
   freezeKernel K v n ≤ freezeKernel K v m:=by
 intro F hF
 change freezeCoordinates K v n F=0 at hF
 change freezeCoordinates K v m F=0
 have h:=AlgHom.congr_fun (freeze_comp K v n m hnm) F
 change freezeCoordinates K v m (freezeCoordinates K v n F)=
   freezeCoordinates K v m F at h
 rw [hF,map_zero] at h
 exact h.symm
theorem coordinate_difference_ne_zero (i:Fin 3) (a:K):
   (MvPolynomial.X i-MvPolynomial.C a:Poly3 K)≠0:=by
 intro h
 have h':=congrArg (MvPolynomial.pderiv i) h
 simp at h'
theorem freezeKernel_lt_succ (v:Fin 3 → K) (n:ℕ) (hn:n < 3):
   freezeKernel K v n < freezeKernel K v (n+1):=by
 classical
 let i:Fin 3:=⟨n,hn⟩
 let F:Poly3 K:=MvPolynomial.X i-MvPolynomial.C (v i)
 have hmem:F∈freezeKernel K v (n+1):=by
   change freezeCoordinates K v (n+1) F=0
   simp [freezeCoordinates,F,i]
 have hnot:F∉freezeKernel K v n:=by
   change freezeCoordinates K v n F≠0
   simpa [freezeCoordinates,F,i] using coordinate_difference_ne_zero K i (v i)
 apply lt_of_le_of_ne (freezeKernel_mono K v n (n+1) (Nat.le_succ n))
 intro heq
 exact hnot (heq.symm ▸ hmem)
def pointKernel (v:Fin 3 → K):Ideal (Poly3 K):=
 RingHom.ker (MvPolynomial.aeval v).toRingHom
instance pointKernel_isPrime (v:Fin 3 → K):(pointKernel K v).IsPrime:=
 RingHom.ker_isPrime (MvPolynomial.aeval v).toRingHom
theorem freezeKernel_three (v:Fin 3 → K):
   freezeKernel K v 3=pointKernel K v:=by
 have h:freezeCoordinates K v 3=
     (Algebra.ofId K (Poly3 K)).comp (MvPolynomial.aeval v):=by
   ext i
   simp [freezeCoordinates]
 apply Ideal.ext
 intro F
 change freezeCoordinates K v 3 F=0 ↔ MvPolynomial.aeval v F=0
 rw [h]
 change MvPolynomial.C (MvPolynomial.aeval v F)=0 ↔ _
 simp
theorem pointKernel_height_ge_three (v:Fin 3 → K):
   (3:ℕ∞) ≤ (pointKernel K v).height:=by
 have h01:=Ideal.height_add_one_le_of_lt_of_isPrime
   (freezeKernel_lt_succ K v 0 (by decide))
 have h12:=Ideal.height_add_one_le_of_lt_of_isPrime
   (freezeKernel_lt_succ K v 1 (by decide))
 have h23:=Ideal.height_add_one_le_of_lt_of_isPrime
   (freezeKernel_lt_succ K v 2 (by decide))
 have h1:(1:ℕ∞) ≤ (freezeKernel K v 1).height:=by
   calc
     1=(0:ℕ∞)+1:=by simp
     _ ≤ (freezeKernel K v 0).height+1:=by gcongr;exact zero_le
     _ ≤ (freezeKernel K v 1).height:=h01
 have h2:(2:ℕ∞) ≤ (freezeKernel K v 2).height:=by
   calc
     2=(1:ℕ∞)+1:=by norm_num
     _ ≤ (freezeKernel K v 1).height+1:=by gcongr
     _ ≤ (freezeKernel K v 2).height:=h12
 rw [←freezeKernel_three K v]
 calc
   3=(2:ℕ∞)+1:=by norm_num
   _ ≤ (freezeKernel K v 2).height+1:=by gcongr
   _ ≤ (freezeKernel K v 3).height:=h23
def cutIdeal (F T:Poly3 K):Ideal (Poly3 K):=Ideal.span {F,T}
def componentSet (F T:Poly3 K):Set (Ideal (Poly3 K)):=
 (cutIdeal K F T).minimalPrimes
theorem componentSet_finite (F T:Poly3 K):(componentSet K F T).Finite:=
 Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
def componentFamily (F T:Poly3 K):Finset (Ideal (Poly3 K)):=
 (componentSet_finite K F T).toFinset
@[simp] theorem mem_componentFamily (F T:Poly3 K) (P:Ideal (Poly3 K)):
   P∈componentFamily K F T ↔ P∈(cutIdeal K F T).minimalPrimes:=
 Set.Finite.mem_toFinset _
theorem component_isPrime (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T):P.IsPrime:=
 ((mem_componentFamily K F T P).mp hP).isPrime
theorem cutIdeal_le_component (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T):cutIdeal K F T ≤ P:=
 ((mem_componentFamily K F T P).mp hP).le
theorem component_height_le_two (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T):P.height ≤ 2:=by
 classical
 have hm:P∈(Ideal.span ({F,T}:Finset (Poly3 K))).minimalPrimes:=by
   simpa only [Finset.coe_insert,Finset.coe_singleton,cutIdeal] using
     (mem_componentFamily K F T P).mp hP
 have hh:=Ideal.height_le_card_of_mem_minimalPrimes_span_finset hm
 have hc:({F,T}:Finset (Poly3 K)).card ≤ 2:=
   (Finset.card_insert_le F {T}).trans (by simp)
 exact hh.trans (by exact_mod_cast hc)
theorem exists_component_of_common_point
   (F T:Poly3 K) (v:Fin 3 → K)
   (hF:MvPolynomial.eval v F=0) (hT:MvPolynomial.eval v T=0):
   ∃ P∈componentFamily K F T,P ≤ pointKernel K v:=by
 have hcut:cutIdeal K F T ≤ pointKernel K v:=by
   apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hF
   · exact hT
 obtain ⟨P,hP,hle⟩:=Ideal.exists_minimalPrimes_le hcut
 exact ⟨P,(mem_componentFamily K F T P).mpr hP,hle⟩
theorem component_ne_pointKernel
   (F T:Poly3 K) (P:Ideal (Poly3 K))
   (hP:P∈componentFamily K F T) (v:Fin 3 → K):
   P≠pointKernel K v:=by
 intro heq
 have hle:=component_height_le_two K F T P hP
 rw [heq] at hle
 have hbad:(3:ℕ∞) ≤ 2:=(pointKernel_height_ge_three K v).trans hle
 norm_num at hbad
end
end ProximityPrize.SubmissionLower.RCN072
end PackedLegacy_I5

/-! Packed from ProximityPrize.SubmissionLower.E6. -/
section PackedLegacy_E6
namespace ProximityPrize.SubmissionLower.RCN264
open RCN072
noncomputable section
variable (K:Type) [Field K]
/-- Irreducible, so that the kernel never unfolds it while comparing components of
different cuts (`regularComponentEquiv`): that failed unfolding cost ~20 s per check. -/
irreducible_def regularComponents (G T H:MvPolynomial (Fin 3) K):
   Finset (Ideal (MvPolynomial (Fin 3) K)):=by
 classical
 exact (componentFamily K G T).filter (fun P => H∉P)
theorem mem_regularComponents {G T H:MvPolynomial (Fin 3) K} {P:Ideal (MvPolynomial (Fin 3) K)}:
   P∈regularComponents K G T H ↔ P∈componentFamily K G T ∧ H∉P:=by
 classical
 rw [regularComponents_def]
 exact Finset.mem_filter
abbrev RegularComponent (G T H:MvPolynomial (Fin 3) K):=
 {P:Ideal (MvPolynomial (Fin 3) K)//P∈regularComponents K G T H}
variable (G T H:MvPolynomial (Fin 3) K)
theorem regularComponent_mem (C:RegularComponent K G T H):
   C.1∈componentFamily K G T:=by
 exact ((mem_regularComponents K).mp C.2).1
instance regularComponent_isPrime (C:RegularComponent K G T H):C.1.IsPrime:=
 component_isPrime K G T C.1 (regularComponent_mem K G T H C)
theorem regularComponent_H_not_mem (C:RegularComponent K G T H):H∉C.1:=by
 exact ((mem_regularComponents K).mp C.2).2
theorem regularComponent_G_mem (C:RegularComponent K G T H):G∈C.1:=
 cutIdeal_le_component K G T C.1 (regularComponent_mem K G T H C)
   (Ideal.subset_span (Set.mem_insert G {T}))
theorem regularComponent_T_mem (C:RegularComponent K G T H):T∈C.1:=
 cutIdeal_le_component K G T C.1 (regularComponent_mem K G T H C)
   (Ideal.subset_span (Set.mem_insert_of_mem G (Set.mem_singleton T)))
theorem regularComponent_ne_point (C:RegularComponent K G T H) (v:Fin 3 → K):
   C.1≠RingHom.ker (MvPolynomial.aeval v).toRingHom:=
 component_ne_pointKernel K G T C.1 (regularComponent_mem K G T H C) v
theorem exists_regular_component (v:Fin 3 → K)
   (hG:MvPolynomial.eval v G=0) (hT:MvPolynomial.eval v T=0)
   (hH:MvPolynomial.eval v H≠0):
   ∃ C:RegularComponent K G T H,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
 classical
 obtain ⟨P,hP,hv⟩:=exists_component_of_common_point K G T v hG hT
 have hnot:H∉P:=by
   intro h
   exact hH (hv h)
 exact ⟨⟨P,(mem_regularComponents K).mpr ⟨hP,hnot⟩⟩,hv⟩
def componentSeeds {Seed:Type*} (S:Finset Seed) (v:Seed → Fin 3 → K)
   (C:RegularComponent K G T H):Finset Seed:=by
 classical
 exact S.filter (fun γ => C.1 ≤ RingHom.ker (MvPolynomial.aeval (v γ)).toRingHom)
theorem componentSeeds_subset {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K) (C:RegularComponent K G T H):
   componentSeeds K G T H S v C ⊆ S:=by
 classical
 exact Finset.filter_subset _ _
theorem componentSeeds_on_prime {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K) (C:RegularComponent K G T H)
   (γ:Seed) (hγ:γ∈componentSeeds K G T H S v C):
   C.1 ≤ RingHom.ker (MvPolynomial.aeval (v γ)).toRingHom:=by
 classical
 exact (Finset.mem_filter.mp hγ).2
theorem card_le_sum_componentSeeds {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K)
   (hG:∀ γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀ γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀ γ∈S,MvPolynomial.eval (v γ) H≠0):
   S.card ≤ ∑ C:RegularComponent K G T H,(componentSeeds K G T H S v C).card:=by
 classical
 letI:DecidableEq Seed:=Classical.decEq Seed
 have hcover:S ⊆ Finset.univ.biUnion (componentSeeds K G T H S v):=by
   intro γ hγ
   obtain ⟨C,hC⟩:=exists_regular_component K G T H (v γ) (hG γ hγ) (hT γ hγ) (hH γ hγ)
   apply Finset.mem_biUnion.mpr
   exact ⟨C,Finset.mem_univ C,Finset.mem_filter.mpr ⟨hγ,hC⟩⟩
 exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
theorem aggregate_component_incidence {Seed:Type*}
   (S:Finset Seed) (v:Seed → Fin 3 → K)
   (hG:∀ γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀ γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀ γ∈S,MvPolynomial.eval (v γ) H≠0)
   (gap nodes pencil:ℕ) (cap budget:Fin 3 → ℕ)
   (degree:RegularComponent K G T H → Fin 3 → ℕ)
   (hcomponent:∀ C,
     (componentSeeds K G T H S v C).card*gap ≤
       nodes*(∑ i,cap i*degree C i)+pencil*gap*degree C 2)
   (hbudget:∀ i,(∑ C,degree C i) ≤ budget i):
   S.card*gap ≤ nodes*(∑ i,cap i*budget i)+pencil*gap*budget 2:=by
 classical
 have hfubini:(∑ C:RegularComponent K G T H,∑ i:Fin 3,cap i*degree C i)=
     ∑ i:Fin 3,cap i*(∑ C:RegularComponent K G T H,degree C i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   S.card*gap ≤ (∑ C:RegularComponent K G T H,
       (componentSeeds K G T H S v C).card)*gap:=
     Nat.mul_le_mul_right gap (card_le_sum_componentSeeds K G T H S v hG hT hH)
   _=∑ C:RegularComponent K G T H,
       (componentSeeds K G T H S v C).card*gap:=by rw [Finset.sum_mul]
   _ ≤ ∑ C:RegularComponent K G T H,
       (nodes*(∑ i,cap i*degree C i)+pencil*gap*degree C 2):=
     Finset.sum_le_sum (fun C _ => hcomponent C)
   _=nodes*(∑ i:Fin 3,cap i*(∑ C:RegularComponent K G T H,degree C i))+
       pencil*gap*(∑ C:RegularComponent K G T H,degree C 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ nodes*(∑ i,cap i*budget i)+pencil*gap*budget 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left nodes (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left (cap i) (hbudget i))))
       (Nat.mul_le_mul_left (pencil*gap) (hbudget 2))
end
end ProximityPrize.SubmissionLower.RCN264
end PackedLegacy_E6

/-! Packed from ProximityPrize.SubmissionLower.CM. -/
section PackedLegacy_CM
namespace ProximityPrize.SubmissionLower.RCN354
noncomputable section
variable {K A S:Type*} [Field K] [CommRing A] [CommRing S]
 [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
theorem pointKernel_isMaximal (phi:A →ₐ[K] K):
   (RingHom.ker phi.toRingHom).IsMaximal:=by
 apply RingHom.ker_isMaximal_of_surjective phi.toRingHom
 intro c
 exact ⟨algebraMap K A c,by simp⟩
theorem quotient_scalar_compatibility (phi:A →ₐ[K] K) (N:Ideal S)
   (hN:N.comap (algebraMap A S)=RingHom.ker phi.toRingHom) (a:A):
   Ideal.Quotient.mkₐ K N (algebraMap A S a)=
     algebraMap K (S ⧸ N) (phi a):=by
 have ha:a-algebraMap K A (phi a)∈RingHom.ker phi.toRingHom:=by
   change phi (a-algebraMap K A (phi a))=0
   simp
 have hamem:algebraMap A S (a-algebraMap K A (phi a))∈N:=by
   change a-algebraMap K A (phi a)∈N.comap (algebraMap A S)
   rw [hN]
   exact ha
 have hz:Ideal.Quotient.mkₐ K N
     (algebraMap A S (a-algebraMap K A (phi a)))=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr hamem
 have hconstant (c:K):
     algebraMap A S (algebraMap K A c)=algebraMap K S c:=
   (IsScalarTower.algebraMap_apply K A S c).symm
 apply sub_eq_zero.mp
 simpa [map_sub,hconstant] using hz
section IntegralLift
variable [IsAlgClosed K] [Algebra.IsIntegral A S]
theorem exists_point_lift
   (hinj:Function.Injective (algebraMap A S)) (phi:A →ₐ[K] K):
   ∃ psi:S →ₐ[K] K,psi.comp (IsScalarTower.toAlgHom K A S)=phi:=by
 classical
 letI:(RingHom.ker phi.toRingHom).IsMaximal:=pointKernel_isMaximal phi
 have hker:RingHom.ker (algebraMap A S) ≤ RingHom.ker phi.toRingHom:=by
   rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
   exact bot_le
 obtain ⟨N,hNmax,hN⟩:=Ideal.exists_ideal_over_maximal_of_isIntegral
   (S:=S) (RingHom.ker phi.toRingHom) hker
 letI:N.IsMaximal:=hNmax
 let q:S →ₐ[K] S ⧸ N:=Ideal.Quotient.mkₐ K N
 have hcomp:(algebraMap K (S ⧸ N)).comp phi.toRingHom=
     (Ideal.Quotient.mk N).comp (algebraMap A S):=by
   ext a
   exact (quotient_scalar_compatibility phi N hN a).symm
 letI:Algebra.IsIntegral K (S ⧸ N):=by
   constructor
   intro z
   obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective z
   exact IsIntegral.map_of_comp_eq phi.toRingHom (Ideal.Quotient.mk N) hcomp
     (Algebra.IsIntegral.isIntegral (R:=A) s)
 let e:K ≃ₐ[K] S ⧸ N:=AlgEquiv.ofBijective (Algebra.ofId K (S ⧸ N))
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S ⧸ N))
 let psi:S →ₐ[K] K:=e.symm.toAlgHom.comp q
 refine ⟨psi,?_⟩
 ext a
 change psi (algebraMap A S a)=phi a
 apply e.injective
 change e (e.symm (q (algebraMap A S a)))=e (phi a)
 rw [e.apply_symm_apply]
 have he (c:K):e c=algebraMap K (S ⧸ N) c:=by
   simpa using e.commutes c
 rw [he]
 exact quotient_scalar_compatibility phi N hN a
def chosenPointLift (hinj:Function.Injective (algebraMap A S))
   (phi:A →ₐ[K] K):S →ₐ[K] K:=
 Classical.choose (exists_point_lift hinj phi)
theorem chosenPointLift_spec (hinj:Function.Injective (algebraMap A S))
   (phi:A →ₐ[K] K):
   (chosenPointLift hinj phi).comp (IsScalarTower.toAlgHom K A S)=phi:=
 Classical.choose_spec (exists_point_lift hinj phi)
end IntegralLift
section IntegralBase
variable [IsAlgClosed K] (R:Type*) [CommRing R]
 [Algebra R A] [Algebra R S] [IsScalarTower R A S] [Algebra.IsIntegral R S]
end IntegralBase
end
end ProximityPrize.SubmissionLower.RCN354
end PackedLegacy_CM

/-! Packed from ProximityPrize.SubmissionLower.A. -/
section PackedLegacy_A

end PackedLegacy_A

/- Library component CW is loaded from Mathlib.RingTheory.Finiteness.Quotient. -/

/- Library component S0 is loaded from Mathlib.Algebra.CharP.Quotient. -/

/- Library component HY is loaded from Mathlib.LinearAlgebra.FreeModule.Determinant. -/

/- Library component HN is loaded from Mathlib.Data.Int.Associated. -/

/- Library component HO is loaded from Mathlib.Data.Int.NatAbs. -/

/- Library component IA is loaded from Mathlib.RingTheory.Int.Basic. -/

/- Library component V8 is loaded from Mathlib.RingTheory.ZMod. -/

/- Library component HQ is loaded from Mathlib.Data.ZMod.QuotientRing. -/

/- Library component S2 is loaded from Mathlib.LinearAlgebra.Quotient.Pi. -/

/- Library component CQ is loaded from Mathlib.LinearAlgebra.FreeModule.Finite.Quotient. -/

/- Library component HZ is loaded from Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient. -/

/- Library component U2 is loaded from Mathlib.RingTheory.Ideal.Basis. -/

/- Library component F4 is loaded from Mathlib.RingTheory.Norm.Basic. -/

/- Library component V1 is loaded from Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative. -/

/- Library component CX is loaded from Mathlib.RingTheory.Ideal.Norm.AbsNorm. -/

/- Library component CS is loaded from Mathlib.NumberTheory.RamificationInertia.Inertia. -/

/-! Packed from ProximityPrize.SubmissionLower.CV. -/
section PackedLegacy_CV
/- Definitions supplied by the imported Mathlib boundary. -/
end PackedLegacy_CV

/- Library component T7 is loaded from Mathlib.RingTheory.Finiteness.NilpotentKer. -/

/- Library component IF is loaded from Mathlib.RingTheory.Jacobson.Artinian. -/

/- Library component IZ is loaded from Mathlib.RingTheory.Spectrum.Prime.TensorProduct. -/

/- Library component AT is loaded from Mathlib.RingTheory.LocalRing.ResidueField.Fiber. -/

/- Library component HX is loaded from Mathlib.GroupTheory.Submonoid.Inverses. -/

/- Library component F2 is loaded from Mathlib.RingTheory.Localization.InvSubmonoid. -/

/- Library component W0 is loaded from Mathlib.Topology.JacobsonSpace. -/

/- Library component IY is loaded from Mathlib.RingTheory.Spectrum.Prime.Jacobson. -/

/- Library component CR is loaded from Mathlib.LinearAlgebra.TensorProduct.Prod. -/

/- Library component U9 is loaded from Mathlib.RingTheory.TensorProduct.Pi. -/

/- Library component F5 is loaded from Mathlib.RingTheory.QuasiFinite.Basic. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier01 : True := by trivial
end ProximityPrize.SubmissionLower

/- Library component F7 is loaded from Mathlib.RingTheory.RamificationInertia.Inertia. -/

/-! Packed from ProximityPrize.SubmissionLower.JA. -/
section PackedLegacy_JA
namespace ProximityPrize.SubmissionLower.RCN373
open scoped Classical
noncomputable section
variable {K R S:Type*} [Field K] [CommRing R] [CommRing S]
 [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
 [Algebra.IsIntegral R S]
theorem pointFiber_quotient_integral (phi:R →ₐ[K] K) (P:Ideal S)
   (hP:P.comap (algebraMap R S)=RingHom.ker phi.toRingHom):
   Algebra.IsIntegral K (S ⧸ P):=by
 have hcomp:(algebraMap K (S ⧸ P)).comp phi.toRingHom=
     (Ideal.Quotient.mk P).comp (algebraMap R S):=by
   ext r
   exact (RCN354.quotient_scalar_compatibility phi P hP r).symm
 constructor
 intro z
 obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective z
 exact IsIntegral.map_of_comp_eq phi.toRingHom (Ideal.Quotient.mk P) hcomp
   (Algebra.IsIntegral.isIntegral (R:=R) s)
variable [IsAlgClosed K]
theorem pointFiber_constants_surjective (phi:R →ₐ[K] K) (P:Ideal S)
   [P.IsMaximal]
   (hP:P.comap (algebraMap R S)=RingHom.ker phi.toRingHom):
   Function.Surjective (algebraMap K (S ⧸ P)):=by
 letI:Algebra.IsIntegral K (S ⧸ P):=pointFiber_quotient_integral phi P hP
 exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S ⧸ P)).2
theorem inertiaDeg_eq_one_of_point_fiber (phi:R →ₐ[K] K) (P:Ideal S)
   [P.IsMaximal]
   (hP:P.comap (algebraMap R S)=RingHom.ker phi.toRingHom):
   P.inertiaDeg R=1:=by
 let p:Ideal R:=RingHom.ker phi.toRingHom
 letI:p.IsMaximal:=RCN354.pointKernel_isMaximal phi
 letI:P.LiesOver p:=⟨hP.symm⟩
 letI:Field (R ⧸ p):=Ideal.Quotient.field p
 letI:Field (S ⧸ P):=Ideal.Quotient.field P
 have hsurj:Function.Surjective (algebraMap (R ⧸ p) (S ⧸ P)):=by
   intro z
   obtain ⟨c,hc⟩:=pointFiber_constants_surjective phi P hP z
   refine ⟨algebraMap K (R ⧸ p) c,?_⟩
   rw [←IsScalarTower.algebraMap_apply K (R ⧸ p) (S ⧸ P),hc]
 rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
 exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
   ⟨(algebraMap (R ⧸ p) (S ⧸ P)).injective,hsurj⟩
end
end ProximityPrize.SubmissionLower.RCN373
end PackedLegacy_JA

/- Library component HV is loaded from Mathlib.FieldTheory.RatFunc.Degree. -/

/- Library component AP is loaded from Mathlib.FieldTheory.RatFunc.Valuation. -/

/- Library component G1 is loaded from Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing. -/

/-! Packed from ProximityPrize.SubmissionLower.CL. -/
section PackedLegacy_CL
namespace ProximityPrize.SubmissionLower.RCN353
open scoped Classical
noncomputable section
variable (K:Type*) [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN353.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev InfinityRing:=(RatFunc.inftyValuation K).valuationSubring
instance infinity_isRankOneDiscrete:
   Valuation.IsRankOneDiscrete (RatFunc.inftyValuation K):=inferInstance
instance infinityRing_isDiscreteValuationRing:
   IsDiscreteValuationRing (InfinityRing K):=inferInstance
theorem infinityRing_isFractionRing:
   IsFractionRing (InfinityRing K) (RatFunc K):=inferInstance
def infinityUniformizer:InfinityRing K:=by
 refine ⟨(RatFunc.X:RatFunc K)⁻¹,?_⟩
 change RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹ ≤ 1
 rw [show RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹=
     WithZero.exp (-1:ℤ) by
   simpa only [one_div] using RatFunc.inftyValuation.X_inv K]
 rw [←WithZero.exp_zero,WithZero.exp_le_exp]
 norm_num
theorem infinityUniformizer_value:
   RatFunc.inftyValuation K
     (algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K))=
     WithZero.exp (-1:ℤ):=by
 change RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹=_
 simpa only [one_div] using RatFunc.inftyValuation.X_inv K
theorem infinityUniformizer_isUniformizer:
   (RatFunc.inftyValuation K).IsUniformizer
     (algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K)):=by
 unfold Valuation.IsUniformizer
 rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
   (v:=RatFunc.inftyValuation K)
   ⟨algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K),
     infinityUniformizer_value K⟩]
 exact infinityUniformizer_value K
theorem infinityUniformizer_ne_zero:infinityUniformizer K≠0:=by
 intro hzero
 have h:=(infinityUniformizer_isUniformizer K).ne_zero
 exact h (by rw [hzero,map_zero])
theorem infinity_maximalIdeal_eq_span:
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).asIdeal=
     Ideal.span {infinityUniformizer K}:=
 (infinityUniformizer_isUniformizer K).is_generator
theorem infinityUniformizer_irreducible:Irreducible (infinityUniformizer K):=
 (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
   (infinity_maximalIdeal_eq_span K)
theorem infinity_intValuation_eq (x:InfinityRing K):
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation x=
     RatFunc.inftyValuation K (algebraMap (InfinityRing K) (RatFunc K) x):=by
 by_cases hx:x=0
 · simp [hx]
 obtain ⟨n,u,rfl⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
   hx (infinityUniformizer_irreducible K)
 have hunit:
     (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation
       (u:InfinityRing K)=1:=by
   simp [IsDiscreteValuationRing.maximalIdeal]
 have hunit':
     RatFunc.inftyValuation K
       (algebraMap (InfinityRing K) (RatFunc K) (u:InfinityRing K))=1:=
   Valuation.Integers.one_of_isUnit
     (Valuation.valuationSubring.integers (RatFunc.inftyValuation K)) u.isUnit
 have hparameter:
     (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation
       (infinityUniformizer K)=WithZero.exp (-1:ℤ):=
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation_singleton
     (infinityUniformizer_ne_zero K) (infinity_maximalIdeal_eq_span K)
 simp only [map_mul,map_pow,hunit,hunit',hparameter,
   infinityUniformizer_value,one_mul]
theorem infinity_valuation_eq (x:RatFunc K):
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).valuation (RatFunc K) x=
     RatFunc.inftyValuation K x:=by
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=InfinityRing K) x
 simp only [map_div₀,
   IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
   infinity_intValuation_eq]
end
end ProximityPrize.SubmissionLower.RCN353
end PackedLegacy_CL

/-! Packed from ProximityPrize.SubmissionLower.R8. -/
section PackedLegacy_R8
namespace ProximityPrize.SubmissionLower.RCN352
open scoped Classical WithZero
noncomputable section
variable (K:Type*) [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN352.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev InfinityRing:=RCN353.InfinityRing K
def constantMap:K →+*InfinityRing K where
 toFun c:=⟨RatFunc.C c,by
   change RatFunc.inftyValuation K (RatFunc.C c) ≤ 1
   by_cases hc:c=0
   · simp [hc]
   · exact le_of_eq (RatFunc.inftyValuation.C K hc)⟩
 map_zero':=Subtype.ext (map_zero RatFunc.C)
 map_one':=Subtype.ext (map_one RatFunc.C)
 map_add' c d:=Subtype.ext (map_add RatFunc.C c d)
 map_mul' c d:=Subtype.ext (map_mul RatFunc.C c d)
theorem polynomial_quotient_value_lt_one
   (f g:Polynomial K) (hg:g≠0) (hdeg:f.degree < g.degree):
   RatFunc.inftyValuation K
     (algebraMap (Polynomial K) (RatFunc K) f/
       algebraMap (Polynomial K) (RatFunc K) g) < 1:=by
 by_cases hf:f=0
 · simp [hf]
 have hfmap:algebraMap (Polynomial K) (RatFunc K) f≠0:=by
   simpa using hf
 have hgmap:algebraMap (Polynomial K) (RatFunc K) g≠0:=by
   simpa using hg
 have hquot:=div_ne_zero hfmap hgmap
 have hnat:f.natDegree < g.natDegree:=by
   rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg] at hdeg
   exact_mod_cast hdeg
 rw [RatFunc.inftyValuation_apply,
   RatFunc.inftyValuation_of_nonzero K hquot,
   RatFunc.intDegree_div hfmap hgmap,
   RatFunc.intDegree_polynomial,RatFunc.intDegree_polynomial,
   ←WithZero.exp_zero,WithZero.exp_lt_exp]
 exact sub_neg.mpr (Int.ofNat_lt.mpr hnat)
theorem exists_constant_difference_lt_one (r:InfinityRing K):
   ∃ c:K,RatFunc.inftyValuation K (r.val-RatFunc.C c) < 1:=by
 by_cases hr:r.val=0
 · exact ⟨0,by simp [hr]⟩
 have hf:r.val.num≠0:=RatFunc.num_ne_zero hr
 have hg:r.val.denom≠0:=r.val.denom_ne_zero
 have hdegree:r.val.num.natDegree ≤ r.val.denom.natDegree:=by
   have hmem:RatFunc.inftyValuation K r.val ≤ 1:=r.property
   rw [RatFunc.inftyValuation_apply,
     RatFunc.inftyValuation_of_nonzero K hr,
     ←WithZero.exp_zero,WithZero.exp_le_exp] at hmem
   dsimp [RatFunc.intDegree] at hmem
   omega
 by_cases hstrict:r.val.num.natDegree < r.val.denom.natDegree
 · refine ⟨0,?_⟩
   have hd:r.val.num.degree < r.val.denom.degree:=by
     rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg]
     exact_mod_cast hstrict
   have h:=polynomial_quotient_value_lt_one K r.val.num r.val.denom hg hd
   simpa only [RatFunc.num_div_denom,map_zero,sub_zero] using h
 · have hsame:r.val.num.natDegree=r.val.denom.natDegree:=by omega
   have hdegfg:r.val.num.degree=r.val.denom.degree:=by
     rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg,hsame]
   let c:K:=r.val.num.leadingCoeff
   have hc:c≠0:=Polynomial.leadingCoeff_ne_zero.mpr hf
   have hpc:r.val.num.degree=(Polynomial.C c*r.val.denom).degree:=by
     rw [Polynomial.degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc)]
     exact hdegfg
   have hlc:r.val.num.leadingCoeff=
       (Polynomial.C c*r.val.denom).leadingCoeff:=by
     rw [(RatFunc.monic_denom r.val).leadingCoeff_C_mul]
   have hcancel:
       (r.val.num-Polynomial.C c*r.val.denom).degree < r.val.denom.degree:=
     (Polynomial.degree_sub_lt hpc hf hlc).trans_eq hdegfg
   have hgmap:algebraMap (Polynomial K) (RatFunc K) r.val.denom≠0:=by
     simpa using hg
   have hquot:r.val-RatFunc.C c=
       algebraMap (Polynomial K) (RatFunc K)
         (r.val.num-Polynomial.C c*r.val.denom)/
       algebraMap (Polynomial K) (RatFunc K) r.val.denom:=by
     calc
       r.val-RatFunc.C c=
           algebraMap (Polynomial K) (RatFunc K) r.val.num/
             algebraMap (Polynomial K) (RatFunc K) r.val.denom-RatFunc.C c:=by
         rw [RatFunc.num_div_denom]
       _=(algebraMap (Polynomial K) (RatFunc K) r.val.num-
             RatFunc.C c*algebraMap (Polynomial K) (RatFunc K) r.val.denom)/
             algebraMap (Polynomial K) (RatFunc K) r.val.denom:=by
         rw [sub_div,mul_div_cancel_right₀ _ hgmap]
       _=_:=by rw [map_sub,map_mul,RatFunc.algebraMap_C]
   refine ⟨c,?_⟩
   rw [hquot]
   exact polynomial_quotient_value_lt_one K
     (r.val.num-Polynomial.C c*r.val.denom) r.val.denom hg hcancel
theorem exists_constant_difference_mem_maximalIdeal (r:InfinityRing K):
   ∃ c:K,r-constantMap K c∈IsLocalRing.maximalIdeal (InfinityRing K):=by
 obtain ⟨c,hc⟩:=exists_constant_difference_lt_one K r
 refine ⟨c,?_⟩
 apply (Valuation.mem_maximalIdeal_iff (RatFunc K) (RatFunc.inftyValuation K)).mpr
 exact hc
abbrev ResidueField:=InfinityRing K ⧸ IsLocalRing.maximalIdeal (InfinityRing K)
def residueConstant:K →+*ResidueField K:=
 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityRing K))).comp (constantMap K)
theorem residueConstant_injective:Function.Injective (residueConstant K):=
 (residueConstant K).injective
theorem residueConstant_surjective:Function.Surjective (residueConstant K):=by
 intro y
 obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y
 obtain ⟨c,hc⟩:=exists_constant_difference_mem_maximalIdeal K r
 refine ⟨c,?_⟩
 have hz:=Ideal.Quotient.eq_zero_iff_mem.mpr hc
 have heq:Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityRing K)) r=
     residueConstant K c:=by
   apply sub_eq_zero.mp
   simpa only [map_sub,residueConstant,RingHom.comp_apply] using hz
 exact heq.symm
def residueEquiv:K ≃+*ResidueField K:=
 RingEquiv.ofBijective (residueConstant K)
   ⟨residueConstant_injective K,residueConstant_surjective K⟩
theorem residueEquiv_apply (c:K):residueEquiv K c=residueConstant K c:=rfl
end
end ProximityPrize.SubmissionLower.RCN352
end PackedLegacy_R8

/- Library component V6 is loaded from Mathlib.RingTheory.Valuation.Integral. -/

/-! Packed from ProximityPrize.SubmissionLower.W5. -/
section PackedLegacy_W5
namespace ProximityPrize.SubmissionLower.RCN359
open scoped Classical nonZeroDivisors WithZero
open IsDedekindDomain
noncomputable section
section NormalizedEquality
variable {L:Type*} [Field L]
local instance _root_.ProximityPrize.SubmissionLower.RCN359.instDecidableEq_proximityPrize :DecidableEq L:=Classical.decEq L
theorem value_le_exp_neg_one {z:ℤᵐ⁰} (hz:z < 1):
   z ≤ WithZero.exp (-1:ℤ):=by
 by_cases hz0:z=0
 · simp [hz0]
 have hlog:z.log < 0:=by
   have h:WithZero.exp z.log < WithZero.exp (0:ℤ):=by
     simpa only [WithZero.exp_log hz0,WithZero.exp_zero] using hz
   exact WithZero.exp_lt_exp.mp h
 calc
   z=WithZero.exp z.log:=(WithZero.exp_log hz0).symm
   _ ≤ WithZero.exp (-1:ℤ):=WithZero.exp_le_exp.mpr (by omega)
theorem eq_of_equiv_surjective (v w:Valuation L ℤᵐ⁰)
   (hv:Function.Surjective v) (hw:Function.Surjective w)
   (h:v.IsEquiv w):v=w:=by
 have hneg:WithZero.exp (-1:ℤ) < 1:=by
   rw [←WithZero.exp_zero,WithZero.exp_lt_exp]
   norm_num
 obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
 have hvπlt:v π < 1:=hπ ▸ hneg
 have hwπlt:w π < 1:=h.lt_one_iff_lt_one.mp hvπlt
 have hlower:WithZero.exp (-1:ℤ) ≤ w π:=by
   obtain ⟨a,ha⟩:=hw (WithZero.exp (-1:ℤ))
   have haw:w a < 1:=ha ▸ hneg
   have hav:v a < 1:=h.lt_one_iff_lt_one.mpr haw
   have hal:v a ≤ v π:=hπ ▸ value_le_exp_neg_one hav
   have hal':w a ≤ w π:=(h a π).mp hal
   simpa only [ha] using hal'
 have hwπ:w π=WithZero.exp (-1:ℤ):=
   le_antisymm (value_le_exp_neg_one hwπlt) hlower
 ext x
 by_cases hx:x=0
 · simp [hx]
 have hvx:v x≠0:=(Valuation.ne_zero_iff v).mpr hx
 have hpower:v (π^(-(v x).log))=v x:=by
   simp [hπ,WithZero.exp_log hvx]
 have hpower':w (π^(-(v x).log))=v x:=by
   simp [hwπ,WithZero.exp_log hvx]
 exact hpower'.symm.trans (h.eq_iff.mp hpower)
end NormalizedEquality
section UnitBall
variable (R L:Type*) [CommRing R] [Field L] [Algebra R L]
 (v:Valuation L ℤᵐ⁰) (hR:∀ r:R,v (algebraMap R L r) ≤ 1)
def unitBallMap:R →+*v.valuationSubring where
 toFun r:=⟨algebraMap R L r,hR r⟩
 map_zero':=Subtype.ext (map_zero _)
 map_one':=Subtype.ext (map_one _)
 map_add' r s:=Subtype.ext (map_add _ r s)
 map_mul' r s:=Subtype.ext (map_mul _ r s)
include hR in
theorem integral_le_one {x:L} (hx:IsIntegral R x):v x ≤ 1:=by
 letI:Algebra R v.valuationSubring:=(unitBallMap R L v hR).toAlgebra
 letI:IsScalarTower R v.valuationSubring L:=
   IsScalarTower.of_algebraMap_eq' rfl
 have hx':IsIntegral v.valuationSubring x:=hx.tower_top
 exact (Valuation.valuationSubring.integers v).isIntegral_iff_v_le_one.mp hx'
def centerIdeal:Ideal R:=
 Ideal.comap (unitBallMap R L v hR) (IsLocalRing.maximalIdeal v.valuationSubring)
instance centerIdeal_isPrime:(centerIdeal R L v hR).IsPrime:=by
 unfold centerIdeal
 infer_instance
theorem mem_centerIdeal (r:R):
   r∈centerIdeal R L v hR ↔ v (algebraMap R L r) < 1:=by
 change unitBallMap R L v hR r∈IsLocalRing.maximalIdeal v.valuationSubring ↔ _
 exact Valuation.mem_maximalIdeal_iff L v
end UnitBall
section Center
variable (S L:Type*) [CommRing S] [IsDedekindDomain S] [Field L]
 [Algebra S L] [IsFractionRing S L]
 (v:Valuation L ℤᵐ⁰) (hS:∀ s:S,v (algebraMap S L s) ≤ 1)
theorem centerIdeal_ne_bot (hv:Function.Surjective v):
   centerIdeal S L v hS≠⊥:=by
 obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
 have hπ0:π≠0:=by
   apply (Valuation.ne_zero_iff v).mp
   rw [hπ]
   exact WithZero.exp_ne_zero
 obtain ⟨a,b,hb,hfrac⟩:=IsFractionRing.div_surjective (A:=S) π
 have hb0:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have ha0:a≠0:=by
   intro hzero
   apply hπ0
   simpa [hzero] using hfrac.symm
 have hvb0:v (algebraMap S L b)≠0:=
   (Valuation.ne_zero_iff v).mpr (by
     simpa only [map_zero] using (IsFractionRing.injective S L).ne hb0)
 have hfraclt:v (algebraMap S L a)/v (algebraMap S L b) < 1:=by
   rw [←map_div₀,hfrac,hπ, ←WithZero.exp_zero,WithZero.exp_lt_exp]
   norm_num
 have halt:v (algebraMap S L a) < 1:=
   ((div_lt_one₀ (zero_lt_iff.mpr hvb0)).mp hfraclt).trans_le (hS b)
 intro hbot
 have ha:=(mem_centerIdeal S L v hS a).mpr halt
 exact ha0 (by simpa only [hbot,Ideal.mem_bot] using ha)
def centerPlace (hv:Function.Surjective v):HeightOneSpectrum S:=
 ⟨centerIdeal S L v hS,inferInstance,centerIdeal_ne_bot S L v hS hv⟩
theorem centerPlace_membership (hv:Function.Surjective v) (s:S):
   s∈(centerPlace S L v hS hv).asIdeal ↔
     v (algebraMap S L s) < 1:=
 mem_centerIdeal S L v hS s
open scoped algebraMap in
theorem center_localization_le (hv:Function.Surjective v):
   HeightOneSpectrum.valuationSubringAtPrime L (centerPlace S L v hS hv) ≤
     v.valuationSubring:=by
 rintro x ⟨a,s,hs,rfl⟩
 have hsnot:s∉(centerPlace S L v hS hv).asIdeal:=hs
 have hsvalue:v (algebraMap S L s)=1:=by
   apply le_antisymm (hS s)
   exact le_of_not_gt fun hlt↦hsnot ((centerPlace_membership S L v hS hv s).mpr hlt)
 suffices v ((algebraMap S L a)/(algebraMap S L s)) ≤ 1 by
   rwa [division_def] at this
 rw [map_div₀,hsvalue,div_one]
 exact hS a
theorem centerPlace_valuation (hv:Function.Surjective v):
   v=(centerPlace S L v hS hv).valuation L:=by
 let p:=centerPlace S L v hS hv
 have hnontrivial:v.IsNontrivial:=by
   obtain ⟨π,hπ⟩:=hv (WithZero.exp (-1:ℤ))
   refine ⟨π,?_⟩
   simp [hπ]
 have htop:v.valuationSubring≠⊤:=by
   simpa only [ne_eq,Valuation.valuationSubring_eq_top_iff,not_not] using hnontrivial
 have hring:HeightOneSpectrum.valuationSubringAtPrime L p=v.valuationSubring:=
   ValuationSubring.eq_of_le_of_ne_top _
     (center_localization_le S L v hS hv) htop
 rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hring
 have hequiv:(p.valuation L).IsEquiv v:=
   (Valuation.isEquiv_iff_valuationSubring _ _).mpr hring
 exact (eq_of_equiv_surjective (p.valuation L) v
   (p.valuation_surjective L) hv hequiv).symm
include hS in
theorem exists_unique_place (hv:Function.Surjective v):
   ∃! p:HeightOneSpectrum S,v=p.valuation L:=by
 refine ⟨centerPlace S L v hS hv,centerPlace_valuation S L v hS hv,?_⟩
 intro q hq
 apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K:=L)
 exact Valuation.IsEquiv.of_eq
   (hq.symm.trans (centerPlace_valuation S L v hS hv))
end Center
end
end ProximityPrize.SubmissionLower.RCN359
end PackedLegacy_W5

/- Library component F8 is loaded from Mathlib.RingTheory.RingHom.Finite. -/

/- Library component IR is loaded from Mathlib.RingTheory.Norm.Transitivity. -/

/- Library component T1 is loaded from Mathlib.RingTheory.Discriminant. -/

/- Library component IM is loaded from Mathlib.RingTheory.Localization.NormTrace. -/

/- Library component IB is loaded from Mathlib.RingTheory.IntegralClosure.IntegralRestrict. -/

/- Library component IC is loaded from Mathlib.RingTheory.Invariant.Galois. -/

/- Library component U5 is loaded from Mathlib.RingTheory.Ideal.IsPrincipal. -/

/- Library component T8 is loaded from Mathlib.RingTheory.Flat.TorsionFree. -/

/- Library component HD is loaded from Mathlib.Algebra.GroupWithZero.Torsion. -/

/- Library component AR is loaded from Mathlib.NumberTheory.RamificationInertia.Ramification. -/

/- Library component AS is loaded from Mathlib.RingTheory.LocalRing.Length. -/

/- Library component IJ is loaded from Mathlib.RingTheory.LocalRing.ResidueField.Instances. -/

/- Library component V2 is loaded from Mathlib.RingTheory.Unramified.Finite. -/

/- Library component V4 is loaded from Mathlib.RingTheory.Unramified.Locus. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier02 : True := by trivial
end ProximityPrize.SubmissionLower

/- Library component G0 is loaded from Mathlib.RingTheory.Unramified.Field. -/

/- Library component V3 is loaded from Mathlib.RingTheory.Unramified.LocalRing. -/

/- Library component IU is loaded from Mathlib.RingTheory.RamificationInertia.Ramification. -/

/- Library component II is loaded from Mathlib.RingTheory.LocalProperties.Projective. -/

/- Library component IL is loaded from Mathlib.RingTheory.Localization.Free. -/

/- Library component W1 is loaded from Mathlib.Topology.LocallyConstant.Basic. -/

/- Library component U8 is loaded from Mathlib.RingTheory.TensorProduct.IsBaseChangePi. -/

/- Library component IX is loaded from Mathlib.RingTheory.Spectrum.Prime.FreeLocus. -/

/- Library component F6 is loaded from Mathlib.RingTheory.RamificationInertia.Basic. -/

/- Library component S4 is loaded from Mathlib.NumberTheory.RamificationInertia.Galois. -/

/- Library component V0 is loaded from Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp. -/

/- Library component S8 is loaded from Mathlib.RingTheory.DedekindDomain.Factorization. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier03 : True := by trivial
end ProximityPrize.SubmissionLower

/- Library component T0 is loaded from Mathlib.RingTheory.DedekindDomain.PID. -/

/- Library component S9 is loaded from Mathlib.RingTheory.DedekindDomain.Instances. -/

/- Library component U4 is loaded from Mathlib.RingTheory.Ideal.Int. -/

/- Library component IS is loaded from Mathlib.RingTheory.NormalClosure. -/

/- Library component U6 is loaded from Mathlib.RingTheory.Ideal.Norm.RelNorm. -/

/-! Packed from ProximityPrize.SubmissionLower.W9. -/
section PackedLegacy_W9
namespace ProximityPrize.SubmissionLower.RCN367
noncomputable section
section Fields
variable (F E Ω:Type*) [Field F] [Field E] [Field Ω]
 [Algebra F E] [Algebra F Ω] [Algebra.IsSeparable F E]
theorem normalClosure_isSeparable:
   Algebra.IsSeparable F (IntermediateField.normalClosure F E Ω):=by
 letI:∀ σ:E →ₐ[F] Ω,Algebra.IsSeparable F σ.fieldRange:=
   fun σ↦AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField σ)
 change Algebra.IsSeparable F
   (⨆ σ:E →ₐ[F] Ω,σ.fieldRange:IntermediateField F Ω)
 infer_instance
end Fields
section Domains
variable (R S:Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
 [Algebra R S] [Module.IsTorsionFree R S]
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instAlgebraFractionRing_proximityPrize :Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R)
 (FractionRing S) (AlgebraicClosure (FractionRing S))
local notation3 "T" => Ring.NormalClosure R S
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instAlgebraSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize :Algebra S E:=
 ((algebraMap L E).comp (algebraMap S L)).toAlgebra
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsScalarTowerFractionRingSubtypeAlgebraicClosureMemIntermediateFieldNormalClosure_proximityPrize :IsScalarTower S L E:=IsScalarTower.of_algebraMap_eq' rfl
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instAlgebraNormalClosureSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize :Algebra T E:=
 inferInstanceAs (Algebra (integralClosure S E) E)
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsScalarTowerNormalClosureSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize :IsScalarTower S T E:=
 inferInstanceAs (IsScalarTower S (integralClosure S E) E)
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsIntegralClosureNormalClosureSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize :IsIntegralClosure T S E:=integralClosure.isIntegralClosure S E
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsScalarTowerFractionRingSubtypeAlgebraicClosureMemIntermediateFieldNormalClosure_proximityPrize_1 :IsScalarTower R L E:=IsScalarTower.to₁₃₄ R K L E
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsScalarTowerSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize :IsScalarTower R S E:=IsScalarTower.to₁₂₄ R S L E
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsScalarTowerNormalClosureSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize_1 :IsScalarTower R T E:=IsScalarTower.to₁₃₄ R S T E
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instFaithfulSMulSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize :FaithfulSMul S E:=
 (faithfulSMul_iff_algebraMap_injective S E).mpr <|
   (FaithfulSMul.algebraMap_injective L E).comp
     (FaithfulSMul.algebraMap_injective S L)
variable [Module.Finite R S]
 [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instFiniteDimensionalFractionRingSubtypeAlgebraicClosureMemIntermediateFieldNormalClosure_proximityPrize :FiniteDimensional L E:=Module.Finite.right K L E
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsFractionRingNormalClosureSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure_proximityPrize :IsFractionRing T E:=
 integralClosure.isFractionRing_of_finite_extension L E
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsSeparableFractionRingSubtypeAlgebraicClosureMemIntermediateFieldNormalClosure_proximityPrize :Algebra.IsSeparable K E:=
 normalClosure_isSeparable K L (AlgebraicClosure L)
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsGaloisFractionRingSubtypeAlgebraicClosureMemIntermediateFieldNormalClosure_proximityPrize :IsGalois K E where
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsSeparableFractionRingSubtypeAlgebraicClosureMemIntermediateFieldNormalClosure_proximityPrize_1 :Algebra.IsSeparable L E:=
 Algebra.isSeparable_tower_top_of_isSeparable K L E
theorem normalClosure_fractionRing_isGalois:
   IsGalois K (FractionRing T):=by
 refine IsGalois.of_equiv_equiv (F:=K) («E»:=E)
   (f:=(FractionRing.algEquiv R K).symm.toRingEquiv)
   (g:=(FractionRing.algEquiv T E).symm.toRingEquiv) ?_
 ext
 simpa using! IsFractionRing.algEquiv_commutes
   (FractionRing.algEquiv R K).symm (FractionRing.algEquiv T E).symm _
variable [IsDedekindDomain S]
theorem normalClosure_finite:Module.Finite S T:=
 IsIntegralClosure.finite S L E T
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instFiniteNormalClosure_proximityPrize :Module.Finite S T:=normalClosure_finite R S
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instFiniteNormalClosure_proximityPrize_1 :Module.Finite R T:=Module.Finite.trans S T
theorem normalClosure_isDedekindDomain:IsDedekindDomain T:=
 integralClosure.isDedekindDomain S L E
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsDedekindDomainNormalClosure_proximityPrize :IsDedekindDomain T:=normalClosure_isDedekindDomain R S
local instance _root_.ProximityPrize.SubmissionLower.RCN367.instIsGaloisFractionRingNormalClosure_proximityPrize :IsGalois K (FractionRing T):=
 normalClosure_fractionRing_isGalois R S
variable [IsDedekindDomain R]
attribute [local instance] FractionRing.liftAlgebra
theorem relNorm_prime_eq_pow
   (P:Ideal S) (p:Ideal R) [P.LiesOver p]
   [P.IsMaximal] [p.IsMaximal]:
   Ideal.relNorm R P=p^P.inertiaDeg R:=by
 obtain ⟨Q,hQmax,hQP⟩:
     ∃ Q:Ideal T,Q.IsMaximal∧Q.LiesOver P:=
   Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
 have:Q.LiesOver p:=Ideal.LiesOver.trans Q P p
 have h:=Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
 have:IsGalois (FractionRing S) (FractionRing T):=
   IsGalois.tower_top_of_isGalois
     (FractionRing R) (FractionRing S) (FractionRing T)
 rwa [←Ideal.relNorm_relNorm R S,
   Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P,map_pow,
   Ideal.inertiaDeg_tower (R:=R) P Q,pow_mul,
   pow_left_inj (Ideal.inertiaDeg_pos Q S).ne'] at h
end Domains
end
end ProximityPrize.SubmissionLower.RCN367
end PackedLegacy_W9

/-! Packed from ProximityPrize.SubmissionLower.G2. -/
section PackedLegacy_G2
namespace ProximityPrize.SubmissionLower.RCN356
open scoped BigOperators nonZeroDivisors
open UniqueFactorizationMonoid IsDedekindDomain
noncomputable section
section Orders
variable {A:Type*} [CommRing A] [IsDedekindDomain A]
def orderAt (v:HeightOneSpectrum A) (x:FractionRing A):ℤ:=
 -(v.valuation (FractionRing A) x).log
theorem orderAt_algebraMap (v:HeightOneSpectrum A) (x:A) (hx:x≠0):
   orderAt v (algebraMap A (FractionRing A) x)=
     ((normalizedFactors (Ideal.span {x})).count v.asIdeal:ℤ):=by
 rw [orderAt,v.valuation_of_algebraMap,v.intValuation_if_neg hx,
   WithZero.log_exp,neg_neg,
   Ideal.count_associates_factors_eq (by simpa using hx) v.isPrime v.ne_bot]
theorem orderAt_div (v:HeightOneSpectrum A) (x y:FractionRing A)
   (hx:x≠0) (hy:y≠0):
   orderAt v (x/y)=orderAt v x-orderAt v y:=by
 unfold orderAt
 rw [map_div₀,WithZero.log_div (by simpa using hx) (by simpa using hy)]
 ring
end Orders
section FixedExtension
variable (R S:Type*) [CommRing R] [CommRing S]
 [IsDedekindDomain R] [IsDedekindDomain S]
 [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
local instance _root_.ProximityPrize.SubmissionLower.RCN356.instAlgebraFractionRing_proximityPrize :Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
def primeFiber (v:HeightOneSpectrum R):Finset (Ideal S):=
 IsDedekindDomain.primesOverFinset v.asIdeal S
theorem mem_primeFiber_iff (v:HeightOneSpectrum R) (P:Ideal S):
   P∈primeFiber R S v ↔ P.IsPrime∧P.LiesOver v.asIdeal:=
 IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S
def fiberPlace (v:HeightOneSpectrum R)
   (P:{P:Ideal S//P∈primeFiber R S v}):HeightOneSpectrum S:=
 ⟨P.1,((mem_primeFiber_iff R S v P.1).mp P.2).1,
   Ideal.ne_bot_of_mem_primesOver v.ne_bot
     ((mem_primeFiber_iff R S v P.1).mp P.2)⟩
theorem factorCount_relNorm_prime (v:HeightOneSpectrum R)
   (P:Ideal S) (hPzero:P≠⊥) (hPprime:P.IsPrime):
   (normalizedFactors (Ideal.relNorm R P)).count v.asIdeal=
     if P.under R=v.asIdeal then P.inertiaDeg R else 0:=by
 classical
 letI:P.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hPzero hPprime
 have hUnderZero:P.under R≠⊥:=
   mt Ideal.eq_bot_of_comap_eq_bot hPzero
 have hUnderPrime:(P.under R).IsPrime:=inferInstance
 have hUnderIrred:Irreducible (P.under R):=
   (Ideal.prime_of_isPrime hUnderZero hUnderPrime).irreducible
 rw [RCN367.relNorm_prime_eq_pow R S P (P.under R),
   hUnderIrred.normalizedFactors_pow,normalize_eq,Multiset.count_replicate]
theorem factorCount_relNorm (v:HeightOneSpectrum R)
   (I:Ideal S) (hI:I≠⊥):
   (normalizedFactors (Ideal.relNorm R I)).count v.asIdeal=
     ∑ P∈primeFiber R S v,
       P.inertiaDeg R*(normalizedFactors I).count P:=by
 classical
 let C:Ideal S → Prop:=fun J↦J≠0∧
   (normalizedFactors (Ideal.relNorm R J)).count v.asIdeal=
     ∑ P∈primeFiber R S v,
       P.inertiaDeg R*(normalizedFactors J).count P
 have hC:C (normalizedFactors I).prod:=by
   refine Multiset.prod_induction C (normalizedFactors I) ?_ ?_ ?_
   · intro J K hJ hK
     change _∧_ at hJ hK ⊢
     refine ⟨mul_ne_zero hJ.1 hK.1,?_⟩
     have hNJ:Ideal.relNorm R J≠0:=by simpa using hJ.1
     have hNK:Ideal.relNorm R K≠0:=by simpa using hK.1
     rw [map_mul,normalizedFactors_mul hNJ hNK,Multiset.count_add,
       hJ.2,hK.2,normalizedFactors_mul hJ.1 hK.1]
     simp only [Multiset.count_add,mul_add,Finset.sum_add_distrib]
   · change _∧_
     exact ⟨one_ne_zero,by
       simp only [map_one,normalizedFactors_one,Multiset.count_zero,
         mul_zero,Finset.sum_const_zero]⟩
   · intro P hP
     have hPzero:P≠⊥:=ne_zero_of_mem_normalizedFactors hP
     have hPprime:P.IsPrime:=(Ideal.mem_normalizedFactors_iff hI).mp hP |>.1
     have hPirred:Irreducible P:=
       (Ideal.prime_of_isPrime hPzero hPprime).irreducible
     have hFactors:normalizedFactors P={P}:=by
       simpa using normalizedFactors_irreducible hPirred
     change _∧_
     refine ⟨hPzero,?_⟩
     rw [factorCount_relNorm_prime R S v P hPzero hPprime,hFactors]
     by_cases hUnder:P.under R=v.asIdeal
     · letI:P.LiesOver v.asIdeal:=by rw [←hUnder];infer_instance
       have hMem:P∈primeFiber R S v:=
         (mem_primeFiber_iff R S v P).mpr ⟨hPprime,inferInstance⟩
       simp [hUnder,Multiset.count_singleton,hMem]
     · have hNotMem:P∉primeFiber R S v:=by
         intro hMem
         letI:P.LiesOver v.asIdeal:=
           ((mem_primeFiber_iff R S v P).mp hMem).2
         exact hUnder (Ideal.over_def P v.asIdeal).symm
       simp [hUnder,Multiset.count_singleton,hNotMem]
 have hCI:C I:=by
   rwa [Ideal.prod_normalizedFactors_eq_self hI] at hC
 exact hCI.2
theorem orderAt_intNorm (v:HeightOneSpectrum R) (x:S) (hx:x≠0):
   orderAt v (algebraMap R (FractionRing R) (Algebra.intNorm R S x))=
     ∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*
         orderAt (fiberPlace R S v P)
           (algebraMap S (FractionRing S) x):=by
 classical
 have hCount:=factorCount_relNorm R S v (Ideal.span {x}) (by simpa using hx)
 rw [Ideal.relNorm_singleton] at hCount
 have hTerms:
     (∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*
         orderAt (fiberPlace R S v P)
           (algebraMap S (FractionRing S) x))=
     ∑ P∈primeFiber R S v,
       (P.inertiaDeg R:ℤ)*((normalizedFactors (Ideal.span {x})).count P:ℤ):=by
   calc
     _=∑ P∈(primeFiber R S v).attach,
         (P.1.inertiaDeg R:ℤ)*
           ((normalizedFactors (Ideal.span {x})).count P.1:ℤ):=by
       apply Finset.sum_congr rfl
       intro P _
       rw [orderAt_algebraMap _ x hx]
       rfl
     _=_:=Finset.sum_attach (primeFiber R S v)
       (fun P:Ideal S↦(P.inertiaDeg R:ℤ)*
         ((normalizedFactors (Ideal.span {x})).count P:ℤ))
 rw [hTerms,orderAt_algebraMap v (Algebra.intNorm R S x) (by simpa using hx)]
 exact_mod_cast hCount
theorem orderAt_fieldNorm (v:HeightOneSpectrum R)
   (x:FractionRing S) (hx:x≠0):
   orderAt v (Algebra.norm (FractionRing R) x)=
     ∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*orderAt (fiberPlace R S v P) x:=by
 classical
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=S) x
 have hbzero:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have hazero:a≠0:=by
   intro ha
   apply hx
   simp [ha]
 have hNorm:
     Algebra.norm (FractionRing R)
         (algebraMap S (FractionRing S) a/algebraMap S (FractionRing S) b)=
       algebraMap R (FractionRing R) (Algebra.intNorm R S a)/
         algebraMap R (FractionRing R) (Algebra.intNorm R S b):=by
   simp [div_eq_mul_inv,Algebra.norm_inv,Algebra.algebraMap_intNorm_fractionRing]
 rw [hNorm,orderAt_div v _ _ (by simpa using hazero) (by simpa using hbzero),
   orderAt_intNorm R S v a hazero,orderAt_intNorm R S v b hbzero,
   ←Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl
 intro P _
 rw [orderAt_div _ _ _ (by simpa using hazero) (by simpa using hbzero),mul_sub]
end FixedExtension
end
end ProximityPrize.SubmissionLower.RCN356
end PackedLegacy_G2

/-! Packed from ProximityPrize.SubmissionLower.W3. -/
section PackedLegacy_W3
namespace ProximityPrize.SubmissionLower.RCN357
open scoped BigOperators Classical
open IsDedekindDomain
noncomputable section
section OneRing
variable (A F:Type*) [CommRing A] [IsDedekindDomain A] [Field F]
 [Algebra A F] [IsFractionRing A F]
def fieldOrder (v:HeightOneSpectrum A) (x:F):ℤ:=
 -(v.valuation F x).log
theorem valuation_transport (v:HeightOneSpectrum A) (x:F):
   v.valuation F x=v.valuation (FractionRing A)
     ((FractionRing.algEquiv A F).symm x):=by
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=A) x
 simp only [map_div₀,AlgEquiv.commutes,
   HeightOneSpectrum.valuation_of_algebraMap]
theorem fieldOrder_transport (v:HeightOneSpectrum A) (x:F):
   fieldOrder A F v x=RCN356.orderAt v
     ((FractionRing.algEquiv A F).symm x):=by
 rw [fieldOrder,valuation_transport]
 rfl
end OneRing
section TwoRings
variable (R S:Type*) [CommRing R] [CommRing S]
 [IsDedekindDomain R] [IsDedekindDomain S]
 [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
local instance _root_.ProximityPrize.SubmissionLower.RCN357.instAlgebraFractionRing_proximityPrize :Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
def placeAbove (v:HeightOneSpectrum R)
   (P:{P:Ideal S//P∈IsDedekindDomain.primesOverFinset v.asIdeal S}):
   HeightOneSpectrum S:=
 ⟨P.1,((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S).mp P.2).1,
   Ideal.ne_bot_of_mem_primesOver v.ne_bot
     ((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S).mp P.2)⟩
variable (F L:Type*) [Field F] [Field L]
 [Algebra R F] [IsFractionRing R F]
 [Algebra S L] [IsFractionRing S L]
 [Algebra F L] [Algebra R L]
 [IsScalarTower R F L] [IsScalarTower R S L]
theorem norm_transport (x:L):
   Algebra.norm (FractionRing R) ((FractionRing.algEquiv S L).symm x)=
     (FractionRing.algEquiv R F).symm (Algebra.norm F x):=by
 have h:=Algebra.norm_eq_of_equiv_equiv
   (FractionRing.algEquiv R F).toRingEquiv
   (FractionRing.algEquiv S L).toRingEquiv
   (by
     ext y
     exact IsFractionRing.algEquiv_commutes
       (FractionRing.algEquiv R F) (FractionRing.algEquiv S L) y)
   ((FractionRing.algEquiv S L).symm x)
 change Algebra.norm (FractionRing R) ((FractionRing.algEquiv S L).symm x)=
   (FractionRing.algEquiv R F).symm
     (Algebra.norm F ((FractionRing.algEquiv S L)
       ((FractionRing.algEquiv S L).symm x))) at h
 simpa only [AlgEquiv.apply_symm_apply] using h
variable [Algebra.IsSeparable F L]
include F L in
theorem canonical_separable:
   Algebra.IsSeparable (FractionRing R) (FractionRing S):=by
 apply Algebra.IsSeparable.of_equiv_equiv
   (A₁:=F) (B₁:=L) (A₂:=FractionRing R) (B₂:=FractionRing S)
   (FractionRing.algEquiv R F).symm.toRingEquiv
   (FractionRing.algEquiv S L).symm.toRingEquiv
 ext y
 exact IsFractionRing.algEquiv_commutes
   (FractionRing.algEquiv R F).symm (FractionRing.algEquiv S L).symm y
theorem fieldOrder_norm (v:HeightOneSpectrum R) (x:L) (hx:x≠0):
   fieldOrder R F v (Algebra.norm F x)=
     ∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
       (P.1.inertiaDeg R:ℤ)*fieldOrder S L (placeAbove R S v P) x:=by
 letI:Algebra.IsSeparable (FractionRing R) (FractionRing S):=
   canonical_separable R S F L
 have h:=RCN356.orderAt_fieldNorm R S v
   ((FractionRing.algEquiv S L).symm x) (by simpa using hx)
 calc
   fieldOrder R F v (Algebra.norm F x)=
       RCN356.orderAt v
         ((FractionRing.algEquiv R F).symm (Algebra.norm F x)):=
     fieldOrder_transport R F v (Algebra.norm F x)
   _=∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
       (P.1.inertiaDeg R:ℤ)*RCN356.orderAt (placeAbove R S v P)
         ((FractionRing.algEquiv S L).symm x):=by
     simpa only [norm_transport R S F L x,RCN356.primeFiber,
       RCN356.fiberPlace,placeAbove] using h
   _=_:=by
     apply Finset.sum_congr rfl
     intro P _
     congr 1
     exact (fieldOrder_transport S L (placeAbove R S v P) x).symm
end TwoRings
end
end ProximityPrize.SubmissionLower.RCN357
end PackedLegacy_W3

/-! Packed from ProximityPrize.SubmissionLower.W8. -/
section PackedLegacy_W8
namespace ProximityPrize.SubmissionLower.RCN366
open scoped BigOperators Classical
open UniqueFactorizationMonoid IsDedekindDomain
noncomputable section
variable (K:Type*) [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN366.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
def primePlace (p:Polynomial K) (hp:Irreducible p):
   HeightOneSpectrum (Polynomial K):=
 ⟨Ideal.span {p},(Ideal.span_singleton_prime hp.ne_zero).mpr hp.prime,
   by simpa using hp.ne_zero⟩
def asFraction (x:RatFunc K):FractionRing (Polynomial K):=
 RatFunc.toFractionRingAlgEquiv K (Polynomial K) x
def finiteOrder (p:Polynomial K) (hp:Irreducible p) (x:RatFunc K):ℤ:=
 RCN356.orderAt (primePlace K p hp) (asFraction K x)
def infinityOrder (x:RatFunc K):ℤ:=
 -(RatFunc.inftyValuation K x).log
theorem finiteOrder_eq_factorCounts
   (p:Polynomial K) (hp:Irreducible p) (hmonic:p.Monic)
   (x:RatFunc K) (hx:x≠0):
   finiteOrder K p hp x=
     ((normalizedFactors x.num).count p:ℤ)-
       ((normalizedFactors x.denom).count p:ℤ):=by
 classical
 have hrepr:asFraction K x=
     algebraMap (Polynomial K) (FractionRing (Polynomial K)) x.num/
       algebraMap (Polynomial K) (FractionRing (Polynomial K)) x.denom:=by
   have h:=congrArg (RatFunc.toFractionRingAlgEquiv K (Polynomial K))
     (RatFunc.num_div_denom x)
   simpa only [asFraction,map_div₀,AlgEquiv.commutes] using h.symm
 rw [finiteOrder,hrepr,
   RCN356.orderAt_div _ _ _ (by simp [RatFunc.num_ne_zero hx])
     (by simp [x.denom_ne_zero]),
   RCN356.orderAt_algebraMap _ x.num (RatFunc.num_ne_zero hx),
   RCN356.orderAt_algebraMap _ x.denom x.denom_ne_zero]
 change ((normalizedFactors (Ideal.span {x.num})).count (Ideal.span {p}):ℤ)-
     ((normalizedFactors (Ideal.span {x.denom})).count (Ideal.span {p}):ℤ)=_
 rw [Ideal.count_span_normalizedFactors_eq (RatFunc.num_ne_zero hx) hp.prime,
   Ideal.count_span_normalizedFactors_eq x.denom_ne_zero hp.prime,
   hmonic.normalize_eq_self]
theorem infinityOrder_eq_neg_intDegree (x:RatFunc K) (hx:x≠0):
   infinityOrder K x= -x.intDegree:=by
 rw [infinityOrder,RatFunc.inftyValuation_apply,
   RatFunc.inftyValuation_of_nonzero K hx,WithZero.log_exp]
theorem exists_monic_primePlace (v:HeightOneSpectrum (Polynomial K)):
   ∃ p:Polynomial K,∃ hp:Irreducible p,
     p.Monic∧primePlace K p hp=v:=by
 classical
 let g:=Submodule.IsPrincipal.generator v.asIdeal
 have hg:Prime g:=Ideal.prime_generator_of_prime v.prime
 have hp:Irreducible (normalize g):=
   (normalize_associated g).irreducible_iff.mpr hg.irreducible
 refine ⟨normalize g,hp,
   Polynomial.monic_normalize (R:=K) (p:=g) hg.ne_zero,?_⟩
 apply HeightOneSpectrum.ext_iff.mpr
 change Ideal.span {normalize g}=v.asIdeal
 calc
   _=Ideal.span {g}:=
     Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated g)
   _=_:=Ideal.span_singleton_generator v.asIdeal
theorem primePlace_injective
   (p q:Polynomial K) (hp:Irreducible p) (hq:Irreducible q)
   (hpm:p.Monic) (hqm:q.Monic)
   (h:primePlace K p hp=primePlace K q hq):p=q:=by
 have hassoc:Associated p q:=Ideal.span_singleton_eq_span_singleton.mp
   (congrArg HeightOneSpectrum.asIdeal h)
 exact hassoc.eq_of_normalized hpm.normalize_eq_self hqm.normalize_eq_self
theorem sum_factor_degrees (p:Polynomial K) (hp:p≠0):
   ((normalizedFactors p).map Polynomial.natDegree).sum=p.natDegree:=by
 have h:=Polynomial.natDegree_eq_of_degree_eq <|
   Polynomial.degree_eq_degree_of_associated (prod_normalizedFactors hp)
 rw [Polynomial.natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)] at h
 exact h
theorem sum_factorCounts_mul_degree
   (p:Polynomial K) (hp:p≠0) (s:Finset (Polynomial K))
   (hs:(normalizedFactors p).toFinset ⊆ s):
   ∑ q∈s,q.natDegree*(normalizedFactors p).count q=p.natDegree:=by
 classical
 have h:=sum_factor_degrees K p hp
 rw [Finset.sum_multiset_map_count] at h
 simp only [nsmul_eq_mul] at h
 norm_cast at h
 have hsum:
     (∑ q∈(normalizedFactors p).toFinset,
       (normalizedFactors p).count q*q.natDegree)=
     ∑ q∈s,(normalizedFactors p).count q*q.natDegree:=by
   apply Finset.sum_subset hs
   intro q _ hq
   have hc:(normalizedFactors p).count q=0:=
     Multiset.count_eq_zero.mpr (by simpa using hq)
   simp [hc]
 rw [hsum] at h
 simpa only [Nat.mul_comm] using h
def factorSupport (x:RatFunc K):Finset (Polynomial K):=by
 classical
 exact (normalizedFactors x.num).toFinset ∪ (normalizedFactors x.denom).toFinset
theorem factorSupport_primes (x:RatFunc K) (hx:x≠0)
   (p:Polynomial K) (hp:p∈factorSupport K x):Irreducible p∧p.Monic:=by
 classical
 rcases Finset.mem_union.mp hp with hnum | hden
 · have h:=(Polynomial.mem_normalizedFactors_iff
     (R:=K) (p:=p) (q:=x.num) (RatFunc.num_ne_zero hx)).mp
     (Multiset.mem_toFinset.mp hnum)
   exact ⟨h.1,h.2.1⟩
 · have h:=(Polynomial.mem_normalizedFactors_iff
     (R:=K) (p:=p) (q:=x.denom) x.denom_ne_zero).mp
     (Multiset.mem_toFinset.mp hden)
   exact ⟨h.1,h.2.1⟩
theorem weighted_finite_order_sum
   (x:RatFunc K) (hx:x≠0) (s:Finset (Polynomial K))
   (hs:∀ p∈s,Irreducible p∧p.Monic)
   (hnum:(normalizedFactors x.num).toFinset ⊆ s)
   (hden:(normalizedFactors x.denom).toFinset ⊆ s):
   (∑ p∈s.attach,(p.1.natDegree:ℤ)*
     finiteOrder K p.1 (hs p.1 p.2).1 x)=x.intDegree:=by
 classical
 have hterms:
     (∑ p∈s.attach,(p.1.natDegree:ℤ)*
       finiteOrder K p.1 (hs p.1 p.2).1 x)=
     ∑ p∈s,(p.natDegree:ℤ)*
       (((normalizedFactors x.num).count p:ℤ)-
         ((normalizedFactors x.denom).count p:ℤ)):=by
   calc
     _=∑ p∈s.attach,(p.1.natDegree:ℤ)*
         (((normalizedFactors x.num).count p.1:ℤ)-
           ((normalizedFactors x.denom).count p.1:ℤ)):=by
       apply Finset.sum_congr rfl
       intro p _
       rw [finiteOrder_eq_factorCounts K p.1 (hs p.1 p.2).1 (hs p.1 p.2).2 x hx]
     _=_:=Finset.sum_attach s (fun p:Polynomial K↦
       (p.natDegree:ℤ)*
         (((normalizedFactors x.num).count p:ℤ)-
           ((normalizedFactors x.denom).count p:ℤ)))
 rw [hterms]
 simp only [mul_sub,Finset.sum_sub_distrib]
 have hn:(∑ p∈s,(p.natDegree:ℤ)*
     ((normalizedFactors x.num).count p:ℤ))=(x.num.natDegree:ℤ):=by
   exact_mod_cast sum_factorCounts_mul_degree K x.num (RatFunc.num_ne_zero hx) s hnum
 have hd:(∑ p∈s,(p.natDegree:ℤ)*
     ((normalizedFactors x.denom).count p:ℤ))=(x.denom.natDegree:ℤ):=by
   exact_mod_cast sum_factorCounts_mul_degree K x.denom x.denom_ne_zero s hden
 rw [hn,hd]
 rfl
end
end ProximityPrize.SubmissionLower.RCN366
end PackedLegacy_W8

/- Library component HW is loaded from Mathlib.FieldTheory.RatFunc.IntermediateField. -/

/- Library component S7 is loaded from Mathlib.RingTheory.Adjoin.Polynomial.Bivariate. -/

/- Library component AQ is loaded from Mathlib.NumberTheory.FunctionField. -/

/-! Packed from ProximityPrize.SubmissionLower.R5. -/
section PackedLegacy_R5
namespace ProximityPrize.SubmissionLower.RCN349
open scoped BigOperators Classical nonZeroDivisors
open IsDedekindDomain RCN357
noncomputable section
variable (K L:Type*) [Field K] [Field L]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance _root_.ProximityPrize.SubmissionLower.RCN349.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev FiniteNormalization:=FunctionField.ringOfIntegers K L
instance finiteNormalization_finite:
   Module.Finite (Polynomial K) (FiniteNormalization K L):=
 IsIntegralClosure.finite (Polynomial K) (RatFunc K) L (FiniteNormalization K L)
instance finiteNormalization_torsionFree:
   Module.IsTorsionFree (Polynomial K) (FiniteNormalization K L):=by
 letI:Module.IsTorsionFree (Polynomial K) L:=
   Module.IsTorsionFree.trans_faithfulSMul (Polynomial K) (RatFunc K) L
 exact IsIntegralClosure.isTorsionFree (Polynomial K) L
abbrev InfinityBase:=RCN353.InfinityRing K
local instance _root_.ProximityPrize.SubmissionLower.RCN349.instIsFractionRingSubtypeRatFuncMemValuationSubringInfinityBase :IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100) _root_.ProximityPrize.SubmissionLower.RCN349.instAlgebraSubtypeRatFuncMemValuationSubringInfinityBase :Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance _root_.ProximityPrize.SubmissionLower.RCN349.instIsScalarTowerSubtypeRatFuncMemValuationSubringInfinityBase :IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=integralClosure (InfinityBase K) L
instance infiniteNormalization_finite:
   Module.Finite (InfinityBase K) (InfiniteNormalization K L):=
 IsIntegralClosure.finite (InfinityBase K) (RatFunc K) L (InfiniteNormalization K L)
instance infiniteNormalization_torsionFree:
   Module.IsTorsionFree (InfinityBase K) (InfiniteNormalization K L):=by
 letI:Module.IsTorsionFree (InfinityBase K) L:=
   Module.IsTorsionFree.trans_faithfulSMul (InfinityBase K) (RatFunc K) L
 exact IsIntegralClosure.isTorsionFree (InfinityBase K) L
instance infiniteNormalization_isDedekindDomain:
   IsDedekindDomain (InfiniteNormalization K L):=
 integralClosure.isDedekindDomain (InfinityBase K) (RatFunc K) L
instance infiniteNormalization_isFractionRing:
   IsFractionRing (InfiniteNormalization K L) L:=
 integralClosure.isFractionRing_of_finite_extension (RatFunc K) L
def infinityPlace:HeightOneSpectrum (InfinityBase K):=
 IsDiscreteValuationRing.maximalIdeal (InfinityBase K)
def infinityContribution (x:L):ℤ:=
 ∑ P∈(IsDedekindDomain.primesOverFinset
     (infinityPlace K).asIdeal (InfiniteNormalization K L)).attach,
   (P.1.inertiaDeg (InfinityBase K):ℤ)*
     fieldOrder (InfiniteNormalization K L) L
       (placeAbove (InfinityBase K) (InfiniteNormalization K L) (infinityPlace K) P) x
theorem infinityContribution_eq_normOrder (x:L) (hx:x≠0):
   infinityContribution K L x=
     RCN366.infinityOrder K (Algebra.norm (RatFunc K) x):=by
 have h:=fieldOrder_norm (InfinityBase K) (InfiniteNormalization K L)
   (RatFunc K) L (infinityPlace K) x hx
 change-((infinityPlace K).valuation (RatFunc K)
     (Algebra.norm (RatFunc K) x)).log=infinityContribution K L x at h
 rw [infinityPlace,RCN353.infinity_valuation_eq] at h
 exact h.symm
theorem asFraction_eq_canonical (x:RatFunc K):
   RCN366.asFraction K x=
     (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm x:=by
 letI:Subsingleton
     ((RatFunc K) →ₐ[Polynomial K] FractionRing (Polynomial K)):=
   IsLocalization.algHom_subsingleton (nonZeroDivisors (Polynomial K))
 have h:=Subsingleton.elim
   (RatFunc.toFractionRingAlgEquiv K (Polynomial K)).toAlgHom
   (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm.toAlgHom
 exact DFunLike.congr_fun h x
theorem finiteOrder_eq_specifiedOrder
   (p:Polynomial K) (hp:Irreducible p) (x:RatFunc K):
   RCN366.finiteOrder K p hp x=
     fieldOrder (Polynomial K) (RatFunc K) (RCN366.primePlace K p hp) x:=by
 rw [RCN366.finiteOrder,asFraction_eq_canonical K]
 exact (fieldOrder_transport (Polynomial K) (RatFunc K)
   (RCN366.primePlace K p hp) x).symm
theorem finitePrimeContribution_eq_normOrder
   (p:Polynomial K) (hp:Irreducible p) (x:L) (hx:x≠0):
   (∑ P∈(IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p hp).asIdeal (FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (FiniteNormalization K L) L
         (placeAbove (Polynomial K) (FiniteNormalization K L)
           (RCN366.primePlace K p hp) P) x)=
     RCN366.finiteOrder K p hp (Algebra.norm (RatFunc K) x):=by
 have h:=fieldOrder_norm (Polynomial K) (FiniteNormalization K L) (RatFunc K) L
   (RCN366.primePlace K p hp) x hx
 rw [←finiteOrder_eq_specifiedOrder K p hp] at h
 exact h.symm
def finiteContribution (s:Finset (Polynomial K))
   (hs:∀ p∈s,Irreducible p∧p.Monic) (x:L):ℤ:=
 ∑ p∈s.attach,(p.1.natDegree:ℤ)*
   ∑ P∈(IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p.1 (hs p.1 p.2).1).asIdeal
       (FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (FiniteNormalization K L) L
         (placeAbove (Polynomial K) (FiniteNormalization K L)
           (RCN366.primePlace K p.1 (hs p.1 p.2).1) P) x
theorem finiteContribution_eq_normOrders
   (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0):
   finiteContribution K L s hs x=
     ∑ p∈s.attach,(p.1.natDegree:ℤ)*
       RCN366.finiteOrder K p.1 (hs p.1 p.2).1
         (Algebra.norm (RatFunc K) x):=by
 unfold finiteContribution
 apply Finset.sum_congr rfl
 intro p _
 rw [finitePrimeContribution_eq_normOrder K L p.1 (hs p.1 p.2).1 x hx]
theorem balanced_fiber_sum
   (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0)
   (hnum:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).num).toFinset ⊆ s)
   (hden:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).denom).toFinset ⊆ s):
   finiteContribution K L s hs x+infinityContribution K L x=0:=by
 have hnorm:Algebra.norm (RatFunc K) x≠0:=Algebra.norm_ne_zero_iff.mpr hx
 rw [finiteContribution_eq_normOrders K L s hs x hx,
   infinityContribution_eq_normOrder K L x hx,
   RCN366.weighted_finite_order_sum K _ hnorm s hs hnum hden,
   RCN366.infinityOrder_eq_neg_intDegree K _ hnorm,
   add_neg_cancel]
theorem finite_orders_support_finite (x:L) (hx:x≠0):
   Function.HasFiniteSupport
     (fun w:HeightOneSpectrum (FiniteNormalization K L)↦
       fieldOrder (FiniteNormalization K L) L w x):=by
 obtain ⟨a,b,hb,rfl⟩:=
   IsFractionRing.div_surjective (A:=FiniteNormalization K L) x
 have hbzero:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have hazero:a≠0:=by
   intro ha
   apply hx
   simp [ha]
 have hspanA:(Ideal.span {a}:Ideal (FiniteNormalization K L))≠0:=by
   simpa using hazero
 have hspanB:(Ideal.span {b}:Ideal (FiniteNormalization K L))≠0:=by
   simpa using hbzero
 have hA:{w:HeightOneSpectrum (FiniteNormalization K L) |
     w.asIdeal∣Ideal.span {a}}.Finite:=Ideal.finite_factors hspanA
 have hB:{w:HeightOneSpectrum (FiniteNormalization K L) |
     w.asIdeal∣Ideal.span {b}}.Finite:=Ideal.finite_factors hspanB
 apply (hA.union hB).subset
 intro w hw
 by_contra hout
 have hn:=not_or.mp hout
 have hna:a∉w.asIdeal:=fun ha↦hn.1 (Ideal.dvd_span_singleton.mpr ha)
 have hnb:b∉w.asIdeal:=fun hb↦hn.2 (Ideal.dvd_span_singleton.mpr hb)
 have hva:w.intValuation a=1:=
   (HeightOneSpectrum.intValuation_eq_one_iff (v:=w)).mpr hna
 have hvb:w.intValuation b=1:=
   (HeightOneSpectrum.intValuation_eq_one_iff (v:=w)).mpr hnb
 apply hw
 simp only [fieldOrder,map_div₀,HeightOneSpectrum.valuation_of_algebraMap,
   hva,hvb,div_self one_ne_zero,WithZero.log_one,neg_zero]
def finiteOrderSupport (x:L) (hx:x≠0):
   Finset (HeightOneSpectrum (FiniteNormalization K L)):=
 (finite_orders_support_finite K L x hx).toFinset
theorem mem_finiteOrderSupport (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (FiniteNormalization K L)):
   w∈finiteOrderSupport K L x hx ↔
     fieldOrder (FiniteNormalization K L) L w x≠0:=by
 simp [finiteOrderSupport]
def baseRepresentative (w:HeightOneSpectrum (FiniteNormalization K L)):Polynomial K:=
 (RCN366.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose
theorem baseRepresentative_spec (w:HeightOneSpectrum (FiniteNormalization K L)):
   ∃ hp:Irreducible (baseRepresentative K L w),
     (baseRepresentative K L w).Monic∧
       RCN366.primePlace K (baseRepresentative K L w) hp=
         HeightOneSpectrum.under (Polynomial K) w:=
 (RCN366.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose_spec
def basePrimesFor (x:L) (hx:x≠0):Finset (Polynomial K):=
 (finiteOrderSupport K L x hx).image (baseRepresentative K L) ∪
   RCN366.factorSupport K (Algebra.norm (RatFunc K) x)
theorem basePrimesFor_primes (x:L) (hx:x≠0)
   (p:Polynomial K) (hp:p∈basePrimesFor K L x hx):Irreducible p∧p.Monic:=by
 rcases Finset.mem_union.mp hp with hleft | hright
 · obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hleft
   obtain ⟨hp,hm,_⟩:=baseRepresentative_spec K L w
   exact ⟨hp,hm⟩
 · exact RCN366.factorSupport_primes K _
     (Algebra.norm_ne_zero_iff.mpr hx) p hright
theorem basePrimesFor_covers (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (FiniteNormalization K L))
   (hw:fieldOrder (FiniteNormalization K L) L w x≠0):
   ∃ p∈basePrimesFor K L x hx,∃ hp:Irreducible p,
     w.asIdeal∈IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p hp).asIdeal (FiniteNormalization K L):=by
 obtain ⟨hp,hm,hplace⟩:=baseRepresentative_spec K L w
 refine ⟨baseRepresentative K L w,
   Finset.mem_union_left _ (Finset.mem_image.mpr
     ⟨w,(mem_finiteOrderSupport K L x hx w).mpr hw,rfl⟩),hp,?_⟩
 rw [hplace]
 letI:w.asIdeal.LiesOver (HeightOneSpectrum.under (Polynomial K) w).asIdeal:=by
   change w.asIdeal.LiesOver (w.asIdeal.under (Polynomial K))
   infer_instance
 exact (IsDedekindDomain.mem_primesOverFinset_iff
   (HeightOneSpectrum.under (Polynomial K) w).ne_bot (FiniteNormalization K L)).mpr
     ⟨w.isPrime,inferInstance⟩
theorem projective_curve_order_sum (x:L) (hx:x≠0):
   finiteContribution K L (basePrimesFor K L x hx)
     (basePrimesFor_primes K L x hx) x+infinityContribution K L x=0:=by
 apply balanced_fiber_sum K L (basePrimesFor K L x hx)
   (basePrimesFor_primes K L x hx) x hx
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_left _ hp)
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_right _ hp)
end
end ProximityPrize.SubmissionLower.RCN349
end PackedLegacy_R5

/- Library component HP is loaded from Mathlib.Data.Real.Embedding. -/

/- Library component V7 is loaded from Mathlib.RingTheory.Valuation.RankOne. -/

/- Library component V5 is loaded from Mathlib.RingTheory.Valuation.Discrete.RankOne. -/

/- Library component S5 is loaded from Mathlib.NumberTheory.RamificationInertia.Valuation. -/

/-! Packed from ProximityPrize.SubmissionLower.R1. -/
section PackedLegacy_R1
namespace ProximityPrize.SubmissionLower.RCN345
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L]
 [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance _root_.ProximityPrize.SubmissionLower.RCN345.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN345.instDecidableEq_proximityPrize_1 :DecidableEq L:=Classical.decEq L
abbrev FiniteNormalization:=RCN349.FiniteNormalization K L
abbrev InfinityBase:=RCN349.InfinityBase K
local instance _root_.ProximityPrize.SubmissionLower.RCN345.instIsFractionRingSubtypeRatFuncMemValuationSubringInfinityBase :IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100) _root_.ProximityPrize.SubmissionLower.RCN345.instAlgebraSubtypeRatFuncMemValuationSubringInfinityBase :Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance _root_.ProximityPrize.SubmissionLower.RCN345.instIsScalarTowerSubtypeRatFuncMemValuationSubringInfinityBase :IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
def parameter:L:=algebraMap (Polynomial K) L Polynomial.X
theorem parameter_eq_ratFunc:
   parameter K L=algebraMap (RatFunc K) L (RatFunc.X:RatFunc K):=by
 change algebraMap (Polynomial K) L Polynomial.X=
   algebraMap (RatFunc K) L (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 exact IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L Polynomial.X
theorem aeval_parameter (f:Polynomial K):
   Polynomial.aeval (parameter K L) f=algebraMap (Polynomial K) L f:=by
 rw [parameter,Polynomial.aeval_algebraMap_apply,Polynomial.aeval_X_left_apply]
theorem polynomial_C_map (c:K):
   algebraMap (Polynomial K) L (Polynomial.C c)=algebraMap K L c:=
 (IsScalarTower.algebraMap_apply K (Polynomial K) L c).symm
section GivenValuation
variable (v:Valuation L ℤᵐ⁰) [htriv:v.IsTrivialOn K]
theorem coefficient_le_one (c:K):v (algebraMap K L c) ≤ 1:=by
 by_cases hc:c=0
 · simp [hc]
 · rw [htriv.eq_one c hc]
theorem polynomial_le_one (ht:v (parameter K L) ≤ 1) (f:Polynomial K):
   v (algebraMap (Polynomial K) L f) ≤ 1:=by
 induction f using Polynomial.induction_on' with
 | add f g hf hg =>
     rw [map_add]
     exact (v.map_add _ _).trans (max_le hf hg)
 | monomial n c =>
     rw [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
       map_mul,map_pow,polynomial_C_map]
     exact mul_le_one₀ (coefficient_le_one K L v c) zero_le
       (pow_le_one₀ zero_le ht)
theorem finiteNormalization_le_one (ht:v (parameter K L) ≤ 1)
   (s:FiniteNormalization K L):
   v (algebraMap (FiniteNormalization K L) L s) ≤ 1:=by
 exact RCN359.integral_le_one (Polynomial K) L v
   (polynomial_le_one K L v ht) s.property
theorem polynomial_value_of_parameter_gt_one (ht:1 < v (parameter K L))
   (f:Polynomial K) (hf:f≠0):
   v (algebraMap (Polynomial K) L f)=v (parameter K L)^f.natDegree:=by
 rw [←aeval_parameter K L f]
 exact Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
   (v:=v) (parameter K L) ht hf
theorem infinityBase_le_one (ht:1 < v (parameter K L)) (r:InfinityBase K):
   v (algebraMap (InfinityBase K) L r) ≤ 1:=by
 change v (algebraMap (RatFunc K) L r.val) ≤ 1
 by_cases hr:r.val=0
 · simp [hr]
 have hdegree:r.val.num.natDegree ≤ r.val.denom.natDegree:=by
   have hmem:RatFunc.inftyValuation K r.val ≤ 1:=r.property
   rw [RatFunc.inftyValuation_apply,RatFunc.inftyValuation_of_nonzero K hr,
     ←WithZero.exp_zero,WithZero.exp_le_exp] at hmem
   dsimp [RatFunc.intDegree] at hmem
   omega
 have hnum:=polynomial_value_of_parameter_gt_one K L v ht
   r.val.num (RatFunc.num_ne_zero hr)
 have hden:=polynomial_value_of_parameter_gt_one K L v ht
   r.val.denom r.val.denom_ne_zero
 rw [←RatFunc.num_div_denom r.val,map_div₀,map_div₀,
   ←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
   ←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
   hnum,hden]
 apply (div_le_one₀ (pow_pos (zero_lt_one.trans ht) _)).mpr
 exact pow_le_pow_right₀ ht.le hdegree
theorem infiniteNormalization_le_one (ht:1 < v (parameter K L))
   (s:InfiniteNormalization K L):
   v (algebraMap (InfiniteNormalization K L) L s) ≤ 1:=by
 exact RCN359.integral_le_one (InfinityBase K) L v
   (infinityBase_le_one K L v ht) s.property
theorem exists_unique_finite_place (hv:Function.Surjective v)
   (ht:v (parameter K L) ≤ 1):
   ∃! p:HeightOneSpectrum (FiniteNormalization K L),v=p.valuation L:=
 RCN359.exists_unique_place (FiniteNormalization K L) L v
   (finiteNormalization_le_one K L v ht) hv
theorem exists_unique_infinite_place (hv:Function.Surjective v)
   (ht:1 < v (parameter K L)):
   ∃! q:HeightOneSpectrum (InfiniteNormalization K L),v=q.valuation L:=
 RCN359.exists_unique_place (InfiniteNormalization K L) L v
   (infiniteNormalization_le_one K L v ht) hv
theorem finite_or_infinite_place (hv:Function.Surjective v):
   (∃ p:HeightOneSpectrum (FiniteNormalization K L),v=p.valuation L)∨
   (∃ q:HeightOneSpectrum (InfiniteNormalization K L),v=q.valuation L):=by
 by_cases ht:v (parameter K L) ≤ 1
 · exact Or.inl (exists_unique_finite_place K L v hv ht).exists
 · exact Or.inr (exists_unique_infinite_place K L v hv (lt_of_not_ge ht)).exists
end GivenValuation
theorem infinitePlace_liesOver
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   q.asIdeal.LiesOver (RCN349.infinityPlace K).asIdeal:=by
 have hbase:HeightOneSpectrum.under (InfinityBase K) q=
     RCN349.infinityPlace K:=by
   apply HeightOneSpectrum.ext
   exact IsLocalRing.eq_maximalIdeal
     ((HeightOneSpectrum.under (InfinityBase K) q).isPrime.isMaximal
       (HeightOneSpectrum.under (InfinityBase K) q).ne_bot)
 have hq:q.asIdeal.LiesOver
     (HeightOneSpectrum.under (InfinityBase K) q).asIdeal:=by
   change q.asIdeal.LiesOver (q.asIdeal.under (InfinityBase K))
   infer_instance
 rwa [hbase] at hq
theorem finitePlace_parameter_le_one
   (p:HeightOneSpectrum (FiniteNormalization K L)):
   p.valuation L (parameter K L) ≤ 1:=by
 rw [parameter,IsScalarTower.algebraMap_apply (Polynomial K) (FiniteNormalization K L) L]
 exact p.valuation_le_one _
theorem infinitePlace_parameter_value
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   q.valuation L (parameter K L)=
     WithZero.exp ((RCN349.infinityPlace K).asIdeal.ramificationIdx'
       q.asIdeal:ℤ):=by
 letI:=infinitePlace_liesOver K L q
 have h:=HeightOneSpectrum.valuation_liesOver (K:=RatFunc K) L
   (RCN349.infinityPlace K) q (RatFunc.X:RatFunc K)
 rw [RCN349.infinityPlace,RCN353.infinity_valuation_eq,
   RatFunc.inftyValuation.X] at h
 rw [parameter_eq_ratFunc]
 simpa [RCN349.infinityPlace] using h.symm
theorem infinitePlace_parameter_gt_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   1 < q.valuation L (parameter K L):=by
 letI:=infinitePlace_liesOver K L q
 rw [infinitePlace_parameter_value, ←WithZero.exp_zero,WithZero.exp_lt_exp]
 exact_mod_cast Nat.pos_iff_ne_zero.mpr
   (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal
     (RCN349.infinityPlace K).ne_bot)
theorem finitePlace_trivial
   (p:HeightOneSpectrum (FiniteNormalization K L)):
   (p.valuation L).IsTrivialOn K:=by
 constructor
 intro c hc
 let cS:FiniteNormalization K L:=
   algebraMap (Polynomial K) (FiniteNormalization K L) (Polynomial.C c)
 have hunit:IsUnit cS:=
   ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C).map
     (algebraMap (Polynomial K) (FiniteNormalization K L))
 have hval:p.valuation L (algebraMap (FiniteNormalization K L) L cS)=1:=
   Valuation.Integers.one_of_isUnit' hunit (p.valuation_le_one (K:=L))
 change p.valuation L (algebraMap (FiniteNormalization K L) L
   (algebraMap (Polynomial K) (FiniteNormalization K L) (Polynomial.C c)))=1 at hval
 rw [←IsScalarTower.algebraMap_apply (Polynomial K) (FiniteNormalization K L) L,
   polynomial_C_map] at hval
 exact hval
theorem infinitePlace_trivial
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   (q.valuation L).IsTrivialOn K:=by
 constructor
 intro c hc
 letI:=infinitePlace_liesOver K L q
 have h:=HeightOneSpectrum.valuation_liesOver (K:=RatFunc K) L
   (RCN349.infinityPlace K) q (algebraMap K (RatFunc K) c)
 rw [RCN349.infinityPlace,RCN353.infinity_valuation_eq] at h
 have hC:RatFunc.inftyValuation K (algebraMap K (RatFunc K) c)=1:=
   RatFunc.inftyValuation.C K hc
 rw [hC,one_pow, ←IsScalarTower.algebraMap_apply K (RatFunc K) L] at h
 exact h.symm
abbrev ChartPlace:=
 Sum (HeightOneSpectrum (FiniteNormalization K L))
   (HeightOneSpectrum (InfiniteNormalization K L))
def chartValuation:ChartPlace K L → Valuation L ℤᵐ⁰:=
 Sum.elim (fun p↦p.valuation L) (fun q↦q.valuation L)
theorem chartValuation_surjective (p:ChartPlace K L):
   Function.Surjective (chartValuation K L p):=by
 rcases p with p | q
 · exact p.valuation_surjective L
 · exact q.valuation_surjective L
theorem chartValuation_trivial (p:ChartPlace K L):
   (chartValuation K L p).IsTrivialOn K:=by
 rcases p with p | q
 · exact finitePlace_trivial K L p
 · exact infinitePlace_trivial K L q
theorem chartValuation_injective:Function.Injective (chartValuation K L):=by
 intro p q h
 rcases p with p | p <;> rcases q with q | q
 · congr 1
   exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
     (K:=L) (Valuation.IsEquiv.of_eq h)
 · have hp:=finitePlace_parameter_le_one K L p
   have hq:=infinitePlace_parameter_gt_one K L q
   change p.valuation L=q.valuation L at h
   rw [h] at hp
   exact False.elim (not_lt_of_ge hp hq)
 · have hp:=infinitePlace_parameter_gt_one K L p
   have hq:=finitePlace_parameter_le_one K L q
   change p.valuation L=q.valuation L at h
   rw [h] at hp
   exact False.elim (not_lt_of_ge hq hp)
 · congr 1
   exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
     (K:=L) (Valuation.IsEquiv.of_eq h)
def NormalizedValuation:=
 {v:Valuation L ℤᵐ⁰//Function.Surjective v∧v.IsTrivialOn K}
def chartMap (p:ChartPlace K L):NormalizedValuation K L:=
 ⟨chartValuation K L p,chartValuation_surjective K L p,chartValuation_trivial K L p⟩
theorem chartMap_bijective:Function.Bijective (chartMap K L):=by
 constructor
 · intro p q h
   exact chartValuation_injective K L (congrArg Subtype.val h)
 · intro v
   letI:v.val.IsTrivialOn K:=v.property.2
   rcases finite_or_infinite_place K L v.val v.property.1 with ⟨p,hp⟩ | ⟨q,hq⟩
   · refine ⟨Sum.inl p,?_⟩
     apply Subtype.ext
     exact hp.symm
   · refine ⟨Sum.inr q,?_⟩
     apply Subtype.ext
     exact hq.symm
end
end ProximityPrize.SubmissionLower.RCN345
end PackedLegacy_R1

/-! Packed from ProximityPrize.SubmissionLower.W4. -/
section PackedLegacy_W4
namespace ProximityPrize.SubmissionLower.RCN358
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K:Type*) [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN358.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev InfinityBase:=RCN349.InfinityBase K
local instance _root_.ProximityPrize.SubmissionLower.RCN358.instAlgebraSubtypeRatFuncMemValuationSubringInfinityBase :Algebra K (InfinityBase K):=
 (RCN352.constantMap K).toAlgebra
def infinityBasePoint:InfinityBase K →ₐ[K] K where
 toRingHom:=(RCN352.residueEquiv K).symm.toRingHom.comp
   (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)))
 commutes' c:=by
   change (RCN352.residueEquiv K).symm
     (RCN352.residueConstant K c)=c
   rw [←RCN352.residueEquiv_apply,RingEquiv.symm_apply_apply]
theorem infinityBasePoint_kernel:
   RingHom.ker (infinityBasePoint K).toRingHom=
     (RCN349.infinityPlace K).asIdeal:=by
 ext r
 change (RCN352.residueEquiv K).symm
     (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)) r)=0 ↔
   r∈IsLocalRing.maximalIdeal (InfinityBase K)
 constructor
 · intro h
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   apply (RCN352.residueEquiv K).symm.injective
   simpa only [map_zero] using h
 · intro h
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr h,map_zero]
variable [IsAlgClosed K]
theorem finiteBase_natDegree_eq_one (f:Polynomial K) (hf:Irreducible f):
   f.natDegree=1:=
 Polynomial.natDegree_eq_of_degree_eq_some
   (IsAlgClosed.degree_eq_one_of_irreducible K hf)
theorem finiteBase_exists_point (p:HeightOneSpectrum (Polynomial K)):
   ∃ phi:Polynomial K →ₐ[K] K,RingHom.ker phi.toRingHom=p.asIdeal:=by
 obtain ⟨f,hf,hm,hplace⟩:=RCN366.exists_monic_primePlace K p
 obtain ⟨alpha,hroot⟩:=IsAlgClosed.exists_root f (by
   rw [IsAlgClosed.degree_eq_one_of_irreducible K hf]
   exact one_ne_zero)
 let phi:Polynomial K →ₐ[K] K:=Polynomial.aeval alpha
 have hkermax:(RingHom.ker phi.toRingHom).IsMaximal:=
   RCN354.pointKernel_isMaximal phi
 have hle:p.asIdeal ≤ RingHom.ker phi.toRingHom:=by
   rw [←hplace]
   change Ideal.span {f} ≤ RingHom.ker phi.toRingHom
   apply (Ideal.span_singleton_le_iff_mem (I:=RingHom.ker phi.toRingHom)).mpr
   change f.eval alpha=0
   exact hroot
 refine ⟨phi,?_⟩
 exact ((p.isPrime.isMaximal p.ne_bot).eq_of_le hkermax.ne_top hle).symm
variable (L:Type*) [Field L]
 [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev FiniteNormalization:=RCN349.FiniteNormalization K L
local instance _root_.ProximityPrize.SubmissionLower.RCN358.instIsFractionRingSubtypeRatFuncMemValuationSubringInfinityBase :IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100) _root_.ProximityPrize.SubmissionLower.RCN358.instAlgebraSubtypeRatFuncMemValuationSubringInfinityBase_1 :Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance _root_.ProximityPrize.SubmissionLower.RCN358.instIsScalarTowerSubtypeRatFuncMemValuationSubringInfinityBase :IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
theorem finitePlace_inertia_one
   (q:HeightOneSpectrum (FiniteNormalization K L)):
   q.asIdeal.inertiaDeg (Polynomial K)=1:=by
 letI:Algebra K (FiniteNormalization K L):=
   ((algebraMap (Polynomial K) (FiniteNormalization K L)).comp Polynomial.C).toAlgebra
 letI:IsScalarTower K (Polynomial K) (FiniteNormalization K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 obtain ⟨phi,hphi⟩:=finiteBase_exists_point K
   (HeightOneSpectrum.under (Polynomial K) q)
 apply RCN373.inertiaDeg_eq_one_of_point_fiber phi q.asIdeal
 exact hphi.symm
theorem infinitePlace_inertia_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   q.asIdeal.inertiaDeg (InfinityBase K)=1:=by
 letI:Algebra K (InfiniteNormalization K L):=
   ((algebraMap (InfinityBase K) (InfiniteNormalization K L)).comp
     (algebraMap K (InfinityBase K))).toAlgebra
 letI:IsScalarTower K (InfinityBase K) (InfiniteNormalization K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.infinitePlace_liesOver K L q
 apply RCN373.inertiaDeg_eq_one_of_point_fiber
   (infinityBasePoint K) q.asIdeal
 rw [infinityBasePoint_kernel]
 exact (Ideal.over_def q.asIdeal (RCN349.infinityPlace K).asIdeal).symm
theorem infinitePlace_inertia'_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   (RCN349.infinityPlace K).asIdeal.inertiaDeg' q.asIdeal=1:=by
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.infinitePlace_liesOver K L q
 rw [Ideal.inertiaDeg'_eq_inertiaDeg]
 exact infinitePlace_inertia_one K L q
theorem infiniteFiber_weight_one
   (Q:{Q:Ideal (InfiniteNormalization K L)//
     Q∈IsDedekindDomain.primesOverFinset
       (RCN349.infinityPlace K).asIdeal (InfiniteNormalization K L)}):
   (Q.1.inertiaDeg (InfinityBase K):ℤ)=1:=by
 have hQ:=infinitePlace_inertia_one K L
   (RCN357.placeAbove (InfinityBase K) (InfiniteNormalization K L)
     (RCN349.infinityPlace K) Q)
 exact_mod_cast hQ
end
end ProximityPrize.SubmissionLower.RCN358
end PackedLegacy_W4

/-! Packed from ProximityPrize.SubmissionLower.Z7. -/
section PackedLegacy_Z7
namespace ProximityPrize.SubmissionLower.RCN187
open scoped BigOperators
noncomputable section
section Multiplicative
variable {K L σ Γ₀:Type*} [Field K] [Field L] [Fintype σ]
 [LinearOrderedCommGroupWithZero Γ₀]
theorem valuation_monomial_le (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (d:σ →₀ ℕ) (c:K) (hd:∀ i,d i ≤ cap i):
   v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 rw [MvPolynomial.eval₂Hom_monomial,
   Finsupp.prod_fintype _ _ (fun _ => pow_zero _),map_mul,map_prod]
 simp only [map_pow]
 calc
   v (coeff c)*(∏ i,v (x i)^d i) ≤
       1*(∏ i,max 1 (v (x i))^cap i):=by
     apply mul_le_mul' (hcoeff c)
     apply Finset.prod_le_prod (fun _ _ => zero_le)
     intro i _
     exact (pow_le_pow_left₀ zero_le (le_max_right _ _) (d i)).trans
       (pow_le_pow_right₀ (le_max_left _ _) (hd i))
   _=_:=one_mul _
theorem valuation_eval_le_box (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 conv_lhs => rw [MvPolynomial.as_sum F,map_sum]
 apply v.map_sum_le
 intro d hd
 apply valuation_monomial_le v coeff hcoeff x cap d
 intro i
 exact (MvPolynomial.monomial_le_degreeOf i hd).trans (hcap i)
theorem max_one_valuation_eval_le_box (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 apply max_le
 · exact Finset.one_le_prod fun _ _ => one_le_pow₀ (le_max_left _ _)
 · exact valuation_eval_le_box v coeff hcoeff x cap F hcap
end Multiplicative
section IntegerPole
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
def poleOrder (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L):ℤ:=
 max 0 (v x).log
theorem log_max_one (z:WithZero (Multiplicative ℤ)):
   (max 1 z).log=max 0 z.log:=by
 by_cases hz:z=0
 · simp [hz]
 rcases le_total 1 z with h | h
 · have hlog:(0:ℤ) ≤ z.log:=by
     simpa using (WithZero.log_le_log (by simp) hz).2 h
   simp only [max_eq_right h,max_eq_right hlog]
 · have hlog:z.log ≤ (0:ℤ):=by
     simpa using (WithZero.log_le_log hz (by simp)).2 h
   simp only [max_eq_left h,WithZero.log_one,max_eq_left hlog]
theorem log_prod_of_one_le {ι:Type*} (s:Finset ι)
   (f:ι → WithZero (Multiplicative ℤ)):
   (∀ i∈s,1 ≤ f i) →
     (∏ i∈s,f i).log=∑ i∈s,(f i).log:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 induction s using Finset.induction_on with
 | empty => intro _;simp
 | @insert i s hi ih =>
     intro hf
     have hfi:1 ≤ f i:=hf i (Finset.mem_insert_self i s)
     have hfs:∀ j∈s,1 ≤ f j:=
       fun j hj => hf j (Finset.mem_insert_of_mem hj)
     have hfi0:f i≠0:=ne_of_gt (zero_lt_one.trans_le hfi)
     have hprod0:(∏ j∈s,f j)≠0:=
       ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfs))
     rw [Finset.prod_insert hi,WithZero.log_mul hfi0 hprod0,
       Finset.sum_insert hi,ih hfs]
theorem poleOrder_eval_le_box
   (v:Valuation L (WithZero (Multiplicative ℤ))) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
     ∑ i,(cap i:ℤ)*poleOrder v (x i):=by
 classical
 have hfactor:∀ i∈(Finset.univ:Finset σ),
     1 ≤ max 1 (v (x i))^cap i:=
   fun _ _ => one_le_pow₀ (le_max_left _ _)
 have hleft0:max 1 (v (MvPolynomial.eval₂Hom coeff x F))≠0:=
   ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
 have hright0:(∏ i,max 1 (v (x i))^cap i)≠0:=
   ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfactor))
 have hlog:=(WithZero.log_le_log hleft0 hright0).2
   (max_one_valuation_eval_le_box v coeff hcoeff x cap F hcap)
 rw [log_prod_of_one_le Finset.univ _ hfactor] at hlog
 simpa only [WithZero.log_pow,log_max_one,nsmul_eq_mul,poleOrder] using hlog
theorem weighted_poleOrder_eval_le_box {τ:Type*} (S:Finset τ)
   (weight:τ → ℕ) (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ t∈S,∀ c:K,v t (coeff c) ≤ 1)
   (x:σ → L) (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   (∑ t∈S,(weight t:ℤ)*poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∑ i,(cap i:ℤ)*(∑ t∈S,(weight t:ℤ)*poleOrder (v t) (x i)):=by
 classical
 calc
   _ ≤ ∑ t∈S,(weight t:ℤ)*
       (∑ i,(cap i:ℤ)*poleOrder (v t) (x i)):=by
     apply Finset.sum_le_sum
     intro t ht
     exact mul_le_mul_of_nonneg_left
       (poleOrder_eval_le_box (v t) coeff (hcoeff t ht) x cap F hcap)
       (Int.natCast_nonneg (weight t))
   _=_:=by
     simp_rw [Finset.mul_sum]
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro i _
     apply Finset.sum_congr rfl
     intro t _
     ring
end IntegerPole
end
end ProximityPrize.SubmissionLower.RCN187
end PackedLegacy_Z7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier04 : True := by trivial
end ProximityPrize.SubmissionLower

/- Library component S3 is loaded from Mathlib.NumberTheory.RamificationInertia.Basic. -/

/-! Packed from ProximityPrize.SubmissionLower.R2. -/
section PackedLegacy_R2
namespace ProximityPrize.SubmissionLower.RCN346
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place:=RCN345.NormalizedValuation K L
def poleOrder (v:Place K L) (x:L):ℤ:=
 RCN187.poleOrder v.val x
theorem poleOrder_nonneg (v:Place K L) (x:L):0 ≤ poleOrder K L v x:=
 le_max_left _ _
theorem poleOrder_eq_zero_of_le_one (v:Place K L) (x:L) (h:v.val x ≤ 1):
   poleOrder K L v x=0:=by
 change max 0 (v.val x).log=0
 rw [←RCN187.log_max_one,max_eq_left h,WithZero.log_one]
variable [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance _root_.ProximityPrize.SubmissionLower.RCN346.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN346.instDecidableEqPlace :DecidableEq (Place K L):=Classical.decEq _
abbrev InfinityBase:=RCN349.InfinityBase K
local instance _root_.ProximityPrize.SubmissionLower.RCN346.instIsFractionRingSubtypeRatFuncMemValuationSubringInfinityBase :IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100) _root_.ProximityPrize.SubmissionLower.RCN346.instAlgebraSubtypeRatFuncMemValuationSubringInfinityBase :Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance _root_.ProximityPrize.SubmissionLower.RCN346.instIsScalarTowerSubtypeRatFuncMemValuationSubringInfinityBase :IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
def infinityFiber:Finset (Ideal (InfiniteNormalization K L)):=
 IsDedekindDomain.primesOverFinset (RCN349.infinityPlace K).asIdeal
   (InfiniteNormalization K L)
def infinityPlace
   (Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}):
   HeightOneSpectrum (InfiniteNormalization K L):=
 RCN357.placeAbove (InfinityBase K) (InfiniteNormalization K L)
   (RCN349.infinityPlace K) Q
def infinityValuation
   (Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}):
   Place K L:=
 RCN345.chartMap K L (Sum.inr (infinityPlace K L Q))
theorem infinityValuation_injective:Function.Injective (infinityValuation K L):=by
 intro P Q h
 apply Subtype.ext
 have hc:=(RCN345.chartMap_bijective K L).1 h
 have hp:=Sum.inr.inj hc
 exact congrArg (fun p:HeightOneSpectrum (InfiniteNormalization K L)↦p.asIdeal) hp
theorem infinity_pole_eq_ramification
   (Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}):
   poleOrder K L (infinityValuation K L Q) (RCN345.parameter K L)=
     ((RCN349.infinityPlace K).asIdeal.ramificationIdx' Q.1:ℤ):=by
 change max 0 (((infinityPlace K L Q).valuation L)
   (RCN345.parameter K L)).log=_
 rw [RCN345.infinitePlace_parameter_value,
   WithZero.log_exp,max_eq_right (Int.natCast_nonneg _)]
 rfl
theorem sum_infinity_ramification_eq_finrank:
   (∑ Q∈(infinityFiber K L).attach,
     (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q.1)=
     Module.finrank (RatFunc K) L:=by
 have h:=Ideal.sum_ramification_inertia (InfiniteNormalization K L) (RatFunc K) L
   (RCN349.infinityPlace K).ne_bot
 calc
   (∑ Q∈(infinityFiber K L).attach,
       (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q.1)=
     ∑ Q∈infinityFiber K L,
       (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q*
         (RCN349.infinityPlace K).asIdeal.inertiaDeg' Q:=by
     rw [←Finset.sum_attach (infinityFiber K L)
       (fun Q:Ideal (InfiniteNormalization K L)↦
         (RCN349.infinityPlace K).asIdeal.ramificationIdx' Q*
           (RCN349.infinityPlace K).asIdeal.inertiaDeg' Q)]
     apply Finset.sum_congr rfl
     intro Q _
     have hf:=RCN358.infinitePlace_inertia'_one K L (infinityPlace K L Q)
     change (RCN349.infinityPlace K).asIdeal.inertiaDeg' Q.1=1 at hf
     rw [hf,mul_one]
   _=Module.finrank (RatFunc K) L:=h
theorem sum_infinity_poles_eq_finrank:
   (∑ Q∈(infinityFiber K L).attach,
     poleOrder K L (infinityValuation K L Q) (RCN345.parameter K L))=
     (Module.finrank (RatFunc K) L:ℤ):=by
 simp_rw [infinity_pole_eq_ramification]
 exact_mod_cast sum_infinity_ramification_eq_finrank K L
def infinityValues:Finset (Place K L):=
 (infinityFiber K L).attach.image (infinityValuation K L)
theorem sum_poles_infinityValues_eq_finrank:
   (∑ v∈infinityValues K L,
     poleOrder K L v (RCN345.parameter K L))=
     (Module.finrank (RatFunc K) L:ℤ):=by
 rw [infinityValues,Finset.sum_image (fun _ _ _ _ h↦infinityValuation_injective K L h)]
 exact sum_infinity_poles_eq_finrank K L
theorem poleOrder_eq_zero_of_not_mem_infinity (v:Place K L)
   (hv:v∉infinityValues K L):
   poleOrder K L v (RCN345.parameter K L)=0:=by
 by_contra hnonzero
 have ht:1 < v.val (RCN345.parameter K L):=
   lt_of_not_ge fun hle↦hnonzero (poleOrder_eq_zero_of_le_one K L v _ hle)
 letI:v.val.IsTrivialOn K:=v.property.2
 obtain ⟨q,hq,_⟩:=
   RCN345.exists_unique_infinite_place K L v.val v.property.1 ht
 have hmem:q.asIdeal∈infinityFiber K L:=
   (IsDedekindDomain.mem_primesOverFinset_iff
     (RCN349.infinityPlace K).ne_bot (InfiniteNormalization K L)).mpr
     ⟨q.isPrime,RCN345.infinitePlace_liesOver K L q⟩
 let Q:{Q:Ideal (InfiniteNormalization K L)//Q∈infinityFiber K L}:=⟨q.asIdeal,hmem⟩
 have hplace:infinityPlace K L Q=q:=by
   apply HeightOneSpectrum.ext
   rfl
 have hvmap:infinityValuation K L Q=v:=by
   apply Subtype.ext
   change (infinityPlace K L Q).valuation L=v.val
   rw [hplace]
   exact hq.symm
 apply hv
 rw [←hvmap]
 exact Finset.mem_image.mpr ⟨Q,Finset.mem_attach _ Q,rfl⟩
theorem finite_sum_pole_le_finrank (W:Finset (Place K L)):
   (∑ v∈W,poleOrder K L v (RCN345.parameter K L)) ≤
     (Module.finrank (RatFunc K) L:ℤ):=by
 have htrim:
     (∑ v∈W,poleOrder K L v (RCN345.parameter K L))=
     ∑ v∈W ∩ infinityValues K L,
       poleOrder K L v (RCN345.parameter K L):=by
   symm
   apply Finset.sum_subset Finset.inter_subset_left
   intro v hvW hvnot
   apply poleOrder_eq_zero_of_not_mem_infinity K L v
   intro hvI
   exact hvnot (Finset.mem_inter.mpr ⟨hvW,hvI⟩)
 calc
   _=∑ v∈W ∩ infinityValues K L,
       poleOrder K L v (RCN345.parameter K L):=htrim
   _ ≤ ∑ v∈infinityValues K L,
       poleOrder K L v (RCN345.parameter K L):=by
     apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
     intro v _ _
     exact poleOrder_nonneg K L v _
   _=(Module.finrank (RatFunc K) L:ℤ):=sum_poles_infinityValues_eq_finrank K L
end
end ProximityPrize.SubmissionLower.RCN346
end PackedLegacy_R2

/-! Packed from ProximityPrize.SubmissionLower.DG. -/
section PackedLegacy_DG
namespace ProximityPrize.SubmissionLower.RCN026
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place:=RCN345.NormalizedValuation K L
def order (v:Place K L) (x:L):ℤ:= -(v.val x).log
def zeroOrder (v:Place K L) (x:L):ℤ:=max 0 (order K L v x)
theorem zeroOrder_nonneg (v:Place K L) (x:L):0 ≤ zeroOrder K L v x:=
 le_max_left _ _
theorem zeroOrder_sub_poleOrder (v:Place K L) (x:L):
   zeroOrder K L v x-RCN346.poleOrder K L v x=order K L v x:=by
 unfold zeroOrder order RCN346.poleOrder RCN187.poleOrder
 omega
variable [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance _root_.ProximityPrize.SubmissionLower.RCN026.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN026.instDecidableEqPlace :DecidableEq (Place K L):=Classical.decEq _
abbrev FiniteNormalization:=RCN349.FiniteNormalization K L
abbrev InfinityBase:=RCN349.InfinityBase K
local instance _root_.ProximityPrize.SubmissionLower.RCN026.instIsFractionRingSubtypeRatFuncMemValuationSubringInfinityBase :IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100) _root_.ProximityPrize.SubmissionLower.RCN026.instAlgebraSubtypeRatFuncMemValuationSubringInfinityBase :Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance _root_.ProximityPrize.SubmissionLower.RCN026.instIsScalarTowerSubtypeRatFuncMemValuationSubringInfinityBase :IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
variable (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
def finiteFiber (p:{p:Polynomial K//p∈s}):
   Finset (Ideal (FiniteNormalization K L)):=
 IsDedekindDomain.primesOverFinset
   (RCN366.primePlace K p.1 (hs p.1 p.2).1).asIdeal
   (FiniteNormalization K L)
abbrev FiniteIndex:=
 Σ p:{p:Polynomial K//p∈s},
   {Q:Ideal (FiniteNormalization K L)//Q∈finiteFiber K L s hs p}
def finitePlace (i:FiniteIndex K L s hs):
   HeightOneSpectrum (FiniteNormalization K L):=
 RCN357.placeAbove (Polynomial K) (FiniteNormalization K L)
   (RCN366.primePlace K i.1.1 (hs i.1.1 i.1.2).1) i.2
theorem finitePlace_injective:Function.Injective (finitePlace K L s hs):=by
 rintro ⟨p,P⟩ ⟨q,Q⟩ h
 have hI:P.1=Q.1:=congrArg HeightOneSpectrum.asIdeal h
 let pbase:=RCN366.primePlace K p.1 (hs p.1 p.2).1
 let qbase:=RCN366.primePlace K q.1 (hs q.1 q.2).1
 letI:P.1.LiesOver pbase.asIdeal:=
   ((IsDedekindDomain.mem_primesOverFinset_iff pbase.ne_bot
     (FiniteNormalization K L)).mp P.2).2
 letI:Q.1.LiesOver qbase.asIdeal:=
   ((IsDedekindDomain.mem_primesOverFinset_iff qbase.ne_bot
     (FiniteNormalization K L)).mp Q.2).2
 have hbase:pbase=qbase:=by
   apply HeightOneSpectrum.ext
   calc
     pbase.asIdeal=P.1.under (Polynomial K):=Ideal.over_def P.1 pbase.asIdeal
     _=Q.1.under (Polynomial K):=congrArg (Ideal.under (Polynomial K)) hI
     _=qbase.asIdeal:=(Ideal.over_def Q.1 qbase.asIdeal).symm
 have hpq:p=q:=Subtype.ext <|
   RCN366.primePlace_injective K p.1 q.1
     (hs p.1 p.2).1 (hs q.1 q.2).1 (hs p.1 p.2).2 (hs q.1 q.2).2 hbase
 subst q
 have hPQ:P=Q:=Subtype.ext hI
 cases hPQ
 rfl
abbrev InfinityIndex:=
 {Q:Ideal (InfiniteNormalization K L)//Q∈RCN346.infinityFiber K L}
abbrev FamilyIndex:=FiniteIndex K L s hs ⊕ InfinityIndex K L
def familyChart:FamilyIndex K L s hs → RCN345.ChartPlace K L:=
 Sum.elim (fun i↦Sum.inl (finitePlace K L s hs i))
   (fun Q↦Sum.inr (RCN346.infinityPlace K L Q))
def familyValuation (i:FamilyIndex K L s hs):Place K L:=
 RCN345.chartMap K L (familyChart K L s hs i)
theorem familyValuation_injective:Function.Injective (familyValuation K L s hs):=by
 intro i j h
 have hc:=(RCN345.chartMap_bijective K L).1 h
 cases i with
 | inl i =>
   cases j with
   | inl j =>
     exact congrArg Sum.inl (finitePlace_injective K L s hs (Sum.inl.inj hc))
   | inr j => cases hc
 | inr i =>
   cases j with
   | inl j => cases hc
   | inr j =>
     have hI:i.1=j.1:=congrArg HeightOneSpectrum.asIdeal (Sum.inr.inj hc)
     exact congrArg Sum.inr (Subtype.ext hI)
theorem finiteContribution_eq_sum (x:L):
   RCN349.finiteContribution K L s hs x=
     ∑ i:FiniteIndex K L s hs,
       RCN357.fieldOrder (FiniteNormalization K L) L
         (finitePlace K L s hs i) x:=by
 rw [Fintype.sum_sigma]
 unfold RCN349.finiteContribution
 simp only [Finset.attach_eq_univ]
 apply Finset.sum_congr rfl
 intro p _
 rw [RCN358.finiteBase_natDegree_eq_one K p.1 (hs p.1 p.2).1]
 simp only [Nat.cast_one,one_mul]
 apply Finset.sum_congr rfl
 intro Q _
 have hweight:=RCN358.finitePlace_inertia_one K L
   (finitePlace K L s hs ⟨p,Q⟩)
 change Q.1.inertiaDeg (Polynomial K)=1 at hweight
 rw [hweight]
 simp only [Nat.cast_one,one_mul]
 rfl
theorem infinityContribution_eq_sum (x:L):
   RCN349.infinityContribution K L x=
     ∑ Q:InfinityIndex K L,
       RCN357.fieldOrder (InfiniteNormalization K L) L
         (RCN346.infinityPlace K L Q) x:=by
 unfold RCN349.infinityContribution
 simp only [Finset.attach_eq_univ]
 apply Finset.sum_congr rfl
 intro Q _
 rw [RCN358.infiniteFiber_weight_one K L Q,one_mul]
 rfl
theorem sum_family_order_eq_contributions (x:L):
   (∑ i:FamilyIndex K L s hs,order K L (familyValuation K L s hs i) x)=
     RCN349.finiteContribution K L s hs x+
       RCN349.infinityContribution K L x:=by
 rw [Fintype.sum_sum_type]
 change
   (∑ i:FiniteIndex K L s hs,
     RCN357.fieldOrder (FiniteNormalization K L) L
       (finitePlace K L s hs i) x)+
   (∑ Q:InfinityIndex K L,
     RCN357.fieldOrder (InfiniteNormalization K L) L
       (RCN346.infinityPlace K L Q) x)=_
 rw [←finiteContribution_eq_sum K L s hs x, ←infinityContribution_eq_sum K L x]
def familyValues:Finset (Place K L):=
 Finset.univ.image (familyValuation K L s hs)
theorem sum_familyValues_order_eq_contributions (x:L):
   (∑ v∈familyValues K L s hs,order K L v x)=
     RCN349.finiteContribution K L s hs x+
       RCN349.infinityContribution K L x:=by
 rw [familyValues,Finset.sum_image
   (fun _ _ _ _ h↦familyValuation_injective K L s hs h)]
 exact sum_family_order_eq_contributions K L s hs x
variable {s hs}
def placesFor (x:L) (hx:x≠0):Finset (Place K L):=
 familyValues K L (RCN349.basePrimesFor K L x hx)
   (RCN349.basePrimesFor_primes K L x hx)
theorem sum_placesFor_order_zero (x:L) (hx:x≠0):
   (∑ v∈placesFor K L x hx,order K L v x)=0:=by
 rw [placesFor,sum_familyValues_order_eq_contributions]
 exact RCN349.projective_curve_order_sum K L x hx
theorem placesFor_covers (x:L) (hx:x≠0) (v:Place K L)
   (hv:order K L v x≠0):v∈placesFor K L x hx:=by
 obtain ⟨c,rfl⟩:=(RCN345.chartMap_bijective K L).2 v
 let s:=RCN349.basePrimesFor K L x hx
 let hs:=RCN349.basePrimesFor_primes K L x hx
 change RCN345.chartMap K L c∈familyValues K L s hs
 rcases c with q | q
 · have hq:RCN357.fieldOrder (FiniteNormalization K L) L q x≠0:=hv
   obtain ⟨p,hp,hirred,hQ⟩:=RCN349.basePrimesFor_covers K L x hx q hq
   let pindex:{p:Polynomial K//p∈s}:=⟨p,hp⟩
   let Q:{Q:Ideal (FiniteNormalization K L)//Q∈finiteFiber K L s hs pindex}:=
     ⟨q.asIdeal,hQ⟩
   let i:FamilyIndex K L s hs:=Sum.inl ⟨pindex,Q⟩
   have heq:familyValuation K L s hs i=
       RCN345.chartMap K L (Sum.inl q):=by
     have hplace:finitePlace K L s hs ⟨pindex,Q⟩=q:=by
       apply HeightOneSpectrum.ext
       rfl
     change RCN345.chartMap K L
       (Sum.inl (finitePlace K L s hs ⟨pindex,Q⟩))=_
     rw [hplace]
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,heq⟩
 · have hQ:q.asIdeal∈RCN346.infinityFiber K L:=
     (IsDedekindDomain.mem_primesOverFinset_iff
       (RCN349.infinityPlace K).ne_bot (InfiniteNormalization K L)).mpr
       ⟨q.isPrime,RCN345.infinitePlace_liesOver K L q⟩
   let Q:InfinityIndex K L:=⟨q.asIdeal,hQ⟩
   let i:FamilyIndex K L s hs:=Sum.inr Q
   have heq:familyValuation K L s hs i=
       RCN345.chartMap K L (Sum.inr q):=by
     have hplace:RCN346.infinityPlace K L Q=q:=by
       apply HeightOneSpectrum.ext
       rfl
     change RCN345.chartMap K L
       (Sum.inr (RCN346.infinityPlace K L Q))=_
     rw [hplace]
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,heq⟩
theorem sum_placesFor_zero_eq_pole (x:L) (hx:x≠0):
   (∑ v∈placesFor K L x hx,zeroOrder K L v x)=
     ∑ v∈placesFor K L x hx,RCN346.poleOrder K L v x:=by
 apply sub_eq_zero.mp
 rw [←Finset.sum_sub_distrib]
 simp_rw [zeroOrder_sub_poleOrder]
 exact sum_placesFor_order_zero K L x hx
theorem finite_zero_places_le_poleMass (x:L) (hx:x≠0)
   (U:Finset (Place K L)) (hU:∀ v∈U,1 ≤ order K L v x):
   (U.card:ℤ) ≤
     ∑ v∈placesFor K L x hx,RCN346.poleOrder K L v x:=by
 have hsub:U ⊆ placesFor K L x hx:=by
   intro v hv
   apply placesFor_covers K L x hx v
   have h:=hU v hv
   omega
 calc
   (U.card:ℤ)=∑ _v∈U,(1:ℤ):=by simp
   _ ≤ ∑ v∈U,zeroOrder K L v x:=by
     apply Finset.sum_le_sum
     intro v hv
     exact (hU v hv).trans (le_max_right _ _)
   _ ≤ ∑ v∈placesFor K L x hx,zeroOrder K L v x:=by
     apply Finset.sum_le_sum_of_subset_of_nonneg hsub
     intro v _ _
     exact zeroOrder_nonneg K L v x
   _=_:=sum_placesFor_zero_eq_pole K L x hx
end
end ProximityPrize.SubmissionLower.RCN026
end PackedLegacy_DG

/-! Packed from ProximityPrize.SubmissionLower.H4. -/
section PackedLegacy_H4
namespace ProximityPrize.SubmissionLower.RCN017
open IsDedekindDomain
noncomputable section
section PointKernels
variable {K S:Type*} [Field K] [CommRing S] [Algebra K S]
def pointKernel (phi:S →ₐ[K] K):Ideal S:=RingHom.ker phi.toRingHom
@[simp] theorem mem_pointKernel (phi:S →ₐ[K] K) (s:S):
   s∈pointKernel phi ↔ phi s=0:=Iff.rfl
theorem point_surjective (phi:S →ₐ[K] K):Function.Surjective phi:=by
 intro c
 exact ⟨algebraMap K S c,by simpa using phi.commutes c⟩
theorem pointKernel_isPrime (phi:S →ₐ[K] K):(pointKernel phi).IsPrime:=
 RingHom.ker_isPrime phi.toRingHom
theorem pointKernel_isMaximal (phi:S →ₐ[K] K):(pointKernel phi).IsMaximal:=
 RingHom.ker_isMaximal_of_surjective phi.toRingHom (point_surjective phi)
theorem pointKernel_injective:
   Function.Injective (pointKernel:(S →ₐ[K] K) → Ideal S):=by
 intro phi psi hker
 apply AlgHom.ext
 intro s
 have hs:s-algebraMap K S (phi s)∈pointKernel phi:=by simp
 have hs':s-algebraMap K S (phi s)∈pointKernel psi:=hker ▸ hs
 have hz:=(mem_pointKernel psi _).mp hs'
 have heq:psi s=phi s:=sub_eq_zero.mp (by simpa using hz)
 exact heq.symm
variable [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]
def parameterDifference (phi:S →ₐ[K] K):S:=
 algebraMap (Polynomial K) S
   (Polynomial.X-Polynomial.C (phi (algebraMap (Polynomial K) S Polynomial.X)))
theorem parameterDifference_mem (phi:S →ₐ[K] K):
   parameterDifference phi∈pointKernel phi:=by
 have hconstant (c:K):
     algebraMap (Polynomial K) S (Polynomial.C c)=algebraMap K S c:=
   (IsScalarTower.algebraMap_apply K (Polynomial K) S c).symm
 simp [parameterDifference,hconstant]
theorem parameterDifference_ne_zero
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):parameterDifference phi≠0:=by
 intro hz
 apply Polynomial.X_sub_C_ne_zero (phi (algebraMap (Polynomial K) S Polynomial.X))
 apply hinj
 simpa only [parameterDifference,map_zero] using hz
theorem pointKernel_ne_bot
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):pointKernel phi≠⊥:=by
 intro hbot
 have hzero:parameterDifference phi=0:=by
   simpa [hbot] using parameterDifference_mem phi
 exact parameterDifference_ne_zero hinj phi hzero
end PointKernels
section ActualPlaces
variable {K S L:Type*} [Field K] [CommRing S] [IsDedekindDomain S]
 [Algebra K S] [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]
def pointPlace (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):HeightOneSpectrum S:=
 ⟨pointKernel phi,pointKernel_isPrime phi,pointKernel_ne_bot hinj phi⟩
@[simp] theorem pointPlace_asIdeal
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S →ₐ[K] K):(pointPlace hinj phi).asIdeal=pointKernel phi:=rfl
variable [Field L] [Algebra S L] [IsFractionRing S L]
end ActualPlaces
section ConcreteNormalization
variable (K L:Type*) [Field K] [Field L]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev ActualNormalization:=FunctionField.ringOfIntegers K L
local instance normalizationScalarAlgebra:Algebra K (ActualNormalization K L):=
 ((algebraMap (Polynomial K) (ActualNormalization K L)).comp
   (Polynomial.C:K →+*Polynomial K)).toAlgebra
local instance normalizationScalarTower:
   IsScalarTower K (Polynomial K) (ActualNormalization K L):=
 IsScalarTower.of_algebraMap_eq (fun _ => rfl)
end ConcreteNormalization
end
end ProximityPrize.SubmissionLower.RCN017
end PackedLegacy_H4

/-! Packed from ProximityPrize.SubmissionLower.H3. -/
section PackedLegacy_H3
namespace ProximityPrize.SubmissionLower.RCN016
open IsDedekindDomain
noncomputable section
section Fractions
variable {S L:Type*} [CommRing S] [IsDedekindDomain S] [Field L]
 [Algebra S L] [IsFractionRing S L]
theorem base_value_lt_one_iff (p:HeightOneSpectrum S) (a:S):
   p.valuation L (algebraMap S L a) < 1 ↔ a∈p.asIdeal:=by
 rw [HeightOneSpectrum.valuation_of_algebraMap,
   HeightOneSpectrum.intValuation_lt_one_iff_mem]
theorem denominator_value_one (p:HeightOneSpectrum S) (b:S)
   (hb:b∉p.asIdeal):p.valuation L (algebraMap S L b)=1:=by
 apply le_antisymm
 · rw [HeightOneSpectrum.valuation_of_algebraMap]
   exact p.intValuation_le_one b
 · exact le_of_not_gt fun h => hb ((base_value_lt_one_iff p b).mp h)
theorem denominator_ne_zero (p:HeightOneSpectrum S) (b:S)
   (hb:b∉p.asIdeal):algebraMap S L b≠0:=by
 have hb0:b≠0:=fun h => hb (h ▸ p.asIdeal.zero_mem)
 simpa only [map_zero] using (IsFractionRing.injective S L).ne hb0
theorem fraction_of_value_le_one (p:HeightOneSpectrum S) (x:L)
   (hx:p.valuation L x ≤ 1):
   ∃ a b:S,b∉p.asIdeal∧x*algebraMap S L b=algebraMap S L a:=by
 have hm:x∈HeightOneSpectrum.valuationSubringAtPrime L p:=by
   rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
   exact hx
 rcases hm with ⟨a,b,hb,rfl⟩
 refine ⟨a,b,hb,?_⟩
 simp [denominator_ne_zero p b hb]
end Fractions
section Overring
variable {K S B L:Type*} [Field K] [CommRing S] [IsDedekindDomain S]
 [CommRing B] [Field L]
 [Algebra S B] [Algebra S L] [Algebra B L] [IsScalarTower S B L]
 [IsFractionRing S L]
variable (hinj:Function.Injective (algebraMap B L))
 (p:HeightOneSpectrum S) (Φ:B →+*K)
 (hker:RingHom.ker (Φ.comp (algebraMap S B))=p.asIdeal)
include hker in
theorem base_point_zero_iff (a:S):
   Φ (algebraMap S B a)=0 ↔ a∈p.asIdeal:=by
 rw [←hker]
 rfl
include hinj
theorem lift_multiplication (x:B) (a b:S)
   (h:algebraMap B L x*algebraMap S L a=algebraMap S L b):
   x*algebraMap S B a=algebraMap S B b:=by
 apply hinj
 simpa only [map_mul, ←IsScalarTower.algebraMap_apply S B L] using h
theorem inverse_fraction (x:B)
   (hx:1 ≤ p.valuation L (algebraMap B L x)):
   ∃ a b:S,b∉p.asIdeal∧
     x*algebraMap S B a=algebraMap S B b∧
     p.valuation L (algebraMap S L a)=
       (p.valuation L (algebraMap B L x))⁻¹:=by
 have hv0:p.valuation L (algebraMap B L x)≠0:=
   ne_of_gt (zero_lt_one.trans_le hx)
 have hx0:algebraMap B L x≠0:=(Valuation.ne_zero_iff _).mp hv0
 have hi:p.valuation L ((algebraMap B L x)⁻¹) ≤ 1:=by
   rw [map_inv₀]
   exact inv_le_one_of_one_le₀ hx
 obtain ⟨a,b,hb,hab⟩:=fraction_of_value_le_one p ((algebraMap B L x)⁻¹) hi
 have hmul:algebraMap B L x*algebraMap S L a=algebraMap S L b:=by
   rw [←hab, ←mul_assoc,mul_inv_cancel₀ hx0,one_mul]
 have hval:p.valuation L (algebraMap S L a)=
     (p.valuation L (algebraMap B L x))⁻¹:=by
   rw [←hab,map_mul,map_inv₀,denominator_value_one p b hb,mul_one]
 exact ⟨a,b,hb,lift_multiplication hinj x a b hmul,hval⟩
include hker in
theorem overring_value_le_one (x:B):
   p.valuation L (algebraMap B L x) ≤ 1:=by
 by_contra h
 have hx:1 < p.valuation L (algebraMap B L x):=lt_of_not_ge h
 obtain ⟨a,b,hb,hmul,hval⟩:=inverse_fraction hinj p x hx.le
 have ha:a∈p.asIdeal:=(base_value_lt_one_iff p a).mp (by
   rw [hval]
   exact inv_lt_one_of_one_lt₀ hx)
 have hzero:=(base_point_zero_iff p Φ hker a).mpr ha
 have hnonzero:Φ (algebraMap S B b)≠0:=by
   exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
 have heq:=congrArg Φ hmul
 rw [map_mul,hzero,mul_zero] at heq
 exact hnonzero heq.symm
include hker in
theorem overring_value_lt_one_of_point_zero (x:B) (hzero:Φ x=0):
   p.valuation L (algebraMap B L x) < 1:=by
 by_contra h
 obtain ⟨a,b,hb,hmul,_⟩:=inverse_fraction hinj p x (le_of_not_gt h)
 have hnonzero:Φ (algebraMap S B b)≠0:=by
   exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
 have heq:=congrArg Φ hmul
 rw [map_mul,hzero,zero_mul] at heq
 exact hnonzero heq.symm
include hker in
theorem point_zero_of_overring_value_lt_one (x:B)
   (hx:p.valuation L (algebraMap B L x) < 1):Φ x=0:=by
 obtain ⟨a,b,hb,hab⟩:=fraction_of_value_le_one p (algebraMap B L x) hx.le
 have hval:p.valuation L (algebraMap S L a) < 1:=by
   rw [←hab,map_mul,denominator_value_one p b hb,mul_one]
   exact hx
 have ha:=(base_value_lt_one_iff p a).mp hval
 have hzero:=(base_point_zero_iff p Φ hker a).mpr ha
 have hnonzero:Φ (algebraMap S B b)≠0:=by
   exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
 have heq:=congrArg Φ (lift_multiplication hinj x b a hab)
 rw [map_mul,hzero] at heq
 exact (mul_eq_zero.mp heq).resolve_right hnonzero
include hker in
theorem overring_value_lt_one_iff (x:B):
   p.valuation L (algebraMap B L x) < 1 ↔ Φ x=0:=
 ⟨point_zero_of_overring_value_lt_one hinj p Φ hker x,
   overring_value_lt_one_of_point_zero hinj p Φ hker x⟩
end Overring
end
end ProximityPrize.SubmissionLower.RCN016
end PackedLegacy_H3

/-! Packed from ProximityPrize.SubmissionLower.H2. -/
section PackedLegacy_H2
namespace ProximityPrize.SubmissionLower.RCN015
open IsDedekindDomain RCN017 RCN016
noncomputable section
abbrev ModelClosure (A L:Type*) [CommRing A] [Field L] [Algebra A L]:=
 integralClosure A L
section Construction
variable {K S A L:Type*} [Field K] [IsAlgClosed K]
 [CommRing S] [IsDedekindDomain S] [CommRing A] [Field L]
 [Algebra K S] [Algebra K A] [Algebra K L]
 [Algebra (Polynomial K) S] [Algebra (Polynomial K) A] [Algebra (Polynomial K) L]
 [Algebra S L] [Algebra A L]
 [IsScalarTower K (Polynomial K) S] [IsScalarTower K (Polynomial K) A]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K S L] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) S L] [IsScalarTower (Polynomial K) A L]
 [IsFractionRing S L] [Algebra.IsIntegral (Polynomial K) S]
def inclusionToModelClosure:S →ₐ[K] ModelClosure A L where
 toFun s:=⟨algebraMap S L s,by
   have hs:IsIntegral (Polynomial K) (algebraMap S L s):=
     (Algebra.IsIntegral.isIntegral (R:=Polynomial K) s).map
       (IsScalarTower.toAlgHom (Polynomial K) S L)
   exact hs.tower_top⟩
 map_zero':=Subtype.ext (map_zero _)
 map_one':=Subtype.ext (map_one _)
 map_add' a b:=Subtype.ext (map_add _ a b)
 map_mul' a b:=Subtype.ext (map_mul _ a b)
 commutes' c:=by
   apply Subtype.ext
   change algebraMap S L (algebraMap K S c)=algebraMap K L c
   exact (IsScalarTower.algebraMap_apply K S L c).symm
theorem modelClosure_base_injective
   (hinj:Function.Injective (algebraMap A L)):
   Function.Injective (algebraMap A (ModelClosure A L)):=by
 intro a b h
 apply hinj
 exact congrArg (fun x:ModelClosure A L => (x:L)) h
theorem modelClosure_embedding_injective:
   Function.Injective (algebraMap (ModelClosure A L) L):=
 Subtype.val_injective
def modelClosurePoint (hinj:Function.Injective (algebraMap A L))
   (φ:A →ₐ[K] K):ModelClosure A L →ₐ[K] K:=
 RCN354.chosenPointLift (modelClosure_base_injective hinj) φ
theorem modelClosurePoint_restrict
   (hinj:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K) (a:A):
   modelClosurePoint hinj φ (algebraMap A (ModelClosure A L) a)=φ a:=
 AlgHom.congr_fun
   (RCN354.chosenPointLift_spec (modelClosure_base_injective hinj) φ) a
def modelPointPlace
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K):
   HeightOneSpectrum S:=
 pointPlace hS ((modelClosurePoint hA φ).comp
   (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)))
theorem modelPointPlace_kernel
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K):
   RingHom.ker ((modelClosurePoint hA φ).toRingHom.comp
     (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)).toRingHom)=
     (modelPointPlace hS hA φ).asIdeal:=rfl
theorem model_value_le_one
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K) (a:A):
   (modelPointPlace hS hA φ).valuation L (algebraMap A L a) ≤ 1:=by
 letI:Algebra S (ModelClosure A L):=
   (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)).toRingHom.toAlgebra
 letI:IsScalarTower S (ModelClosure A L) L:=
   IsScalarTower.of_algebraMap_eq (fun _ => rfl)
 have h:=overring_value_le_one (L:=L) modelClosure_embedding_injective
   (modelPointPlace hS hA φ) (modelClosurePoint hA φ).toRingHom
   (modelPointPlace_kernel hS hA φ) (algebraMap A (ModelClosure A L) a)
 simpa only [←IsScalarTower.algebraMap_apply A (ModelClosure A L) L] using h
theorem model_value_lt_one_iff
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K) (a:A):
   (modelPointPlace hS hA φ).valuation L (algebraMap A L a) < 1 ↔ φ a=0:=by
 letI:Algebra S (ModelClosure A L):=
   (inclusionToModelClosure (K:=K) (S:=S) (A:=A) (L:=L)).toRingHom.toAlgebra
 letI:IsScalarTower S (ModelClosure A L) L:=
   IsScalarTower.of_algebraMap_eq (fun _ => rfl)
 have h:=overring_value_lt_one_iff (L:=L) modelClosure_embedding_injective
   (modelPointPlace hS hA φ) (modelClosurePoint hA φ).toRingHom
   (modelPointPlace_kernel hS hA φ) (algebraMap A (ModelClosure A L) a)
 simpa only [←IsScalarTower.algebraMap_apply A (ModelClosure A L) L,
   AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,modelClosurePoint_restrict] using h
theorem modelPointPlace_injective
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)):
   Function.Injective (modelPointPlace hS hA:(A →ₐ[K] K) → HeightOneSpectrum S):=by
 intro φ ψ h
 apply RCN017.pointKernel_injective
 apply Ideal.ext
 intro a
 change φ a=0 ↔ ψ a=0
 rw [←model_value_lt_one_iff hS hA φ a, ←model_value_lt_one_iff hS hA ψ a,h]
theorem model_zero_order_ge_one
   (hS:Function.Injective (algebraMap (Polynomial K) S))
   (hA:Function.Injective (algebraMap A L)) (φ:A →ₐ[K] K)
   (a:A) (ha:a≠0) (hzero:φ a=0):
   1 ≤-((modelPointPlace hS hA φ).valuation L (algebraMap A L a)).log:=by
 have hv0:(modelPointPlace hS hA φ).valuation L (algebraMap A L a)≠0:=
   (Valuation.ne_zero_iff _).mpr (by simpa only [map_zero] using hA.ne ha)
 have hvlt:=(model_value_lt_one_iff hS hA φ a).mpr hzero
 have hlog:((modelPointPlace hS hA φ).valuation L (algebraMap A L a)).log < (0:ℤ):=by
   simpa using (WithZero.log_lt_log hv0 (by simp)).2 hvlt
 omega
end Construction
end
end ProximityPrize.SubmissionLower.RCN015
end PackedLegacy_H2

/-! Packed from ProximityPrize.SubmissionLower.G8. -/
section PackedLegacy_G8
namespace ProximityPrize.SubmissionLower.RCN000
open IsDedekindDomain
noncomputable section
variable (K A L:Type*) [Field K] [IsAlgClosed K]
 [CommRing A] [IsDomain A] [Field L]
 [Algebra K A] [Algebra K L] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K A L] [IsScalarTower (Polynomial K) A L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev Normalization:=FunctionField.ringOfIntegers K L
def actualPointPlace (φ:A →ₐ[K] K):HeightOneSpectrum (Normalization K L):=
 RCN015.modelPointPlace
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ
theorem actualPointPlace_injective:
   Function.Injective (actualPointPlace K A L):=
 RCN015.modelPointPlace_injective
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L)
theorem actual_model_value_le_one (φ:A →ₐ[K] K) (a:A):
   (actualPointPlace K A L φ).valuation L (algebraMap A L a) ≤ 1:=
 RCN015.model_value_le_one
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ a
theorem actual_model_value_lt_one_iff (φ:A →ₐ[K] K) (a:A):
   (actualPointPlace K A L φ).valuation L (algebraMap A L a) < 1 ↔ φ a=0:=
 RCN015.model_value_lt_one_iff
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ a
theorem actual_model_zero_order_ge_one
   (φ:A →ₐ[K] K) (a:A) (ha:a≠0) (hzero:φ a=0):
   1 ≤-((actualPointPlace K A L φ).valuation L (algebraMap A L a)).log:=
 RCN015.model_zero_order_ge_one
   (FunctionField.ringOfIntegers.algebraMap_injective K L)
   (IsFractionRing.injective A L) φ a ha hzero
end
end ProximityPrize.SubmissionLower.RCN000
end PackedLegacy_G8

/-! Packed from ProximityPrize.SubmissionLower.R0. -/
section PackedLegacy_R0
namespace ProximityPrize.SubmissionLower.RCN344
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place:=RCN345.NormalizedValuation K L
structure SeparableCoordinate where
 embedding:RatFunc K →ₐ[K] L
 finite:letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L
 separable:letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc K) L
namespace SeparableCoordinate
def value (c:SeparableCoordinate K L):L:=
 c.embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
def degree (c:SeparableCoordinate K L):ℕ:=
 letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
 Module.finrank (RatFunc K) L
variable [IsAlgClosed K]
theorem finite_sum_pole_le_degree (c:SeparableCoordinate K L)
   (W:Finset (Place K L)):
   (∑ v∈W,RCN346.poleOrder K L v (value K L c)) ≤
     (degree K L c:ℤ):=by
 letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
 letI:Algebra (Polynomial K) L:=
   (c.embedding.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra
 letI:IsScalarTower (Polynomial K) (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦(c.embedding.commutes a).symm
 letI:IsScalarTower K (Polynomial K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦by
     change algebraMap K L a=
       c.embedding (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) a))
     rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
     exact (c.embedding.commutes a).symm
 letI:FiniteDimensional (RatFunc K) L:=c.finite
 letI:Algebra.IsSeparable (RatFunc K) L:=c.separable
 exact RCN346.finite_sum_pole_le_finrank K L W
end SeparableCoordinate
abbrev Coordinate:=K ⊕ SeparableCoordinate K L
def coordinateValue:Coordinate K L → L:=
 Sum.elim (algebraMap K L) (SeparableCoordinate.value K L)
def coordinateDegree:Coordinate K L → ℕ:=
 Sum.elim (fun _↦0) (SeparableCoordinate.degree K L)
theorem constant_value_le_one (v:Place K L) (c:K):
   v.val (algebraMap K L c) ≤ 1:=by
 letI:v.val.IsTrivialOn K:=v.property.2
 exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v.val c
variable [IsAlgClosed K]
theorem finite_sum_coordinate_pole_le_degree (c:Coordinate K L)
   (W:Finset (Place K L)):
   (∑ v∈W,RCN346.poleOrder K L v (coordinateValue K L c)) ≤
     (coordinateDegree K L c:ℤ):=by
 rcases c with a | c
 · have hz:∀ v:Place K L,
       RCN346.poleOrder K L v (algebraMap K L a)=0:=
     fun v↦RCN346.poleOrder_eq_zero_of_le_one K L v _
       (constant_value_le_one K L v a)
   simp only [coordinateValue,coordinateDegree,Sum.elim_inl,hz,Finset.sum_const_zero,
     Nat.cast_zero,le_refl]
 · exact SeparableCoordinate.finite_sum_pole_le_degree K L c W
variable {σ:Type*} [Fintype σ]
theorem finite_sum_polynomial_pole_le_box (W:Finset (Place K L))
   (c:σ → Coordinate K L) (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   (∑ v∈W,RCN346.poleOrder K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F)) ≤
     ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 have hlocal:=RCN187.weighted_poleOrder_eval_le_box
   W (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ a↦constant_value_le_one K L v a)
   (fun i↦coordinateValue K L (c i)) cap F hcap
 simp only [Nat.cast_one,one_mul] at hlocal
 calc
   _ ≤ ∑ i,(cap i:ℤ)*
       ∑ v∈W,RCN346.poleOrder K L v (coordinateValue K L (c i)):=hlocal
   _ ≤ _:=by
     apply Finset.sum_le_sum
     intro i _
     exact mul_le_mul_of_nonneg_left
       (finite_sum_coordinate_pole_le_degree K L (c i) W) (Int.natCast_nonneg _)
section FixedSeparator
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance _root_.ProximityPrize.SubmissionLower.RCN344.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN344.instDecidableEqPlace :DecidableEq (Place K L):=Classical.decEq _
theorem finite_zero_places_le_box (c:σ → Coordinate K L)
   (cap:σ → ℕ) (F:MvPolynomial σ K) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F≠0)
   (U:Finset (Place K L))
   (hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F)):
   (U.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 exact (RCN026.finite_zero_places_le_poleMass K L _ hF U hU).trans
   (finite_sum_polynomial_pole_le_box K L _ c cap F hcap)
section AffineModel
variable (A:Type*) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
def modelPlace (φ:A →ₐ[K] K):Place K L:=
 RCN345.chartMap K L
   (Sum.inl (RCN000.actualPointPlace K A L φ))
theorem modelPlace_injective:Function.Injective (modelPlace K L A):=by
 intro φ ψ h
 have hchart:=(RCN345.chartMap_bijective K L).1 h
 exact RCN000.actualPointPlace_injective K A L (Sum.inl.inj hchart)
theorem map_model_eval (x:σ → A) (F:MvPolynomial σ K):
   algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)) F:=by
 have hhom:(algebraMap A L).comp (MvPolynomial.eval₂Hom (algebraMap K A) x)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)):=by
   ext a
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C]
     exact (IsScalarTower.algebraMap_apply K A L a).symm
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X']
 exact DFunLike.congr_fun hhom F
theorem finite_model_zero_points_le_box
   (x:σ → A) (c:σ → Coordinate K L)
   (hc:∀ i,coordinateValue K L (c i)=algebraMap A L (x i))
   (cap:σ → ℕ) (F:MvPolynomial σ K) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (S:Finset (A →ₐ[K] K))
   (hS:∀ φ∈S,φ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   (S.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(coordinateDegree K L (c i):ℤ):=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦coordinateValue K L (c i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=by
   simp_rw [hc]
   exact (map_model_eval K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦coordinateValue K L (c i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦coordinateValue K L (c i)) F):=by
   intro v hv
   obtain ⟨φ,hφ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one K A L φ _ hF (hS φ hφ)
 have h:=finite_zero_places_le_box K L c cap F hcap hnonzero U hU
 have hcard:U.card=S.card:=Finset.card_image_of_injective _ (modelPlace_injective K L A)
 rwa [hcard] at h
end AffineModel
end FixedSeparator
end
end ProximityPrize.SubmissionLower.RCN344
end PackedLegacy_R0

/-! Packed from ProximityPrize.SubmissionLower.L. -/
section PackedLegacy_L
namespace ProximityPrize.SubmissionLower.RCN002
noncomputable section
abbrev CoordinateRing (K:Type) [Field K]
   (P:Ideal (MvPolynomial (Fin 3) K)):=MvPolynomial (Fin 3) K ⧸ P
abbrev CoordinateField (K:Type) [Field K]
   (P:Ideal (MvPolynomial (Fin 3) K)):=FractionRing (CoordinateRing K P)
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def coordinateEvaluation:MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P:=
 (IsScalarTower.toAlgHom K (CoordinateRing K P) (CoordinateField K P)).comp
   (Ideal.Quotient.mkₐ K P)
def coordinate (i:Fin 3):CoordinateField K P:=
 coordinateEvaluation K P (MvPolynomial.X i)
theorem coordinateEvaluation_eq_aeval:
   coordinateEvaluation K P=MvPolynomial.aeval (coordinate K P):=
 MvPolynomial.aeval_unique (coordinateEvaluation K P)
theorem aeval_coordinate_eq_quotient (f:MvPolynomial (Fin 3) K):
   MvPolynomial.aeval (coordinate K P) f=
     algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P f):=by
 rw [←coordinateEvaluation_eq_aeval]
 rfl
theorem coordinateEvaluation_ker:
   RingHom.ker (coordinateEvaluation K P).toRingHom=P:=by
 change RingHom.ker ((algebraMap (CoordinateRing K P) (CoordinateField K P)).comp
   (Ideal.Quotient.mk P))=P
 rw [RingHom.ker_comp_of_injective _
   (IsFractionRing.injective (CoordinateRing K P) (CoordinateField K P)),Ideal.mk_ker]
theorem aeval_coordinate_ker:
   RingHom.ker (MvPolynomial.aeval (coordinate K P)).toRingHom=P:=by
 rw [←coordinateEvaluation_eq_aeval]
 exact coordinateEvaluation_ker K P
theorem adjoin_coordinates_eq_top:
   IntermediateField.adjoin K (Set.range (coordinate K P))=⊤:=by
 apply top_unique
 intro x _
 obtain ⟨a,b,_,hab⟩:=
   IsFractionRing.div_surjective (CoordinateRing K P) x
 obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective a
 obtain ⟨g,rfl⟩:=Ideal.Quotient.mk_surjective b
 apply (IntermediateField.mem_adjoin_range_iff K (coordinate K P) x).mpr
 refine ⟨f,g,?_⟩
 rw [aeval_coordinate_eq_quotient,aeval_coordinate_eq_quotient]
 exact hab.symm
section AlgebraicallyClosed
variable [IsAlgClosed K]
theorem coordinate_eq_scalar_of_isAlgebraic (i:Fin 3)
   (h:IsAlgebraic K (coordinate K P i)):
   ∃ c:K,algebraMap K (CoordinateField K P) c=coordinate K P i:=by
 let S:IntermediateField K (CoordinateField K P):=
   IntermediateField.adjoin K {coordinate K P i}
 letI:Algebra.IsAlgebraic K S:=
   IntermediateField.isAlgebraic_adjoin_simple h.isIntegral
 obtain ⟨c,hc⟩:=
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S)).2
     (⟨coordinate K P i,IntermediateField.mem_adjoin_simple_self K _⟩:S)
 refine ⟨c,?_⟩
 have hcast:=congrArg (algebraMap S (CoordinateField K P)) hc
 simpa only [IntermediateField.algebraMap_apply,
   IntermediateField.coe_algebraMap_apply] using hcast
theorem eq_point_kernel_of_coordinates_algebraic
   (h:∀ i,IsAlgebraic K (coordinate K P i)):
   ∃ v:Fin 3 → K,P=RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
 classical
 choose v hv using fun i => coordinate_eq_scalar_of_isAlgebraic K P i (h i)
 have heval:coordinateEvaluation K P=
     (IsScalarTower.toAlgHom K K (CoordinateField K P)).comp (MvPolynomial.aeval v):=by
   apply MvPolynomial.algHom_ext
   intro i
   simp only [AlgHom.comp_apply,MvPolynomial.aeval_X]
   change coordinate K P i=algebraMap K (CoordinateField K P) (v i)
   exact (hv i).symm
 refine ⟨v,?_⟩
 calc
   P=RingHom.ker (coordinateEvaluation K P).toRingHom:=
     (coordinateEvaluation_ker K P).symm
   _=RingHom.ker ((algebraMap K (CoordinateField K P)).comp
       (MvPolynomial.aeval v).toRingHom):=by rw [heval];rfl
   _=RingHom.ker (MvPolynomial.aeval v).toRingHom:=
     RingHom.ker_comp_of_injective _ (algebraMap K (CoordinateField K P)).injective
theorem exists_transcendental_coordinate_of_ne_point_kernel
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   ∃ i:Fin 3,Transcendental K (coordinate K P i):=by
 classical
 by_contra hnone
 have halg:∀ i,IsAlgebraic K (coordinate K P i):=by
   intro i
   by_contra hi
   exact hnone ⟨i,hi⟩
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic K P halg
 exact hnonpoint v hv
end AlgebraicallyClosed
end
end ProximityPrize.SubmissionLower.RCN002
end PackedLegacy_L

/-! Packed from ProximityPrize.SubmissionLower.Z. -/
section PackedLegacy_Z
namespace ProximityPrize.SubmissionLower.RCN005
open RCN002
noncomputable section
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def rationalBaseEmbedding (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   RatFunc K →ₐ[K] CoordinateField K P:=
 RatFunc.liftAlgHom (Polynomial.aeval (coordinate K P i))
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
     (Polynomial.aeval (coordinate K P i)).toRingHom
     (transcendental_iff_injective.mp hi))
theorem rationalBaseEmbedding_polynomial (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)) (f:Polynomial K):
   rationalBaseEmbedding K P i hi (algebraMap (Polynomial K) (RatFunc K) f)=
     Polynomial.aeval (coordinate K P i) f:=by
 exact RatFunc.liftRingHom_algebraMap _ _ f
abbrev rationalBaseAlgebra (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   Algebra (RatFunc K) (CoordinateField K P):=
 (rationalBaseEmbedding K P i hi).toRingHom.toAlgebra
theorem rationalBaseScalarTower (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IsScalarTower K (RatFunc K) (CoordinateField K P):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 exact IsScalarTower.of_algebraMap_eq fun c =>
   ((rationalBaseEmbedding K P i hi).commutes c).symm
theorem rational_variable_image (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   algebraMap (RatFunc K) (CoordinateField K P)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=coordinate K P i:=by
 change rationalBaseEmbedding K P i hi
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=coordinate K P i
 rw [rationalBaseEmbedding_polynomial,Polynomial.aeval_X]
theorem adjoin_two_coordinates_over_ratFunc_eq_top
   (i j k:Fin 3) (hi:Transcendental K (coordinate K P i))
   (hcover:∀ l:Fin 3,l=i∨l=j∨l=k):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P j,coordinate K P k}:Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   rationalBaseScalarTower K P i hi
 let S:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K) {coordinate K P j,coordinate K P k}
 have hcoords:Set.range (coordinate K P) ⊆ S.restrictScalars K:=by
   rintro x ⟨l,rfl⟩
   rcases hcover l with hl | hl | hl
   · subst l
     have hmem:=S.algebraMap_mem
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
     rw [rational_variable_image K P i hi] at hmem
     exact hmem
   · subst l
     exact IntermediateField.mem_adjoin_pair_left (RatFunc K)
       (coordinate K P j) (coordinate K P k)
   · subst l
     exact IntermediateField.mem_adjoin_pair_right (RatFunc K)
       (coordinate K P j) (coordinate K P k)
 have htop:S.restrictScalars K=⊤:=by
   apply top_unique
   rw [←adjoin_coordinates_eq_top K P]
   exact IntermediateField.adjoin_le_iff.mpr hcoords
 exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
end
end ProximityPrize.SubmissionLower.RCN005
end PackedLegacy_Z

/-! Packed from ProximityPrize.SubmissionLower.H0. -/
section PackedLegacy_H0
namespace ProximityPrize.SubmissionLower.RCN006
open RCN002 RCN005
noncomputable section
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
abbrev polynomialBaseAlgebra (i:Fin 3):
   Algebra (Polynomial K) (CoordinateField K P):=
 (Polynomial.aeval (coordinate K P i)).toRingHom.toAlgebra
theorem polynomialBaseScalarTower (i:Fin 3):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   IsScalarTower K (Polynomial K) (CoordinateField K P):=by
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
 exact IsScalarTower.of_algebraMap_eq fun c =>
   ((Polynomial.aeval (coordinate K P i)).commutes c).symm
theorem polynomialRationalScalarTower (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P):=by
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 exact IsScalarTower.of_algebraMap_eq fun f =>
   (rationalBaseEmbedding_polynomial K P i hi f).symm
def quotientCoordinate (i:Fin 3):CoordinateRing K P:=
 Ideal.Quotient.mk P (MvPolynomial.X i)
abbrev quotientPolynomialAlgebra (i:Fin 3):
   Algebra (Polynomial K) (CoordinateRing K P):=
 (Polynomial.aeval (quotientCoordinate K P i)).toRingHom.toAlgebra
theorem quotientBaseScalarTower (i:Fin 3):
   letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
   IsScalarTower K (Polynomial K) (CoordinateRing K P):=by
 letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
 exact IsScalarTower.of_algebraMap_eq fun c =>
   ((Polynomial.aeval (quotientCoordinate K P i)).commutes c).symm
theorem quotientCoordinate_fraction (i:Fin 3):
   algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i)=
     coordinate K P i:=rfl
theorem quotient_polynomial_fraction (i:Fin 3) (f:Polynomial K):
   algebraMap (CoordinateRing K P) (CoordinateField K P)
       (Polynomial.aeval (quotientCoordinate K P i) f)=
     Polynomial.aeval (coordinate K P i) f:=by
 have hhom:
     (IsScalarTower.toAlgHom K (CoordinateRing K P) (CoordinateField K P)).comp
         (Polynomial.aeval (quotientCoordinate K P i))=
       Polynomial.aeval (coordinate K P i):=by
   apply Polynomial.algHom_ext
   simp only [AlgHom.comp_apply,Polynomial.aeval_X]
   rfl
 exact AlgHom.congr_fun hhom f
theorem quotientFractionScalarTower (i:Fin 3):
   @IsScalarTower (Polynomial K) (CoordinateRing K P) (CoordinateField K P)
     (quotientPolynomialAlgebra K P i).toSMul
     (inferInstance:Algebra (CoordinateRing K P) (CoordinateField K P)).toSMul
     (polynomialBaseAlgebra K P i).toSMul:=by
 letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i
 exact IsScalarTower.of_algebraMap_eq fun f =>
   (quotient_polynomial_fraction K P i f).symm
end
end ProximityPrize.SubmissionLower.RCN006
end PackedLegacy_H0

/-! Packed from ProximityPrize.SubmissionLower.M. -/
section PackedLegacy_M
namespace ProximityPrize.SubmissionLower.RCN007
open scoped Classical BigOperators
open RCN002 RCN005 RCN006
noncomputable section
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
abbrev PointOn:=
 {v:Fin 3 → K//P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom}
def pointHom (v:PointOn K P):CoordinateRing K P →ₐ[K] K:=
 Ideal.Quotient.liftₐ P (MvPolynomial.aeval v.1) (fun F hF↦v.2 hF)
theorem pointHom_mk (v:PointOn K P) (F:MvPolynomial (Fin 3) K):
   pointHom K P v (Ideal.Quotient.mk P F)=MvPolynomial.aeval v.1 F:=rfl
theorem pointHom_coordinate (v:PointOn K P) (i:Fin 3):
   pointHom K P v (quotientCoordinate K P i)=v.1 i:=by
 rw [quotientCoordinate,pointHom_mk,MvPolynomial.aeval_X]
theorem pointHom_injective:Function.Injective (pointHom K P):=by
 intro v w h
 apply Subtype.ext
 funext i
 have hi:=DFunLike.congr_fun h (quotientCoordinate K P i)
 simpa only [pointHom_coordinate] using hi
theorem quotient_eval_eq_mk (F:MvPolynomial (Fin 3) K):
   MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P))
     (quotientCoordinate K P) F=Ideal.Quotient.mk P F:=by
 have hhom:MvPolynomial.aeval (quotientCoordinate K P)=Ideal.Quotient.mkₐ K P:=by
   apply MvPolynomial.algHom_ext
   intro i
   rw [MvPolynomial.aeval_X]
   rfl
 exact AlgHom.congr_fun hhom F
theorem quotient_eval_ne_zero_of_not_mem (F:MvPolynomial (Fin 3) K) (hF:F∉P):
   MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P))
     (quotientCoordinate K P) F≠0:=by
 rw [quotient_eval_eq_mk]
 intro hzero
 exact hF (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
def ProjectionsFiniteSeparable:Prop:=
 ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
def actualCoordinateDegree (i:Fin 3):ℕ:=
 if hi:Transcendental K (coordinate K P i) then
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   Module.finrank (RatFunc K) (CoordinateField K P)
 else 0
theorem actualCoordinateDegree_of_transcendental (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   actualCoordinateDegree K P i=
     (letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
      Module.finrank (RatFunc K) (CoordinateField K P)):=by
 simp only [actualCoordinateDegree,dif_pos hi]
variable [IsAlgClosed K]
def coordinateData (hproj:ProjectionsFiniteSeparable K P) (i:Fin 3):
   RCN344.Coordinate K (CoordinateField K P):=
 if hi:Transcendental K (coordinate K P i) then
   Sum.inr {
     embedding:=rationalBaseEmbedding K P i hi
     finite:=(hproj i hi).1
     separable:=(hproj i hi).2}
 else
   Sum.inl ((coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose)
theorem coordinateData_value (hproj:ProjectionsFiniteSeparable K P) (i:Fin 3):
   RCN344.coordinateValue K (CoordinateField K P)
     (coordinateData K P hproj i)=coordinate K P i:=by
 unfold coordinateData
 split_ifs with hi
 · exact rational_variable_image K P i hi
 · exact (coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose_spec
theorem coordinateData_degree (hproj:ProjectionsFiniteSeparable K P) (i:Fin 3):
   RCN344.coordinateDegree K (CoordinateField K P)
     (coordinateData K P hproj i)=actualCoordinateDegree K P i:=by
 unfold coordinateData actualCoordinateDegree
 split_ifs <;> rfl
theorem finite_zero_points_le_box_of_separator
   (hproj:ProjectionsFiniteSeparable K P)
   (i₀:Fin 3) (hi₀:Transcendental K (coordinate K P i₀))
   (F:MvPolynomial (Fin 3) K) (hF:F∉P)
   (cap:Fin 3 → ℕ) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (S:Finset (Fin 3 → K))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   (S.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(actualCoordinateDegree K P i:ℤ):=by
 classical
 letI:Algebra (Polynomial K) (CoordinateRing K P):=quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (CoordinateField K P):=polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i₀ hi₀
 letI:=quotientBaseScalarTower K P i₀
 letI:=polynomialBaseScalarTower K P i₀
 letI:=quotientFractionScalarTower K P i₀
 letI:=polynomialRationalScalarTower K P i₀ hi₀
 letI:=rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=(hproj i₀ hi₀).1
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=(hproj i₀ hi₀).2
 let c:=coordinateData K P hproj
 have hc:∀ i,RCN344.coordinateValue K (CoordinateField K P) (c i)=
     algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i):=by
   intro i
   rw [quotientCoordinate_fraction]
   exact coordinateData_value K P hproj i
 let liftPoint:{v:Fin 3 → K//v∈S} → (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w h
   have hvw:=pointHom_injective K P h
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) hvw
 let points:=S.attach.image liftPoint
 have hpoints:∀ φ∈points,φ (MvPolynomial.eval₂Hom
     (algebraMap K (CoordinateRing K P)) (quotientCoordinate K P) F)=0:=by
   intro φ hφ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hφ
   rw [quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hcount:=RCN344.finite_model_zero_points_le_box
   K (CoordinateField K P) (CoordinateRing K P) (quotientCoordinate K P)
   c hc cap F hcap (quotient_eval_ne_zero_of_not_mem K P F hF) points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rw [hcard] at hcount
 simpa only [c,coordinateData_degree] using hcount
theorem finite_zero_points_le_box
   (hproj:ProjectionsFiniteSeparable K P)
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 3) K) (hF:F∉P)
   (cap:Fin 3 → ℕ) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (S:Finset (Fin 3 → K))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   (S.card:ℤ) ≤ ∑ i,(cap i:ℤ)*(actualCoordinateDegree K P i:ℤ):=by
 obtain ⟨i,hi⟩:=exists_transcendental_coordinate_of_ne_point_kernel K P hnonpoint
 exact finite_zero_points_le_box_of_separator K P hproj i hi F hF cap hcap S hSP hSF
end
end ProximityPrize.SubmissionLower.RCN007
end PackedLegacy_M

/- Library component S6 is loaded from Mathlib.Order.GameAdd. -/

/- Library component HK is loaded from Mathlib.Data.DFinsupp.WellFounded. -/

/- Library component HM is loaded from Mathlib.Data.Finsupp.WellFounded. -/

/- Library component CP is loaded from Mathlib.Data.Finsupp.MonomialOrder. -/

/- Library component S1 is loaded from Mathlib.Algebra.DirectSum.Algebra. -/

/- Library component HA is loaded from Mathlib.Algebra.DirectSum.Internal. -/

/- Library component T9 is loaded from Mathlib.RingTheory.GradedAlgebra.Basic. -/

/- Library component U1 is loaded from Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule. -/

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier05 : True := by trivial
end ProximityPrize.SubmissionLower

/- Library component U0 is loaded from Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal. -/

/- Library component IP is loaded from Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous. -/

/- Library component F3 is loaded from Mathlib.RingTheory.MvPolynomial.Homogeneous. -/

/- Library component IO is loaded from Mathlib.RingTheory.MvPolynomial.MonomialOrder. -/

/- Library component HL is loaded from Mathlib.Data.Finsupp.MonomialOrder.DegLex. -/

/- Library component IN is loaded from Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex. -/

/- Library component HH is loaded from Mathlib.Algebra.MvPolynomial.Division. -/

/- Library component AO is loaded from Mathlib.Algebra.MvPolynomial.NoZeroDivisors. -/

/-! Packed from ProximityPrize.SubmissionLower.FI. -/
section PackedLegacy_FI
namespace ProximityPrize.SubmissionLower.RCN224
open RCN002
noncomputable section
variable (K:Type) [Field K]
def graphEquation (a b:K):MvPolynomial (Fin 3) K:=
 MvPolynomial.X 0-(MvPolynomial.C a+MvPolynomial.X 2*MvPolynomial.C b)
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem coordinate_algebraic_of_scalar (i:Fin 3) (c:K)
   (hc:coordinate K P i=algebraMap K (CoordinateField K P) c):
   IsAlgebraic K (coordinate K P i):=by
 refine ⟨Polynomial.X-Polynomial.C c,Polynomial.X_sub_C_ne_zero c,?_⟩
 simp [hc]
theorem seed_transcendental_of_affine_coordinates [IsAlgClosed K]
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (a b c d:K)
   (hy:coordinate K P 0=algebraMap K (CoordinateField K P) a+
     coordinate K P 2*algebraMap K (CoordinateField K P) b)
   (hr:coordinate K P 1=algebraMap K (CoordinateField K P) c+
     coordinate K P 2*algebraMap K (CoordinateField K P) d):
   Transcendental K (coordinate K P 2):=by
 intro hz
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic K P 2 hz
 have hy':coordinate K P 0=algebraMap K (CoordinateField K P) (a+z*b):=by
   simpa only [map_add,map_mul,hz] using hy
 have hr':coordinate K P 1=algebraMap K (CoordinateField K P) (c+z*d):=by
   simpa only [map_add,map_mul,hz] using hr
 have hall:∀ i:Fin 3,IsAlgebraic K (coordinate K P i):=by
   intro i
   fin_cases i
   · exact coordinate_algebraic_of_scalar K P 0 _ hy'
   · exact coordinate_algebraic_of_scalar K P 1 _ hr'
   · exact coordinate_algebraic_of_scalar K P 2 _ hz.symm
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic K P hall
 exact hnonpoint v hv
theorem affine_coordinates_of_polynomial_pencil
   (ξ:K) (Q:Polynomial (CoordinateField K P)) (Q₀ Q₁:Polynomial K)
   (hQ:Q=Q₀.map (algebraMap K (CoordinateField K P))+
     Polynomial.C (coordinate K P 2)*Q₁.map (algebraMap K (CoordinateField K P)))
   (hy:Q.eval (algebraMap K (CoordinateField K P) ξ)=coordinate K P 0)
   (hr:Q.derivative.eval (algebraMap K (CoordinateField K P) ξ)=coordinate K P 1):
   coordinate K P 0=algebraMap K (CoordinateField K P) (Q₀.eval ξ)+
       coordinate K P 2*algebraMap K (CoordinateField K P) (Q₁.eval ξ)∧
     coordinate K P 1=algebraMap K (CoordinateField K P) (Q₀.derivative.eval ξ)+
       coordinate K P 2*algebraMap K (CoordinateField K P) (Q₁.derivative.eval ξ):=by
 constructor
 · rw [←hy,hQ]
   simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
     Polynomial.eval_map_apply]
 · rw [←hr,hQ,Polynomial.derivative_add,Polynomial.derivative_C_mul]
   simp only [Polynomial.derivative_map,Polynomial.eval_add,Polynomial.eval_mul,
     Polynomial.eval_C,Polynomial.eval_map_apply]
end
end ProximityPrize.SubmissionLower.RCN224
end PackedLegacy_FI

/-! Packed from ProximityPrize.SubmissionLower.BM. -/
section PackedLegacy_BM
namespace ProximityPrize.SubmissionLower.RCN147
noncomputable section
variable {K L:Type*} [Field K] [Field L]
theorem degree_lt_card_of_natDegree_le {ι:Type*}
   (I:Finset ι) (w:ℕ) (hw:w < I.card) (P:Polynomial L)
   (hP:P.natDegree ≤ w):P.degree < (I.card:WithBot ℕ):=
 lt_of_le_of_lt Polynomial.degree_le_natDegree
   (WithBot.coe_lt_coe.mpr (hP.trans_lt hw))
theorem mapped_affine_pencil_natDegree_le
   (coefficients:K →+*L) (P₀ P₁:Polynomial K) (w:ℕ)
   (h₀:P₀.natDegree ≤ w) (h₁:P₁.natDegree ≤ w) (γ:L):
   (P₀.map coefficients+Polynomial.C γ*P₁.map coefficients).natDegree ≤ w:=by
 apply (Polynomial.natDegree_add_le _ _).trans
 exact max_le (Polynomial.natDegree_map_le.trans h₀)
   ((Polynomial.natDegree_C_mul_le γ _).trans (Polynomial.natDegree_map_le.trans h₁))
theorem exists_basefield_affine_pencil_of_identity_nodes {ι τ:Type*}
   (coefficients:K →+*L) (I:Finset ι) (x u₀ u₁:ι → K)
   (w:ℕ) (hw:w < I.card) (hinj:Set.InjOn x I)
   (γ:τ → L) (P:τ → Polynomial L)
   (hdegree:∀ t,(P t).natDegree ≤ w)
   (hvalues:∀ t i,i∈I →
     (P t).eval (coefficients (x i))=coefficients (u₀ i)+γ t*coefficients (u₁ i)):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     ∀ t,P t=P₀.map coefficients+Polynomial.C (γ t)*P₁.map coefficients:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 obtain ⟨S,hSI,hcard⟩:=Finset.exists_subset_card_eq (show w+1 ≤ I.card by omega)
 have hxS:Set.InjOn x S:=by
   intro i hi j hj hij
   exact hinj (hSI hi) (hSI hj) hij
 let P₀:Polynomial K:=Lagrange.interpolate S x u₀
 let P₁:Polynomial K:=Lagrange.interpolate S x u₁
 have h₀:P₀.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₀ hxS
 have h₁:P₁.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₁ hxS
 have heval₀:∀ i∈S,P₀.eval (x i)=u₀ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₀ hxS hi
 have heval₁:∀ i∈S,P₁.eval (x i)=u₁ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₁ hxS hi
 have hnodes:Set.InjOn (fun i => coefficients (x i)) S:=by
   intro i hi j hj hij
   exact hxS hi hj (coefficients.injective hij)
 have hws:w < S.card:=by omega
 refine ⟨P₀,P₁,h₀,h₁,?_⟩
 intro t
 apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hnodes
   (degree_lt_card_of_natDegree_le S w hws (P t) (hdegree t))
   (degree_lt_card_of_natDegree_le S w hws _
     (mapped_affine_pencil_natDegree_le coefficients P₀ P₁ w h₀ h₁ (γ t)))
 intro i hi
 simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_map_apply,heval₀ i hi,heval₁ i hi] using hvalues t i (hSI hi)
end
end ProximityPrize.SubmissionLower.RCN147
end PackedLegacy_BM

/-! Packed from ProximityPrize.SubmissionLower.E. -/
section PackedLegacy_E
namespace ProximityPrize.SubmissionLower.RCN136
noncomputable section
variable {K L:Type*} [Field K] [Field L]
def collectX (K:Type*) [Field K]:
   MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 3) (Polynomial K):=
 (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 3)).trans
   (MvPolynomial.optionEquivRight K (Fin 3))
@[simp] theorem collectX_C (a:K):
   collectX K (MvPolynomial.C a)=MvPolynomial.C (Polynomial.C a):=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_zero:
   collectX K (MvPolynomial.X (0:Fin 4))=MvPolynomial.C Polynomial.X:=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_succ (i:Fin 3):
   collectX K (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
def surfaceMap (φ:Polynomial K →+*L):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 3) L:=
 (MvPolynomial.map φ).comp (collectX K).toRingHom
@[simp] theorem surfaceMap_C (φ:Polynomial K →+*L) (a:K):
   surfaceMap φ (MvPolynomial.C a)=MvPolynomial.C (φ (Polynomial.C a)):=by
 simp [surfaceMap]
@[simp] theorem surfaceMap_X_zero (φ:Polynomial K →+*L):
   surfaceMap φ (MvPolynomial.X (0:Fin 4))=MvPolynomial.C (φ Polynomial.X):=by
 simp [surfaceMap]
@[simp] theorem surfaceMap_X_succ (φ:Polynomial K →+*L) (i:Fin 3):
   surfaceMap φ (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [surfaceMap]
theorem surfaceMap_injective (φ:Polynomial K →+*L) (hφ:Function.Injective φ):
   Function.Injective (surfaceMap φ):=
 (MvPolynomial.map_injective φ hφ).comp (collectX K).injective
theorem surfaceMap_ne_zero (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):surfaceMap φ Q≠0:=by
 intro h
 apply hQ
 apply surfaceMap_injective φ hφ
 simpa only [map_zero] using h
theorem surfaceMap_eq_eval₂Hom (φ:Polynomial K →+*L):
   surfaceMap φ=
     MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
       (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem eval_surfaceMap (φ:Polynomial K →+*L)
   (v:Fin 3 → L) (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval v (surfaceMap φ Q)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v) Q:=by
 have hhom:(MvPolynomial.eval v).comp (surfaceMap φ)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp
   · intro i
     refine Fin.cases ?_ (fun j => ?_) i <;> simp
 exact RingHom.congr_fun hhom Q
theorem surfaceMap_monomial (φ:Polynomial K →+*L)
   (d:Fin 4 →₀ ℕ) (a:K):
   surfaceMap φ (MvPolynomial.monomial d a)=
     MvPolynomial.monomial d.tail (φ (Polynomial.C a)*(φ Polynomial.X)^d 0):=by
 rw [surfaceMap_eq_eval₂Hom,MvPolynomial.eval₂Hom_monomial]
 simp only [RingHom.comp_apply,Finsupp.prod_pow,Fin.prod_univ_succ,Fin.cases_zero,
   Fin.cases_succ,MvPolynomial.monomial_eq,Finsupp.tail_apply,
   map_mul,map_pow]
 ring
theorem support_surfaceMap_subset (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K):
   (surfaceMap φ Q).support ⊆ Q.support.image Finsupp.tail:=by
 classical
 have hsum:surfaceMap φ Q=
     ∑ d∈Q.support,surfaceMap φ (MvPolynomial.monomial d (MvPolynomial.coeff d Q)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 intro e he
 rw [hsum] at he
 obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
 rw [surfaceMap_monomial] at hed
 have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
 exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
theorem surfaceMap_degreeOf_le (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K) (i:Fin 3):
   (surfaceMap φ Q).degreeOf i ≤ Q.degreeOf i.succ:=by
 classical
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro e he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
 exact MvPolynomial.monomial_le_degreeOf i.succ hd
theorem surfaceMap_separated_caps (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K) (ell s zcap:ℕ)
   (hy:Q.degreeOf 1 ≤ ell) (hr:Q.degreeOf 2 ≤ s) (hz:Q.degreeOf 3 ≤ zcap):
   (surfaceMap φ Q).degreeOf 0 ≤ ell∧
     (surfaceMap φ Q).degreeOf 1 ≤ s∧
     (surfaceMap φ Q).degreeOf 2 ≤ zcap:=
 ⟨(surfaceMap_degreeOf_le φ Q 0).trans hy,
   (surfaceMap_degreeOf_le φ Q 1).trans hr,
   (surfaceMap_degreeOf_le φ Q 2).trans hz⟩
end
end ProximityPrize.SubmissionLower.RCN136
end PackedLegacy_E

/- Library component HF is loaded from Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra. -/

/- Library component IQ is loaded from Mathlib.RingTheory.Nilpotent.Exp. -/

/- Library component HE is loaded from Mathlib.Algebra.Lie.Derivation.Basic. -/

/-! Packed from ProximityPrize.SubmissionLower.R3. -/
section PackedLegacy_R3
namespace ProximityPrize.SubmissionLower.RCN347
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section Derivation
variable {K A:Type*} [CommRing K] [CommRing A] [Algebra K A]
theorem leibniz_product (D:Derivation K A A) (a b:A):
   D (a*b)=D a*b+a*D b:=by
 calc
   D (a*b)=a*D b+b*D a:=by
     simpa only [smul_eq_mul] using D.leibniz a b
   _=D a*b+a*D b:=by ac_rfl
theorem iterate_zero (D:Derivation K A A) (n:ℕ):D^[n] (0:A)=0:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih]
theorem iterate_add (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a+b)=D^[n] a+D^[n] b:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih,map_add]
theorem iterate_one_of_ne_zero (D:Derivation K A A) (n:ℕ) (hn:n≠0):
   D^[n] (1:A)=0:=by
 cases n with
 | zero => exact (hn rfl).elim
 | succ n =>
   rw [Function.iterate_succ_apply,D.map_one_eq_zero]
   exact iterate_zero D n
theorem iterate_product (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a*b)=
     ∑ ij∈antidiagonal n,
       n.choose ij.1 • (D^[ij.1] a*D^[ij.2] b):=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [sum_antidiagonal_choose_succ_nsmul (M:=A)
     (fun i j => D^[i] a*D^[j] b) n]
   simp only [Function.iterate_succ_apply',ih,map_sum,map_nsmul,
     leibniz_product,smul_add,sum_add_distrib]
   rw [add_comm,add_right_inj]
   refine sum_congr rfl fun ⟨i,j⟩ hij => ?_
   rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
end Derivation
section NormalizedCoefficients
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem factorial_cast_ne_zero_below_characteristic
   (p:ℕ) [CharP L p]:∀ n:ℕ,n < p → (n.factorial:L)≠0:=by
 intro n
 induction n with
 | zero =>
   intro hn
   simp
 | succ n ih =>
   intro hn
   have hcast:((n+1:ℕ):L)≠0:=by
     intro hz
     have hdiv:p∣n+1:=(CharP.cast_eq_zero_iff L p (n+1)).mp hz
     exact (Nat.not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) hdiv)
   rw [Nat.factorial_succ,Nat.cast_mul]
   exact mul_ne_zero hcast (ih (by omega))
noncomputable def jetCoefficient
   (D:Derivation K A A) (value:A →+*L) (a:A) (n:ℕ):L:=
 value (D^[n] a)/(n.factorial:L)
theorem factorial_term_product
   (n i j:ℕ) (hij:i+j=n) (x y:L)
   (hn:(n.factorial:L)≠0)
   (hi:(i.factorial:L)≠0)
   (hj:(j.factorial:L)≠0):
   (n.choose i:L)*(x*y)/(n.factorial:L)=
     (x/(i.factorial:L))*(y/(j.factorial:L)):=by
 have hle:i ≤ n:=by omega
 have hsub:n-i=j:=by omega
 have hnat:=Nat.choose_mul_factorial_mul_factorial hle
 rw [hsub] at hnat
 have hcast:(n.choose i:L)*(i.factorial:L)*(j.factorial:L)=
     (n.factorial:L):=by
   simpa only [Nat.cast_mul] using congrArg (fun k:ℕ => (k:L)) hnat
 field_simp
 linear_combination (x*y)*hcast
theorem jetCoefficient_zero (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 0 n=0:=by
 simp [jetCoefficient,iterate_zero]
theorem jetCoefficient_one (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 1 n=if n=0 then 1 else 0:=by
 by_cases hn:n=0
 · subst n
   simp [jetCoefficient]
 · simp [jetCoefficient,iterate_one_of_ne_zero D n hn,hn]
theorem jetCoefficient_add
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ):
   jetCoefficient D value (a+b) n=
     jetCoefficient D value a n+jetCoefficient D value b n:=by
 simp only [jetCoefficient,iterate_add,map_add,add_div]
theorem jetCoefficient_product
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ)
   (hfactorial:∀ i ≤ n,(i.factorial:L)≠0):
   jetCoefficient D value (a*b) n=
     ∑ ij∈antidiagonal n,
       jetCoefficient D value a ij.1*jetCoefficient D value b ij.2:=by
 unfold jetCoefficient
 rw [iterate_product,map_sum,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=n:=mem_antidiagonal.mp hij
 have hi:ij.1 ≤ n:=by omega
 have hj:ij.2 ≤ n:=by omega
 rw [map_nsmul,nsmul_eq_mul,map_mul]
 exact factorial_term_product n ij.1 ij.2 hsum
   (value (D^[ij.1] a)) (value (D^[ij.2] b))
   (hfactorial n le_rfl) (hfactorial ij.1 hi) (hfactorial ij.2 hj)
noncomputable def jetPolynomial
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A):Polynomial L:=
 ∑ j∈range bound,Polynomial.monomial j (jetCoefficient D value a j)
theorem jetPolynomial_coeff
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A) (j:ℕ):
   (jetPolynomial D value bound a).coeff j=
     if j < bound then jetCoefficient D value a j else 0:=by
 classical
 simp [jetPolynomial,Polynomial.coeff_monomial]
theorem jetPolynomial_zero
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ):
   jetPolynomial D value bound 0=0:=by
 ext j
 simp [jetPolynomial_coeff,jetCoefficient_zero]
theorem jetPolynomial_one
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (hbound:0 < bound):
   jetPolynomial D value bound 1=1:=by
 ext j
 by_cases hj:j=0
 · subst j
   simp [jetPolynomial_coeff,jetCoefficient_one,hbound]
 · simp [jetPolynomial_coeff,jetCoefficient_one,hj,Polynomial.coeff_one]
theorem jetPolynomial_add
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A):
   jetPolynomial D value bound (a+b)=
     jetPolynomial D value bound a+jetPolynomial D value bound b:=by
 ext j
 by_cases hj:j < bound <;>
   simp [jetPolynomial_coeff,jetCoefficient_add,hj]
theorem X_pow_dvd_jetPolynomial_product_error
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0):
   (Polynomial.X:Polynomial L)^bound∣
     jetPolynomial D value bound (a*b)-
       jetPolynomial D value bound a*jetPolynomial D value bound b:=by
 rw [Polynomial.X_pow_dvd_iff]
 intro j hj
 rw [Polynomial.coeff_sub]
 apply sub_eq_zero.mpr
 rw [jetPolynomial_coeff,if_pos hj,Polynomial.coeff_mul,
   jetCoefficient_product D value a b j (fun k hk =>
     hfactorial k (lt_of_le_of_lt hk hj))]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=j:=mem_antidiagonal.mp hij
 have hi:ij.1 < bound:=by omega
 have hk:ij.2 < bound:=by omega
 rw [jetPolynomial_coeff,if_pos hi,jetPolynomial_coeff,if_pos hk]
end NormalizedCoefficients
end ProximityPrize.SubmissionLower.RCN347
end PackedLegacy_R3

/-! Packed from ProximityPrize.SubmissionLower.R4. -/
section PackedLegacy_R4
namespace ProximityPrize.SubmissionLower.RCN348
open RCN347
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section TaylorMap
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
noncomputable def truncationIdeal (L:Type*) [Field L] (bound:ℕ):Ideal (Polynomial L):=
 Ideal.span ({(Polynomial.X:Polynomial L)^bound}:Set (Polynomial L))
abbrev TruncatedPolynomials (L:Type*) [Field L] (bound:ℕ):=
 Polynomial L ⧸ truncationIdeal L bound
noncomputable def taylorHom
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0):
   A →+*TruncatedPolynomials L bound where
 toFun a:=Ideal.Quotient.mk (truncationIdeal L bound)
   (jetPolynomial D value bound a)
 map_zero':=by rw [jetPolynomial_zero,map_zero]
 map_one':=by rw [jetPolynomial_one D value bound hbound,map_one]
 map_add' a b:=by rw [jetPolynomial_add,map_add]
 map_mul' a b:=by
   rw [←map_mul]
   apply Ideal.Quotient.eq.mpr
   apply Ideal.mem_span_singleton.mpr
   exact X_pow_dvd_jetPolynomial_product_error D value bound a b hfactorial
theorem iterate_eq_zero_of_derivation_eq_zero
   (D:Derivation K A A) (a:A) (ha:D a=0) (n:ℕ) (hn:n≠0):
   D^[n] a=0:=by
 cases n with
 | zero => exact (hn rfl).elim
 | succ n =>
   rw [Function.iterate_succ_apply,ha]
   exact iterate_zero D n
theorem jetPolynomial_of_derivation_eq_zero
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound) (a:A) (ha:D a=0):
   jetPolynomial D value bound a=Polynomial.C (value a):=by
 ext j
 by_cases hj:j=0
 · subst j
   simp [jetPolynomial_coeff,jetCoefficient,hbound]
 · have hiter:=iterate_eq_zero_of_derivation_eq_zero D a ha j hj
   simp [jetPolynomial_coeff,jetCoefficient,hiter,Polynomial.coeff_C,hj]
theorem jetPolynomial_algebraMap
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound) (c:K):
   jetPolynomial D value bound (algebraMap K A c)=
     Polynomial.C (value (algebraMap K A c)):=
 jetPolynomial_of_derivation_eq_zero D value bound hbound _ (D.map_algebraMap c)
theorem jetCoefficient_derivation
   (D:Derivation K A A) (value:A →+*L) (a:A) (n:ℕ)
   (hn:(n.factorial:L)≠0)
   (hsucc:((n+1).factorial:L)≠0):
   jetCoefficient D value (D a) n=
     jetCoefficient D value a (n+1)*(n+1:L):=by
 have hcast:(n+1:L)≠0:=by
   have hmul:(n+1:L)*(n.factorial:L)≠0:=by
     simpa only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hsucc
   exact (mul_ne_zero_iff.mp hmul).1
 simp only [jetCoefficient,Function.iterate_succ_apply,
   Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
 field_simp
theorem jetPolynomial_derivation_eq_derivative
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A)
   (hfactorial:∀ j ≤ bound,(j.factorial:L)≠0)
   (hlast:jetCoefficient D value a bound=0):
   jetPolynomial D value bound (D a)=
     (jetPolynomial D value bound a).derivative:=by
 ext j
 rw [Polynomial.coeff_derivative,jetPolynomial_coeff,jetPolynomial_coeff]
 by_cases hj:j < bound
 · rw [if_pos hj,jetCoefficient_derivation D value a j
     (hfactorial j hj.le) (hfactorial (j+1) (by omega))]
   by_cases hnext:j+1 < bound
   · rw [if_pos hnext]
   · have heq:j+1=bound:=by omega
     simp [heq,hlast]
 · have hnext:¬j+1 < bound:=by omega
   rw [if_neg hj,if_neg hnext,zero_mul]
theorem jetPolynomial_derivation_eq_derivative_of_char
   (D:Derivation K A A) (value:A →+*L) (p bound:ℕ) [CharP L p]
   (hbound:bound < p) (a:A)
   (hlast:jetCoefficient D value a bound=0):
   jetPolynomial D value bound (D a)=
     (jetPolynomial D value bound a).derivative:=by
 apply jetPolynomial_derivation_eq_derivative D value bound a
 · intro j hj
   exact factorial_cast_ne_zero_below_characteristic p j (lt_of_le_of_lt hj hbound)
 · exact hlast
theorem jetPolynomial_eq_shorter_of_tails_zero
   (D:Derivation K A A) (value:A →+*L) (small bound:ℕ) (a:A)
   (hsmall:small ≤ bound)
   (htails:∀ j,small ≤ j → j < bound → jetCoefficient D value a j=0):
   jetPolynomial D value bound a=jetPolynomial D value small a:=by
 ext j
 rw [jetPolynomial_coeff,jetPolynomial_coeff]
 by_cases hj:j < small
 · rw [if_pos hj,if_pos (lt_of_lt_of_le hj hsmall)]
 · rw [if_neg hj]
   by_cases hb:j < bound
   · rw [if_pos hb,htails j (by omega) hb]
   · rw [if_neg hb]
theorem eq_zero_of_quotient_eq_zero_of_natDegree_lt
   (bound:ℕ) (Q:Polynomial L) (hdegree:Q.natDegree < bound)
   (hzero:Ideal.Quotient.mk (truncationIdeal L bound) Q=0):Q=0:=by
 have hmem:=Ideal.Quotient.eq_zero_iff_mem.mp hzero
 have hdvd:(Polynomial.X:Polynomial L)^bound∣Q:=
   Ideal.mem_span_singleton.mp hmem
 have hcoeff:=Polynomial.X_pow_dvd_iff.mp hdvd
 ext j
 rw [Polynomial.coeff_zero]
 by_cases hj:j < bound
 · exact hcoeff j hj
 · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdegree (by omega))
end TaylorMap
section PolynomialRelation
variable {K A L σ:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem polynomial_relation_of_taylor_substitution
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:0 < bound)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0)
   (coordinates:σ → A) (polynomials:σ → Polynomial L)
   (hcoordinates:∀ i,
     jetPolynomial D value bound (coordinates i)=polynomials i)
   (F:MvPolynomial σ K)
   (hrelation:MvPolynomial.eval₂Hom (algebraMap K A) coordinates F=0)
   (hdegree:(MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F).natDegree < bound):
   MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F=0:=by
 let τ:=taylorHom D value bound hbound hfactorial
 let mk:=Ideal.Quotient.mk (truncationIdeal L bound)
 have hhom:τ.comp (MvPolynomial.eval₂Hom (algebraMap K A) coordinates)=
     mk.comp (MvPolynomial.eval₂Hom
       (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials):=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C]
     change mk (jetPolynomial D value bound (algebraMap K A c))=
       mk (Polynomial.C (value (algebraMap K A c)))
     rw [jetPolynomial_algebraMap D value bound hbound]
   · intro i
     simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X']
     change mk (jetPolynomial D value bound (coordinates i))=mk (polynomials i)
     rw [hcoordinates]
 apply eq_zero_of_quotient_eq_zero_of_natDegree_lt bound _ hdegree
 have hF:=RingHom.congr_fun hhom F
 change τ (MvPolynomial.eval₂Hom (algebraMap K A) coordinates F)=
   mk (MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F) at hF
 rw [hrelation,map_zero] at hF
 exact hF.symm
end PolynomialRelation
end ProximityPrize.SubmissionLower.RCN348
end PackedLegacy_R4

end Compact_PackedLegacyCore0


