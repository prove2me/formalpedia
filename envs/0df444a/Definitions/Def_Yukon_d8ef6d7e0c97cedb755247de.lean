-- Prove2me | Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
-- name    : Yukon_d8ef6d7e0c97cedb755247de
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T23:04:30.269882+00:00
-- url     : https://prove2.me/theorems/0681de86-ff21-4132-be2d-c88384c8bf32
-- title:
--   LowerFoundation source part 3/3
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:foundation-single-import-5240db76b67a04b038f5a4b0ab3cdf0afd6bbd9480d1f2da7ca81f06df77aaa3
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZTc3ZTYyNzA0ZDU3MzBkMWQ3NmUxMWFhOTRjZWRjY2I2YmZkN2JmOTUxOWJlZDQ4ODQ0Mzk2YjEzNGQxZGQxMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tc2luZ2xlLWltcG9ydC01MjQwZGI3NmI2N2EwNGIwMzhmNWE0YjBhYjNjZGYwYWZkNmJiZDk0ODBkMWYyZGE3Y2E4MWYwNmRmNzdhYWEzIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZDhlZjZkN2UwYzk3Y2VkYjc1NTI0N2RlIiwidiI6Mn0]

import Definitions.Def_Yukon_badab604496abada22e6e52a
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
import Definitions.Def_Yukon_2d0e6914e1f35ef62dbe39e4
import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7
import Definitions.Def_Yukon_d283689b285597996aeda737
import Definitions.Def_Yukon_57f2f4a582b59c53cdee835d
import Definitions.Def_Yukon_6b274c76f1610f2d89b18673
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_Yukon_01021eded3220e2800cfca71
import Definitions.Def_Yukon_db9e62887577419e408bc32c
import Definitions.Def_Yukon_7bdfb5c7976bc55dd3e2bf3e
import Definitions.Def_Yukon_b760202e5c2c83529b0a7edc
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.X6. -/
section PackedLegacy_X6
namespace ProximityPrize.SubmissionLower.RCN014
open RCN002 RCN005 RCN011 RCN010
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
theorem planeEvaluation_surjective_of_finite_generatingPair
   {F E:Type} [Field F] [Field E] [Algebra F E]
   [FiniteDimensional F E]
   (y r:E)
   (hgen:IntermediateField.adjoin F ({y,r}:Set E)=⊤):
   Function.Surjective
     (RCN361.planeEval F E y r):=by
 let φ:Polynomial (Polynomial F) →ₐ[F] E:={
   toRingHom:=RCN361.planeEval F E y r
   commutes':=fun a↦by simp [RCN361.planeEval]}
 let A:Subalgebra F E:=φ.range
 let inclusion:A →ₗ[F] E:=A.val
 letI:Module.Finite F A:=
   Module.Finite.of_injective inclusion Subtype.val_injective
 have hAfield:IsField A:=IsField.of_isDomain_of_finite F A
 let L:IntermediateField F E:=A.toIntermediateField' hAfield
 have hy:y∈L:=by
   change y∈A
   refine ⟨Polynomial.C Polynomial.X,?_⟩
   simp [φ,RCN361.planeEval]
 have hr:r∈L:=by
   change r∈A
   refine ⟨Polynomial.X,?_⟩
   simp [φ,RCN361.planeEval]
 have htop:L=⊤:=by
   apply top_unique
   rw [←hgen]
   apply IntermediateField.adjoin_le_iff.mpr
   intro x hx
   rcases hx with hx | hx
   · subst x
     exact hy
   · rw [Set.mem_singleton_iff] at hx
     subst x
     exact hr
 intro x
 have hxL:x∈L:=by rw [htop];trivial
 change x∈A at hxL
 exact hxL
variable (K:Type) [Field K]
 (order:Fin 3 ≃ Fin 3)
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
def mappedPrimaryPiece
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (surface:B) (multiplicity:I → ℕ) (i:I):Ideal B:=
 Ideal.span {surface} ⊔ (Ideal.map f (relation i))^multiplicity i
theorem mappedPrimaryPiece_pairwise_coprime
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (hcoprime:Pairwise fun i j↦IsCoprime (relation i) (relation j))
   (surface:B) (multiplicity:I → ℕ):
   Pairwise fun i j↦IsCoprime
     (mappedPrimaryPiece f relation surface multiplicity i)
     (mappedPrimaryPiece f relation surface multiplicity j):=by
 intro i j hij
 have hmap:IsCoprime (Ideal.map f (relation i)) (Ideal.map f (relation j)):=by
   apply Ideal.isCoprime_iff_sup_eq.mpr
   rw [←Ideal.map_sup,(hcoprime hij).sup_eq,Ideal.map_top]
 have hpows:(Ideal.map f (relation i))^multiplicity i ⊔
     (Ideal.map f (relation j))^multiplicity j=⊤:=
   Ideal.pow_sup_pow_eq_top hmap.sup_eq
 apply Ideal.isCoprime_iff_sup_eq.mpr
 apply top_unique
 rw [←hpows]
 exact sup_le
   ((le_sup_right:(Ideal.map f (relation i))^multiplicity i ≤
     mappedPrimaryPiece f relation surface multiplicity i).trans le_sup_left)
   ((le_sup_right:(Ideal.map f (relation j))^multiplicity j ≤
     mappedPrimaryPiece f relation surface multiplicity j).trans le_sup_right)
theorem span_pair_le_mappedPrimaryPiece
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (surface tail:B) (multiplicity:I → ℕ) (i:I)
   (htail:tail∈mappedPrimaryPiece f relation surface multiplicity i):
   Ideal.span {surface,tail} ≤
     mappedPrimaryPiece f relation surface multiplicity i:=by
 rw [Ideal.span_le]
 intro x hx
 rcases hx with hx | hx
 · rw [hx]
   exact (show Ideal.span {surface} ≤
       mappedPrimaryPiece f relation surface multiplicity i from le_sup_left)
     (Ideal.subset_span (Set.mem_singleton surface))
 · rw [Set.mem_singleton_iff] at hx
   subst x
   exact htail
end
end ProximityPrize.SubmissionLower.RCN014
end PackedLegacy_X6

/-! Packed from ProximityPrize.SubmissionLower.FJ. -/
section PackedLegacy_FJ
namespace ProximityPrize.SubmissionLower.RCN226
open RCN011 RCN021 RCN022 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoefficientRing:=Polynomial (RatFunc K)
def projectedFactor:Polynomial (RatFunc K):=
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))
theorem planeEvaluation_comp_C:
   (planeEvaluation K L order e ht).comp
     (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
       Polynomial.eval₂RingHom
         (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
         (e (MvPolynomial.X (order 2))):=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 apply Polynomial.ringHom_ext
 · intro c
   change planeEvaluation K L order e ht
       (Polynomial.C (Polynomial.C c))=
     Polynomial.aeval (e (MvPolynomial.X (order 2))) (Polynomial.C c)
   rw [planeEvaluation_C_C,Polynomial.aeval_C]
   rfl
 · change planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
     Polynomial.aeval (e (MvPolynomial.X (order 2))) Polynomial.X
   rw [planeEvaluation_C_X,Polynomial.aeval_X]
theorem relationKernel_comap_C:
   (relationKernel K L order e ht).comap
     (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
       Ideal.span {projectedFactor K L order e ht}:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_C,
   show Polynomial.eval₂RingHom
     (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
     (e (MvPolynomial.X (order 2)))=
       (Polynomial.aeval (e (MvPolynomial.X (order 2)))).toRingHom from rfl]
 change RingHom.ker (Polynomial.aeval (e (MvPolynomial.X (order 2))))=
   Ideal.span {minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))}
 rw [minpoly.ker_aeval_eq_span_minpoly]
theorem projectedFactor_monic
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (projectedFactor K L order e ht).Monic:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 exact minpoly.monic (IsIntegral.of_finite _ _)
theorem projectedFactor_irreducible
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Irreducible (projectedFactor K L order e ht):=
 by
   letI:Algebra (RatFunc K) L:=
     (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
   letI:FiniteDimensional (RatFunc K) L:=hfinite
   exact minpoly.irreducible (IsIntegral.of_finite _ _)
theorem relationKernel_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (relationKernel K L order e ht).IsMaximal:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 apply RingHom.ker_isMaximal_of_surjective
 exact planeEvaluation_surjective_of_finite_generatingPair
   (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
end
end ProximityPrize.SubmissionLower.RCN226
end PackedLegacy_FJ

/-! Packed from ProximityPrize.SubmissionLower.C7. -/
section PackedLegacy_C7
namespace ProximityPrize.SubmissionLower.RCN191
open RCN011 RCN021 RCN022 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoeffPrime:Ideal (Polynomial (RatFunc K)):=
 Ideal.span {projectedFactor K L order e ht}
theorem coeffPrime_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (CoeffPrime K L order e ht).IsMaximal:=
 PrincipalIdealRing.isMaximal_of_irreducible
   (projectedFactor_irreducible K L order e ht hfinite)
abbrev LocalCoefficient
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 @Localization.AtPrime (Polynomial (RatFunc K)) _
   (CoeffPrime K L order e ht)
   (coeffPrime_isMaximal K L order e ht hfinite).isPrime
local instance localCoefficientSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (LocalCoefficient K L order e ht hfinite):=
 (inferInstance:CommRing
   (LocalCoefficient K L order e ht hfinite)).toSemiring
local instance localizedPlaneSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 (inferInstance:CommRing
   (Polynomial (LocalCoefficient K L order e ht hfinite))).toSemiring
def localizePlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   PlaneRing K →+*Polynomial (LocalCoefficient K L order e ht hfinite):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))
def localizedRelation
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Ideal (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 Ideal.map (localizePlane K L order e ht hfinite)
   (relationKernel K L order e ht)
theorem localizedRelation_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (localizedRelation K L order e ht hfinite).IsMaximal:=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 have hJmax:J.IsMaximal:=
   relationKernel_isMaximal K L order e ht hfinite hgen
 letI:J.IsPrime:=hJmax.isPrime
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K))
       (J:Set (PlaneRing K)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   apply hr
   have hrJ:r∈J.comap c:=haJ
   have hcomap:J.comap c=p:=by
     simpa only [J,c,p] using
       relationKernel_comap_C K L order e ht
   rwa [hcomap] at hrJ
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra (PlaneRing K) (Polynomial Rp):=
   Polynomial.algebra (Polynomial (RatFunc K)) Rp
 have hf:f=algebraMap (PlaneRing K) (Polynomial Rp):=rfl
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
     (Polynomial Rp):=by
   exact Polynomial.isLocalization p.primeCompl Rp
 have hunder:(localizedRelation K L order e ht hfinite).under
     (PlaneRing K)=J:=by
   change (Ideal.map f J).under (PlaneRing K)=J
   rw [hf]
   exact IsLocalization.under_map_of_isPrime_disjoint
     (I:=J) (p.primeCompl.map c.toMonoidHom) (Polynomial Rp)
       hJmax.isPrime hdisjoint
 letI:((localizedRelation K L order e ht hfinite).under
     (PlaneRing K)).IsMaximal:=
   hunder ▸ hJmax
 have hunder':(Ideal.map
     (algebraMap (PlaneRing K) (Polynomial Rp)) J).under (PlaneRing K)=J:=by
   rw [←hf]
   exact hunder
 letI:((Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).under
     (PlaneRing K)).IsMaximal:=hunder'.symm ▸ hJmax
 change (Ideal.map f J).IsMaximal
 rw [hf]
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
abbrev LocalizedPlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 Polynomial (LocalCoefficient K L order e ht hfinite)
end
end ProximityPrize.SubmissionLower.RCN191
end PackedLegacy_C7

/-! Packed from ProximityPrize.SubmissionLower.DM. -/
section PackedLegacy_DM
namespace ProximityPrize.SubmissionLower.RCN034
open RCN002 RCN005 RCN011 RCN010 RCN371
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type) [Field K]
end
end ProximityPrize.SubmissionLower.RCN034
end PackedLegacy_DM

/-! Packed from ProximityPrize.SubmissionLower.L7. -/
section PackedLegacy_L7
namespace ProximityPrize.SubmissionLower.RCN189
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A B:Type*} [CommRing A] [CommRing B]
 (M:Submonoid A) [Algebra A B] [IsLocalization M B]
end
end ProximityPrize.SubmissionLower.RCN189
end PackedLegacy_L7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier20 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.L8. -/
section PackedLegacy_L8
namespace ProximityPrize.SubmissionLower.RCN190
open RCN189
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A B:Type*} [CommRing A] [CommRing B]
 (M:Submonoid A) [Algebra A B] [IsLocalization M B]
end
end ProximityPrize.SubmissionLower.RCN190
end PackedLegacy_L8

/-! Packed from ProximityPrize.SubmissionLower.EC. -/
section PackedLegacy_EC
namespace ProximityPrize.SubmissionLower.RCN113
open RCN002 RCN011 RCN371 RCN021 RCN125 RCN093 RCN034 RCN190
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K:Type) [Field K]
def flagPlaneMap (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Original K →+*PlaneRing K:=
 (planeMap K order).comp (flagAlgHom lam mu nu).toRingHom
def flagRelationKernel
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=
 relationKernel K (CoordinateField K P) order
   (flagEvaluation K P lam mu nu) ht
end
end ProximityPrize.SubmissionLower.RCN113
end PackedLegacy_EC

/-! Packed from ProximityPrize.SubmissionLower.Z1. -/
section PackedLegacy_Z1
namespace ProximityPrize.SubmissionLower.RCN120
open RCN002 RCN011 RCN371 RCN021 RCN022 RCN125 RCN093
noncomputable section
set_option autoImplicit false
@[reducible] def residueAlgebra
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   (q:Polynomial F) (J:Ideal B)
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   Algebra (AdjoinRoot q) (B ⧸ J):=
 (Ideal.quotientMap J (algebraMap (Polynomial F) B) (by rw [hcontract])).toAlgebra'
   (fun _ _ => mul_comm _ _)
theorem quotient_finrank_eq_natDegree_mul_residue_finrank
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   [IsScalarTower F (Polynomial F) B]
   (q:Polynomial F) (hq:Irreducible q)
   (J:Ideal B) [J.IsMaximal]
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   letI:=residueAlgebra q J hcontract
   Module.finrank F (B ⧸ J)=
     q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
 letI:Fact (Irreducible q):=⟨hq⟩
 let aResidue:Algebra (AdjoinRoot q) (B ⧸ J):=
   residueAlgebra q J hcontract
 letI:Algebra (AdjoinRoot q) (B ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (B ⧸ J):=aResidue.toSMul
 let aBase:Algebra F (AdjoinRoot q):=inferInstance
 letI:SMul F (AdjoinRoot q):=aBase.toSMul
 let aTotal:Algebra F (B ⧸ J):=inferInstance
 letI:SMul F (B ⧸ J):=aTotal.toSMul
 letI:IsScalarTower F (AdjoinRoot q) (B ⧸ J):=
   IsScalarTower.of_algebraMap_eq (R:=F) (S:=AdjoinRoot q)
     (A:=B ⧸ J) fun c => by
       change Ideal.Quotient.mk J (algebraMap F B c)=
         Ideal.Quotient.mk J
           (algebraMap (Polynomial F) B (Polynomial.C c))
       apply congrArg (Ideal.Quotient.mk J)
       change algebraMap F B c=algebraMap (Polynomial F) B
         (algebraMap F (Polynomial F) c)
       exact IsScalarTower.algebraMap_apply F (Polynomial F) B c
 letI:Module.Free F (AdjoinRoot q):=
   Module.Free.of_divisionRing F (AdjoinRoot q)
 letI:Module.Free (AdjoinRoot q) (B ⧸ J):=
   Module.Free.of_divisionRing (AdjoinRoot q) (B ⧸ J)
 calc
   Module.finrank F (B ⧸ J)=
       Module.finrank F (AdjoinRoot q)*
         Module.finrank (AdjoinRoot q) (B ⧸ J):=
     (Module.finrank_mul_finrank F (AdjoinRoot q) (B ⧸ J)).symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
     rw [show Module.finrank F (AdjoinRoot q)=q.natDegree by
       change Module.finrank F (Polynomial F ⧸ Ideal.span {q})=q.natDegree
       exact finrank_quotient_span_eq_natDegree]
variable (K:Type) [Field K]
@[reducible] def flagBaseAlgebra
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Algebra (RatFunc K) (CoordinateField K P):=
 (elementEmbedding K (CoordinateField K P)
   (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
end
end ProximityPrize.SubmissionLower.RCN120
end PackedLegacy_Z1
end Compact_PackedLegacy


