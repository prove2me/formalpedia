-- Prove2me | Definitions.Def_Yukon_74e50608097e19dffcbac46b
-- name    : Yukon_74e50608097e19dffcbac46b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T21:49:58.416802+00:00
-- url     : https://prove2.me/theorems/269d995b-72eb-4a9d-90ec-e85a20233203
-- title:
--   LowerFoundation source part 1/5
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-compact-module-Yukon_74e50608097e19dffcbac46b
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmRlMjA2ODMyZjc0Njk5N2Q3MGI4NTBhYTc4OTRlNzVhNzY2ODg3ZDJkYzdmMWQ2MzQ5YmU4ZjkwNzQ5MDk4MiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tY29tcGFjdC1tb2R1bGUtWXVrb25fNzRlNTA2MDgwOTdlMTlkZmZjYmFjNDZiIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNzRlNTA2MDgwOTdlMTlkZmZjYmFjNDZiIiwidiI6Mn0]

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
/-! Packed from ProximityPrize.SubmissionLower.M3. -/
section PackedLegacy_M3
namespace ProximityPrize.SubmissionLower.RCN199
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN341 RCN095 RCN114 RCN295 RCN187 RCN207 RCN064 RCN204 RCN271 RCN257
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K:Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K
structure MovingPoleBudget (P:Ideal Poly) [P.IsPrime] (H G:Poly) where
 zCost:ℕ
 yzCost:ℕ
 allCost:ℕ
 movingCost:ℕ
 zPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitZFlag)) ≤ (zCost:ℤ)
 yzPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitYZFlag)) ≤ (yzCost:ℤ)
 allPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitAllFlag)) ≤ (allCost:ℤ)
 movingPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,movingPoleTarget P H G v) ≤ (movingCost:ℤ)
namespace MovingPoleBudget
variable {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
 {H G:MvPolynomial (Fin 3) K}
def weightedCost (budget:MovingPoleBudget P H G) (r:FlagDegree):ℕ:=
 r.zOnly*budget.zCost+r.yz*budget.yzCost+r.all*budget.allCost
theorem sum_flagPole_le (budget:MovingPoleBudget P H G) (r:FlagDegree)
   (W:Finset (Place K (CoordinateField K P))):
   (∑ v∈W,flagPole v.val (coordinate K P) r) ≤ (budget.weightedCost r:ℤ):=by
 have hz:=budget.zPole W
 have hy:=budget.yzPole W
 have ha:=budget.allPole W
 simp only [exponentSetPoleWeight_unitZ] at hz
 simp only [exponentSetPoleWeight_unitYZ] at hy
 simp only [exponentSetPoleWeight_unitAll] at ha
 have h:=add_le_add (add_le_add
   (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
   (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
   (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
 simpa only [flagPole,Finset.sum_add_distrib,←Finset.mul_sum,
   weightedCost,Nat.cast_add,Nat.cast_mul] using h
end MovingPoleBudget
end
end ProximityPrize.SubmissionLower.RCN199
end PackedLegacy_M3

/-! Packed from ProximityPrize.SubmissionLower.I7. -/
section PackedLegacy_I7
namespace ProximityPrize.SubmissionLower.RCN076
open RCN208
noncomputable section
set_option autoImplicit false
variable {K E:Type} [Field K] [Field E]
local notation "Poly" => MvPolynomial (Fin 3) K
theorem pderiv_mem_span_of_mul (F U Q:Poly) (hQ:Q=F*U):
   MvPolynomial.pderiv (1:Fin 3) Q∈
     Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
 apply Ideal.mem_span_pair.mpr
 refine ⟨MvPolynomial.pderiv (1:Fin 3) U,U,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul]
 ring
theorem pderiv_mem_span_of_dvd (F Q:Poly) (hFQ:F∣Q):
   MvPolynomial.pderiv (1:Fin 3) Q∈
     Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
 obtain ⟨U,hU⟩:=hFQ
 exact pderiv_mem_span_of_mul F U Q hU
theorem map_derivative_span (φ:K →+*E) (F H:Poly)
   (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly)):
   MvPolynomial.map φ H∈Ideal.span
     ({MvPolynomial.map φ F,
       MvPolynomial.pderiv (1:Fin 3) (MvPolynomial.map φ F)}:
         Set (MvPolynomial (Fin 3) E)):=by
 obtain ⟨A,B,hAB⟩:=Ideal.mem_span_pair.mp h
 apply Ideal.mem_span_pair.mpr
 refine ⟨MvPolynomial.map φ A,MvPolynomial.map φ B,?_⟩
 rw [MvPolynomial.pderiv_map]
 simpa only [map_add,map_mul] using congrArg (MvPolynomial.map φ) hAB
theorem scalar_derivative_span [Algebra K E] (F H:Poly)
   (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly)):
   scalarPolynomialMap K E H∈Ideal.span
     ({scalarPolynomialMap K E F,
       MvPolynomial.pderiv (1:Fin 3) (scalarPolynomialMap K E F)}:
         Set (MvPolynomial (Fin 3) E)):=
 map_derivative_span (algebraMap K E) F H h
theorem map_pderiv_ne_zero_of_mem_span (ev:Poly →+*E) (F H:Poly)
   (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (hF:ev F=0) (hH:ev H≠0):
   ev (MvPolynomial.pderiv (1:Fin 3) F)≠0:=by
 intro hD
 obtain ⟨A,B,hAB⟩:=Ideal.mem_span_pair.mp h
 apply hH
 rw [←hAB,map_add,map_mul,map_mul,hF,hD]
 ring
end
end ProximityPrize.SubmissionLower.RCN076
end PackedLegacy_I7
end Compact_PackedLegacy


