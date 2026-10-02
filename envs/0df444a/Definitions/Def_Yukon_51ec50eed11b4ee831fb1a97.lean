-- Prove2me | Definitions.Def_Yukon_51ec50eed11b4ee831fb1a97
-- name    : Yukon_51ec50eed11b4ee831fb1a97
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T20:49:26.969935+00:00
-- url     : https://prove2.me/theorems/a05322bc-33e9-40d2-a8b3-609980a97b4a
-- title:
--   LowerFoundation source part 3/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:bootstrap-v25-88d147ea07f99a61e287b2f60697d2b76be4d704aebaa309c46e0cdecdafb72d
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjY4MDRmMmMyODZlMzRiODViYzU4NWY0MDI5MGY0NTk2Y2E0NDhiMTk5MGU1NmVlMGZjOWM4MzJhNjQ1NDA0MSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmJvb3RzdHJhcC12MjUtODhkMTQ3ZWEwN2Y5OWE2MWUyODdiMmY2MDY5N2QyYjc2YmU0ZDcwNGFlYmFhMzA5YzQ2ZTBjZGVjZGFmYjcyZCIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzUxZWM1MGVlZDExYjRlZTgzMWZiMWE5NyIsInYiOjJ9]

import Definitions.Def_Yukon_1967cf3ee0b4edc44d1596c2
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
import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7
import Definitions.Def_Yukon_7ec25d71d45b2c1c93aeaa4b
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_Yukon_73cb364285b0db29404203c2
import Definitions.Def_Yukon_ba7304588491aaabedef2404
import Definitions.Def_Yukon_b64c002b9f6caec7014c6911
import Definitions.Def_Yukon_cd1b61f69d8bf8bcce480752
import Definitions.Def_Yukon_01021eded3220e2800cfca71
import Definitions.Def_Yukon_db9e62887577419e408bc32c
import Definitions.Def_Yukon_7bdfb5c7976bc55dd3e2bf3e
import Definitions.Def_Yukon_df15ca12ddf2d8e2d1b3970a
import Definitions.Def_Yukon_b760202e5c2c83529b0a7edc
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacyCore2


/-! Packed from ProximityPrize.SubmissionLower.DE. -/
section PackedLegacy_DE
namespace ProximityPrize.SubmissionLower.RCN024
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_dvd_columns
   (M:Matrix ι ι (Polynomial K)) (a:Polynomial K) (columns:Finset ι)
   (hdiv:∀ j∈columns,∀ i,a∣M i j):
   a^columns.card∣M.det:=by
 classical
 rw [Matrix.det_apply']
 apply Finset.dvd_sum
 intro permutation _
 have hpart:
     (∏ _j∈columns,a)∣∏ j∈columns,M (permutation j) j:=by
   apply Finset.prod_dvd_prod_of_dvd
   intro j hj
   exact hdiv j hj (permutation j)
 have hfull:
     (∏ j∈columns,M (permutation j) j)∣
       ∏ j:ι,M (permutation j) j:=
   Finset.prod_dvd_prod_of_subset columns Finset.univ
     (fun j => M (permutation j) j) (Finset.subset_univ columns)
 have hproduct:a^columns.card∣∏ j:ι,M (permutation j) j:=by
   simpa using hpart.trans hfull
 exact dvd_mul_of_dvd_right hproduct _
theorem irreducible_pow_corank_dvd_det
   (M:Matrix ι ι (Polynomial K)) (mu:Polynomial K)
   (hmu:Irreducible mu):
   mu^(Fintype.card ι-((AdjoinRoot.mk mu).mapMatrix M).rank)∣M.det:=by
 classical
 letI:Fact (Irreducible mu):=⟨hmu⟩
 let reduceMatrix:Matrix ι ι (Polynomial K) →+*
     Matrix ι ι (AdjoinRoot mu):=(AdjoinRoot.mk mu).mapMatrix
 let reduced:Matrix ι ι (AdjoinRoot mu):=reduceMatrix M
 obtain ⟨V,U,e,hV,hU,hnormal⟩:=Matrix.exists_rank_normal_form reduced
 let liftEntry:AdjoinRoot mu → Polynomial K:=
   Function.surjInv (AdjoinRoot.mk_surjective (g:=mu))
 have hliftEntry (x:AdjoinRoot mu):AdjoinRoot.mk mu (liftEntry x)=x:=by
   exact Function.surjInv_eq (AdjoinRoot.mk_surjective (g:=mu)) x
 let Vlift:Matrix ι ι (Polynomial K):=fun i j => liftEntry (V i j)
 let Ulift:Matrix ι ι (Polynomial K):=fun i j => liftEntry (U i j)
 have hmapV:reduceMatrix Vlift=V:=by
   ext i j
   exact hliftEntry (V i j)
 have hmapU:reduceMatrix Ulift=U:=by
   ext i j
   exact hliftEntry (U i j)
 let transformed:Matrix ι ι (Polynomial K):=Vlift*M*Ulift
 have hmapTransformed:reduceMatrix transformed=
     (Matrix.fromBlocks 1 0 0 0).submatrix e e:=by
   change reduceMatrix (Vlift*M*Ulift)=_
   rw [map_mul,map_mul,hmapV,hmapU]
   exact hnormal
 let zeroEmbedding:Fin (Fintype.card ι-reduced.rank) ↪ ι:={
   toFun:=fun j => e.symm (Sum.inr j)
   inj':=by
     intro i j hij
     exact Sum.inr.inj (e.symm.injective hij)
 }
 let zeroColumns:Finset ι:=Finset.univ.map zeroEmbedding
 have hcard:zeroColumns.card=Fintype.card ι-reduced.rank:=by
   simp [zeroColumns]
 have hcolumns:∀ j∈zeroColumns,∀ i,mu∣transformed i j:=by
   intro j hj i
   obtain ⟨j0,_,rfl⟩:=Finset.mem_map.mp hj
   apply AdjoinRoot.mk_eq_zero.mp
   change reduceMatrix transformed i (e.symm (Sum.inr j0))=0
   rw [hmapTransformed]
   simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
   cases e i <;> rfl
 have hVdet:¬mu∣Vlift.det:=by
   intro hdiv
   have hzero:AdjoinRoot.mk mu Vlift.det=0:=AdjoinRoot.mk_eq_zero.mpr hdiv
   have hdetmap:AdjoinRoot.mk mu Vlift.det=V.det:=by
     rw [(AdjoinRoot.mk mu).map_det,hmapV]
   have hVdetUnit:IsUnit V.det:=(Matrix.isUnit_iff_isUnit_det _).mp hV
   exact hVdetUnit.ne_zero (hdetmap ▸ hzero)
 have hUdet:¬mu∣Ulift.det:=by
   intro hdiv
   have hzero:AdjoinRoot.mk mu Ulift.det=0:=AdjoinRoot.mk_eq_zero.mpr hdiv
   have hdetmap:AdjoinRoot.mk mu Ulift.det=U.det:=by
     rw [(AdjoinRoot.mk mu).map_det,hmapU]
   have hUdetUnit:IsUnit U.det:=(Matrix.isUnit_iff_isUnit_det _).mp hU
   exact hUdetUnit.ne_zero (hdetmap ▸ hzero)
 have hdetdiv:=pow_card_dvd_det_of_dvd_columns
   transformed mu zeroColumns hcolumns
 rw [hcard] at hdetdiv
 change mu^(Fintype.card ι-reduced.rank)∣
     (Vlift*M*Ulift).det at hdetdiv
 rw [Matrix.det_mul,Matrix.det_mul] at hdetdiv
 have hprime:Prime mu:=hmu.prime
 have hafterV:mu^(Fintype.card ι-reduced.rank)∣M.det*Ulift.det:=
   hprime.pow_dvd_of_dvd_mul_left _ hVdet (by simpa [mul_assoc] using hdetdiv)
 have hafterU:mu^(Fintype.card ι-reduced.rank)∣M.det:=
   hprime.pow_dvd_of_dvd_mul_right _ hUdet hafterV
 simpa [reduced,reduceMatrix] using hafterU
section SylvesterCorank
variable {F:Type*} [Field F] [DecidableEq F]
def remainderOn (D:Polynomial F) (N:ℕ) (hD:D.Monic):
   Polynomial.degreeLT F N →ₗ[F] Polynomial.degreeLT F D.natDegree where
 toFun p:=⟨(p:Polynomial F) %ₘ D,
   Polynomial.mem_degreeLT.mpr (by
     simpa only [Polynomial.degree_eq_natDegree hD.ne_zero] using
       Polynomial.degree_modByMonic_lt (p:Polynomial F) hD)⟩
 map_add' p q:=Subtype.ext (Polynomial.add_modByMonic _ _)
 map_smul' c p:=Subtype.ext (Polynomial.smul_modByMonic c (p:Polynomial F))
theorem remainderOn_surjective (D:Polynomial F) (N:ℕ) (hD:D.Monic)
   (hdegree:D.natDegree ≤ N):Function.Surjective (remainderOn D N hD):=by
 intro q
 have hqN:(q:Polynomial F).degree < (N:WithBot ℕ):=
   (Polynomial.mem_degreeLT.mp q.property).trans_le (by exact_mod_cast hdegree)
 refine ⟨⟨q,Polynomial.mem_degreeLT.mpr hqN⟩,?_⟩
 apply Subtype.ext
 exact (Polynomial.modByMonic_eq_self_iff hD).mpr (by
   rw [Polynomial.degree_eq_natDegree hD.ne_zero]
   exact Polynomial.mem_degreeLT.mp q.property)
theorem sylvester_rank_eq_finrank_range
   (p q:Polynomial F) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n):
   (Polynomial.sylvester p q m n).rank=
     Module.finrank F (LinearMap.range (Polynomial.sylvesterMap p q hp hq)):=by
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd F m n)
     (Polynomial.degreeLT.basis F (m+n))
     (Polynomial.sylvesterMap p q hp hq)=Polynomial.sylvester p q m n:=
   Polynomial.toMatrix_sylvesterMap' p q hp hq
 rw [Matrix.rank_eq_finrank_range_toLin _
   (Polynomial.degreeLT.basis F (m+n)) (Polynomial.degreeLT.basisProd F m n)]
 rw [←hmatrix,Matrix.toLin_toMatrix]
theorem common_divisor_natDegree_le_sylvester_corank
   (p q D:Polynomial F) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hD:D.Monic) (hDdegree:D.natDegree ≤ m+n)
   (hDp:D∣p) (hDq:D∣q):
   D.natDegree ≤ m+n-(Polynomial.sylvester p q m n).rank:=by
 let R:=remainderOn D (m+n) hD
 let L:=Polynomial.sylvesterMap p q hp hq
 have hsurj:Function.Surjective R:=
   remainderOn_surjective D (m+n) hD hDdegree
 have hcontain:LinearMap.range L ≤ LinearMap.ker R:=by
   rintro output ⟨input,rfl⟩
   rw [LinearMap.mem_ker]
   apply Subtype.ext
   change ((R (L input):Polynomial F))=0
   simp only [R,L,remainderOn,Polynomial.sylvesterMap,LinearMap.coe_mk,
     AddHom.coe_mk]
   apply (Polynomial.modByMonic_eq_zero_iff_dvd hD).mpr
   exact dvd_add (dvd_mul_of_dvd_left hDp _) (dvd_mul_of_dvd_left hDq _)
 have hremainderRank:Module.finrank F (LinearMap.range R)=D.natDegree:=by
   rw [LinearMap.range_eq_top.mpr hsurj,finrank_top]
   simpa using Module.finrank_eq_card_basis
     (Polynomial.degreeLT.basis F D.natDegree)
 have hnull:=LinearMap.finrank_range_add_finrank_ker R
 rw [hremainderRank] at hnull
 have hdomain:Module.finrank F (Polynomial.degreeLT F (m+n))=m+n:=by
   simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F (m+n))
 rw [hdomain] at hnull
 have hmono:=Submodule.finrank_mono hcontain
 have hmatrix:=sylvester_rank_eq_finrank_range p q m n hp hq
 change (Polynomial.sylvester p q m n).rank=
   Module.finrank F (LinearMap.range L) at hmatrix
 omega
theorem sum_common_divisor_natDegrees_le_sylvester_corank
   {I:Type*} [Fintype I]
   (p q:Polynomial F) (D:I → Polynomial F) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n) (hpne:p≠0)
   (hmonic:∀ i,(D i).Monic)
   (hcoprime:Pairwise fun i j => IsCoprime (D i) (D j))
   (hDp:∀ i,D i∣p) (hDq:∀ i,D i∣q):
   (∑ i,(D i).natDegree) ≤
     m+n-(Polynomial.sylvester p q m n).rank:=by
 classical
 let Dprod:Polynomial F:=∏ i,D i
 have hDprodMonic:Dprod.Monic:=by
   dsimp [Dprod]
   simpa using Polynomial.monic_prod_of_monic Finset.univ D
     (fun i _ => hmonic i)
 have hDprodP:Dprod∣p:=by
   dsimp [Dprod]
   exact Fintype.prod_dvd_of_coprime hcoprime hDp
 have hDprodQ:Dprod∣q:=by
   dsimp [Dprod]
   exact Fintype.prod_dvd_of_coprime hcoprime hDq
 have hDprodDegree:Dprod.natDegree=∑ i,(D i).natDegree:=by
   dsimp [Dprod]
   simpa using Polynomial.natDegree_prod_of_monic
     (s:=Finset.univ) (f:=D) (fun i _ => hmonic i)
 have hDdegree:Dprod.natDegree ≤ m+n:=by
   have hle:=Polynomial.natDegree_le_of_dvd hDprodP hpne
   omega
 rw [←hDprodDegree]
 exact common_divisor_natDegree_le_sylvester_corank p q Dprod m n
   hp hq hDprodMonic hDdegree hDprodP hDprodQ
end SylvesterCorank
section IrreducibleAggregation
theorem sum_irreducible_coranks_le_det_natDegree
   {I:Type*} [Fintype I]
   (M:Matrix ι ι (Polynomial K)) (mu:I → Polynomial K) (c:I → ℕ)
   (hmonic:∀ i,(mu i).Monic)
   (hirreducible:∀ i,Irreducible (mu i))
   (hcoprime:Pairwise fun i j => IsCoprime (mu i) (mu j))
   (hcorank:∀ i,
     c i ≤ Fintype.card ι-((AdjoinRoot.mk (mu i)).mapMatrix M).rank)
   (hdet:M.det≠0):
   (∑ i,c i*(mu i).natDegree) ≤ M.det.natDegree:=by
 classical
 have hfactor (i:I):(mu i)^c i∣M.det:=
   (pow_dvd_pow (mu i) (hcorank i)).trans
     (irreducible_pow_corank_dvd_det M (mu i) (hirreducible i))
 have hpowersCoprime:Pairwise fun i j =>
     IsCoprime ((mu i)^c i) ((mu j)^c j):=by
   intro i j hij
   exact (hcoprime hij).pow
 have hprodDvd:(∏ i,(mu i)^c i)∣M.det:=
   Fintype.prod_dvd_of_coprime hpowersCoprime hfactor
 have hprodMonic:(∏ i,(mu i)^c i).Monic:=by
   simpa using Polynomial.monic_prod_of_monic Finset.univ
     (fun i => (mu i)^c i) (fun i _ => (hmonic i).pow _)
 have hdegree:(∏ i,(mu i)^c i).natDegree=
     ∑ i,c i*(mu i).natDegree:=by
   rw [Polynomial.natDegree_prod_of_monic
     (s:=Finset.univ) (f:=fun i => (mu i)^c i)
     (fun i _ => (hmonic i).pow _)]
   apply Finset.sum_congr rfl
   intro i _
   exact Polynomial.natDegree_pow (mu i) (c i)
 rw [←hdegree]
 exact Polynomial.natDegree_le_of_dvd hprodDvd hdet
end IrreducibleAggregation
section RelationKernel
variable {K₀ E₁ E₂:Type} [Field K₀] [DecidableEq K₀]
 [Field E₁] [Field E₂] [Algebra K₀ E₁] [Algebra K₀ E₂]
theorem planeEval_quotientRoot_eq_aeval_map
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   (r:E₁) (P:Polynomial (Polynomial K₀)):
   RCN361.planeEval K₀ E₁
     (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r P=
     Polynomial.aeval r (P.map (AdjoinRoot.mk mu)):=by
 let y:E₁:=algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)
 have hcoeff:
     (algebraMap (AdjoinRoot mu) E₁).comp (AdjoinRoot.mk mu)=
       Polynomial.eval₂RingHom (algebraMap K₀ E₁) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     simpa only [RingHom.comp_apply,AdjoinRoot.mk_C,
       Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.algebraMap_eq] using
       (IsScalarTower.algebraMap_apply K₀ (AdjoinRoot mu) E₁ c).symm
   · simp only [RingHom.comp_apply,AdjoinRoot.mk_X,
       Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,y]
 let rhs:Polynomial (Polynomial K₀) →+*E₁:=
   (Polynomial.aeval r).toRingHom.comp
     (Polynomial.mapRingHom (AdjoinRoot.mk mu))
 have heq:RCN361.planeEval K₀ E₁ y r=rhs:=by
   apply Polynomial.ringHom_ext
   · intro c
     simpa only [RCN361.planeEval,RingHom.comp_apply,
       Polynomial.coe_mapRingHom,Polynomial.map_C,
       Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.aeval_C,
       rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using
       (congrFun (congrArg DFunLike.coe hcoeff) c).symm
   · simp only [RCN361.planeEval,RingHom.comp_apply,
       Polynomial.coe_mapRingHom,Polynomial.map_X,
       Polynomial.coe_evalRingHom,Polynomial.eval_X,Polynomial.aeval_X,
       rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
 exact DFunLike.congr_fun heq P
theorem mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   (r:E₁) (P:Polynomial (Polynomial K₀)):
   P∈RCN361.relationIdeal K₀ E₁
       (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r ↔
     minpoly (AdjoinRoot mu) r∣P.map (AdjoinRoot.mk mu):=by
 change RCN361.planeEval K₀ E₁
     (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r P=0 ↔ _
 rw [planeEval_quotientRoot_eq_aeval_map]
 exact minpoly.dvd_iff.symm
theorem relationIdeal_eq_of_adjoinRoot_minpoly_eq
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   [Algebra (AdjoinRoot mu) E₂] [IsScalarTower K₀ (AdjoinRoot mu) E₂]
   (r₁:E₁) (r₂:E₂)
   (hmin:minpoly (AdjoinRoot mu) r₁=minpoly (AdjoinRoot mu) r₂):
   RCN361.relationIdeal K₀ E₁
       (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r₁=
     RCN361.relationIdeal K₀ E₂
       (algebraMap (AdjoinRoot mu) E₂ (AdjoinRoot.root mu)) r₂:=by
 apply Ideal.ext
 intro P
 rw [mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map,
   mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map,hmin]
theorem relative_minpolys_pairwise_coprime_of_relationIdeal_injective
   {I:Type*} [Fintype I]
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   (E:I → Type) [∀ i,Field (E i)]
   [∀ i,Algebra K₀ (E i)]
   [∀ i,Algebra (AdjoinRoot mu) (E i)]
   [∀ i,IsScalarTower K₀ (AdjoinRoot mu) (E i)]
   [∀ i,FiniteDimensional (AdjoinRoot mu) (E i)]
   (r:∀ i,E i)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K₀ (E i)
       (algebraMap (AdjoinRoot mu) (E i) (AdjoinRoot.root mu)) (r i))):
   Pairwise fun i j => IsCoprime
     (minpoly (AdjoinRoot mu) (r i)) (minpoly (AdjoinRoot mu) (r j)):=by
 intro i j hij
 have hiIntegral:IsIntegral (AdjoinRoot mu) (r i):=
   IsIntegral.of_finite (AdjoinRoot mu) (r i)
 have hjIntegral:IsIntegral (AdjoinRoot mu) (r j):=
   IsIntegral.of_finite (AdjoinRoot mu) (r j)
 have hiIrreducible:=minpoly.irreducible hiIntegral
 have hjIrreducible:=minpoly.irreducible hjIntegral
 apply hiIrreducible.coprime_iff_not_dvd.mpr
 intro hdvd
 have hassociated:=hiIrreducible.associated_of_dvd hjIrreducible hdvd
 have hmin:minpoly (AdjoinRoot mu) (r i)=
     minpoly (AdjoinRoot mu) (r j):=
   Polynomial.eq_of_monic_of_associated
     (minpoly.monic hiIntegral) (minpoly.monic hjIntegral) hassociated
 have hk:=relationIdeal_eq_of_adjoinRoot_minpoly_eq
   (K₀:=K₀) (E₁:=E i) (E₂:=E j) mu (r i) (r j) hmin
 exact hij (hkernels hk)
end RelationKernel
section SingleComponent
variable {E:Type*} [Field E] [Algebra K E]
end SingleComponent
section SingleComponentBidegree
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀]
end SingleComponentBidegree
section ExistingGeneratingPair
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀] [FiniteDimensional K₀ E₀]
end ExistingGeneratingPair
section FiniteWithoutSeparability
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀]
theorem finiteDimensional_of_integral_generating_pair
   (y r:E₀) (hy:IsIntegral K₀ y) (hr:IsIntegral K₀ r)
   (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
   FiniteDimensional K₀ E₀:=by
 letI:FiniteDimensional K₀
     (IntermediateField.adjoin K₀ ({y,r}:Set E₀)):=
   IntermediateField.finiteDimensional_adjoin_pair hy hr
 letI:FiniteDimensional K₀ (⊤:IntermediateField K₀ E₀):=by
   rw [←hgen]
   infer_instance
 exact Module.Finite.of_surjective
   (IntermediateField.topEquiv (F:=K₀) (E:=E₀)).toLinearMap
   (IntermediateField.topEquiv (F:=K₀) (E:=E₀)).surjective
theorem finite_of_proper_plane_roots
   (P Q:Polynomial (Polynomial K₀))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬P∣Q) (y r:E₀)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r Q=0)
   (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
   FiniteDimensional K₀ E₀:=by
 classical
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=RCN364.resultant_aeval_eq_zero_of_common_root P Q
   P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive))
     y r hP hQ
 have hyIntegral:IsIntegral K₀ y:=
   IsAlgebraic.isIntegral ⟨Polynomial.resultant P Q P.natDegree Q.natDegree,
     hresne,hresroot⟩
 let S:IntermediateField K₀ E₀:=IntermediateField.adjoin K₀ {y}
 let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K₀ y⟩
 let g:Polynomial K₀ →+*S:=Polynomial.eval₂RingHom (algebraMap K₀ S) yS
 let Py:Polynomial S:=P.map g
 have hPyne:Py≠0:=by
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K₀ S) P
     (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.bimap_specialization] at h
   exact h
 have hcoefficient:(algebraMap S E₀).comp g=
     Polynomial.eval₂RingHom (algebraMap K₀ E₀) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap S E₀
         (Polynomial.eval₂ (algebraMap K₀ S) yS (Polynomial.C c))=
       Polynomial.eval₂ (algebraMap K₀ E₀) y (Polynomial.C c)
     rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
     exact (IsScalarTower.algebraMap_apply K₀ S E₀ c).symm
   · change algebraMap S E₀
         (Polynomial.eval₂ (algebraMap K₀ S) yS Polynomial.X)=
       Polynomial.eval₂ (algebraMap K₀ E₀) y Polynomial.X
     rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
     rfl
 have hPyroot:Polynomial.aeval r Py=0:=by
   change Polynomial.eval₂ (algebraMap S E₀) r (P.map g)=0
   rw [Polynomial.eval₂_map,hcoefficient]
   exact hP
 have hrIntegralS:IsIntegral S r:=
   IsAlgebraic.isIntegral ⟨Py,hPyne,hPyroot⟩
 letI:FiniteDimensional K₀ S:=
   IntermediateField.adjoin.finiteDimensional hyIntegral
 letI:Algebra.IsIntegral K₀ S:=Algebra.IsIntegral.of_finite K₀ S
 have hrIntegral:IsIntegral K₀ r:=isIntegral_trans r hrIntegralS
 exact finiteDimensional_of_integral_generating_pair y r hyIntegral hrIntegral hgen
end FiniteWithoutSeparability
end
end ProximityPrize.SubmissionLower.RCN024
end PackedLegacy_DE

/-! Packed from ProximityPrize.SubmissionLower.DF. -/
section PackedLegacy_DF
namespace ProximityPrize.SubmissionLower.RCN025
open scoped Classical BigOperators
open RCN024
noncomputable section
section ScalarBridge
variable {K B E:Type} [Field K] [Field B] [Field E]
 [Algebra K B] [Algebra K E] [Algebra B E] [IsScalarTower K B E]
theorem adjoin_singleton_eq_top_of_pair_eq_top
   (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hy:∃ b:B,algebraMap B E b=y):
   IntermediateField.adjoin B ({r}:Set E)=⊤:=by
 have hgenAll:IntermediateField.adjoin B ({y,r}:Set E)=⊤:=
   IntermediateField.adjoin_eq_top_of_adjoin_eq_top
     (F:=K) (E:=B) (K:=E) hgen
 apply le_antisymm le_top
 rw [←hgenAll]
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases Set.mem_insert_iff.mp hx with hxy | hxr
 · subst x
   obtain ⟨b,rfl⟩:=hy
   exact IntermediateField.adjoin.algebraMap_mem B {r} b
 · have:x=r:=Set.mem_singleton_iff.mp hxr
   subst x
   exact IntermediateField.subset_adjoin B {r} (Set.mem_singleton r)
end ScalarBridge
section MinpolyTower
variable {K E:Type} [Field K] [DecidableEq K] [Field E] [Algebra K E]
 [FiniteDimensional K E]
theorem minpoly_natDegree_dvd_finrank (y:E):
   (minpoly K y).natDegree∣Module.finrank K E:=by
 classical
 have hyIntegral:IsIntegral K y:=IsIntegral.of_finite K y
 let mu:Polynomial K:=minpoly K y
 have hmuIrreducible:Irreducible mu:=minpoly.irreducible hyIntegral
 letI:Fact (Irreducible mu):=⟨hmuIrreducible⟩
 let baseHom:AdjoinRoot mu →ₐ[K] E:=
   AdjoinRoot.liftAlgHom mu (Algebra.ofId K E) y (by
     change Polynomial.aeval y mu=0
     exact minpoly.aeval K y)
 letI:Algebra (AdjoinRoot mu) E:=baseHom.toRingHom.toAlgebra
 haveI:IsScalarTower K (AdjoinRoot mu) E:=
   IsScalarTower.of_algebraMap_eq fun c => (baseHom.commutes c).symm
 letI:Module.Finite (AdjoinRoot mu) E:=
   Module.Finite.of_restrictScalars_finite K (AdjoinRoot mu) E
 letI:FiniteDimensional K (AdjoinRoot mu):=
   (AdjoinRoot.powerBasis hmuIrreducible.ne_zero).finite
 have hbase:Module.finrank K (AdjoinRoot mu)=mu.natDegree:=by
   change Module.finrank K (Polynomial K ⧸ Ideal.span {mu})=mu.natDegree
   exact finrank_quotient_span_eq_natDegree
 refine ⟨Module.finrank (AdjoinRoot mu) E,?_⟩
 rw [←Module.finrank_mul_finrank K (AdjoinRoot mu) E,hbase]
end MinpolyTower
section FixedResiduePolynomial
variable {K:Type} [Field K] [DecidableEq K]
 {I:Type*} [Fintype I]
theorem sum_relative_finrank_le_sylvester_corank
   (mu:Polynomial K) [Fact (Irreducible mu)]
   (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   [∀ i,Algebra (AdjoinRoot mu) (E i)]
   [∀ i,IsScalarTower K (AdjoinRoot mu) (E i)]
   [∀ i,FiniteDimensional (AdjoinRoot mu) (E i)]
   (r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin (AdjoinRoot mu)
     ({r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K (E i)
       (algebraMap (AdjoinRoot mu) (E i) (AdjoinRoot.root mu)) (r i)))
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hPne:P.map (AdjoinRoot.mk mu)≠0)
   (hProot:∀ i,Polynomial.aeval (r i) (P.map (AdjoinRoot.mk mu))=0)
   (hQroot:∀ i,Polynomial.aeval (r i) (Q.map (AdjoinRoot.mk mu))=0):
   (∑ i,Module.finrank (AdjoinRoot mu) (E i)) ≤
     m+n-(Polynomial.sylvester
       (P.map (AdjoinRoot.mk mu)) (Q.map (AdjoinRoot.mk mu)) m n).rank:=by
 classical
 let D:I → Polynomial (AdjoinRoot mu):=
   fun i => minpoly (AdjoinRoot mu) (r i)
 have hmonic:∀ i,(D i).Monic:=fun i =>
   minpoly.monic (IsIntegral.of_finite (AdjoinRoot mu) (r i))
 have hcoprime:Pairwise fun i j => IsCoprime (D i) (D j):=by
   exact relative_minpolys_pairwise_coprime_of_relationIdeal_injective
     mu E r hkernels
 have hDp:∀ i,D i∣P.map (AdjoinRoot.mk mu):=fun i =>
   minpoly.dvd (AdjoinRoot mu) (r i) (hProot i)
 have hDq:∀ i,D i∣Q.map (AdjoinRoot.mk mu):=fun i =>
   minpoly.dvd (AdjoinRoot mu) (r i) (hQroot i)
 have hdegree:∀ i,(D i).natDegree=
     Module.finrank (AdjoinRoot mu) (E i):=fun i =>
   (Field.primitive_element_iff_minpoly_natDegree_eq
     (AdjoinRoot mu) (r i)).mp (hgen i)
 have hbound:=sum_common_divisor_natDegrees_le_sylvester_corank
   (P.map (AdjoinRoot.mk mu)) (Q.map (AdjoinRoot.mk mu)) D m n
   (Polynomial.natDegree_map_le.trans hPcap)
   (Polynomial.natDegree_map_le.trans hQcap) hPne
   hmonic hcoprime hDp hDq
 simpa only [hdegree] using hbound
end FixedResiduePolynomial
section MinpolyGrouping
variable {K:Type} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
 {I:Type*} [Fintype I]
theorem sum_grouped_weights_le_det_natDegree
   (M:Matrix ι ι (Polynomial K))
   (mu:I → Polynomial K) (relativeDegree:I → ℕ)
   (hmonic:∀ i,(mu i).Monic)
   (hirreducible:∀ i,Irreducible (mu i))
   (fiberCorank:∀ f∈(Finset.univ.image mu),
     (∑ i with mu i=f,relativeDegree i) ≤
       Fintype.card ι-((AdjoinRoot.mk f).mapMatrix M).rank)
   (hdet:M.det≠0):
   (∑ i,relativeDegree i*(mu i).natDegree) ≤ M.det.natDegree:=by
 classical
 let roots:Finset (Polynomial K):=Finset.univ.image mu
 let c:roots → ℕ:=fun f => ∑ i with mu i=f.1,relativeDegree i
 have hrootsMonic:∀ f:roots,(f.1).Monic:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hmonic i
 have hrootsIrreducible:∀ f:roots,Irreducible f.1:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hirreducible i
 have hrootsCoprime:Pairwise fun f g:roots => IsCoprime f.1 g.1:=by
   intro f g hfg
   apply (hrootsIrreducible f).coprime_iff_not_dvd.mpr
   intro hdvd
   have hassociated:=
     (hrootsIrreducible f).associated_of_dvd (hrootsIrreducible g) hdvd
   have heq:f.1=g.1:=Polynomial.eq_of_monic_of_associated
     (hrootsMonic f) (hrootsMonic g) hassociated
   exact hfg (Subtype.ext heq)
 have hc:∀ f:roots,
     c f ≤ Fintype.card ι-((AdjoinRoot.mk f.1).mapMatrix M).rank:=by
   intro f
   exact fiberCorank f.1 f.2
 have houter:=sum_irreducible_coranks_le_det_natDegree
   (K:=K) (I:=roots) M (fun f:roots => f.1) c
     hrootsMonic hrootsIrreducible hrootsCoprime hc hdet
 have hregroup:
     (∑ f:roots,c f*f.1.natDegree)=
       ∑ i,relativeDegree i*(mu i).natDegree:=by
   change (∑ f:roots,
     (∑ i with mu i=f.1,relativeDegree i)*f.1.natDegree)=_
   have hattach:
       (∑ f:roots,
         (∑ i with mu i=f.1,relativeDegree i)*f.1.natDegree)=
       ∑ f∈roots,
         (∑ i with mu i=f,relativeDegree i)*f.natDegree:=by
     rw [show (Finset.univ:Finset roots)=roots.attach from
       Finset.univ_eq_attach roots]
     exact Finset.sum_attach roots (fun f:Polynomial K =>
       (∑ i with mu i=f,relativeDegree i)*f.natDegree)
   rw [hattach]
   simp_rw [Finset.sum_mul]
   calc
     (∑ f∈roots,∑ i with mu i=f,
         relativeDegree i*f.natDegree)=
         ∑ f∈roots,∑ i with mu i=f,
           relativeDegree i*(mu i).natDegree:=by
       apply Finset.sum_congr rfl
       intro f hf
       apply Finset.sum_congr rfl
       intro i hi
       rw [(Finset.mem_filter.mp hi).2]
     _=∑ i∈(Finset.univ:Finset I),
         relativeDegree i*(mu i).natDegree:=
       Finset.sum_fiberwise_of_maps_to
         (s:=Finset.univ) (t:=roots) (g:=mu)
         (fun i _ => Finset.mem_image_of_mem mu (Finset.mem_univ i)) _
     _=∑ i,relativeDegree i*(mu i).natDegree:=by rfl
 rwa [hregroup] at houter
end MinpolyGrouping
section FinitePlaneFamily
variable {K:Type} [Field K] [DecidableEq K]
 {I:Type*} [Fintype I]
 (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 [∀ i,FiniteDimensional K (E i)]
theorem sum_finrank_le_resultant_of_relationIdeal_injective
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) Q=0)
   (hPspecial:∀ f∈
     (Finset.univ.image (fun i => minpoly K (y i))),
       P.map (AdjoinRoot.mk f)≠0)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ i,Module.finrank K (E i)) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 classical
 let mu:I → Polynomial K:=fun i => minpoly K (y i)
 let relativeDegree:I → ℕ:=fun i =>
   Module.finrank K (E i)/(mu i).natDegree
 have hmuMonic:∀ i,(mu i).Monic:=fun i =>
   minpoly.monic (IsIntegral.of_finite K (y i))
 have hmuIrreducible:∀ i,Irreducible (mu i):=fun i =>
   minpoly.irreducible (IsIntegral.of_finite K (y i))
 have htotal:∀ i,relativeDegree i*(mu i).natDegree=
     Module.finrank K (E i):=by
   intro i
   exact Nat.div_mul_cancel (minpoly_natDegree_dvd_finrank (K:=K) (y i))
 have hfiber:∀ f∈(Finset.univ.image mu),
     (∑ i with mu i=f,relativeDegree i) ≤
       m+n-((AdjoinRoot.mk f).mapMatrix
         (Polynomial.sylvester P Q m n)).rank:=by
   intro f hf
   let J:={i:I//mu i=f}
   have hJnonempty:Nonempty J:=by
     obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hf
     exact ⟨⟨i,hi⟩⟩
   let j₀:J:=Classical.choice hJnonempty
   have hfIrreducible:Irreducible f:=by
     simpa only [←j₀.property] using hmuIrreducible j₀.1
   letI:Fact (Irreducible f):=⟨hfIrreducible⟩
   let fiberBaseHom:∀ j:J,AdjoinRoot f →ₐ[K] E j.1:=fun j =>
     AdjoinRoot.liftAlgHom f (Algebra.ofId K (E j.1)) (y j.1) (by
       change Polynomial.aeval (y j.1) f=0
       calc
         _=Polynomial.aeval (y j.1) (mu j.1):=
           congrArg (Polynomial.aeval (y j.1)) j.property.symm
         _=0:=minpoly.aeval K (y j.1))
   letI:∀ j:J,Algebra (AdjoinRoot f) (E j.1):=
     fun j => (fiberBaseHom j).toRingHom.toAlgebra
   letI:∀ j:J,IsScalarTower K (AdjoinRoot f) (E j.1):=
     fun j => IsScalarTower.of_algebraMap_eq
       (fun c => ((fiberBaseHom j).commutes c).symm)
   letI:∀ j:J,Module.Finite (AdjoinRoot f) (E j.1):=
     fun j => Module.Finite.of_restrictScalars_finite K (AdjoinRoot f) (E j.1)
   letI:FiniteDimensional K (AdjoinRoot f):=
     (AdjoinRoot.powerBasis hfIrreducible.ne_zero).finite
   have hroot (j:J):
       algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f)=y j.1:=by
     change fiberBaseHom j (AdjoinRoot.root f)=y j.1
     exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId K (E j.1))
       (y j.1) _
   have hgenRelative:∀ j:J,
       IntermediateField.adjoin (AdjoinRoot f)
         ({r j.1}:Set (E j.1))=⊤:=by
     intro j
     exact adjoin_singleton_eq_top_of_pair_eq_top
       (y j.1) (r j.1) (hgen j.1)
         ⟨AdjoinRoot.root f,hroot j⟩
   have hkernelFiber:Function.Injective (fun j:J =>
       RCN361.relationIdeal K (E j.1)
         (algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f)) (r j.1)):=by
     intro a b hab
     apply Subtype.ext
     apply hkernels
     simpa only [hroot] using hab
   have hProotFiber:∀ j:J,
       Polynomial.aeval (r j.1) (P.map (AdjoinRoot.mk f))=0:=by
     intro j
     rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
     exact hProot j.1
   have hQrootFiber:∀ j:J,
       Polynomial.aeval (r j.1) (Q.map (AdjoinRoot.mk f))=0:=by
     intro j
     rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
     exact hQroot j.1
   have hfixed:=sum_relative_finrank_le_sylvester_corank
     (K:=K) (I:=J) f (fun j:J => E j.1) (fun j => r j.1)
     hgenRelative hkernelFiber P Q m n hPcap hQcap
     (hPspecial f (by simpa only [mu] using hf)) hProotFiber hQrootFiber
   have hbase:Module.finrank K (AdjoinRoot f)=f.natDegree:=by
     change Module.finrank K (Polynomial K ⧸ Ideal.span {f})=f.natDegree
     exact finrank_quotient_span_eq_natDegree
   have hrelative (j:J):relativeDegree j.1=
       Module.finrank (AdjoinRoot f) (E j.1):=by
     change Module.finrank K (E j.1)/(mu j.1).natDegree=_
     rw [j.property, ←Module.finrank_mul_finrank K (AdjoinRoot f) (E j.1),
       hbase]
     exact Nat.mul_div_cancel_left _ hfIrreducible.natDegree_pos
   have hsum:(∑ i with mu i=f,relativeDegree i)=
       ∑ j:J,Module.finrank (AdjoinRoot f) (E j.1):=by
     calc
       _=∑ j:J,relativeDegree j.1:=by
         simpa only [J,Finset.subtype_univ] using
           (Finset.sum_subtype_eq_sum_filter
             (s:=(Finset.univ:Finset I)) relativeDegree
             (p:=fun i => mu i=f)).symm
       _=_:=by
         apply Finset.sum_congr rfl
         intro j _
         exact hrelative j
   rw [hsum]
   simpa only [Fintype.card_fin, ←Polynomial.sylvester_map_map] using hfixed
 have hdet:(Polynomial.sylvester P Q m n).det≠0:=by
   simpa only [Polynomial.resultant] using hresultant
 have hfiber':∀ f∈(Finset.univ.image mu),
     (∑ i with mu i=f,relativeDegree i) ≤
       Fintype.card (Fin (m+n))-((AdjoinRoot.mk f).mapMatrix
         (Polynomial.sylvester P Q m n)).rank:=by
   simpa only [Fintype.card_fin] using hfiber
 have houter:=sum_grouped_weights_le_det_natDegree
   (K:=K) (I:=I) (M:=Polynomial.sylvester P Q m n)
   mu relativeDegree hmuMonic hmuIrreducible hfiber' hdet
 simpa only [Polynomial.resultant,htotal] using houter
theorem sum_finrank_le_planar_bound_without_separability
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i)) ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hspecial:∀ f∈
     (Finset.univ.image (fun i => minpoly K (y i))),
       P.map (AdjoinRoot.mk f)≠0:=by
   intro f hf
   obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
   letI:Fact (Irreducible (minpoly K (y i))):=
     ⟨minpoly.irreducible (IsIntegral.of_finite K (y i))⟩
   have hcoeff:Polynomial.eval₂RingHom
       (algebraMap K (AdjoinRoot (minpoly K (y i))))
         (AdjoinRoot.root (minpoly K (y i)))=
       AdjoinRoot.mk (minpoly K (y i)):=by
     apply Polynomial.ringHom_ext
     · intro c
       simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
         AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
     · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
         AdjoinRoot.mk_X]
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K (AdjoinRoot (minpoly K (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly K (y i)))
   rw [RCN360.bimap_specialization,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 exact (sum_finrank_le_resultant_of_relationIdeal_injective
   (K:=K) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
     hkernels hProot hQroot hspecial hresultant).trans
       (bivariate_resultant_natDegree_le
         (F:=K) P Q P.natDegree Q.natDegree)
end FinitePlaneFamily
end
end ProximityPrize.SubmissionLower.RCN025
end PackedLegacy_DF

/-! Packed from ProximityPrize.SubmissionLower.AW. -/
section PackedLegacy_AW
namespace ProximityPrize.SubmissionLower.RCN008
open scoped Classical BigOperators
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
 RCN024
 RCN025
noncomputable section
variable (K:Type) [Field K]
section FixedOrder
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
end FixedOrder
section OriginalOrder
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
end OriginalOrder
end
end ProximityPrize.SubmissionLower.RCN008
end PackedLegacy_AW

/-! Packed from ProximityPrize.SubmissionLower.X7. -/
section PackedLegacy_X7
namespace ProximityPrize.SubmissionLower.RCN021
open scoped Classical BigOperators
open RCN371 RCN011
 RCN009 RCN013
 RCN008
 RCN024
 RCN025 RCN022
noncomputable section
set_option maxHeartbeats 1000000
variable (K:Type) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance _root_.ProximityPrize.SubmissionLower.RCN021.instIsLocalizationCollectedCoefficientDenominatorsRationalPolynomials :IsLocalization (coefficientDenominators K)
   (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
section OneEvaluation
variable (L:Type) [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3) (e:Original K →ₐ[K] L)
def collectedEvaluation:Collected K →+*L:=
 e.toRingHom.comp (collect K order).symm.toRingHom
@[simp] theorem collectedEvaluation_collect (F:Original K):
   collectedEvaluation K L order e (collect K order F)=e F:=by
 simp [collectedEvaluation]
@[simp] theorem collectedEvaluation_C (H:Polynomial K):
   collectedEvaluation K L order e (MvPolynomial.C H)=
     Polynomial.aeval (e (MvPolynomial.X (order 0))) H:=by
 have hhom:e.toRingHom.comp (coefficientLift K order)=
     (Polynomial.aeval (e (MvPolynomial.X (order 0)))).toRingHom:=by
   apply Polynomial.ringHom_ext
   · intro a
     change e (coefficientLift K order (Polynomial.C a))=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) (Polynomial.C a)
     rw [coefficientLift_C,Polynomial.aeval_C]
     exact e.commutes a
   · change e (coefficientLift K order Polynomial.X)=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) Polynomial.X
     rw [coefficientLift_X,Polynomial.aeval_X]
 exact RingHom.congr_fun hhom H
theorem coefficientDenominators_disjoint_of_evaluation
   (G:Original K) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collect K order G}:Set (Collected K)):Set (Collected K)):=by
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨H,hH,rfl⟩:=Submonoid.mem_map.mp ha
 have hH0:H≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hH
 obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hI
 have hzero:Polynomial.aeval (e (MvPolynomial.X (order 0))) H=0:=by
   have heval:=congrArg (collectedEvaluation K L order e) hU
   simpa only [map_mul,collectedEvaluation_collect,collectedEvaluation_C,
     hroot,zero_mul] using heval
 exact hH0 (transcendental_iff.mp ht H hzero)
theorem rationalMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (rationalMap K order G):=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collect K order G}:Set (Collected K)))
   (collected_principal_isPrime K order G hG)
   (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)
 have hp':
     (Ideal.span ({rationalMap K order G}:Set (RationalPolynomials K))).IsPrime:=by
   simpa only [Ideal.map_span,Set.image_singleton, ←rationalMap_eq] using hp
 exact ((Ideal.span_singleton_prime
   (rationalMap_ne_zero K order G hG.ne_zero)).mp hp').irreducible
theorem rationalMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   rationalMap K order G∣rationalMap K order H ↔ G∣H:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collect K order H)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalMap_eq] using hdiv
   have hu:collect K order H∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K order G hG)
     (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)] at hu
   obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collect K order).symm U,?_⟩
   apply (collect K order).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
 · exact fun hdiv↦map_dvd (rationalMap K order) hdiv
theorem planeMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (planeMap K order G):=
 (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_evaluation K L order e G hG hroot ht)
theorem planeMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_evaluation K L order e G H hG hroot ht).mp hrat
 · exact fun hdiv↦map_dvd (planeMap K order) hdiv
def planeEvaluation
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   PlaneRing K →+*L:=
 (Polynomial.evalRingHom (e (MvPolynomial.X (order 1)))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
       (e (MvPolynomial.X (order 2)))))
@[simp] theorem planeEvaluation_C_C
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))) (a:RatFunc K):
   planeEvaluation K L order e ht (Polynomial.C (Polynomial.C a))=
     elementEmbedding K L (e (MvPolynomial.X (order 0))) ht a:=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht Polynomial.X=
     e (MvPolynomial.X (order 1)):=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_C_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
     e (MvPolynomial.X (order 2)):=by
 simp [planeEvaluation]
theorem elementEmbedding_polynomial (s:L) (hs:Transcendental K s)
   (f:Polynomial K):
   elementEmbedding K L s hs (algebraMap (Polynomial K) (RatFunc K) f)=
     Polynomial.aeval s f:=
 RatFunc.liftRingHom_algebraMap _ _ f
theorem planeEvaluation_comp_planeMap
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (planeEvaluation K L order e ht).comp (planeMap K order)=e.toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,planeEvaluation_C_C,
     elementEmbedding_polynomial,Polynomial.aeval_C]
   exact (e.commutes a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,planeEvaluation_C_C,
       elementEmbedding_variable]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,planeEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h↦hj (Fin.ext h)
     have hjone:j.val≠1:=fun h↦hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,planeEvaluation_C_X]
   rfl
def relationKernel
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=RingHom.ker (planeEvaluation K L order e ht)
theorem relationKernel_contract
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (relationKernel K L order e ht).comap (planeMap K order)=
     RingHom.ker e.toRingHom:=by
 rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_planeMap]
end OneEvaluation
section FixedFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (e:∀ i,Original K →ₐ[K] E i)
theorem finite_sum_finrank_bound
   (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
   (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree):
   letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
     (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i)) ≤
       (planeMap K order H).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
   (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hHroot i
   have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=by
     intro i
     have hGeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hGroots i
     have hHeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hHroots i
     exact finite_of_proper_plane_roots (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
       hGeval hHeval (hgen i)
   letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change relationKernel K (E i) order (e i) (ht i)=
       relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [relationKernel_contract] using hc
   exact ⟨hfinite,
     sum_finrank_le_planar_bound_without_separability
       (K:=RatFunc K) (I:=I) E
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (fun i↦e i (MvPolynomial.X (order 2)))
       (fun i↦e i (MvPolynomial.X (order 1))) hgen
       hrelation hGroots hHroots⟩
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end FixedFamily
end
end ProximityPrize.SubmissionLower.RCN021
end PackedLegacy_X7

/-! Packed from ProximityPrize.SubmissionLower.EE. -/
section PackedLegacy_EE
namespace ProximityPrize.SubmissionLower.RCN124
open scoped Classical BigOperators
open RCN371 RCN011
 RCN009 RCN013
 RCN008
 RCN024
 RCN025 RCN022
 RCN021 RCN012
noncomputable section
theorem sum_finrank_le_ordinary_resultant_without_separability
   {F:Type} [Field F] {I:Type*} [Fintype I]
   (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra F (E i)]
   [∀ i,FiniteDimensional F (E i)]
   (P Q:Polynomial (Polynomial F))
   (hP:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin F
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦
     RCN361.relationIdeal F (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval F (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval F (E i)
     (y i) (r i) Q=0):
   (∑ i,Module.finrank F (E i)) ≤
     (Polynomial.resultant P Q).natDegree:=by
 classical
 letI:DecidableEq F:=Classical.decEq F
 have hspecial:∀ f∈
     (Finset.univ.image (fun i↦minpoly F (y i))),
       P.map (AdjoinRoot.mk f)≠0:=by
   intro f hf
   obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
   letI:Fact (Irreducible (minpoly F (y i))):=
     ⟨minpoly.irreducible (IsIntegral.of_finite F (y i))⟩
   have hcoeff:Polynomial.eval₂RingHom
       (algebraMap F (AdjoinRoot (minpoly F (y i))))
         (AdjoinRoot.root (minpoly F (y i)))=
       AdjoinRoot.mk (minpoly F (y i)):=by
     apply Polynomial.ringHom_ext
     · intro c
       simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
         AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
     · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
         AdjoinRoot.mk_X]
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap F (AdjoinRoot (minpoly F (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly F (y i)))
   rw [RCN360.bimap_specialization,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 simpa only using
   (sum_finrank_le_resultant_of_relationIdeal_injective
     (K:=F) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
       hkernels hProot hQroot hspecial hresultant)
variable (K:Type) [Field K]
theorem finite_sum_finrank_bound_trapezoid
   (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
   (E:I → Type)
   [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   (e:∀ i,Original K →ₐ[K] E i)
   (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
         (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
   (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree)
   (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hHouter:(planeMap K order H).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hHsupport:∀ d∈(rationalMap K order H).support,
     d 0+d 1 ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalH-m*n ≤ cap):
   letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
     (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
       (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i)) ≤ cap:=by
 classical
 letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
   (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
     (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hbase:=finite_sum_finrank_bound K order E e ht hgen hkernels
     G H hG hGroot hHroot hproper hpositive
   have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=hbase.1
   letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order G)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order H)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hHroot i
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change relationKernel K (E i) order (e i) (ht i)=
       relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [relationKernel_contract] using hc
   refine ⟨hfinite,?_⟩
   exact (sum_finrank_le_ordinary_resultant_without_separability E
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     (fun i↦e i (MvPolynomial.X (order 2)))
     (fun i↦e i (MvPolynomial.X (order 1))) hgen hrelation
     hGroots hHroots).trans
       (planeMap_trapezoid_resultant_natDegree_le K order G H
         n mCap totalG totalH cap hHne hGouter hHouter
         hGsupport hHsupport hbudget)
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end
end ProximityPrize.SubmissionLower.RCN124
end PackedLegacy_EE

/-! Packed from ProximityPrize.SubmissionLower.Y7. -/
section PackedLegacy_Y7
namespace ProximityPrize.SubmissionLower.RCN093
open scoped Classical BigOperators
open RCN002 RCN005
 RCN022 RCN011
 RCN371
open RCN125 RCN124
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def affineU (lam:K):CoordinateField K P:=
 coordinate K P 0+lam • coordinate K P 2
def affineV (μ ν:K):CoordinateField K P:=
 coordinate K P 1+μ • coordinate K P 0+ν • coordinate K P 2
def flagEvaluation (lam μ ν:K):
   MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P:=
 MvPolynomial.aeval ![affineU K P lam,affineV K P μ ν,
   coordinate K P 2]
@[simp] theorem flagEvaluation_X_zero (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 0)=affineU K P lam:=by
 simp [flagEvaluation]
@[simp] theorem flagEvaluation_X_one (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 1)=affineV K P μ ν:=by
 simp [flagEvaluation]
@[simp] theorem flagEvaluation_X_two (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 2)=coordinate K P 2:=by
 simp [flagEvaluation]
theorem flagEvaluation_flag (lam μ ν:K)
   (F:MvPolynomial (Fin 3) K):
   flagEvaluation K P lam μ ν (flagAlgHom lam μ ν F)=
     coordinateEvaluation K P F:=by
 change MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K P))
     ![coordinate K P 0+lam • coordinate K P 2,
       coordinate K P 1+μ • coordinate K P 0+ν • coordinate K P 2,
       coordinate K P 2] (flagAlgHom lam μ ν F)=_
 rw [show lam • coordinate K P 2=
     algebraMap K (CoordinateField K P) lam*coordinate K P 2 by
       simp [Algebra.smul_def],
   show μ • coordinate K P 0=
     algebraMap K (CoordinateField K P) μ*coordinate K P 0 by
       simp [Algebra.smul_def],
   show ν • coordinate K P 2=
     algebraMap K (CoordinateField K P) ν*coordinate K P 2 by
       simp [Algebra.smul_def],
   eval₂Hom_flag_at_affine]
 rw [coordinateEvaluation_eq_aeval]
 have hx:(![coordinate K P 0,coordinate K P 1,coordinate K P 2]:
     Fin 3 → CoordinateField K P)=coordinate K P:=by
   funext i
   fin_cases i <;> rfl
 rw [hx]
 exact (MvPolynomial.aeval_eq_eval₂Hom (coordinate K P) F).symm
theorem flagEvaluation_kernel_contract (lam μ ν:K):
   (RingHom.ker (flagEvaluation K P lam μ ν).toRingHom).comap
       (flagAlgHom lam μ ν).toRingHom=P:=by
 rw [RingHom.comap_ker]
 have hcomp:(flagEvaluation K P lam μ ν).comp (flagAlgHom lam μ ν)=
     coordinateEvaluation K P:=by
   apply AlgHom.ext
   intro F
   exact flagEvaluation_flag K P lam μ ν F
 have hring:=congrArg
   (fun f:MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P↦
     f.toRingHom) hcomp
 rw [show (flagEvaluation K P lam μ ν).toRingHom.comp
     (flagAlgHom lam μ ν).toRingHom=
     (coordinateEvaluation K P).toRingHom from hring,
   coordinateEvaluation_ker]
public theorem top_of_affine_flag_mem
   [Algebra (RatFunc K) (CoordinateField K P)]
   [IsScalarTower K (RatFunc K) (CoordinateField K P)]
   (lam μ ν:K)
   (L:IntermediateField (RatFunc K) (CoordinateField K P))
   (hU:affineU K P lam∈L) (hV:affineV K P μ ν∈L)
   (hZ:coordinate K P 2∈L):L=⊤:=by
 have hlam:algebraMap K (CoordinateField K P) lam∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) lam)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (CoordinateField K P)] using h
 have hμ:algebraMap K (CoordinateField K P) μ∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) μ)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (CoordinateField K P)] using h
 have hν:algebraMap K (CoordinateField K P) ν∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) ν)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (CoordinateField K P)] using h
 have hY:coordinate K P 0∈L:=by
   have h:=L.sub_mem hU (L.mul_mem hlam hZ)
   simpa only [affineU,Algebra.smul_def,add_sub_cancel_right] using h
 have hS:coordinate K P 1∈L:=by
   have h:=L.sub_mem hV
     (L.add_mem (L.mul_mem hμ hY) (L.mul_mem hν hZ))
   have heq:affineV K P μ ν-
       (algebraMap K (CoordinateField K P) μ*coordinate K P 0+
         algebraMap K (CoordinateField K P) ν*coordinate K P 2)=
       coordinate K P 1:=by
     simp only [affineV,Algebra.smul_def]
     ring
   rwa [heq] at h
 have hcoords:Set.range (coordinate K P) ⊆ L.restrictScalars K:=by
   rintro x ⟨i,rfl⟩
   fin_cases i
   · exact hY
   · exact hS
   · exact hZ
 have htop:L.restrictScalars K=⊤:=by
   apply top_unique
   rw [←adjoin_coordinates_eq_top K P]
   exact IntermediateField.adjoin_le_iff.mpr hcoords
 exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
theorem flag_generators_u (lam μ ν:K)
   (hU:Transcendental K (affineU K P lam)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     (elementEmbedding K (CoordinateField K P) (affineU K P lam)
       hU).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P 2,affineV K P μ ν}:
       Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (affineU K P lam)
     hU).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((elementEmbedding K (CoordinateField K P) (affineU K P lam)
       hU).commutes c).symm
 let L:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {coordinate K P 2,affineV K P μ ν}
 have hZ:coordinate K P 2∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hV:affineV K P μ ν∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hUmem:affineU K P lam∈L:=by
   change elementEmbedding K (CoordinateField K P) (affineU K P lam) hU
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [elementEmbedding_variable] at hbase
 exact top_of_affine_flag_mem K P lam μ ν L hUmem hV hZ
theorem flag_generators_v (lam μ ν:K)
   (hV:Transcendental K (affineV K P μ ν)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     (elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
       hV).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P 2,affineU K P lam}:
       Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
     hV).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
       hV).commutes c).symm
 let L:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {coordinate K P 2,affineU K P lam}
 have hZ:coordinate K P 2∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hU:affineU K P lam∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hVmem:affineV K P μ ν∈L:=by
   change elementEmbedding K (CoordinateField K P) (affineV K P μ ν) hV
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [elementEmbedding_variable] at hbase
 exact top_of_affine_flag_mem K P lam μ ν L hU hVmem hZ
theorem flag_generators_z (lam μ ν:K)
   (hZ:Transcendental K (coordinate K P 2)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     (elementEmbedding K (CoordinateField K P) (coordinate K P 2)
       hZ).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({affineU K P lam,affineV K P μ ν}:
       Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (coordinate K P 2)
     hZ).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((elementEmbedding K (CoordinateField K P) (coordinate K P 2)
       hZ).commutes c).symm
 let L:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {affineU K P lam,affineV K P μ ν}
 have hU:affineU K P lam∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hV:affineV K P μ ν∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hZmem:coordinate K P 2∈L:=by
   change elementEmbedding K (CoordinateField K P) (coordinate K P 2) hZ
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [elementEmbedding_variable] at hbase
 exact top_of_affine_flag_mem K P lam μ ν L hU hV hZmem
section Family
variable {I:Type} [Fintype I]
 (Q:I → Ideal (MvPolynomial (Fin 3) K)) [∀ i,(Q i).IsPrime]
theorem flagEvaluation_kernel_family_injective
   (hinj:Function.Injective Q) (lam μ ν:K):
   Function.Injective (fun i↦
     RingHom.ker (flagEvaluation K (Q i) lam μ ν).toRingHom):=by
 intro i j hij
 apply hinj
 have hc:=congrArg (Ideal.comap (flagAlgHom lam μ ν).toRingHom) hij
 simpa only [flagEvaluation_kernel_contract] using hc
theorem finite_sum_flag_finrank_trapezoid
   (hinj:Function.Injective Q) (lam μ ν:K)
   (order:Fin 3 ≃ Fin 3)
   (ht:∀ i,Transcendental K
     (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (CoordinateField K (Q i)):=
       (elementEmbedding K (CoordinateField K (Q i))
         (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
         (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 2)),
         flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 1))}:
         Set (CoordinateField K (Q i)))=⊤)
   (G H:MvPolynomial (Fin 3) K) (hG:Irreducible G)
   (hGmem:∀ i,G∈Q i) (hHmem:∀ i,H∈Q i)
   (hproper:¬ G∣H)
   (hpositive:0 <
     (planeMap K order (flagAlgHom lam μ ν G)).natDegree)
   (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
   (hGouter:(planeMap K order
     (flagAlgHom lam μ ν G)).natDegree ≤ n)
   (hHouter:(planeMap K order
     (flagAlgHom lam μ ν H)).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order
     (flagAlgHom lam μ ν G)).support,d 0+d 1 ≤ totalG)
   (hHsupport:∀ d∈(rationalMap K order
     (flagAlgHom lam μ ν H)).support,d 0+d 1 ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalH-m*n ≤ cap):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (Q i)):=
     fun i↦(elementEmbedding K (CoordinateField K (Q i))
       (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
       (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (Q i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤ cap:=by
 let e:∀ i,MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K (Q i):=
   fun i↦flagEvaluation K (Q i) lam μ ν
 have hGroot:∀ i,e i (flagAlgHom lam μ ν G)=0:=by
   intro i
   rw [show e i (flagAlgHom lam μ ν G)=coordinateEvaluation K (Q i) G
     from flagEvaluation_flag K (Q i) lam μ ν G]
   change G∈RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
   rw [coordinateEvaluation_ker]
   exact hGmem i
 have hHroot:∀ i,e i (flagAlgHom lam μ ν H)=0:=by
   intro i
   rw [show e i (flagAlgHom lam μ ν H)=coordinateEvaluation K (Q i) H
     from flagEvaluation_flag K (Q i) lam μ ν H]
   change H∈RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
   rw [coordinateEvaluation_ker]
   exact hHmem i
 exact finite_sum_finrank_bound_trapezoid K order
   (fun i↦CoordinateField K (Q i)) e ht hgen
   (flagEvaluation_kernel_family_injective K Q hinj lam μ ν)
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H)
   ((flag_irreducible_iff lam μ ν G).mpr hG)
   hGroot hHroot (by simpa only [flag_dvd_iff] using hproper) hpositive
   n mCap totalG totalH cap (flag_ne_zero lam μ ν hHne)
   hGouter hHouter hGsupport hHsupport hbudget
end Family
end
end ProximityPrize.SubmissionLower.RCN093
end PackedLegacy_Y7

/-! Packed from ProximityPrize.SubmissionLower.BB. -/
section PackedLegacy_BB
namespace ProximityPrize.SubmissionLower.RCN118
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN272
 RCN273
open RCN323 RCN075 RCN095 RCN114 RCN187 RCN295
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
structure PrincipalCycleBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj)
   (wholeCap:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 cycle_le:∀ C:RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   (∑ v∈RCN026.placesFor Ω
       (CoordinateField Ω C.1) b hb,
     RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCap
structure FlagProjectionCycleBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   (p:FlagDegree) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (B:GenericExactPolePolynomial G T H (flagSupport p) separator
     hseparator hproj)
   (zCap yzCap allCap:ℕ) where
 zCost:RegularComponent Ω G T H → ℕ
 yzCost:RegularComponent Ω G T H → ℕ
 allCost:RegularComponent Ω G T H → ℕ
 cycle_le:∀ C:RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   (∑ v∈RCN026.placesFor Ω
       (CoordinateField Ω C.1) b hb,
     RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
       ((p.zOnly*zCost C+p.yz*yzCost C+
         p.all*allCost C:ℕ):ℤ)
 sum_zCost_le:(∑ C:RegularComponent Ω G T H,zCost C) ≤ zCap
 sum_yzCost_le:(∑ C:RegularComponent Ω G T H,yzCost C) ≤ yzCap
 sum_allCost_le:(∑ C:RegularComponent Ω G T H,allCost C) ≤ allCap
def FlagProjectionCycleBudget.ofNestedProjectionBudgets
   {G T H:MvPolynomial (Fin 3) Ω}
   {p:FlagDegree} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericExactPolePolynomial G T H (flagSupport p) separator
     hseparator hproj)
   (BZ:GenericExactPolePolynomial G T H (flagSupport unitZFlag) separator
     hseparator hproj)
   (BYZ:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) separator
     hseparator hproj)
   (BAll:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) separator
     hseparator hproj)
   {zCap yzCap allCap:ℕ}
   (zBudget:PrincipalCycleBudget (flagSupport unitZFlag) separator
     hseparator hproj BZ zCap)
   (yzBudget:PrincipalCycleBudget (flagSupport unitYZFlag) separator
     hseparator hproj BYZ yzCap)
   (allBudget:PrincipalCycleBudget (flagSupport unitAllFlag) separator
     hseparator hproj BAll allCap):
   FlagProjectionCycleBudget p separator hseparator hproj B
     zCap yzCap allCap where
 zCost:=zBudget.cost
 yzCost:=yzBudget.cost
 allCost:=allBudget.cost
 sum_zCost_le:=zBudget.sum_cost_le
 sum_yzCost_le:=yzBudget.sum_cost_le
 sum_allCost_le:=allBudget.sum_cost_le
 cycle_le:=by
   intro C
   dsimp only
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   let bZ:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) BZ.polynomial
   let hbZ:bZ≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 BZ.polynomial (BZ.proper C)
   let bYZ:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) BYZ.polynomial
   let hbYZ:bYZ≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 BYZ.polynomial (BYZ.proper C)
   let bAll:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) BAll.polynomial
   let hbAll:bAll≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 BAll.polynomial (BAll.proper C)
   let W:=RCN026.placesFor Ω
     (CoordinateField Ω C.1) b hb
   have hZsupport:
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
         (flagSupport unitZFlag)) ≤
       ∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bZ hbZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bZ:=by
     exact support_sum_le_principal_poleMass_of_exact
       (coordinate Ω C.1) (flagSupport unitZFlag) bZ hbZ
       (BZ.exact_pole C) W
   have hYZsupport:
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
         (flagSupport unitYZFlag)) ≤
       ∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bYZ hbYZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bYZ:=by
     exact support_sum_le_principal_poleMass_of_exact
       (coordinate Ω C.1) (flagSupport unitYZFlag) bYZ hbYZ
       (BYZ.exact_pole C) W
   have hAllsupport:
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
         (flagSupport unitAllFlag)) ≤
       ∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bAll hbAll,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bAll:=by
     exact support_sum_le_principal_poleMass_of_exact
       (coordinate Ω C.1) (flagSupport unitAllFlag) bAll hbAll
       (BAll.exact_pole C) W
   have hZcycle:
       (∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bZ hbZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bZ) ≤
       (zBudget.cost C:ℤ):=by
     simpa only using zBudget.cycle_le C
   have hYZcycle:
       (∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bYZ hbYZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bYZ) ≤
       (yzBudget.cost C:ℤ):=by
     simpa only using yzBudget.cycle_le C
   have hAllcycle:
       (∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bAll hbAll,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bAll) ≤
       (allBudget.cost C:ℤ):=by
     simpa only using allBudget.cycle_le C
   have hlocal:∀ v∈W,
       poleOrder v.val b ≤
         (p.zOnly:ℤ)*exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitZFlag)+
         (p.yz:ℤ)*exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitYZFlag)+
         (p.all:ℤ)*exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitAllFlag):=by
     intro v _
     rw [B.exact_pole C v]
     exact exponentSetPoleWeight_flagSupport_le_three v.val
       (coordinate Ω C.1) p
   calc
     (∑ v∈W,RCN346.poleOrder Ω
         (CoordinateField Ω C.1) v b) ≤
         ∑ v∈W,
           ((p.zOnly:ℤ)*exponentSetPoleWeight v.val
               (coordinate Ω C.1) (flagSupport unitZFlag)+
            (p.yz:ℤ)*exponentSetPoleWeight v.val
               (coordinate Ω C.1) (flagSupport unitYZFlag)+
            (p.all:ℤ)*exponentSetPoleWeight v.val
               (coordinate Ω C.1) (flagSupport unitAllFlag)):=by
       apply Finset.sum_le_sum
       intro v hv
       exact hlocal v hv
     _=(p.zOnly:ℤ)*
           (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitZFlag))+
         (p.yz:ℤ)*
           (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitYZFlag))+
         (p.all:ℤ)*
           (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitAllFlag)):=by
       simp only [Finset.sum_add_distrib,Finset.mul_sum]
     _ ≤ (p.zOnly:ℤ)*(zBudget.cost C:ℤ)+
         (p.yz:ℤ)*(yzBudget.cost C:ℤ)+
         (p.all:ℤ)*(allBudget.cost C:ℤ):=by
       exact add_le_add
         (add_le_add
           (mul_le_mul_of_nonneg_left (hZsupport.trans hZcycle) (by positivity))
           (mul_le_mul_of_nonneg_left (hYZsupport.trans hYZcycle) (by positivity)))
         (mul_le_mul_of_nonneg_left (hAllsupport.trans hAllcycle) (by positivity))
     _=((p.zOnly*zBudget.cost C+p.yz*yzBudget.cost C+
         p.all*allBudget.cost C:ℕ):ℤ):=by
       push_cast
       ring
end
end ProximityPrize.SubmissionLower.RCN118
end PackedLegacy_BB

/-! Packed from ProximityPrize.SubmissionLower.Y8. -/
section PackedLegacy_Y8
namespace ProximityPrize.SubmissionLower.RCN097
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain RCN022 RCN351 RCN344 RCN295 RCN075 RCN002 RCN005 RCN007 RCN264 RCN093
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
/-- Finite avoidance inside an infinite subset `S` (used to keep the flag coefficients in the
image of `K[X]`, where the H-free derivation is defined). -/
theorem exists_nonzero_avoiding_finite_subsingleton_in
   {K ι:Type*} [Field K] [Finite ι] (S:Set K) (hS:S.Infinite)
   (Bad:ι → K → Prop)
   (hsingle:∀ i {a b},Bad i a → Bad i b → a=b):
   ∃ a:K,a∈S∧a≠0∧∀ i,¬ Bad i a:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq ι:=Classical.decEq ι
 letI:Fintype ι:=Fintype.ofFinite ι
 let representative:ι → K:=fun i↦
   if h:∃ a,Bad i a then Classical.choose h else 0
 let forbidden:Finset K:=Finset.univ.image representative
 obtain ⟨a,haS,ha⟩:=(hS.diff (insert 0 forbidden).finite_toSet).nonempty
 refine ⟨a,haS,?_,?_⟩
 · intro hzero
   exact ha (hzero ▸ Finset.mem_insert_self 0 forbidden)
 · intro i hbad
   have hex:∃ b,Bad i b:=⟨a,hbad⟩
   have hrepbad:Bad i (representative i):=by
     simp only [representative,dif_pos hex]
     exact Classical.choose_spec hex
   have hab:a=representative i:=hsingle i hbad hrepbad
   have hmem:representative i∈forbidden:=by
     exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
   exact ha (Finset.mem_insert_of_mem (hab ▸ hmem))
theorem valuation_shear_bad_coefficient_subsingleton
   {K L:Type*} [Field K] [Field L] [Algebra K L]
   (v:RCN345.NormalizedValuation K L)
   (r z:L):
   ∀ {a b:K},
     v.val (r+a • z) < max (v.val r) (v.val z) →
     v.val (r+b • z) < max (v.val r) (v.val z) → a=b:=by
 intro a b ha hb
 by_contra hab
 have hab0:a-b≠0:=sub_ne_zero.mpr hab
 letI:v.val.IsTrivialOn K:=v.property.2
 have hdiff:v.val ((r+a • z)-(r+b • z)) <
     max (v.val r) (v.val z):=v.val.map_sub_lt ha hb
 have hvaldiff:v.val ((r+a • z)-(r+b • z))=v.val z:=by
   rw [show (r+a • z)-(r+b • z)=(a-b) • z by module,
     Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one (a-b) hab0,one_mul]
 rw [hvaldiff] at hdiff
 have hzr:v.val z < v.val r:=by
   simpa only [lt_max_iff,lt_self_iff_false,or_false] using hdiff
 have hmax:max (v.val r) (v.val z)=v.val r:=max_eq_left hzr.le
 have ha0:a≠0:=by
   intro ha0
   rw [ha0,zero_smul,add_zero,hmax] at ha
   exact (lt_irrefl _ ha).elim
 have haz:v.val (a • z)=v.val z:=by
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 have hsum:v.val (r+a • z)=v.val r:=by
   apply v.val.map_add_eq_of_lt_left
   rwa [haz]
 rw [hsum,hmax] at ha
 exact (lt_irrefl _ ha).elim
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
 {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
variable (W:∀ i,
 Finset (RCN345.NormalizedValuation K (E i)))
end FiniteFamily
section RegularComponents
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
 {G T H:MvPolynomial (Fin 3) Ω}
structure NestedFlagProjectionData
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 lam:Ω
 lam_ne:lam≠0
 hU:∀ C:RegularComponent Ω G T H,
   Transcendental Ω (affineU Ω C.1 lam)
 finiteU:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1)
 separableU:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1)
 exactU:∀ C:RegularComponent Ω G T H,
   ∀ v∈componentRelevantPlaces hseparator hproj C,
     v.val (affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 0))
         (v.val (coordinate Ω C.1 2))
 mu:Ω
 mu_ne:mu≠0
 hV:∀ C:RegularComponent Ω G T H,
   Transcendental Ω
     (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
 finiteV:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1)
 separableV:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1)
 exactV:∀ C:RegularComponent Ω G T H,
   ∀ v∈componentRelevantPlaces hseparator hproj C,
     v.val (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 1))
         (v.val (affineU Ω C.1 lam))
theorem nestedV_eq_affineV
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Ω G T H):
   coordinate Ω C.1 1+D.mu • affineU Ω C.1 D.lam=
     affineV Ω C.1 D.mu (D.mu*D.lam):=by
 simp only [affineU,affineV]
 simp only [smul_add,smul_smul,add_assoc]
end RegularComponents
end
end ProximityPrize.SubmissionLower.RCN097
end PackedLegacy_Y8

/-! Packed from ProximityPrize.SubmissionLower.DN. -/
section PackedLegacy_DN
namespace ProximityPrize.SubmissionLower.RCN035
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential RCN344 RCN369 RCN370
 RCN351
open RCN022 RCN097
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
theorem element_transcendental_finite_separable_of_differential_ne_zero
   (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
   (base:SeparableCoordinate K L) (t:L)
   (hdt:D K L t≠0):
   ∃ ht:Transcendental K t,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L t ht).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L t ht).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L):=by
 have ht:Transcendental K t:=by
   show ¬ IsAlgebraic K t
   intro halg
   obtain ⟨c,hc⟩:=eq_algebraMap_of_isAlgebraic K L t halg
   apply hdt
   rw [←hc]
   exact (D K L).map_algebraMap c
 let embeddingT:=elementEmbedding K L t ht
 have hfiniteT:
     letI:Algebra (RatFunc K) L:=embeddingT.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L:=
   finiteDimensional_elementEmbedding K L base.embedding base.finite t ht
 refine ⟨ht,hfiniteT,?_⟩
 have hcriterionBase:=
   isSeparable_iff_span_parameterDifferential K L base.embedding base.finite
 have hcriterionT:=
   isSeparable_iff_span_parameterDifferential K L embeddingT hfiniteT
 have hspanBase:Submodule.span L
     ({D K L (SeparableCoordinate.value K L base)}:Set Ω[L⁄K])=⊤:=by
   have h:=hcriterionBase.mp base.separable
   exact h
 apply hcriterionT.mpr
 have hparamT:parameterDifferential K L embeddingT=D K L t:=by
   unfold parameterDifferential embeddingT
   rw [elementEmbedding_variable]
 rw [hparamT]
 apply top_unique
 rw [←hspanBase]
 apply Submodule.span_le.mpr
 intro x hx
 rw [Set.mem_singleton_iff.mp hx]
 have htmem:D K L t∈Submodule.span L
     ({D K L (SeparableCoordinate.value K L base)}:Set Ω[L⁄K]):=by
   rw [hspanBase]
   trivial
 obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp htmem
 have hb0:b≠0:=by
   intro hzero
   apply hdt
   rw [←hb,hzero,zero_smul]
 apply Submodule.mem_span_singleton.mpr
 refine ⟨b⁻¹,?_⟩
 rw [←hb,smul_smul,inv_mul_cancel₀ hb0,one_smul]
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
 {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
variable (W:∀ i,
 Finset (RCN345.NormalizedValuation K (E i)))
theorem exists_common_exact_finite_separable_affine_adaptive_in
   (S:Set K) (hS:S.Infinite)
   (base:∀ i,SeparableCoordinate K (E i))
   (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃ a:K,a∈S∧a≠0∧∀ i,
     ∃ ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 let J:=I ⊕ Sigma fun i:I => {v//v∈W i}
 let Bad:J → K → Prop
   | Sum.inl i,a => D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr iv,a => iv.2.1.val (r iv.1+a • z iv.1) <
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
   intro j a b ha hb
   rcases j with i | ⟨i,v⟩
   · by_cases hdz:D K (E i) (z i)=0
     · have hdr:D K (E i) (r i)≠0:=
         (hactive i).resolve_right (fun hn => hn hdz)
       change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
       exfalso
       apply hdr
       simpa only [hdz,smul_zero,add_zero] using ha
     · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
         hdz ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,haS,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton_in S hS Bad hsingle
 refine ⟨a,haS,ha0,fun i => ?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inl i)
 have hD:D K (E i) (r i+a • z i)≠0:=by
   rw [map_add,(D K (E i)).map_smul]
   exact hdiff
 obtain ⟨ht,hfinite,hsep⟩:=
   element_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (base i) (r i+a • z i) hD
 refine ⟨ht,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr ⟨i,⟨v,hv⟩⟩)
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
theorem exists_common_exact_finite_separable_affine_adaptive
   (base:∀ i,SeparableCoordinate K (E i))
   (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃ a:K,a≠0∧∀ i,
     ∃ ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 obtain ⟨a,-,h⟩:=exists_common_exact_finite_separable_affine_adaptive_in E r z W
   Set.univ Set.infinite_univ base hactive
 exact ⟨a,h⟩
theorem exists_common_exact_finite_separable_affine_adaptive_avoiding_one_in
   (S:Set K) (hS:S.Infinite)
   (Extra:K → Prop)
   (hextra:∀ {a b},Extra a → Extra b → a=b)
   (base:∀ i,SeparableCoordinate K (E i))
   (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃ a:K,a∈S∧a≠0∧¬ Extra a∧∀ i,
     ∃ ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 let J:=Unit ⊕ (I ⊕ Sigma fun i:I => {v//v∈W i})
 let Bad:J → K → Prop
   | Sum.inl _,a => Extra a
   | Sum.inr (Sum.inl i),a =>
       D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr (Sum.inr iv),a => iv.2.1.val (r iv.1+a • z iv.1) <
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
   intro j a b ha hb
   rcases j with _ | i | ⟨i,v⟩
   · exact hextra ha hb
   · by_cases hdz:D K (E i) (z i)=0
     · have hdr:D K (E i) (r i)≠0:=
         (hactive i).resolve_right (fun hn => hn hdz)
       change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
       exfalso
       apply hdr
       simpa only [hdz,smul_zero,add_zero] using ha
     · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
         hdz ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,haS,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton_in S hS Bad hsingle
 refine ⟨a,haS,ha0,havoid (Sum.inl ()),fun i => ?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inr (Sum.inl i))
 have hD:D K (E i) (r i+a • z i)≠0:=by
   rw [map_add,(D K (E i)).map_smul]
   exact hdiff
 obtain ⟨ht,hfinite,hsep⟩:=
   element_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (base i) (r i+a • z i) hD
 refine ⟨ht,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr (Sum.inr ⟨i,⟨v,hv⟩⟩))
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
theorem exists_common_exact_finite_separable_affine_adaptive_avoiding_one
   (Extra:K → Prop)
   (hextra:∀ {a b},Extra a → Extra b → a=b)
   (base:∀ i,SeparableCoordinate K (E i))
   (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃ a:K,a≠0∧¬ Extra a∧∀ i,
     ∃ ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 obtain ⟨a,-,h⟩:=exists_common_exact_finite_separable_affine_adaptive_avoiding_one_in E r z W
   Set.univ Set.infinite_univ Extra hextra base hactive
 exact ⟨a,h⟩
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN035
end PackedLegacy_DN

/-! Packed from ProximityPrize.SubmissionLower.Y1. -/
section PackedLegacy_Y1
namespace ProximityPrize.SubmissionLower.RCN042
open scoped Classical TensorProduct
open Polynomial KaehlerDifferential RCN344 RCN022 RCN369 RCN370
 RCN351
open RCN341
noncomputable section
variable {K:Type} {L:Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
def coordinateOfGate (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L)):Coordinate K L:=
 if hx:Transcendental K x then
   Sum.inr {
     embedding:=elementEmbedding K L x hx
     finite:=(hgate hx).1
     separable:=(hgate hx).2}
 else
   Sum.inl ((eq_algebraMap_of_isAlgebraic K L x (not_not.mp hx)).choose)
@[simp] theorem coordinateOfGate_value (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L)):
   coordinateValue K L (coordinateOfGate x hgate)=x:=by
 unfold coordinateOfGate
 split_ifs with hx
 · exact elementEmbedding_variable K L x hx
 · exact (eq_algebraMap_of_isAlgebraic K L x (not_not.mp hx)).choose_spec
@[simp] theorem coordinateOfGate_degree_of_transcendental (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L))
   (hx:Transcendental K x):
   coordinateDegree K L (coordinateOfGate x hgate)=
     (letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L x hx).toRingHom.toAlgebra
      Module.finrank (RatFunc K) L):=by
 unfold coordinateOfGate coordinateDegree SeparableCoordinate.degree
 rw [dif_pos hx]
 rfl
@[simp] theorem coordinateOfGate_degree_of_isAlgebraic (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L))
   (hx:IsAlgebraic K x):
   coordinateDegree K L (coordinateOfGate x hgate)=0:=by
 unfold coordinateOfGate coordinateDegree
 rw [dif_neg (fun htr => htr hx)]
 rfl
theorem one_le_coordinateDegree_of_transcendental_value
   (c:Coordinate K L)
   (hc:Transcendental K (coordinateValue K L c)):
   1 ≤ coordinateDegree K L c:=by
 rcases c with a | c
 · exact (hc (isAlgebraic_algebraMap a)).elim
 · letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
   letI:FiniteDimensional (RatFunc K) L:=c.finite
   exact Module.finrank_pos
section FiniteFamily
variable {I:Type*} [Fintype I]
 (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
theorem sum_coordinateOfGate_degree_eq
   (x:∀ i,E i)
   (hgate:∀ i,∀ hx:Transcendental K (x i),
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) (E i))∧
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) (E i))):
   (∑ i,coordinateDegree K (E i) (coordinateOfGate (x i) (hgate i)))=
     ∑ i:{i:I//Transcendental K (x i)},
       (letI:Algebra (RatFunc K) (E i.1):=
         (elementEmbedding K (E i.1) (x i.1) i.2).toRingHom.toAlgebra
        Module.finrank (RatFunc K) (E i.1)):=by
 classical
 let s:Set I:={i | Transcendental K (x i)}
 let degree:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (E i.1):=
     (elementEmbedding K (E i.1) (x i.1) i.2).toRingHom.toAlgebra
   Module.finrank (RatFunc K) (E i.1)
 apply Finset.sum_congr_set s
   (fun i => coordinateDegree K (E i) (coordinateOfGate (x i) (hgate i))) degree
 · intro i hi
   exact coordinateOfGate_degree_of_transcendental (x i) (hgate i) hi
 · intro i hi
   exact coordinateOfGate_degree_of_isAlgebraic (x i) (hgate i) (not_not.mp hi)
end FiniteFamily
def literalToSeparableCoordinate
   {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P):
   SeparableCoordinate K (RCN002.CoordinateField K P) where
 embedding:=RCN005.rationalBaseEmbedding
   K P D.index D.transcendental
 finite:=D.finite
 separable:=D.separable
theorem differential_ne_zero_of_gate (x:L)
   (hx:Transcendental K x)
   (hgate:
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L)):
   D K L x≠0:=by
 have h:=parameterDifferential_ne_zero_of_isSeparable K L
   (elementEmbedding K L x hx) hgate.1 hgate.2
 unfold parameterDifferential at h
 rwa [elementEmbedding_variable] at h
end
end ProximityPrize.SubmissionLower.RCN042
end PackedLegacy_Y1

/-! Packed from ProximityPrize.SubmissionLower.A3. -/
section PackedLegacy_A3
namespace ProximityPrize.SubmissionLower.RCN046
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN264 RCN095 RCN341 RCN340 RCN237 RCN295 RCN042
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveUnitProjectionFamily
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 zProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 yzProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 allProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 zValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (zProjection C)=
     coordinate Omega C.1 2
 allTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega
     (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 zPole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitZFlag)=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (coordinateValue Omega (CoordinateField Omega C.1) (zProjection C))
 yzPole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitYZFlag)=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (coordinateValue Omega (CoordinateField Omega C.1) (yzProjection C))
 allPole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitAllFlag)=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 sum_zDegree_le:
   (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1) (zProjection C)) ≤
     flagMixed p q unitZFlag
 sum_yzDegree_le:
   (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1) (yzProjection C)) ≤
     flagMixed p q unitYZFlag
 sum_allDegree_le:
   (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1) (allProjection C)) ≤
     flagMixed p q unitAllFlag
def AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q):
   AdaptiveUnitPoleBudget base p q where
 zCost:=fun C => coordinateDegree Omega (CoordinateField Omega C.1)
   (P.zProjection C)
 yzCost:=fun C => coordinateDegree Omega (CoordinateField Omega C.1)
   (P.yzProjection C)
 allCost:=fun C => coordinateDegree Omega (CoordinateField Omega C.1)
   (P.allProjection C)
 sum_zCost_le:=P.sum_zDegree_le
 sum_yzCost_le:=P.sum_yzDegree_le
 sum_allCost_le:=P.sum_allDegree_le
 zPole:=by
   intro C
   unfold LiteralSupportPoleBound
   dsimp only
   intro W
   calc
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitZFlag))=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (coordinateValue Omega (CoordinateField Omega C.1)
             (P.zProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.zPole_eq C v
     _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
         (P.zProjection C):ℤ):=
       finite_sum_coordinate_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.zProjection C) W
 yzPole:=by
   intro C
   unfold LiteralSupportPoleBound
   dsimp only
   intro W
   calc
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitYZFlag))=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (coordinateValue Omega (CoordinateField Omega C.1)
             (P.yzProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.yzPole_eq C v
     _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
         (P.yzProjection C):ℤ):=
       finite_sum_coordinate_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.yzProjection C) W
 allPole:=by
   intro C
   unfold LiteralSupportPoleBound
   dsimp only
   intro W
   calc
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitAllFlag))=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (coordinateValue Omega (CoordinateField Omega C.1)
             (P.allProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.allPole_eq C v
     _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
         (P.allProjection C):ℤ):=
       finite_sum_coordinate_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.allProjection C) W
def AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q):
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q:=
 P.toAdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily
theorem AdaptiveUnitProjectionFamily.one_le_zDegree_of_transcendental
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q)
   (C:RegularComponent Omega G T H)
   (hZ:Transcendental Omega (coordinate Omega C.1 2)):
   1 ≤ coordinateDegree Omega (CoordinateField Omega C.1)
     (P.zProjection C):=by
 apply one_le_coordinateDegree_of_transcendental_value
 rwa [P.zValue C]
theorem AdaptiveUnitProjectionFamily.one_le_toPrimeFlagBudgetFamily_zCost
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q)
   (C:RegularComponent Omega G T H)
   (hZ:Transcendental Omega (coordinate Omega C.1 2)):
   1 ≤ P.toPrimeFlagBudgetFamily.zCost C:=
 P.one_le_zDegree_of_transcendental C hZ
end
end ProximityPrize.SubmissionLower.RCN046
end PackedLegacy_A3

/-! Packed from ProximityPrize.SubmissionLower.DS. -/
section PackedLegacy_DS
namespace ProximityPrize.SubmissionLower.RCN044
open scoped Classical WithZero
open IsDedekindDomain RCN187 RCN002 RCN005
 RCN006
open RCN344 RCN341
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
def literalRelevantPlaces
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P):
   Finset (Place Omega (CoordinateField Omega P)):=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega P):=
   quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega P):=
   polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P i0 htr
 letI:=quotientBaseScalarTower Omega P i0
 letI:=polynomialBaseScalarTower Omega P i0
 letI:=quotientFractionScalarTower Omega P i0
 letI:=polynomialRationalScalarTower Omega P i0 htr
 letI:=rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=D.separable
 exact Finset.univ.biUnion (fun i:Fin 3 =>
   if hi:coordinate Omega P i≠0 then
     RCN026.placesFor Omega (CoordinateField Omega P)
       (coordinate Omega P i) hi
   else ∅)
theorem coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (v:Place Omega (CoordinateField Omega P))
   (hv:v∉literalRelevantPlaces D) (i:Fin 3):
   poleOrder v.val (coordinate Omega P i)=0:=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega P):=
   quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega P):=
   polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P i0 htr
 letI:=quotientBaseScalarTower Omega P i0
 letI:=polynomialBaseScalarTower Omega P i0
 letI:=quotientFractionScalarTower Omega P i0
 letI:=polynomialRationalScalarTower Omega P i0 htr
 letI:=rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=D.separable
 by_cases hi:coordinate Omega P i=0
 · simp [hi,poleOrder]
 · have hnot:v∉RCN026.placesFor Omega
       (CoordinateField Omega P) (coordinate Omega P i) hi:=by
     intro hmem
     apply hv
     unfold literalRelevantPlaces
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:RCN026.order Omega (CoordinateField Omega P) v
       (coordinate Omega P i)=0:=by
     by_contra hne
     exact hnot (RCN026.placesFor_covers Omega
       (CoordinateField Omega P) (coordinate Omega P i) hi v hne)
   unfold RCN026.order at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Omega P i)).log=0:=by omega
   rw [hlog]
   simp
end
end ProximityPrize.SubmissionLower.RCN044
end PackedLegacy_DS

/-! Packed from ProximityPrize.SubmissionLower.J7. -/
section PackedLegacy_J7
namespace ProximityPrize.SubmissionLower.RCN096
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain RCN022 RCN351 RCN344 RCN295 RCN075 RCN002 RCN005 RCN007 RCN264 RCN093 RCN097
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem directional_bad_coefficient_subsingleton
   {K:Type*} [Field K] (G:MvPolynomial (Fin 3) K)
   (hS:MvPolynomial.pderiv (1:Fin 3) G≠0):
   ∀ {a b:K},
     MvPolynomial.pderiv (0:Fin 3) G-
         MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G=0 →
     MvPolynomial.pderiv (0:Fin 3) G-
         MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G=0 →
     a=b:=by
 intro a b ha hb
 have ha':MvPolynomial.pderiv (0:Fin 3) G=
     MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G:=
   sub_eq_zero.mp ha
 have hb':MvPolynomial.pderiv (0:Fin 3) G=
     MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G:=
   sub_eq_zero.mp hb
 have habmul:MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G=
     MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G:=
   ha'.symm.trans hb'
 have hfactor:(MvPolynomial.C a-MvPolynomial.C b)*
     MvPolynomial.pderiv (1:Fin 3) G=0:=by
   rw [sub_mul,habmul,sub_self]
 have hCsub:MvPolynomial.C a-MvPolynomial.C b=0:=
   (mul_eq_zero.mp hfactor).resolve_right hS
 apply MvPolynomial.C_injective
 exact sub_eq_zero.mp hCsub
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
 {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
variable (W:∀ i,
 Finset (RCN345.NormalizedValuation K (E i)))
end FiniteFamily
section RegularComponents
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
end RegularComponents
end
end ProximityPrize.SubmissionLower.RCN096
end PackedLegacy_J7

/-! Packed from ProximityPrize.SubmissionLower.J8. -/
section PackedLegacy_J8
namespace ProximityPrize.SubmissionLower.RCN099
open scoped Classical WithZero
open IsDedekindDomain RCN187 RCN344 RCN264 RCN075 RCN093 RCN097 RCN002 RCN005 RCN007 RCN022
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem poleOrder_eq_max_of_valuation_eq_max
   {L:Type*} [Field L]
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x y z:L)
   (h:v x=max (v y) (v z)):
   poleOrder v x=max (poleOrder v y) (poleOrder v z):=by
 unfold poleOrder
 rw [h]
 by_cases hy:v y=0
 · rw [hy]
   simp
 by_cases hz:v z=0
 · rw [hz]
   simp
 rcases le_total (v y) (v z) with hyz | hzy
 · rw [max_eq_right hyz]
   rw [max_eq_right
     (max_le_max_left 0 ((WithZero.log_le_log hy hz).2 hyz))]
 · rw [max_eq_left hzy]
   rw [max_eq_left
     (max_le_max_left 0 ((WithZero.log_le_log hz hy).2 hzy))]
theorem valuation_le_one_of_poleOrder_eq_zero
   {L:Type*} [Field L]
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L)
   (h:poleOrder v x=0):
   v x ≤ 1:=by
 by_cases hx:v x=0
 · simp [hx]
 by_contra hnot
 have hlt:(1:WithZero (Multiplicative ℤ)) < v x:=
   lt_of_not_ge hnot
 have hlog:0 < (v x).log:=by
   simpa only [WithZero.log_one] using
     ((WithZero.log_lt_log one_ne_zero hx).2 hlt)
 unfold poleOrder at h
 rw [max_eq_right hlog.le] at h
 omega
section RegularComponents
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 2)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
theorem nested_u_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   poleOrder v.val (affineU Omega C.1 D.lam)=
     max (poleOrder v.val (coordinate Omega C.1 0))
       (poleOrder v.val (coordinate Omega C.1 2)):=by
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _
     (D.exactU C v hv)
 · have hY:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 0
   have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 2
   have hYle:v.val (coordinate Omega C.1 0) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hY
   have hZle:v.val (coordinate Omega C.1 2) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hZ
   letI:v.val.IsTrivialOn Omega:=v.property.2
   have hscalar:
       v.val (D.lam • coordinate Omega C.1 2)=
         v.val (coordinate Omega C.1 2):=by
     rw [Algebra.smul_def,map_mul,
       Valuation.IsTrivialOn.eq_one D.lam D.lam_ne,one_mul]
   have hUle:v.val (affineU Omega C.1 D.lam) ≤ 1:=by
     unfold affineU
     exact (v.val.map_add _ _).trans
       (by rw [hscalar];exact max_le hYle hZle)
   have hU:poleOrder v.val (affineU Omega C.1 D.lam)=0:=
     RCN346.poleOrder_eq_zero_of_le_one
       Omega (CoordinateField Omega C.1) v _ hUle
   rw [hU,hY,hZ]
   simp
theorem nested_v_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   poleOrder v.val (affineV Omega C.1 D.mu (D.mu*D.lam))=
     max (poleOrder v.val (coordinate Omega C.1 1))
       (max (poleOrder v.val (coordinate Omega C.1 0))
         (poleOrder v.val (coordinate Omega C.1 2))):=by
 rw [←nestedV_eq_affineV D C]
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · calc
     poleOrder v.val
         (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)=
         max (poleOrder v.val (coordinate Omega C.1 1))
           (poleOrder v.val (affineU Omega C.1 D.lam)):=
       poleOrder_eq_max_of_valuation_eq_max v.val _ _ _
         (D.exactV C v hv)
     _=max (poleOrder v.val (coordinate Omega C.1 1))
         (max (poleOrder v.val (coordinate Omega C.1 0))
           (poleOrder v.val (coordinate Omega C.1 2))):=by
       rw [nested_u_pole D C v]
 · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 1
   have hY:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 0
   have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 2
   have hU:poleOrder v.val (affineU Omega C.1 D.lam)=0:=by
     rw [nested_u_pole D C v,hY,hZ]
     simp
   have hSle:v.val (coordinate Omega C.1 1) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hS
   have hUle:v.val (affineU Omega C.1 D.lam) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hU
   letI:v.val.IsTrivialOn Omega:=v.property.2
   have hscalar:v.val (D.mu • affineU Omega C.1 D.lam)=
       v.val (affineU Omega C.1 D.lam):=by
     rw [Algebra.smul_def,map_mul,
       Valuation.IsTrivialOn.eq_one D.mu D.mu_ne,one_mul]
   have hVle:v.val
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam) ≤ 1:=
     (v.val.map_add _ _).trans
       (by rw [hscalar];exact max_le hSle hUle)
   have hV:poleOrder v.val
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)=0:=
     RCN346.poleOrder_eq_zero_of_le_one
       Omega (CoordinateField Omega C.1) v _ hVle
   rw [hV,hS,hY,hZ]
   simp
theorem hAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   Transcendental Omega (affineV Omega C.1 D.mu (D.mu*D.lam)):=by
 rw [←nestedV_eq_affineV D C]
 exact D.hV C
theorem elementEmbedding_affineV_eq_nested
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C)=
     elementEmbedding Omega (CoordinateField Omega C.1)
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)
       (D.hV C):=by
 apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial Omega))
 ext
 change elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C)
       (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)=
   elementEmbedding Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)
       (D.hV C)
       (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)
 rw [elementEmbedding_variable,elementEmbedding_variable]
 exact (nestedV_eq_affineV D C).symm
theorem separableAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
       (hAffineV D C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=by
 rw [elementEmbedding_affineV_eq_nested D C]
 exact D.separableV C
end RegularComponents
end
end ProximityPrize.SubmissionLower.RCN099
end PackedLegacy_J8

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier16 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.ED. -/
section PackedLegacy_ED
namespace ProximityPrize.SubmissionLower.RCN115
open scoped Classical BigOperators
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN075 RCN323 RCN118 RCN093 RCN125 RCN371 RCN011
 RCN022
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
structure SeparablePrincipalProjection
   {G T H:MvPolynomial (Fin 3) Omega}
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator))
   (hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj) where
 parameter:∀ C:RegularComponent Omega G T H,
   SeparableCoordinate Omega (CoordinateField Omega C.1)
 pole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   RCN346.poleOrder Omega (CoordinateField Omega C.1) v b=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (SeparableCoordinate.value Omega (CoordinateField Omega C.1)
         (parameter C))
def SeparablePrincipalProjection.cost
   {G T H:MvPolynomial (Fin 3) Omega}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   {B:GenericExactPolePolynomial G T H E separator hseparator hproj}
   (P:SeparablePrincipalProjection E separator hseparator hproj B)
   (C:RegularComponent Omega G T H):ℕ:=
 SeparableCoordinate.degree Omega (CoordinateField Omega C.1) (P.parameter C)
def SeparablePrincipalProjection.toPrincipalCycleBudget
   {G T H:MvPolynomial (Fin 3) Omega}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   {B:GenericExactPolePolynomial G T H E separator hseparator hproj}
   (P:SeparablePrincipalProjection E separator hseparator hproj B)
   (wholeCap:ℕ)
   (hsum:(∑ C:RegularComponent Omega G T H,P.cost C) ≤ wholeCap):
   PrincipalCycleBudget E separator hseparator hproj B wholeCap where
 cost:=P.cost
 cycle_le:=by
   intro C
   dsimp only
   let htr:=hseparator C
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 separator
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 separator
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 separator htr
   letI:=quotientBaseScalarTower Omega C.1 separator
   letI:=polynomialBaseScalarTower Omega C.1 separator
   letI:=quotientFractionScalarTower Omega C.1 separator
   letI:=polynomialRationalScalarTower Omega C.1 separator htr
   letI:=rationalBaseScalarTower Omega C.1 separator htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   let W:=RCN026.placesFor Omega
     (CoordinateField Omega C.1) b hb
   calc
     (∑ v∈W,RCN346.poleOrder Omega
         (CoordinateField Omega C.1) v b)=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (SeparableCoordinate.value Omega (CoordinateField Omega C.1)
             (P.parameter C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.pole_eq C v
     _ ≤ (SeparableCoordinate.degree Omega (CoordinateField Omega C.1)
         (P.parameter C):ℤ):=
       SeparableCoordinate.finite_sum_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.parameter C) W
     _=(P.cost C:ℤ):=rfl
 sum_cost_le:=hsum
def flagSeparableCoordinate
   {G T H:MvPolynomial (Fin 3) Omega}
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hsep:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
   (C:RegularComponent Omega G T H):
   SeparableCoordinate Omega (CoordinateField Omega C.1) where
 embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))) (ht C)
 finite:=hfinite C
 separable:=hsep C
@[simp] theorem flagSeparableCoordinate_value
   {G T H:MvPolynomial (Fin 3) Omega}
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hsep:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
   (C:RegularComponent Omega G T H):
   SeparableCoordinate.value Omega (CoordinateField Omega C.1)
       (flagSeparableCoordinate lam mu nu order ht hfinite hsep C)=
     flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)):=by
 exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))) (ht C)
def principalCycleBudget_of_flag_trapezoid
   {G T H:MvPolynomial (Fin 3) Omega}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj)
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hgen:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 1))}:
         Set (CoordinateField Omega C.1))=⊤)
   (hsep:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
   (hpole:∀ (C:RegularComponent Omega G T H)
       (v:Place Omega (CoordinateField Omega C.1)),
     let b:=MvPolynomial.eval₂Hom
       (algebraMap Omega (CoordinateField Omega C.1))
       (coordinate Omega C.1) B.polynomial
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v b=
       RCN346.poleOrder Omega (CoordinateField Omega C.1) v
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (order 0))))
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hpositive:0 <
     (planeMap Omega order (flagAlgHom lam mu nu G)).natDegree)
   (n mCap totalG totalT cap:ℕ) (hTne:T≠0)
   (hGouter:(planeMap Omega order
     (flagAlgHom lam mu nu G)).natDegree ≤ n)
   (hTouter:(planeMap Omega order
     (flagAlgHom lam mu nu T)).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap Omega order
     (flagAlgHom lam mu nu G)).support,d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap Omega order
     (flagAlgHom lam mu nu T)).support,d 0+d 1 ≤ totalT)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   PrincipalCycleBudget E separator hseparator hproj B cap:=by
 have hinj:Function.Injective
     (fun C:RegularComponent Omega G T H↦C.1):=by
   intro C D hCD
   exact Subtype.ext hCD
 have hfamily:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:RegularComponent Omega G T H↦C.1)
   hinj lam mu nu order ht hgen G T hG
   (fun C↦regularComponent_G_mem Omega G T H C)
   (fun C↦regularComponent_T_mem Omega G T H C)
   hproper hpositive n mCap totalG totalT cap hTne
   hGouter hTouter hGsupport hTsupport hbudget
 let hfinite:=hfamily.1
 let P:SeparablePrincipalProjection E separator hseparator hproj B:={
   parameter:=fun C↦
     flagSeparableCoordinate lam mu nu order ht hfinite hsep C
   pole_eq:=by
     intro C v
     simpa only [flagSeparableCoordinate_value] using hpole C v}
 apply P.toPrincipalCycleBudget cap
 change (∑ C:RegularComponent Omega G T H,
   SeparableCoordinate.degree Omega (CoordinateField Omega C.1)
     (flagSeparableCoordinate lam mu nu order ht hfinite hsep C)) ≤ cap
 convert hfamily.2 using 1
 apply Finset.sum_congr rfl
 intro C _
 rfl
end
end ProximityPrize.SubmissionLower.RCN115
end PackedLegacy_ED
end Compact_PackedLegacyCore2


