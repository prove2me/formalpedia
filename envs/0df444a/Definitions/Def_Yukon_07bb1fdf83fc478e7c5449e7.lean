-- Prove2me | Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
-- name    : Yukon_07bb1fdf83fc478e7c5449e7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T21:00:18.339231+00:00
-- url     : https://prove2.me/theorems/6d963d25-8865-4bb8-9299-0f641cccc79a
-- title:
--   LowerFoundation source part 4/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:bootstrap-v25-fc276d260668c8dcb6fb9481bbe712d425d017cb8b033dd14c81205dfe37808c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjE5NTEzNDQ2OTEwMzk3ZDEzY2ViZjU1OTliODA2YjZkNTZhZTRiZjNiZGRkY2VmMjNmMjE2OTVkZWM1MWUzYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmJvb3RzdHJhcC12MjUtZmMyNzZkMjYwNjY4YzhkY2I2ZmI5NDgxYmJlNzEyZDQyNWQwMTdjYjhiMDMzZGQxNGM4MTIwNWRmZTM3ODA4YyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzA3YmIxZmRmODNmYzQ3OGU3YzU0NDllNyIsInYiOjJ9]

import Definitions.Def_Yukon_51ec50eed11b4ee831fb1a97
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


/-! Packed from ProximityPrize.SubmissionLower.Z0. -/
section PackedLegacy_Z0
namespace ProximityPrize.SubmissionLower.RCN116
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN187 RCN075 RCN295 RCN095 RCN114 RCN125 RCN093 RCN097 RCN099 RCN115 RCN118 RCN123 RCN272 RCN371 RCN011
 RCN022
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable {hseparator:∀ C:RegularComponent Omega G T H,
 Transcendental Omega (coordinate Omega C.1 2)}
variable {hproj:∀ C:RegularComponent Omega G T H,
 ProjectionsFiniteSeparable Omega C.1}
theorem elementEmbedding_congr
   {L:Type} [Field L] [Algebra Omega L]
   {s t:L} (hs:Transcendental Omega s)
   (ht:Transcendental Omega t) (h:s=t):
   elementEmbedding Omega L s hs=elementEmbedding Omega L t ht:=by
 subst t
 rfl
theorem elementEmbedding_coordinate_eq_rationalBaseEmbedding
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (i:Fin 3) (hs ht:Transcendental Omega (coordinate Omega P i)):
   elementEmbedding Omega (CoordinateField Omega P)
       (coordinate Omega P i) hs=
     rationalBaseEmbedding Omega P i ht:=by
 rfl
structure FlagProjectionPositivity
   (D:NestedFlagProjectionData hseparator hproj)
   (G:MvPolynomial (Fin 3) Omega):Prop where
 u:0 < (planeMap Omega uOrder
   (flagAlgHom D.lam D.mu (D.mu*D.lam) G)).natDegree
 v:0 < (planeMap Omega vOrder
   (flagAlgHom D.lam D.mu (D.mu*D.lam) G)).natDegree
 z:0 < (planeMap Omega zOrder
   (flagAlgHom D.lam D.mu (D.mu*D.lam) G)).natDegree
theorem unitZ_polynomial_pole
   (B:GenericExactPolePolynomial G T H (flagSupport unitZFlag) 2
     hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   poleOrder v.val b=poleOrder v.val (coordinate Omega C.1 2):=by
 dsimp only
 calc
   poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B.polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitZFlag):=B.exact_pole C v
   _=poleOrder v.val (coordinate Omega C.1 2):=
     exponentSetPoleWeight_unitZ v.val (coordinate Omega C.1)
theorem unitYZ_polynomial_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (B:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) 2
     hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   poleOrder v.val b=poleOrder v.val (affineU Omega C.1 D.lam):=by
 dsimp only
 calc
   poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B.polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitYZFlag):=B.exact_pole C v
   _=max (poleOrder v.val (coordinate Omega C.1 0))
         (poleOrder v.val (coordinate Omega C.1 2)):=
     exponentSetPoleWeight_unitYZ v.val (coordinate Omega C.1)
   _=poleOrder v.val (affineU Omega C.1 D.lam):=
     (nested_u_pole D C v).symm
theorem unitAll_polynomial_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (B:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) 2
     hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   poleOrder v.val b=
     poleOrder v.val (affineV Omega C.1 D.mu (D.mu*D.lam)):=by
 dsimp only
 calc
   poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B.polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitAllFlag):=B.exact_pole C v
   _=max (poleOrder v.val (coordinate Omega C.1 1))
         (max (poleOrder v.val (coordinate Omega C.1 0))
           (poleOrder v.val (coordinate Omega C.1 2))):=
     exponentSetPoleWeight_unitAll v.val (coordinate Omega C.1)
   _=poleOrder v.val
         (affineV Omega C.1 D.mu (D.mu*D.lam)):=
     (nested_v_pole D C v).symm
def flagProjectionCycleBudget6543_of_nested
   (D:NestedFlagProjectionData hseparator hproj)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport shearedSurfaceFlag)
   (hTsupport:T.support ⊆ flagSupport shearedAgreementFlag)
   (hpositive:FlagProjectionPositivity D G)
   (B:GenericExactPolePolynomial G T H
     (flagSupport shearedAgreementFlag) 2 hseparator hproj)
   (BZ:GenericExactPolePolynomial G T H
     (flagSupport unitZFlag) 2 hseparator hproj)
   (BYZ:GenericExactPolePolynomial G T H
     (flagSupport unitYZFlag) 2 hseparator hproj)
   (BAll:GenericExactPolePolynomial G T H
     (flagSupport unitAllFlag) 2 hseparator hproj):
   FlagProjectionCycleBudget shearedAgreementFlag 2 hseparator hproj B
     flagZMixedCap flagYZMixedCap flagAllMixedCap:=by
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let gCaps:=flagTrapezoidCaps_flagAlgHom shearedSurfaceFlag G
   lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom shearedAgreementFlag T
   lam mu nu hTsupport
 let htZ:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0))):=by
   intro C
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using hseparator C
 let htU:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0))):=by
   intro C
   simpa [uOrder,lam,mu,nu] using D.hU C
 let htV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0))):=by
   intro C
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using hAffineV D C
 have hembZ (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0)))
         (htZ C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) (hseparator C):=
   elementEmbedding_congr (htZ C) (hseparator C)
     (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hembU (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0)))
         (htU C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineU Omega C.1 D.lam) (D.hU C):=
   elementEmbedding_congr (htU C) (D.hU C)
     (by simp [uOrder,lam,mu,nu])
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0)))
         (htV C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C):=
   elementEmbedding_congr (htV C) (hAffineV D C)
     (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let zBudget:PrincipalCycleBudget (flagSupport unitZFlag) 2
     hseparator hproj BZ flagZMixedCap:=
   principalCycleBudget_of_flag_trapezoid BZ lam mu nu zOrder
     htZ
     (by
       intro C
       rw [hembZ C]
       simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
         flag_generators_z Omega C.1 lam mu nu (hseparator C))
     (by
       intro C
       rw [hembZ C,
         elementEmbedding_coordinate_eq_rationalBaseEmbedding C.1 2
           (hseparator C) (hseparator C)]
       exact (hproj C 2 (hseparator C)).2)
     (by intro C v;simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu,
         RCN346.poleOrder] using
       unitZ_polynomial_pole BZ C v)
     hG hproper hpositive.z 5 1179639 26 6684622 flagZMixedCap hTne
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.zOuter)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.zOuter)
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.zTotal)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.zTotal)
     RCN123.z_trapezoid_budget6543
 let yzBudget:PrincipalCycleBudget (flagSupport unitYZFlag) 2
     hseparator hproj BYZ flagYZMixedCap:=
   principalCycleBudget_of_flag_trapezoid BYZ lam mu nu uOrder
     htU
     (by
       intro C
       rw [hembU C]
       simpa [uOrder,lam,mu,nu] using
         flag_generators_u Omega C.1 lam mu nu (D.hU C))
     (by
       intro C
       rw [hembU C]
       exact D.separableU C)
     (by intro C v;simpa [uOrder,lam,mu,nu,
         RCN346.poleOrder] using
       unitYZ_polynomial_pole D BYZ C v)
     hG hproper hpositive.u 5 1179639 376 98434322 flagYZMixedCap hTne
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.uOuter)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.uOuter)
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.uTotal)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.uTotal)
     RCN123.u_trapezoid_budget6543
 let allBudget:PrincipalCycleBudget (flagSupport unitAllFlag) 2
     hseparator hproj BAll flagAllMixedCap:=
   principalCycleBudget_of_flag_trapezoid BAll lam mu nu vOrder
     htV
     (by
       intro C
       rw [hembV C]
       simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
         flag_generators_v Omega C.1 lam mu nu (hAffineV D C))
     (by
       intro C
       rw [hembV C]
       exact separableAffineV D C)
     (by intro C v;simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu,
         RCN346.poleOrder] using
       unitAll_polynomial_pole D BAll C v)
     hG hproper hpositive.v 26 6684622 376 98434322 flagAllMixedCap hTne
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.vOuter)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.vOuter)
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.vTotal)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.vTotal)
     RCN123.v_trapezoid_budget6543
 exact FlagProjectionCycleBudget.ofNestedProjectionBudgets B BZ BYZ BAll
   zBudget yzBudget allBudget
end
end ProximityPrize.SubmissionLower.RCN116
end PackedLegacy_Z0

/-! Packed from ProximityPrize.SubmissionLower.X9. -/
section PackedLegacy_X9
namespace ProximityPrize.SubmissionLower.RCN037
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044 RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370
 RCN351
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def LiteralProjectionGate
   (C:RegularComponent Omega G T H) (j:Fin 3):Prop:=
 ∀ hj:Transcendental Omega (coordinate Omega C.1 j),
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 j) hj).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 j) hj).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
theorem base_differential_ne_zero
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (B:SeparableLiteralCoordinate P):
   D Omega (CoordinateField Omega P) (coordinate Omega P B.index)≠0:=by
 have h:=parameterDifferential_ne_zero_of_isSeparable Omega
   (CoordinateField Omega P)
   (rationalBaseEmbedding Omega P B.index B.transcendental)
   B.finite B.separable
 unfold RCN369.parameterDifferential at h
 have hvalue:rationalBaseEmbedding Omega P B.index B.transcendental
     (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)=
       coordinate Omega P B.index:=
   (rationalBaseEmbedding_polynomial Omega P B.index B.transcendental
     Polynomial.X).trans (Polynomial.aeval_X _)
 rwa [hvalue] at h
theorem poleOrder_eq_zero_of_isAlgebraic
   {L:Type*} [Field L] [Algebra Omega L]
   (v:RCN346.Place Omega L) (x:L)
   (hx:IsAlgebraic Omega x):
   RCN187.poleOrder v.val x=0:=by
 obtain ⟨a,rfl⟩:=eq_algebraMap_of_isAlgebraic Omega L x hx
 exact RCN346.poleOrder_eq_zero_of_le_one Omega L v _
   (constant_value_le_one Omega L v a)
structure AdaptiveNestedProjectionData
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0) where
 lam:Omega
 lam_ne:lam≠0
 mu:Omega
 mu_ne:mu≠0
 uProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 allProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 uGate:∀ C:RegularComponent Omega G T H,
   ∀ htr:Transcendental Omega (affineU Omega C.1 lam),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 allAffineTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega (affineV Omega C.1 mu (mu*lam))
 allFinite:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)
 allSeparable:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)
 uValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=
     affineU Omega C.1 lam
 allValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (allProjection C)=
     affineV Omega C.1 mu (mu*lam)
 allTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega
     (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 uPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (uProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
       (RCN187.poleOrder v.val (coordinate Omega C.1 2))
 allPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
       (max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)))
 directional:MvPolynomial.pderiv (0:Fin 3) G-
   MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0
theorem exists_adaptiveNestedProjectionData
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   Nonempty (AdaptiveNestedProjectionData base hY hZ hSderiv):=by
 classical
 let ActiveU:={C:RegularComponent Omega G T H//
   D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0}
 let EU:ActiveU → Type:=fun C => CoordinateField Omega C.1.1
 let rY:∀ C:ActiveU,EU C:=fun C => coordinate Omega C.1.1 0
 let z:∀ C:ActiveU,EU C:=fun C => coordinate Omega C.1.1 2
 let WU:∀ C:ActiveU,Finset (Place Omega (EU C)):=
   fun C => literalRelevantPlaces (base C.1)
 let baseU:∀ C:ActiveU,SeparableCoordinate Omega (EU C):=
   fun C => literalToSeparableCoordinate (base C.1)
 obtain ⟨lam,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_affine_adaptive EU rY z WU
     baseU (fun C => C.2)
 let U:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=
   fun C => affineU Omega C.1 lam
 have hUgate:∀ C:RegularComponent Omega G T H,
     ∀ htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
   intro C htr
   by_cases hactive:
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     obtain ⟨hs,hfinite,hsep,_⟩:=hlam CU
     have hp:htr=hs:=Subsingleton.elim _ _
     cases hp
     exact ⟨hfinite,hsep⟩
   · have hzero:=not_or.mp hactive
     have hYalg:IsAlgebraic Omega (coordinate Omega C.1 0):=by
       apply not_not.mp
       intro hy
       exact (differential_ne_zero_of_gate _ hy (hY C hy))
         (not_ne_iff.mp hzero.1)
     have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=by
       apply not_not.mp
       intro hz
       exact (differential_ne_zero_of_gate _ hz (hZ C hz))
         (not_ne_iff.mp hzero.2)
     exact (htr (hYalg.add (hZalg.smul lam))).elim
 let uProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=
   fun C => coordinateOfGate (U C) (hUgate C)
 have huValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=U C:=
   fun C => coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)):=by
   intro C v
   by_cases hactive:
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     by_cases hv:v∈literalRelevantPlaces (base C)
     · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
         simpa only [WU,rY,z,U,affineU] using
           (hlam CU).choose_spec.2.2 v hv)
     · have h0:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
           (base C) v hv 0
       have h2:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
           (base C) v hv 2
       have h0le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h0
       have h2le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h2
       letI:v.val.IsTrivialOn Omega:=v.property.2
       have hscalar:v.val (lam • coordinate Omega C.1 2)=
           v.val (coordinate Omega C.1 2):=by
         rw [Algebra.smul_def,map_mul,
           Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
       have hUle:v.val (U C) ≤ 1:=by
         exact (v.val.map_add _ _).trans
           (by rw [hscalar];exact max_le h0le h2le)
       have hU0:RCN187.poleOrder v.val (U C)=0:=
         RCN346.poleOrder_eq_zero_of_le_one Omega
           (CoordinateField Omega C.1) v _ hUle
       rw [hU0,h0,h2]
       simp
   · have hzero:=not_or.mp hactive
     have hYalg:IsAlgebraic Omega (coordinate Omega C.1 0):=by
       apply not_not.mp
       intro hy
       exact (differential_ne_zero_of_gate _ hy (hY C hy))
         (not_ne_iff.mp hzero.1)
     have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=by
       apply not_not.mp
       intro hz
       exact (differential_ne_zero_of_gate _ hz (hZ C hz))
         (not_ne_iff.mp hzero.2)
     have hUalg:IsAlgebraic Omega (U C):=hYalg.add (hZalg.smul lam)
     rw [poleOrder_eq_zero_of_isAlgebraic v _ hUalg,
       poleOrder_eq_zero_of_isAlgebraic v _ hYalg,
       poleOrder_eq_zero_of_isAlgebraic v _ hZalg]
     simp
 have hactiveV:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 1)≠0∨
       D Omega (CoordinateField Omega C.1) (U C)≠0:=by
   intro C
   by_cases hactive:
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     obtain ⟨hs,hfinite,hsep,_⟩:=hlam CU
     exact Or.inr (differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
   · have hzero:=not_or.mp hactive
     have hb:=base_differential_ne_zero (base C)
     generalize hidx:(base C).index=i at hb
     fin_cases i
     · exact (hb (not_ne_iff.mp hzero.1)).elim
     · exact Or.inl hb
     · exact (hb (not_ne_iff.mp hzero.2)).elim
 let EC:RegularComponent Omega G T H → Type:=
   fun C => CoordinateField Omega C.1
 let rS:∀ C,EC C:=fun C => coordinate Omega C.1 1
 let W:∀ C,Finset (Place Omega (EC C)):=
   fun C => literalRelevantPlaces (base C)
 let baseC:∀ C,SeparableCoordinate Omega (EC C):=
   fun C => literalToSeparableCoordinate (base C)
 let Extra:Omega → Prop:=fun mu =>
   MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G=0
 have hextra:∀ {a b},Extra a → Extra b → a=b:=by
   exact directional_bad_coefficient_subsingleton G hSderiv
 obtain ⟨mu,hmu0,hmudir,hmu⟩:=
   exists_common_exact_finite_separable_affine_adaptive_avoiding_one
     EC rS U W Extra hextra baseC hactiveV
 let V:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=
   fun C => coordinate Omega C.1 1+mu • U C
 let hV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (V C):=fun C => (hmu C).choose
 let vProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (vProjection C)=V C:=by
   intro C
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1) (V C) (hV C)
 have hvPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 1
     have hY:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 0
     have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C) ≤ 1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (affineV Omega C.1 mu (mu*lam)):=fun C => by
   rw [show affineV Omega C.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 mu (mu*lam)) (hVAff C)=
       elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C):=
   elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])
 refine ⟨{
   lam:=lam
   lam_ne:=hlam0
   mu:=mu
   mu_ne:=hmu0
   uProjection:=uProjection
   allProjection:=vProjection
   uGate:=hUgate
   allAffineTranscendental:=hVAff
   allFinite:=?_
   allSeparable:=?_
   uValue:=huValue
   allValue:=?_
   allTranscendental:=?_
   uPole:=?_
   allPole:=?_
   directional:=hmudir}⟩
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.1
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.2.1
 · intro C
   rw [hvValue C]
   simp only [V,U,affineU,affineV]
   simp only [smul_add,smul_smul,add_assoc]
 · intro C
   rw [hvValue C]
   exact hV C
 · intro C v
   rw [huValue C]
   exact huPole C v
 · intro C v
   rw [hvValue C,hvPole C v,huPole C v]
end
end ProximityPrize.SubmissionLower.RCN037
end PackedLegacy_X9

/-! Packed from ProximityPrize.SubmissionLower.C0. -/

/-! Packed from ProximityPrize.SubmissionLower.BA. -/
section PackedLegacy_BA
namespace ProximityPrize.SubmissionLower.RCN117
open scoped Classical
open RCN267 RCN125 RCN097 RCN116 RCN011
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
theorem derivative_planeMap (order:Equiv (Fin 3) (Fin 3)) (F:Poly3 K):
   Polynomial.derivative (planeMap K order F)=
     planeMap K order (MvPolynomial.pderiv (order 1) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add P Q hP hQ => simp [hP,hQ]
 | mul_X P i hP =>
     obtain ⟨j,rfl⟩:=order.surjective i
     fin_cases j <;>
       simp [MvPolynomial.pderiv_mul,hP,Polynomial.derivative_mul,
         planeMap_X_first,planeMap_X_outer,planeMap_X_inner,
         Pi.single_apply] <;> ring
theorem planeMap_natDegree_pos_of_pderiv_ne_zero
   (order:Equiv (Fin 3) (Fin 3)) (F:Poly3 K)
   (hderiv:MvPolynomial.pderiv (order 1) F≠0):
   0 < (planeMap K order F).natDegree:=by
 apply Nat.pos_of_ne_zero
 intro hzero
 have hplanezero:Polynomial.derivative (planeMap K order F)=0:=
   Polynomial.derivative_of_natDegree_zero hzero
 rw [derivative_planeMap] at hplanezero
 apply hderiv
 apply planeMap_injective K order
 simpa only [map_zero] using hplanezero
theorem pderiv_one_flagAlgHom (lam mu nu:K) (F:Poly3 K):
   MvPolynomial.pderiv (1:Fin 3) (flagAlgHom lam mu nu F)=
     flagAlgHom lam mu nu (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add P Q hP hQ => simp [hP,hQ]
 | mul_X P i hP =>
     fin_cases i <;>
       simp [flagImage,hP,MvPolynomial.pderiv_mul,
         Derivation.leibniz] <;> ring
theorem pderiv_zero_flagAlgHom_nested (lam mu:K) (F:Poly3 K):
   MvPolynomial.pderiv (0:Fin 3)
       (flagAlgHom lam mu (mu*lam) F)=
     flagAlgHom lam mu (mu*lam)
       (MvPolynomial.pderiv (0:Fin 3) F-
         MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add P Q hP hQ =>
     simp [hP,hQ,mul_add,sub_eq_add_neg] <;> ring
 | mul_X P i hP =>
     fin_cases i <;>
       simp [flagImage,hP,MvPolynomial.pderiv_mul,
         Derivation.leibniz] <;> ring
theorem flag_u_z_outer_positive_of_pderiv
   (lam mu:K) (G:Poly3 K)
   (hderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   0 < (planeMap K uOrder
         (flagAlgHom lam mu (mu*lam) G)).natDegree∧
     0 < (planeMap K zOrder
         (flagAlgHom lam mu (mu*lam) G)).natDegree:=by
 have hflag:MvPolynomial.pderiv (1:Fin 3)
     (flagAlgHom lam mu (mu*lam) G)≠0:=by
   rw [pderiv_one_flagAlgHom]
   exact (flagEquiv lam mu (mu*lam)).injective.ne hderiv
 constructor
 · apply planeMap_natDegree_pos_of_pderiv_ne_zero uOrder
   simpa [uOrder] using hflag
 · apply planeMap_natDegree_pos_of_pderiv_ne_zero zOrder
   simpa [zOrder,Equiv.swap_apply_def] using hflag
section Characteristic
variable (p:ℕ) [CharP K p]
theorem flag_v_outer_positive_of_directional
   (lam mu:K) (G:Poly3 K)
   (hdirectional:MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0):
   0 < (planeMap K vOrder
       (flagAlgHom lam mu (mu*lam) G)).natDegree:=by
 apply planeMap_natDegree_pos_of_pderiv_ne_zero vOrder
 simpa [vOrder,Equiv.swap_apply_def,
   pderiv_zero_flagAlgHom_nested] using
   (flagEquiv lam mu (mu*lam)).injective.ne hdirectional
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega p]
 {G T H:MvPolynomial (Fin 3) Omega}
variable
   {hseparator:∀ C:RCN264.RegularComponent
       Omega G T H,
     Transcendental Omega
       (RCN002.coordinate Omega C.1 2)}
   {hproj:∀ C:RCN264.RegularComponent
       Omega G T H,
     RCN007.ProjectionsFiniteSeparable Omega C.1}
end Characteristic
end
end ProximityPrize.SubmissionLower.RCN117
end PackedLegacy_BA

/-! Packed from ProximityPrize.SubmissionLower.Y0. -/
section PackedLegacy_Y0
namespace ProximityPrize.SubmissionLower.RCN039
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN046 RCN037 RCN095 RCN114 RCN093 RCN123 RCN121 RCN117 RCN116 RCN125 RCN022
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamily_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionData base hY hZ hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamily base p q:=by
 classical
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let zProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (coordinate Omega C.1 2) (hZ C)
 let uProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
 let vProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
   finite:=D.allFinite C
   separable:=D.allSeparable C}
 let gCaps:=flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let sZ:={C:RegularComponent Omega G T H//
   Transcendental Omega (coordinate Omega C.1 2)}
 have hinjZ:Function.Injective (fun C:sZ => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htZ:∀ C:sZ,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (zOrder 0))):=by
   intro C
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using C.2
 have hembZ (C:sZ):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (coordinate Omega C.1.1 2) C.2:=
   elementEmbedding_congr (htZ C) C.2
     (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenZ:∀ C:sZ,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembZ C]
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_z Omega C.1.1 lam mu nu C.2
 have hfamilyZ:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sZ => C.1.1) hinjZ lam mu nu zOrder
   htZ hgenZ G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
   p.all q.all (p.yz+p.all) (q.yz+q.all)
   (flagMixed p q unitZFlag) hTne
   (by simpa only [gCaps] using gCaps.zOuter)
   (by simpa only [tCaps] using tCaps.zOuter)
   (by simpa only [gCaps] using gCaps.zTotal)
   (by simpa only [tCaps] using tCaps.zTotal)
   (z_flag_trapezoid_budget p q)
 have hsumZ:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (zProj C)) ≤
       flagMixed p q unitZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => coordinate Omega C.1 2) hZ
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sZ,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sZ,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembZ C]
     _ ≤ _:=hfamilyZ.2
 let sU:={C:RegularComponent Omega G T H//
   Transcendental Omega (affineU Omega C.1 D.lam)}
 have hinjU:Function.Injective (fun C:sU => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htU:∀ C:sU,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (uOrder 0))):=by
   intro C
   simpa [uOrder,lam,mu,nu] using C.2
 have hembU (C:sU):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (affineU Omega C.1.1 D.lam) C.2:=
   elementEmbedding_congr (htU C) C.2
     (by simp [uOrder,lam,mu,nu])
 have hgenU:∀ C:sU,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembU C]
   simpa [uOrder,lam,mu,nu] using
     flag_generators_u Omega C.1.1 lam mu nu C.2
 have hfamilyU:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sU => C.1.1) hinjU lam mu nu uOrder
   htU hgenU G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
   p.all q.all (p.zOnly+p.yz+p.all)
   (q.zOnly+q.yz+q.all) (flagMixed p q unitYZFlag) hTne
   (by simpa only [gCaps] using gCaps.uOuter)
   (by simpa only [tCaps] using tCaps.uOuter)
   (by simpa only [gCaps] using gCaps.uTotal)
   (by simpa only [tCaps] using tCaps.uTotal)
   (u_flag_trapezoid_budget p q)
 have hsumU:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (uProj C)) ≤
       flagMixed p q unitYZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => affineU Omega C.1 D.lam) D.uGate
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sU,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sU,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembU C]
     _ ≤ _:=hfamilyU.2
 let htV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu
         (MvPolynomial.X (vOrder 0))):=by
   intro C
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     D.allAffineTranscendental C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam))
           (D.allAffineTranscendental C):=
   elementEmbedding_congr (htV C) (D.allAffineTranscendental C)
     (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenV:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 2)),
         flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 1))}:
         Set (CoordinateField Omega C.1))=⊤:=by
   intro C
   rw [hembV C]
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_v Omega C.1 lam mu nu (D.allAffineTranscendental C)
 have hinjV:Function.Injective
     (fun C:RegularComponent Omega G T H => C.1):=by
   intro C E hCE
   exact Subtype.ext hCE
 have hfamilyV:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:RegularComponent Omega G T H => C.1)
   hinjV lam mu nu vOrder htV hgenV G T hG
   (fun C => regularComponent_G_mem Omega G T H C)
   (fun C => regularComponent_T_mem Omega G T H C)
   hproper
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
   (p.yz+p.all) (q.yz+q.all)
   (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
   (flagMixed p q unitAllFlag) hTne
   (by simpa only [gCaps] using gCaps.vOuter)
   (by simpa only [tCaps] using tCaps.vOuter)
   (by simpa only [gCaps] using gCaps.vTotal)
   (by simpa only [tCaps] using tCaps.vTotal)
   (v_flag_trapezoid_budget p q)
 have hsumV:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (vProj C)) ≤
       flagMixed p q unitAllFlag:=by
   calc
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (affineV Omega C.1 D.mu (D.mu*D.lam))
               (D.allAffineTranscendental C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rfl
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (flagEvaluation Omega C.1 lam mu nu
               (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembV C]
     _ ≤ _:=hfamilyV.2
 have hvValue (C:RegularComponent Omega G T H):
     coordinateValue Omega (CoordinateField Omega C.1) (vProj C)=
       affineV Omega C.1 D.mu (D.mu*D.lam):=by
   dsimp only [vProj,coordinateValue,SeparableCoordinate.value,Sum.elim_inr]
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
 refine {
   zProjection:=zProj
   yzProjection:=uProj
   allProjection:=vProj
   zValue:=?_
   allTranscendental:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   sum_zDegree_le:=hsumZ
   sum_yzDegree_le:=hsumU
   sum_allDegree_le:=hsumV}
 · intro C
   exact coordinateOfGate_value _ _
 · intro C
   rw [hvValue C]
   exact D.allAffineTranscendental C
 · intro C v
   rw [exponentSetPoleWeight_unitZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
 · intro C v
   rw [exponentSetPoleWeight_unitYZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
   rw [←D.uValue C]
   exact (D.uPole C v).symm
 · intro C v
   rw [exponentSetPoleWeight_unitAll]
   change _=RCN187.poleOrder v.val _
   rw [hvValue C, ←D.allValue C]
   exact (D.allPole C v).symm
theorem exists_adaptiveUnitProjectionFamily_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamily base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionData base hY hZ hSderiv
 exact ⟨adaptiveUnitProjectionFamily_of_nested p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport⟩
end
end ProximityPrize.SubmissionLower.RCN039
end PackedLegacy_Y0

/-! Packed from ProximityPrize.SubmissionLower.E1. -/
section PackedLegacy_E1
namespace ProximityPrize.SubmissionLower.RCN240
open scoped Classical BigOperators
open RCN159 RCN164 RCN275 RCN276 RCN174 RCN286 RCN266 RCN238 RCN095
set_option maxHeartbeats 1500000
set_option maxRecDepth 50000
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance _root_.ProximityPrize.SubmissionLower.RCN240.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN240.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN240
end PackedLegacy_E1

/-! Packed from ProximityPrize.SubmissionLower.EI. -/
section PackedLegacy_EI
namespace ProximityPrize.SubmissionLower.RCN131
open scoped Classical BigOperators
open RCN095 RCN130 RCN240 RCN276 RCN266 RCN222 RCN275 RCN174 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
theorem linear_cost_cumulative (cz cy ca:ℕ) (f:FlagDegree)
   (hzy:cz ≤ cy) (hya:cy ≤ ca):
   f.zOnly*cz+f.yz*cy+f.all*ca=
     cz*(f.zOnly+f.yz+f.all)+
       (cy-cz)*(f.yz+f.all)+(ca-cy)*f.all:=by
 have hy:cz+(cy-cz)=cy:=by omega
 have ha:cz+(cy-cz)+(ca-cy)=ca:=by omega
 calc
   f.zOnly*cz+f.yz*cy+f.all*ca=
       f.zOnly*cz+f.yz*(cz+(cy-cz))+
         f.all*(cz+(cy-cz)+(ca-cy)):=by rw [ha,hy]
   _=_:=by ring
variable {K:Type} [Field K]
end
end ProximityPrize.SubmissionLower.RCN131
end PackedLegacy_EI

/-! Packed from ProximityPrize.SubmissionLower.Y5. -/
section PackedLegacy_Y5
namespace ProximityPrize.SubmissionLower.RCN084
open scoped Classical BigOperators
open RCN095 RCN121 RCN071 RCN137 RCN264 RCN341 RCN037 RCN039 RCN046 RCN237 RCN002 RCN005 RCN003 RCN001
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K
def exactFlag (A:Poly):FlagDegree:=
 let s:=MvPolynomial.weightedTotalDegree flagSWeights A
 let m:=MvPolynomial.weightedTotalDegree flagYSWeights A
 let t:=MvPolynomial.weightedTotalDegree flagTotalWeights A
 ⟨t-m,m-s,s⟩
theorem flag_weights_nested (A:Poly):
   MvPolynomial.weightedTotalDegree flagSWeights A ≤
     MvPolynomial.weightedTotalDegree flagYSWeights A∧
   MvPolynomial.weightedTotalDegree flagYSWeights A ≤
     MvPolynomial.weightedTotalDegree flagTotalWeights A:=by
 constructor
 all_goals
   apply Finset.sup_le
   intro d hd
 · have h:=MvPolynomial.le_weightedTotalDegree flagYSWeights hd
   rw [flag_weight_fin3] at h ⊢
   change d 0*0+d 1*1+d 2*0 ≤ _
   change d 0*1+d 1*1+d 2*0 ≤ _ at h
   simpa using (show d 1 ≤ MvPolynomial.weightedTotalDegree flagYSWeights A by omega)
 · have h:=MvPolynomial.le_weightedTotalDegree flagTotalWeights hd
   rw [flag_weight_fin3] at h ⊢
   change d 0*1+d 1*1+d 2*0 ≤ _
   change d 0*1+d 1*1+d 2*1 ≤ _ at h
   omega
theorem exactFlag_cumulative (A:Poly):
   (exactFlag A).all=MvPolynomial.weightedTotalDegree flagSWeights A∧
   (exactFlag A).yz+(exactFlag A).all=MvPolynomial.weightedTotalDegree flagYSWeights A∧
   (exactFlag A).zOnly+(exactFlag A).yz+(exactFlag A).all=
     MvPolynomial.weightedTotalDegree flagTotalWeights A:=by
 have h:=flag_weights_nested A
 dsimp [exactFlag]
 omega
theorem polynomialIn_exactFlag (A:Poly):PolynomialInFlag (exactFlag A) A:=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree flagSWeights hd
 have hm:=MvPolynomial.le_weightedTotalDegree flagYSWeights hd
 have ht:=MvPolynomial.le_weightedTotalDegree flagTotalWeights hd
 rw [flag_weight_fin3] at hs hm ht
 have hc:=exactFlag_cumulative A
 change d 0*0+d 1*1+d 2*0 ≤ _ at hs
 change d 0*1+d 1*1+d 2*0 ≤ _ at hm
 change d 0*1+d 1*1+d 2*1 ≤ _ at ht
 unfold InFlag
 omega
theorem inFlag_weight_caps (A:Poly) (p:FlagDegree) (hA:PolynomialInFlag p A):
   MvPolynomial.weightedTotalDegree flagSWeights A ≤ p.all∧
   MvPolynomial.weightedTotalDegree flagYSWeights A ≤ p.yz+p.all∧
   MvPolynomial.weightedTotalDegree flagTotalWeights A ≤ p.zOnly+p.yz+p.all:=by
 refine ⟨?_,?_,?_⟩
 all_goals
   apply Finset.sup_le
   intro d hd
   have h:=hA d hd
   rw [flag_weight_fin3]
 · change d 0*0+d 1*1+d 2*0 ≤ _;exact by simpa using h.1
 · change d 0*1+d 1*1+d 2*0 ≤ _;exact by simpa using h.2.1
 · change d 0*1+d 1*1+d 2*1 ≤ _;exact by simpa using h.2.2
theorem sum_flagMixed_le_of_cumulative {I:Type*} [Fintype I]
   (f:I → FlagDegree) (p q r:FlagDegree)
   (hs:(∑ i,(f i).all) ≤ p.all)
   (hm:(∑ i,((f i).yz+(f i).all)) ≤ p.yz+p.all)
   (ht:(∑ i,((f i).zOnly+(f i).yz+(f i).all)) ≤ p.zOnly+p.yz+p.all):
   (∑ i,flagMixed (f i) q r) ≤ flagMixed p q r:=by
 let z:=flagMixed unitZFlag q r
 let y:=flagMixed unitYZFlag q r
 let a:=flagMixed unitAllFlag q r
 have hzy:z ≤ y:=by simp [z,y,flagMixed,unitZFlag,unitYZFlag];nlinarith
 have hya:y ≤ a:=by simp [y,a,flagMixed,unitYZFlag,unitAllFlag];nlinarith
 have heq (v:FlagDegree):flagMixed v q r=
     z*(v.zOnly+v.yz+v.all)+(y-z)*(v.yz+v.all)+(a-y)*v.all:=by
   calc
     flagMixed v q r=v.zOnly*z+v.yz*y+v.all*a:=by
       simp only [z,y,a,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
       ring
     _=_:=RCN131.linear_cost_cumulative z y a v hzy hya
 rw [Finset.sum_congr rfl (fun i _↦heq (f i)),heq p]
 simp only [Finset.sum_add_distrib, ←Finset.mul_sum]
 simpa only [Finset.sum_add_distrib] using Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_left z ht) (Nat.mul_le_mul_left (y-z) hm))
   (Nat.mul_le_mul_left (a-y) hs)
def activeFactors (F N:Poly):Finset Poly:=
 (normalizedFactorSet F).filter fun g↦¬ g∣N∧MvPolynomial.pderiv (1:Fin 3) g≠0
theorem activeFactors_spec (F N:Poly) (g:↥(activeFactors F N)):
   Irreducible g.1∧g.1∣F∧¬ g.1∣N∧MvPolynomial.pderiv (1:Fin 3) g.1≠0:=by
 have h:=Finset.mem_filter.mp g.2
 exact ⟨(normalizedFactorSet_spec F g.1 h.1).1,
   (normalizedFactorSet_spec F g.1 h.1).2,h.2⟩
theorem activeFactors_mixed_sum_le (F N:Poly) (hF:F≠0)
   (p q r:FlagDegree) (hsupport:PolynomialInFlag p F):
   (∑ g:↥(activeFactors F N),flagMixed (exactFlag g.1) q r) ≤ flagMixed p q r:=by
 have hc:=inFlag_weight_caps F p hsupport
 have hw (w:Fin 3 → ℕ):
     (∑ g:↥(activeFactors F N),MvPolynomial.weightedTotalDegree w g.1) ≤
       MvPolynomial.weightedTotalDegree w F:=by
   rw [Finset.sum_coe_sort]
   exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
     (sum_weightedTotalDegree_le_of_prod_dvd_fin3 w (normalizedFactorSet F) id F hF
       (normalizedFactorSet_product_dvd F hF))
 apply sum_flagMixed_le_of_cumulative
 · simpa only [(exactFlag_cumulative _).1] using (hw flagSWeights).trans hc.1
 · calc
     _=∑ g:↥(activeFactors F N),MvPolynomial.weightedTotalDegree flagYSWeights g.1:=
       Finset.sum_congr rfl (fun g _↦(exactFlag_cumulative g.1).2.1)
     _ ≤ _:=(hw flagYSWeights).trans hc.2.1
 · calc
     _=∑ g:↥(activeFactors F N),MvPolynomial.weightedTotalDegree flagTotalWeights g.1:=
       Finset.sum_congr rfl (fun g _↦(exactFlag_cumulative g.1).2.2)
     _ ≤ _:=(hw flagTotalWeights).trans hc.2.2
variable [IsAlgClosed K]
def IsolatedPoint (F N A:Poly) (v:Fin 3 → K):Prop:=
 ∀ D:Ideal Poly,D.IsPrime →
   (∀ w:Fin 3 → K,D≠RingHom.ker (MvPolynomial.aeval w).toRingHom) →
   D ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom → F∈D → N∈D → A∉D
theorem exists_active_factor_of_isolated (F N A R:Poly) (hF:F≠0)
   (v:Fin 3 → K) (hvF:MvPolynomial.eval v F=0)
   (hvA:MvPolynomial.eval v A=0) (hvR:MvPolynomial.eval v R≠0)
   (hvD:MvPolynomial.eval v (MvPolynomial.pderiv (1:Fin 3) F)≠0)
   (hi:IsolatedPoint F N A v):
   ∃ g:↥(activeFactors F N),MvPolynomial.eval v g.1=0:=by
 obtain ⟨g,hg,hgv⟩:=exists_normalizedFactorSet_zero (MvPolynomial.eval v) F hF hvF
 have hs:=normalizedFactorSet_spec F g hg
 have hproper:¬ g∣N:=by
   intro hgN
   obtain ⟨D,hD⟩:=exists_regular_component K g A R v hgv hvA hvR
   have hmem:=regularComponent_G_mem K g A R D
   exact hi D.1 inferInstance (regularComponent_ne_point K g A R D) hD
     (D.1.mem_of_dvd hs.2 hmem) (D.1.mem_of_dvd hgN hmem)
     (regularComponent_T_mem K g A R D)
 have hderiv:MvPolynomial.pderiv (1:Fin 3) g≠0:=by
   intro hz
   obtain ⟨b,hb⟩:=hs.2
   apply hvD
   rw [hb,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hz,map_zero,hgv]
   ring
 exact ⟨⟨g,Finset.mem_filter.mpr ⟨hg,hproper,hderiv⟩⟩,hgv⟩
theorem isolated_points_card_le (F N A R:Poly) (p q r:FlagDegree)
   (hF:F≠0) (hFp:PolynomialInFlag p F)
   (hNq:PolynomialInFlag q N) (hAr:PolynomialInFlag r A)
   (base:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     SeparableLiteralCoordinate C.1)
   (hY:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     LiteralProjectionGate C 0)
   (hZ:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     LiteralProjectionGate C 2)
   (points:Finset (Fin 3 → K))
   (hcover:∀ v∈points,∃ g:↥(activeFactors F N),MvPolynomial.eval v g.1=0)
   (hN:∀ v∈points,MvPolynomial.eval v N=0)
   (hA:∀ v∈points,MvPolynomial.aeval v A=0)
   (hR:∀ v∈points,MvPolynomial.eval v R≠0)
   (hisolated:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     ∀ v∈points,C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom → A∉C.1):
   points.card ≤ flagMixed p q r:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 let S (g:↥(activeFactors F N)):Finset (Fin 3 → K):=
   points.filter fun (v:Fin 3 → K)↦MvPolynomial.eval v g.1=(0:K)
 have hcoverage:points ⊆ Finset.univ.biUnion S:=by
   intro v hv
   obtain ⟨g,hg⟩:=hcover v hv
   exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hv,hg⟩⟩
 have hcount (g:↥(activeFactors F N)):(S g).card ≤ flagMixed (exactFlag g.1) q r:=by
   have hg:=activeFactors_spec F N g
   obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
     (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
     ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
     ((support_subset_flagSupport_iff _ _).mpr hNq)
   let B:=P.toPrimeFlagBudgetFamily
   calc
     (S g).card ≤ ∑ C:RegularComponent K g.1 N R,
         (componentSeeds K g.1 N R (S g) id C).card:=
       card_le_sum_componentSeeds K g.1 N R (S g) id
         (fun v hv↦(Finset.mem_filter.mp hv).2)
         (fun v hv↦hN v (Finset.mem_filter.mp hv).1)
         (fun v hv↦hR v (Finset.mem_filter.mp hv).1)
     _ ≤ ∑ C:RegularComponent K g.1 N R,B.weightedCost r C:=by
       apply Finset.sum_le_sum
       intro C _
       by_cases hempty:(componentSeeds K g.1 N R (S g) id C).Nonempty
       · obtain ⟨v,hv⟩:=hempty
         have hvP:=componentSeeds_on_prime K g.1 N R (S g) id C v hv
         have hvS:=componentSeeds_subset K g.1 N R (S g) id C hv
         apply (B.primeBudget C).zero_le r A hAr
           (hisolated g C v (Finset.mem_filter.mp hvS).1 hvP)
         · intro w hw
           exact componentSeeds_on_prime K g.1 N R (S g) id C w hw
         · intro w hw
           exact hA w (Finset.mem_filter.mp
             (componentSeeds_subset K g.1 N R (S g) id C hw)).1
       · simp only [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.zero_le]
     _ ≤ flagMixed (exactFlag g.1) q r:=B.sum_weightedCost_le r
 exact ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le).trans
   ((Finset.sum_le_sum (fun g _↦hcount g)).trans (activeFactors_mixed_sum_le F N hF p q r hFp))
theorem degreeOf_le_flag_total (F:Poly) (p:FlagDegree) (hF:PolynomialInFlag p F)
   (i:Fin 3):F.degreeOf i ≤ p.zOnly+p.yz+p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=(hF d hd).2.2
 have hi:i=0∨i=1∨i=2:=by omega
 rcases hi with rfl | rfl | rfl <;> omega
theorem exists_small_projection_data (F N R:Poly) (hF:F≠0)
   (p q:FlagDegree) (hFp:PolynomialInFlag p F) (hNq:PolynomialInFlag q N)
   (c:ℕ) [CharP K c] (hdeg:p.zOnly+p.yz+p.all < c)
   (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c):
   ∃ base:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
       SeparableLiteralCoordinate C.1,
     (∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,LiteralProjectionGate C 0)∧
     (∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,LiteralProjectionGate C 2):=by
 have hgate (g:↥(activeFactors F N)) (C:RegularComponent K g.1 N R)
     (i:Fin 3) (hi:Transcendental K (coordinate K C.1 i)):
     letI:Algebra (RatFunc K) (CoordinateField K C.1):=rationalBaseAlgebra K C.1 i hi
     FiniteDimensional (RatFunc K) (CoordinateField K C.1)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1):=by
   have hg:=activeFactors_spec F N g
   have hgdeg (j:Fin 3):g.1.degreeOf j ≤ p.zOnly+p.yz+p.all:=
     (coordinate_degree_le_of_dvd j g.1 F hg.2.1 hF).trans (degreeOf_le_flag_total F p hFp j)
   have hNdeg (j:Fin 3):=degreeOf_le_flag_total N q hNq j
   apply finite_separable_at_of_original_coordinate_gate K C.1 i hi c g.1 N
     hg.1 (regularComponent_G_mem K _ _ _ C) (regularComponent_T_mem K _ _ _ C)
     hg.2.2.1 (fun j↦(hgdeg j).trans_lt hdeg)
   have hprod (u v:Fin 3):N.degreeOf u*g.1.degreeOf v+g.1.degreeOf u*N.degreeOf v ≤
       2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all):=by
     calc
       _ ≤ (q.zOnly+q.yz+q.all)*(p.zOnly+p.yz+p.all)+
           (p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all):=
         Nat.add_le_add (Nat.mul_le_mul (hNdeg u) (hgdeg v))
           (Nat.mul_le_mul (hgdeg u) (hNdeg v))
       _=_:=by ring
   have hi3:i=0∨i=1∨i=2:=by omega
   rcases hi3 with rfl | rfl | rfl
   · rw [coordinateMixedDegree_zero];exact (hprod 1 2).trans_lt hmix
   · rw [coordinateMixedDegree_one];exact (hprod 0 2).trans_lt hmix
   · rw [coordinateMixedDegree_two];exact (hprod 0 1).trans_lt hmix
 refine ⟨fun g C↦Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates C.1
   (regularComponent_ne_point K _ _ _ C) (hgate g C 0) (hgate g C 2)),?_,?_⟩
 · exact fun g C↦hgate g C 0
 · exact fun g C↦hgate g C 2
end
end ProximityPrize.SubmissionLower.RCN084
end PackedLegacy_Y5

/-! Packed from ProximityPrize.SubmissionLower.D1. -/
section PackedLegacy_D1
namespace ProximityPrize.SubmissionLower.RCN206
open scoped Classical BigOperators
open RCN095 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
def surfaceFlag (a b s:ℕ):FlagDegree:=⟨a,b+1,s+2⟩
def fiberFlag (a b s:ℕ):FlagDegree:=⟨a,b+1,s+3⟩
def directionFlag (a b s:ℕ):FlagDegree:=⟨2*a,2*b+1,2*s+3⟩
def centreFlag (a b s:ℕ):FlagDegree:=unitYZFlag+directionFlag a b s
section Cumulative
variable {I:Type*} [Fintype I] (flags:I → FlagDegree) (p:FlagDegree)
 (hs:(∑ i,(flags i).all) ≤ p.all)
 (hm:(∑ i,((flags i).yz+(flags i).all)) ≤ p.yz+p.all)
 (ht:(∑ i,((flags i).zOnly+(flags i).yz+(flags i).all)) ≤ p.zOnly+p.yz+p.all)
include hs hm ht
end Cumulative
end
end ProximityPrize.SubmissionLower.RCN206
end PackedLegacy_D1

/-! Packed from ProximityPrize.SubmissionLower.CommonShearDegreePrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.DD. -/
section PackedLegacy_DD
namespace ProximityPrize.SubmissionLower.RCN023
open scoped Classical BigOperators
open Field RCN002 RCN005 RCN007
noncomputable section
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
variable [IsAlgClosed K]
end
end ProximityPrize.SubmissionLower.RCN023
end PackedLegacy_DD

/-! Packed from ProximityPrize.SubmissionLower.X0. -/
section PackedLegacy_X0
namespace ProximityPrize.SubmissionLower.RCN368
open scoped Classical
noncomputable section
end
end ProximityPrize.SubmissionLower.RCN368
end PackedLegacy_X0

/-! Packed from ProximityPrize.SubmissionLower.I2. -/
section PackedLegacy_I2
namespace ProximityPrize.SubmissionLower.RCN067
open scoped Classical
open RCN002 RCN007
 RCN238
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
local instance _root_.ProximityPrize.SubmissionLower.RCN067.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN067.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
end
end ProximityPrize.SubmissionLower.RCN067
end PackedLegacy_I2

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier17 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DT. -/
section PackedLegacy_DT
namespace ProximityPrize.SubmissionLower.RCN045
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open RCN002 RCN005 RCN006
 RCN007
open RCN136 RCN231 RCN229 RCN313 RCN065 RCN319 RCN238 RCN264 RCN243 RCN306 RCN023 RCN001 RCN008 RCN369 RCN344 RCN368 RCN022 RCN067
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
local instance _root_.ProximityPrize.SubmissionLower.RCN045.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN045.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
variable [IsAlgClosed Ω]
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN045.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN045
end PackedLegacy_DT

/-! Packed from ProximityPrize.SubmissionLower.EO. -/
section PackedLegacy_EO
namespace ProximityPrize.SubmissionLower.RCN142
open RCN002 RCN007 RCN045 RCN023
noncomputable section
variable (K:Type) [Field K] [IsAlgClosed K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem transcendental_add_smul_of_transcendental_isAlgebraic
   (r z:CoordinateField K P) (a:K)
   (hr:Transcendental K r) (hz:IsAlgebraic K z):
   Transcendental K (r+a • z):=by
 intro hs
 apply hr
 have hscaled:IsAlgebraic K (a • z):=hz.smul a
 have hsub:IsAlgebraic K ((r+a • z)-a • z):=hs.sub hscaled
 simpa using hsub
end
end ProximityPrize.SubmissionLower.RCN142
end PackedLegacy_EO

/-! Packed from ProximityPrize.SubmissionLower.CommonShearFiberPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.CommonShearFamilyPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.CommonShearConsumerPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.CommonShearTightPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.L2. -/
section PackedLegacy_L2
namespace ProximityPrize.SubmissionLower.RCN181
open scoped BigOperators
open Set UniqueFactorizationMonoid RCN100 RCN180 RCN137
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
local instance _root_.ProximityPrize.SubmissionLower.RCN181.instStrongNormalizationMonoidPoly4 :StrongNormalizationMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance _root_.ProximityPrize.SubmissionLower.RCN181.instNormalizedGCDMonoidPoly4 :NormalizedGCDMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)
def submoduleReconstructLinear {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K)) :
   V →ₗ[K] Poly4 K :=
 (reconstructLinear (K:=K) D w L s).comp V.subtype
theorem submoduleReconstructLinear_injective {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K)) :
   Function.Injective (submoduleReconstructLinear V):=by
 intro x y h
 apply Subtype.ext
 exact reconstructLinear_injective (K:=K) D w L s h
def commonDivisorProof {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) :
   ∀ v:V,commonGCD V b ∣ submoduleReconstructLinear V v:=by
 intro v
 exact commonGCD_dvd V b v
def commonQuotientLinear {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V)
   (hH:commonGCD V b ≠ 0):V →ₗ[K] Poly4 K :=
 quotientLinear (submoduleReconstructLinear V) (commonGCD V b) hH
   (commonDivisorProof V b)
def quotientDvdSubmodule {V:Type*} [AddCommGroup V] [Module K V]
   (q:V →ₗ[K] Poly4 K) (F:Poly4 K):Submodule K V where
 carrier:={v | F ∣ q v}
 zero_mem':=by simp
 add_mem':=by
   intro x y hx hy
   change F ∣ q x at hx
   change F ∣ q y at hy
   change F ∣ q (x + y)
   rw [map_add]
   exact dvd_add hx hy
 smul_mem':=by
   intro a x hx
   change F ∣ q x at hx
   change F ∣ q (a • x)
   rw [map_smul,MvPolynomial.smul_eq_C_mul]
   exact dvd_mul_of_dvd_right hx _
theorem quotientDvdSubmodule_ne_top {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V)
   (hH:commonGCD V b ≠ 0) (F:Poly4 K) (hF:Irreducible F) :
   quotientDvdSubmodule (commonQuotientLinear V b hH) F ≠ ⊤:=by
 intro htop
 have hall:∀ v:V,F ∣ commonQuotientLinear V b hH v:=by
   intro v
   have hv:v ∈ quotientDvdSubmodule (commonQuotientLinear V b hH) F:=by
     rw [htop]
     trivial
   exact hv
 have hmul:commonGCD V b * F ∣ commonGCD V b:=by
   apply (dvd_commonGCD_iff V b (commonGCD V b * F)).2
   intro v
   have hq:=hall v
   have heq:=recon_eq_mul_quotientPolynomial
     (submoduleReconstructLinear V) (commonGCD V b)
     (commonDivisorProof V b) v
   change commonGCD V b * F ∣ submoduleReconstructLinear V v
   rw [heq]
   exact mul_dvd_mul_left (commonGCD V b) hq
 have hFone:F ∣ (1:Poly4 K):=by
   apply (mul_dvd_mul_iff_left hH).mp
   simpa using hmul
 exact hF.not_isUnit (isUnit_iff_dvd_one.mpr hFone)
theorem exists_common_quotient_isRelPrime {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] [Nonempty ι] (b:Module.Basis ι K V)
   (hH:commonGCD V b ≠ 0) (P:Poly4 K) (hP:P ≠ 0)
   (hcard:(normalizedFactorSet P).card < ENat.card K) :
   ∃ v:V,v ≠ 0 ∧ IsRelPrime (commonQuotientLinear V b hH v) P:=by
 classical
 letI:DecidableEq (Fin 4):=Classical.decEq _
 by_cases hunit:IsUnit P
 · let i:ι:=Classical.choice inferInstance
   refine ⟨b i,b.ne_zero i,hunit.isRelPrime_right⟩
 · let S:=normalizedFactorSet P
   have hSne:S.Nonempty:=by
     obtain ⟨F,hF⟩:=exists_mem_normalizedFactors hP hunit
     exact ⟨F,Multiset.mem_toFinset.mpr hF⟩
   let bad:S → Submodule K V:=fun F ↦
     quotientDvdSubmodule (commonQuotientLinear V b hH) F.1
   have hproper:∀ F:S,bad F ≠ ⊤:=by
     intro F
     exact quotientDvdSubmodule_ne_top V b hH F.1
       (normalizedFactorSet_spec P F.1 F.2).1
   have hsmall:(Finset.univ:Finset S).card < ENat.card K:=by
     simpa [S] using hcard
   have hss:=RCN133.finite_iUnion_ssubset
     (Finset.univ:Finset S) bad hproper hsmall
   obtain ⟨v,hv⟩:=Set.ssubset_univ_iff_nonempty_compl.mp hss
   have havoid:∀ F:S,v ∉ bad F:=by
     intro F hmem
     apply hv
     simp only [Set.mem_iUnion,Finset.mem_univ,true_and]
     exact ⟨F,trivial,hmem⟩
   have hv0:v ≠ 0:=by
     intro hz
     obtain ⟨F,hF⟩:=hSne
     have hnot:=havoid ⟨F,hF⟩
     apply hnot
     subst v
     change F ∣ commonQuotientLinear V b hH 0
     simp
   refine ⟨v,hv0,?_⟩
   apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
   · intro hzero
     exact hP hzero.2
   · intro z hz hzq hzPdiv
     obtain ⟨F,hFnorm,hassoc⟩ :=
       exists_mem_normalizedFactors_of_dvd hP hz hzPdiv
     have hnot:=havoid
       (⟨F,Multiset.mem_toFinset.mpr hFnorm⟩:S)
     apply hnot
     change F ∣ commonQuotientLinear V b hH v
     exact hassoc.dvd_iff_dvd_left.mp hzq
theorem irreducible_positive_degree_sum_fin4
   (F:Poly4 K) (hF:Irreducible F) :
   0 < F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3:=by
 by_contra hn
 have hsum:F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 = 0 :=
   Nat.eq_zero_of_not_pos hn
 have h0:F.degreeOf (0:Fin 4) = 0:=by omega
 have h1:F.degreeOf (1:Fin 4) = 0:=by omega
 have h2:F.degreeOf (2:Fin 4) = 0:=by omega
 have h3:F.degreeOf (3:Fin 4) = 0:=by omega
 have hdeg (i:Fin 4):F.degreeOf i = 0:=by
   fin_cases i
   · simpa using h0
   · simpa using h1
   · simpa using h2
   · simpa using h3
 have heq:F = MvPolynomial.C (F.coeff 0):=by
   apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
   apply Nat.eq_zero_of_le_zero
   rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
   intro d hd
   have hd0:d = 0:=by
     ext i
     have hi:=MvPolynomial.monomial_le_degreeOf i hd
     rw [hdeg i] at hi
     exact Nat.eq_zero_of_le_zero hi
   simp [hd0]
 have hc:F.coeff 0 ≠ 0:=by
   intro hz
   apply hF.ne_zero
   rw [heq,hz,map_zero]
 apply hF.not_isUnit
 rw [heq]
 exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
theorem normalizedFactorSet_card_le_degree_sum_fin4
   (P:Poly4 K) (hP:P ≠ 0) :
   (normalizedFactorSet P).card ≤
     P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3:=by
 classical
 calc
   (normalizedFactorSet P).card =
       ∑ _F ∈ normalizedFactorSet P,(1:ℕ):=by simp
   _ ≤ ∑ F ∈ normalizedFactorSet P,
       (F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3):=by
     apply Finset.sum_le_sum
     intro F hF
     exact irreducible_positive_degree_sum_fin4 F
       (normalizedFactorSet_spec P F hF).1
   _ = (∑ F ∈ normalizedFactorSet P,F.degreeOf 0) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 1) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 2) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 3):=by
     simp only [Finset.sum_add_distrib]
   _ ≤ P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3:=by
     gcongr <;> exact normalizedFactorSet_degree_budget P hP _
theorem degreeOf_X_le_of_mem_flagBox (P:Poly4 K)
   (D w L s:ℕ) (hbox:P ∈ globalCoefficientBox K D w L s) :
   P.degreeOf (0:Fin 4) ≤ D - 1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hc:=(hbox hd).2.2
 omega
theorem normalizedFactorSet_card_le_of_mem_flagBox
   (P:Poly4 K) (D w L s:ℕ) (hw:0 < w) (hP:P ≠ 0)
   (hbox:P ∈ globalCoefficientBox K D w L s) :
   (normalizedFactorSet P).card ≤
     (D - 1) + (D - 1) / w + s + L:=by
 have hsum:=normalizedFactorSet_card_le_degree_sum_fin4 P hP
 have hX:=degreeOf_X_le_of_mem_flagBox P D w L s hbox
 have hY:P.degreeOf (1:Fin 4) ≤ (D - 1) / w:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   apply (Nat.le_div_iff_mul_le hw).mpr
   have hc:=(hbox hd).2.2
   have hm:d 1 * w = w * d 1:=Nat.mul_comm _ _
   omega
 have hR:P.degreeOf (2:Fin 4) ≤ s:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hZ:P.degreeOf (3:Fin 4) ≤ L:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hL:=(hbox hd).1
   omega
 omega
end
end ProximityPrize.SubmissionLower.RCN181
end PackedLegacy_L2

/-! Packed from ProximityPrize.SubmissionLower.L4. -/
section PackedLegacy_L4
namespace ProximityPrize.SubmissionLower.RCN183
open scoped BigOperators
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN130 RCN234 RCN156 RCN081
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance _root_.ProximityPrize.SubmissionLower.RCN183.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN183.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance _root_.ProximityPrize.SubmissionLower.RCN183.instStrongNormalizationMonoidGlobalPoly :StrongNormalizationMonoid GlobalPoly :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance _root_.ProximityPrize.SubmissionLower.RCN183.instNormalizedGCDMonoidGlobalPoly :NormalizedGCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid GlobalPoly
theorem field_cardinality :
   Fintype.card IRSProfile.Field = (2130706433:ℕ) ^ 6:=by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem normalizedFactorSet_card_lt_field_of_mem_flagBox
   (P:GlobalPoly) (D L s:ℕ) (hP:P ≠ 0)
   (hbox:P ∈ globalCoefficientBox IRSProfile.Field D 131071 L s)
   (hsmall:(D - 1) + (D - 1) / 131071 + s + L <
     (2130706433:ℕ) ^ 6) :
   (normalizedFactorSet P).card < ENat.card IRSProfile.Field:=by
 have hle:=normalizedFactorSet_card_le_of_mem_flagBox
   P D 131071 L s (by decide) hP hbox
 rw [ENat.card_eq_coe_fintype_card,field_cardinality]
 exact_mod_cast hle.trans_lt hsmall
theorem commonGCD_mem_flagBox
   {D L s:ℕ}
   (V:Submodule IRSProfile.Field (CoefficientIndex D 131071 L s → IRSProfile.Field))
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field V) :
   commonGCD V b ∈ globalCoefficientBox IRSProfile.Field D 131071 L s:=by
 let i:ι:=Classical.choice inferInstance
 let Q:=reconstruct IRSProfile.Field D 131071 L s (b i).1
 have hQ:Q ≠ 0:=by
   apply reconstruct_ne_zero IRSProfile.Field D 131071 L s
   intro hb
   apply b.ne_zero i
   exact Subtype.ext hb
 exact mem_flagGlobalCoefficientBox_of_dvd (commonGCD V b) Q
   D 131071 L s hQ (commonGCD_dvd_basis V b i)
   (reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s (b i).1)
local instance _root_.ProximityPrize.SubmissionLower.RCN183.instGCDMonoidGlobalPoly :GCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
@[simp] theorem submoduleReconstructLinear_apply
   {D L s:ℕ}
   (V:Submodule IRSProfile.Field
     (CoefficientIndex D 131071 L s → IRSProfile.Field)) (v:V) :
   submoduleReconstructLinear V v =
     reconstruct IRSProfile.Field D 131071 L s v.1:=rfl
end
end ProximityPrize.SubmissionLower.RCN183
end PackedLegacy_L4

/-! Packed from ProximityPrize.SubmissionLower.Y6. -/
section PackedLegacy_Y6
namespace ProximityPrize.SubmissionLower.RCN086
open scoped Classical BigOperators
open RCN313 RCN136 RCN238 RCN053 RCN054 RCN095 RCN207 RCN234 RCN198
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 35000
variable {K Ω:Type} [Field K] [Field Ω]
def tailSelector (d j:ℕ):K:=if j=d then 1 else 0
theorem selected_term_identity (F:MvPolynomial (Fin 4) K) (d:ℕ):
   agreementNumerator F d (tailSelector d) 0 0 0=
     numerator K F d*(-MvPolynomial.X (0:Fin 4))^d:=by
 classical
 unfold agreementNumerator clearedTaylorNumerator
 rw [Finset.sum_eq_single d]
 · simp [commonNumeratorTerm,tailSelector,affineSeedPolynomial]
 · intro j _ hj
   simp [commonNumeratorTerm,tailSelector,hj]
 · intro hd
   exact (hd (Finset.mem_range.mpr (Nat.lt_succ_self d))).elim
def globalTailCut (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (d:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (agreementNumerator F d (tailSelector d) 0 0 0)
theorem globalTailCut_eq (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (d:ℕ):
   globalTailCut φ F d=
     surfaceMap φ (numerator K F d)*MvPolynomial.C ((-φ Polynomial.X)^d):=by
 simp [globalTailCut,selected_term_identity,map_mul,map_pow,map_neg]
theorem tail_scalar_ne_zero (φ:Polynomial K →+*Ω)
   (hφ:Function.Injective φ) (d:ℕ):(-φ Polynomial.X)^d≠0:=by
 apply pow_ne_zero
 apply neg_ne_zero.mpr
 intro h
 have hX:(Polynomial.X:Polynomial K)=0:=hφ (by simpa using h)
 exact Polynomial.X_ne_zero hX
theorem globalTailCut_dvd_iff (φ:Polynomial K →+*Ω)
   (hφ:Function.Injective φ) (F:MvPolynomial (Fin 4) K) (d:ℕ)
   (G:MvPolynomial (Fin 3) Ω):
   G∣globalTailCut φ F d ↔ G∣surfaceMap φ (numerator K F d):=by
 rw [globalTailCut_eq]
 let c:Ω:=(-φ Polynomial.X)^d
 have hc:c≠0:=tail_scalar_ne_zero φ hφ d
 constructor
 · intro h
   have hh:=h.mul_right (MvPolynomial.C c⁻¹)
   simpa only [c,mul_assoc, ←map_mul,mul_inv_cancel₀ hc,map_one,mul_one] using hh
 · intro h
   exact h.mul_right _
theorem selected_globalTailCut_zero (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ) (globalTailCut φ F (w+1))=0:=by
 rw [globalTailCut_eq,map_mul]
 have hzero:=RCN068.selected_firstTail_zero φ F selected γ w hdegree hsolution
 change MvPolynomial.aeval _ (surfaceMap φ (numerator K F (w+1)))=0 at hzero
 rw [hzero,zero_mul]
theorem exists_filtered_certificate (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (d:ℕ) (hd:2 ≤ d) (coeffs:ℕ → K) (x u0 u1:K):
   ∃ (B:Fin (d-1+1) → MvPolynomial (Fin 3) Ω)
     (c:Fin (d-1+1) → FlagDegree),
     surfaceMap φ (agreementNumerator F d coeffs x u0 u1)=
       filteredCut (d-1) B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F))∧
     (∀ j,PolynomialInFlag (c j) (B j))∧
     (∀ j,c j+(d-1-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
       j.val • (⟨a,b,s+3⟩:FlagDegree)=center a b s+(d-1) • direction a b s):=by
 classical
 let B0:=fun j => surfaceMap φ (agreementCoefficients F d coeffs x u0 u1 j)
 refine ⟨(fun j => B0 j.val),(fun j => coefficientFlag a (b+1) (s+2) d j.val),?_,?_,?_⟩
 · rw [surfaceMap_agreementNumerator_eq_coefficient_sum φ F d hd]
   have hk:d-1+1=d:=by omega
   calc
     _=∑ j:Fin (d-1+1),surfaceMap φ (polyH K F)^(d-1-j.val)*
         surfaceMap φ (polyG K F)^j.val*B0 j.val:=by
       let f:=fun j:ℕ => surfaceMap φ (polyH K F)^(d-1-j)*
         surfaceMap φ (polyG K F)^j*B0 j
       change (∑ j∈Finset.range d,f j)=∑ j:Fin (d-1+1),f j.val
       rw [Finset.sum_range]
       let E:Fin d ≃ Fin (d-1+1):={
         toFun:=fun j => ⟨j.val,by have:=j.isLt;omega⟩
         invFun:=fun j => ⟨j.val,by have:=j.isLt;omega⟩
         left_inv:=fun j => rfl
         right_inv:=fun j => rfl}
       exact Fintype.sum_equiv E _ _ (fun _ => rfl)
     _=_:=by
       unfold filteredCut
       apply Finset.sum_congr rfl
       intro j _
       ring
 · intro j
   apply surfaceMap_agreementCoefficients_in_flag φ F a (b+1) (s+2)
     (by omega) (by omega) hR (by omega) (by omega) d hd coeffs x u0 u1 j.val
   have:=j.isLt
   omega
 · intro j
   have hj:j.val<d:=by have:=j.isLt;omega
   have h:=coefficientFlag_add_baseMonomial a (b+1) (s+2) d j.val
     (by omega) (by omega) hj
   rw [(shifted_flags a b s).1,(shifted_flags a b s).2.1,
     (shifted_flags a b s).2.2] at h
   refine h.trans ?_
   have hk:d-1+1=d:=by omega
   simpa only [hk] using class_total a b s (d-1)
theorem globalTailCut_certificate (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (w:ℕ) (hw:1 ≤ w):
   ∃ (B:Fin (w+1) → MvPolynomial (Fin 3) Ω)
     (c:Fin (w+1) → FlagDegree),
     globalTailCut φ F (w+1)=
       filteredCut w B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F))∧
     (∀ j,PolynomialInFlag (c j) (B j))∧
     (∀ j,c j+(w-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
       j.val • (⟨a,b,s+3⟩:FlagDegree)=center a b s+w • direction a b s):=by
 have h:=exists_filtered_certificate φ a b s F hR hYR hAll (w+1) (by omega)
   (tailSelector (w+1)) 0 0 0
 rw [show w+1-1=w by omega] at h
 exact h
end
end ProximityPrize.SubmissionLower.RCN086
end PackedLegacy_Y6

/-! Packed from ProximityPrize.SubmissionLower.FD. -/
section PackedLegacy_FD
namespace ProximityPrize.SubmissionLower.RCN212
open scoped Classical BigOperators WithZero
open RCN133 RCN184 RCN295 RCN095 RCN187
noncomputable section
set_option maxHeartbeats 1000000
def liftExponent (d:Fin 3 →₀ ℕ):Fin 4 →₀ ℕ:=
 Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+Finsupp.single 2 (d 2)
def shiftExponent (d:Fin 3 →₀ ℕ):Fin 4 →₀ ℕ:=
 liftExponent d+Finsupp.single 3 1
abbrev quadraticSupport:=flagSupport (2 • unitAllFlag)
abbrev linearSupport:=flagSupport unitYZFlag
def movingSupport:Finset (Fin 4 →₀ ℕ):=
 quadraticSupport.image liftExponent ∪ linearSupport.image shiftExponent
theorem liftExponent_injective:Function.Injective liftExponent:=by
 intro d e h
 ext i
 have hh:=DFunLike.congr_fun h i.castSucc
 fin_cases i <;> simpa [liftExponent] using hh
theorem shiftExponent_injective:Function.Injective shiftExponent:=by
 intro d e h
 exact liftExponent_injective (add_right_cancel h)
theorem mem_movingSupport (d:Fin 4 →₀ ℕ):
   d∈movingSupport ↔ d 0+d 1+d 2+d 3 ≤ 2∧d 3 ≤ 1∧d 1+2*d 3 ≤ 2:=by
 classical
 constructor
 · intro hd
   rcases Finset.mem_union.mp hd with hd | hd
   · obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hd
     have he:=(mem_flagSupport_iff _ _).mp he
     simp only [InFlag,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag] at he
     simp [liftExponent]
     omega
   · obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hd
     have he:=(mem_flagSupport_iff _ _).mp he
     simp only [InFlag,unitYZFlag] at he
     simp [shiftExponent,liftExponent]
     omega
 · rintro ⟨ht,hw,hr⟩
   let e:=exponentOfTriple (d 0,d 1,d 2)
   have heq0:e 0=d 0∧e 1=d 1∧e 2=d 2:=by simp [e,exponentOfTriple]
   have hdw:d 3=0∨d 3=1:=by omega
   rcases hdw with hdw | hdw
   · apply Finset.mem_union_left
     refine Finset.mem_image.mpr ⟨e,?_,?_⟩
     · rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag,heq0.1,heq0.2.1,heq0.2.2]
       omega
     · ext i;fin_cases i <;> simp [liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]
   · apply Finset.mem_union_right
     refine Finset.mem_image.mpr ⟨e,?_,?_⟩
     · rw [mem_flagSupport_iff]
       simp [InFlag,unitYZFlag,heq0.1,heq0.2.1,heq0.2.2]
       omega
     · ext i;fin_cases i <;> simp [shiftExponent,liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]
theorem movingSupport_downwardClosed:ExponentSetDownwardClosed movingSupport:=by
 intro d hd e he
 rw [mem_movingSupport] at hd ⊢
 have h0:=he 0;have h1:=he 1;have h2:=he 2;have h3:=he 3
 omega
theorem zero_mem_movingSupport:(0:Fin 4 →₀ ℕ)∈movingSupport:=by
 simp [mem_movingSupport]
def quadraticIndex (d:quadraticSupport):movingSupport:=
 ⟨liftExponent d.1,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
def linearIndex (d:linearSupport):movingSupport:=
 ⟨shiftExponent d.1,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
theorem quadraticIndex_injective:Function.Injective quadraticIndex:=
 fun _ _ h↦Subtype.ext (liftExponent_injective (congrArg Subtype.val h))
theorem linearIndex_injective:Function.Injective linearIndex:=
 fun _ _ h↦Subtype.ext (shiftExponent_injective (congrArg Subtype.val h))
def supportIndex:quadraticSupport ⊕ linearSupport → movingSupport:=
 Sum.elim quadraticIndex linearIndex
theorem supportIndex_bijective:Function.Bijective supportIndex:=by
 constructor
 · intro d e h
   cases d with
   | inl d =>
     cases e with
     | inl e => exact congrArg Sum.inl (quadraticIndex_injective h)
     | inr e => have hh:=DFunLike.congr_fun (congrArg Subtype.val h) 3
                simp [supportIndex,quadraticIndex,linearIndex,liftExponent,shiftExponent] at hh
   | inr d =>
     cases e with
     | inl e => have hh:=DFunLike.congr_fun (congrArg Subtype.val h) 3
                simp [supportIndex,quadraticIndex,linearIndex,liftExponent,shiftExponent] at hh
     | inr e => exact congrArg Sum.inr (linearIndex_injective h)
 · intro d
   rcases Finset.mem_union.mp d.2 with hd | hd
   · obtain ⟨e,he,h⟩:=Finset.mem_image.mp hd
     exact ⟨Sum.inl ⟨e,he⟩,Subtype.ext h⟩
   · obtain ⟨e,he,h⟩:=Finset.mem_image.mp hd
     exact ⟨Sum.inr ⟨e,he⟩,Subtype.ext h⟩
variable {K L:Type*} [Field K] [Field L] [Algebra K L]
def restrictQ:(movingSupport → K) →ₗ[K] (quadraticSupport → K):=
 LinearMap.funLeft K K quadraticIndex
def restrictU:(movingSupport → K) →ₗ[K] (linearSupport → K):=
 LinearMap.funLeft K K linearIndex
theorem restrictU_surjective:Function.Surjective (restrictU (K:=K)):=
 LinearMap.funLeft_surjective_of_injective K K _ linearIndex_injective
def quadraticPolynomial (c:movingSupport → K):=polynomialOfSupport quadraticSupport (restrictQ c)
def linearPolynomial (c:movingSupport → K):=polynomialOfSupport linearSupport (restrictU c)
theorem quadraticPolynomial_inFlag (c:movingSupport → K):
   PolynomialInFlag (2 • unitAllFlag) (quadraticPolynomial c):=
 (support_subset_flagSupport_iff _ _).mp (support_polynomialOfSupport_subset _ _)
theorem linearPolynomial_inFlag (c:movingSupport → K):
   PolynomialInFlag unitYZFlag (linearPolynomial c):=
 (support_subset_flagSupport_iff _ _).mp (support_polynomialOfSupport_subset _ _)
def movingCoordinates (x:Fin 3 → L) (w:L):Fin 4 → L:=![x 0,x 1,x 2,w]
theorem evaluation_lift (x:Fin 3 → L) (w:L) (d:Fin 3 →₀ ℕ) (a:K):
   MvPolynomial.eval₂Hom (algebraMap K L) (movingCoordinates x w)
     (MvPolynomial.monomial (liftExponent d) a)=
   MvPolynomial.eval₂Hom (algebraMap K L) x (MvPolynomial.monomial d a):=by
 simp [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,Fin.prod_univ_four,
   Fin.prod_univ_three,liftExponent,movingCoordinates]
theorem evaluation_shift (x:Fin 3 → L) (w:L) (d:Fin 3 →₀ ℕ) (a:K):
   MvPolynomial.eval₂Hom (algebraMap K L) (movingCoordinates x w)
     (MvPolynomial.monomial (shiftExponent d) a)=
   MvPolynomial.eval₂Hom (algebraMap K L) x (MvPolynomial.monomial d a)*w:=by
 simp [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,Fin.prod_univ_four,
   Fin.prod_univ_three,shiftExponent,liftExponent,movingCoordinates,mul_assoc]
theorem coefficientEvaluation_eq (x:Fin 3 → L) (w:L) (c:movingSupport → K):
   coefficientEvaluation (movingCoordinates x w) movingSupport c=
     MvPolynomial.eval₂Hom (algebraMap K L) x (quadraticPolynomial c)+
     MvPolynomial.eval₂Hom (algebraMap K L) x (linearPolynomial c)*w:=by
 let e:=Equiv.ofBijective supportIndex supportIndex_bijective
 change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _)=_
 simp only [polynomialOfSupport,map_sum]
 rw [←e.sum_comp]
 simp only [Fintype.sum_sum_type,e,Equiv.ofBijective_apply,supportIndex,Sum.elim_inl,
   Sum.elim_inr,quadraticIndex,linearIndex]
 simp only [evaluation_lift,evaluation_shift]
 simp [quadraticPolynomial,linearPolynomial,polynomialOfSupport,map_sum,
   Finset.sum_mul,restrictQ,restrictU,LinearMap.funLeft,quadraticIndex,linearIndex]
theorem coordinate_mem (i:Fin 3):Finsupp.single i.castSucc 1∈movingSupport:=by
 fin_cases i <;> simp [mem_movingSupport]
theorem exists_coordinate_evaluation (x:Fin 3 → L) (w:L) (i:Fin 3):
   ∃ c:movingSupport → K,
     coefficientEvaluation (movingCoordinates x w) movingSupport c=x i:=by
 refine ⟨deltaCoefficient movingSupport ⟨Finsupp.single i.castSucc 1,coordinate_mem i⟩,?_⟩
 change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _)=_
 rw [polynomialOfSupport_deltaCoefficient]
 fin_cases i <;> simp [MvPolynomial.eval₂Hom_monomial,movingCoordinates]
theorem exponentSetPoleWeight_moving (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (w:L):
   exponentSetPoleWeight v (movingCoordinates x w) movingSupport=
     max (2*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))+poleOrder v w):=by
 let q:Fin 4 → ℤ:=fun i↦poleOrder v (movingCoordinates x w i)
 let a:=max (q 1) (max (q 0) (q 2))
 let b:=max (q 0) (q 2)
 have hq:∀ i,0 ≤ q i:=fun i↦le_max_left _ _
 have ha0:q 0 ≤ a:=(le_max_left _ _).trans (le_max_right _ _)
 have ha1:q 1 ≤ a:=le_max_left _ _
 have ha2:q 2 ≤ a:=(le_max_right _ _).trans (le_max_right _ _)
 have hb0:q 0 ≤ b:=le_max_left _ _
 have hb2:q 2 ≤ b:=le_max_right _ _
 have ha:0 ≤ a:=(hq 1).trans ha1
 change exponentSetPoleWeight v (movingCoordinates x w) movingSupport=max (2*a) (b+q 3)
 have hweight (d:Fin 4 →₀ ℕ):exponentPoleWeight v (movingCoordinates x w) d=
     (d 0:ℤ)*q 0+(d 1:ℤ)*q 1+(d 2:ℤ)*q 2+(d 3:ℤ)*q 3:=by
   simp [exponentPoleWeight,Fin.sum_univ_four,q]
 apply le_antisymm
 · unfold exponentSetPoleWeight
   apply Finset.max'_le
   intro z hz
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact (by omega:0 ≤ 2*a).trans (le_max_left _ _)
   obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   rcases (mem_movingSupport d).mp hd with ⟨ht,hw,hr⟩
   rw [hweight]
   have hdw:d 3=0∨d 3=1:=by omega
   rcases hdw with hdw | hdw
   · have ht':(d 0:ℤ)+d 1+d 2 ≤ 2:=by exact_mod_cast (by omega:d 0+d 1+d 2 ≤ 2)
     have h0:=mul_le_mul_of_nonneg_left ha0 (Int.natCast_nonneg (d 0))
     have h1:=mul_le_mul_of_nonneg_left ha1 (Int.natCast_nonneg (d 1))
     have h2:=mul_le_mul_of_nonneg_left ha2 (Int.natCast_nonneg (d 2))
     simp only [hdw,Nat.cast_zero,zero_mul,add_zero]
     apply le_trans _ (le_max_left _ _)
     nlinarith
   · have hd1:d 1=0:=by omega
     have ht':(d 0:ℤ)+d 2 ≤ 1:=by exact_mod_cast (by omega:d 0+d 2 ≤ 1)
     have hb:0 ≤ b:=(hq 0).trans hb0
     have h0:=mul_le_mul_of_nonneg_left hb0 (Int.natCast_nonneg (d 0))
     have h2:=mul_le_mul_of_nonneg_left hb2 (Int.natCast_nonneg (d 2))
     simp only [hdw,hd1,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero]
     apply le_trans _ (le_max_right _ _)
     nlinarith
 · have hmem (d:Fin 4 →₀ ℕ) (hd:d∈movingSupport):
       exponentPoleWeight v (movingCoordinates x w) d ≤
         exponentSetPoleWeight v (movingCoordinates x w) movingSupport:=by
     apply Finset.le_max'
     exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
   have hs (i:Fin 3):2*q i.castSucc ≤ exponentSetPoleWeight v (movingCoordinates x w) movingSupport:=by
     have hm:Finsupp.single i.castSucc 2∈movingSupport:=by fin_cases i <;> simp [mem_movingSupport]
     have hh:=hmem _ hm
     fin_cases i <;> simpa [hweight] using hh
   have hw (i:Fin 3) (hi:i=0∨i=2):q i.castSucc+q 3 ≤
       exponentSetPoleWeight v (movingCoordinates x w) movingSupport:=by
     have hm:Finsupp.single i.castSucc 1+Finsupp.single 3 1∈movingSupport:=by
       rcases hi with rfl | rfl <;> simp [mem_movingSupport]
     have hh:=hmem _ hm
     rcases hi with rfl | rfl <;> simpa [hweight] using hh
   have hs0:=hs 0;have hs1:=hs 1;have hs2:=hs 2
   have hw0:=hw 0 (Or.inl rfl);have hw2:=hw 2 (Or.inr rfl)
   dsimp [a,b] at*
   omega
end
end ProximityPrize.SubmissionLower.RCN212
end PackedLegacy_FD

/-! Packed from ProximityPrize.SubmissionLower.EJ. -/
section PackedLegacy_EJ
namespace ProximityPrize.SubmissionLower.RCN134
open scoped BigOperators
open RCN002
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
def embeddingPoint (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] L):Fin 3 → L:=
 fun i => f (coordinate K P i)
theorem embeddingPoint_aeval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] L):
   MvPolynomial.aeval (embeddingPoint P f)=
     f.comp (coordinateEvaluation K P):=by
 apply MvPolynomial.algHom_ext
 intro i
 simp only [MvPolynomial.aeval_X,AlgHom.comp_apply,embeddingPoint,coordinate]
theorem embeddingPoint_kernel (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] L):
   RingHom.ker (MvPolynomial.aeval (embeddingPoint P f)).toRingHom=P:=by
 rw [embeddingPoint_aeval]
 change RingHom.ker (f.toRingHom.comp
   (coordinateEvaluation K P).toRingHom)=P
 rw [RingHom.ker_comp_of_injective _ f.injective,coordinateEvaluation_ker]
theorem embeddingPoint_injective (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]:
   Function.Injective (embeddingPoint (L:=L) P):=by
 intro f g hfg
 have he:f.comp (coordinateEvaluation K P)=
     g.comp (coordinateEvaluation K P):=by
   rw [←embeddingPoint_aeval, ←embeddingPoint_aeval,hfg]
 apply IsLocalization.algHom_ext (nonZeroDivisors (CoordinateRing K P))
 apply AlgHom.ext
 intro a
 obtain ⟨A,rfl⟩:=Ideal.Quotient.mk_surjective a
 exact AlgHom.congr_fun he A
variable {I:Type} (P:I → Ideal (MvPolynomial (Fin 3) K))
 [∀ i,(P i).IsPrime]
section CommonBase
variable {B:Type} [Field B] [Algebra K B] [Algebra B L]
 [IsScalarTower K B L]
 [∀ i,Algebra B (CoordinateField K (P i))]
 [∀ i,IsScalarTower K B (CoordinateField K (P i))]
def commonBaseEmbeddingPoint
   (z:Σ i,CoordinateField K (P i) →ₐ[B] L):Fin 3 → L:=
 embeddingPoint (P z.1) (z.2.restrictScalars K)
theorem commonBaseEmbeddingPoint_injective (hP:Function.Injective P):
   Function.Injective (commonBaseEmbeddingPoint (B:=B) (L:=L) P):=by
 rintro ⟨i,f⟩ ⟨j,g⟩ hfg
 have hij:P i=P j:=by
   rw [←embeddingPoint_kernel (P i) (f.restrictScalars K),
     ←embeddingPoint_kernel (P j) (g.restrictScalars K)]
   exact congrArg (fun v:Fin 3 → L =>
     RingHom.ker (MvPolynomial.aeval v).toRingHom) hfg
 obtain rfl:=hP hij
 have hr:f.restrictScalars K=g.restrictScalars K:=
   embeddingPoint_injective (P i) hfg
 have hf:f=g:=by
   apply AlgHom.ext
   intro a
   exact AlgHom.congr_fun hr a
 cases hf
 rfl
variable [Fintype I] [IsAlgClosed L]
 [∀ i,FiniteDimensional B (CoordinateField K (P i))]
 [∀ i,Algebra.IsSeparable B (CoordinateField K (P i))]
def genericFiberPoints:Finset (Fin 3 → L):=by
 classical
 exact Finset.univ.image (commonBaseEmbeddingPoint (B:=B) (L:=L) P)
theorem genericFiberPoints_card (hP:Function.Injective P):
   (genericFiberPoints (B:=B) (L:=L) P).card=
     ∑ i,Module.finrank B (CoordinateField K (P i)):=by
 classical
 rw [genericFiberPoints,
   Finset.card_image_of_injective _ (commonBaseEmbeddingPoint_injective P hP)]
 simp only [Finset.card_univ,Fintype.card_sigma,AlgHom.card]
end CommonBase
end
end ProximityPrize.SubmissionLower.RCN134
end PackedLegacy_EJ

/-! Packed from ProximityPrize.SubmissionLower.D3. -/
section PackedLegacy_D3
namespace ProximityPrize.SubmissionLower.RCN208
open scoped Classical
open RCN002 RCN072 RCN264 RCN022 RCN207 RCN134
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {K L:Type} [Field K] [Field L]
def coordinateFieldMap (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (ev:MvPolynomial (Fin 3) K →+*L) (hker:RingHom.ker ev=P):
   CoordinateField K P →+*L:=
 let hz:∀ A,A∈P → ev A=0:=fun A hA↦by
   exact RingHom.mem_ker.mp (hker.symm ▸ hA)
 IsFractionRing.lift (K:=CoordinateField K P)
   (RingHom.lift_injective_of_ker_le_ideal P hz hker.le)
theorem coordinateFieldMap_eval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (ev:MvPolynomial (Fin 3) K →+*L) (hker:RingHom.ker ev=P)
   (A:MvPolynomial (Fin 3) K):
   coordinateFieldMap P ev hker (coordinateEvaluation K P A)=ev A:=by
 unfold coordinateFieldMap
 change IsFractionRing.lift _
   (algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P A))=ev A
 rw [IsFractionRing.lift_algebraMap,Ideal.Quotient.lift_mk]
def movingValue (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G Q U:MvPolynomial (Fin 3) K):CoordinateField K P:=
 coordinateEvaluation K P Q+
   coordinateEvaluation K P U*coordinateEvaluation K P G/
     coordinateEvaluation K P H
def scalarPolynomialMap (K E:Type) [Field K] [Field E] [Algebra K E]:
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 3) E:=
 MvPolynomial.map (algebraMap K E)
theorem comap_le_of_embedding_point {E:Type} [Field E] [Algebra K E]
   (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] E) (D:Ideal (MvPolynomial (Fin 3) E))
   (hD:D ≤ RingHom.ker
     (MvPolynomial.aeval (embeddingPoint P f):MvPolynomial (Fin 3) E →ₐ[E] E).toRingHom):
   D.comap (scalarPolynomialMap K E) ≤ P:=by
 intro A hA
 rw [←embeddingPoint_kernel P f]
 apply RingHom.mem_ker.mpr
 have hv:=RingHom.mem_ker.mp (hD hA)
 simpa only [MvPolynomial.aeval_eq_eval₂Hom,scalarPolynomialMap,
   MvPolynomial.eval₂Hom_map_hom,Algebra.algebraMap_self,RingHom.id_comp,
   AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hv
end
end ProximityPrize.SubmissionLower.RCN208
end PackedLegacy_D3

/-! Packed from ProximityPrize.SubmissionLower.A9. -/
section PackedLegacy_A9
namespace ProximityPrize.SubmissionLower.RCN064
open scoped Classical BigOperators WithZero
open RCN212 RCN184 RCN133 RCN295 RCN095 RCN114 RCN187 RCN344 RCN002 RCN005 RCN006 RCN341 RCN044 RCN037 RCN207 RCN208 RCN264 RCN042 RCN035 RCN022
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
public theorem exact_of_avoids {K L σ:Type*} [Field K] [Field L]
   [Algebra K L] [Fintype σ] [DecidableEq σ]
   (v:RCN345.NormalizedValuation K L) (x:σ → L)
   (E:Finset (σ →₀ ℕ)) (c:E → K)
   (hc:c∉cancellationSubmodule v.val (constant_value_le_one K L v) x E):
   v.val (coefficientEvaluation x E c)=WithZero.exp (exponentSetPoleWeight v.val x E):=by
 apply le_antisymm
 · exact valuation_eval_le_exp_exponentSet v.val (algebraMap K L)
     (constant_value_le_one K L v) x E _ (support_polynomialOfSupport_subset _ _)
 · exact le_of_not_gt hc
theorem exists_common_coefficients {K I:Type*} [Field K] [Infinite K] [Finite I]
   (L:I → Type*) [∀ i,Field (L i)] [∀ i,Algebra K (L i)]
   (x:∀ i,Fin 3 → L i) (w:∀ i,L i) (index:I → Fin 3)
   (hd:∀ i,KaehlerDifferential.D K (L i) (x i (index i))≠0)
   (V:∀ i,Finset (RCN345.NormalizedValuation K (L i))):
   ∃ c:movingSupport → K,∀ i,
     coefficientEvaluation (x i) linearSupport (restrictU c)≠0∧
     KaehlerDifferential.D K (L i)
       (coefficientEvaluation (movingCoordinates (x i) (w i)) movingSupport c)≠0∧
     ∀ v∈V i,
       v.val (coefficientEvaluation (movingCoordinates (x i) (w i)) movingSupport c)=
         WithZero.exp (max (2*max (poleOrder v.val (x i 1))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))+poleOrder v.val (w i)))∧
       v.val (coefficientEvaluation (x i) linearSupport (restrictU c))=
         WithZero.exp (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))):=by
 classical
 let evJ i:=coefficientEvaluation (K:=K) (movingCoordinates (x i) (w i)) movingSupport
 let evU i:=(coefficientEvaluation (K:=K) (x i) linearSupport).comp restrictU
 let Extra:=I × Bool
 let Pole:=Sigma fun i:I↦{v//v∈V i} × Bool
 let bad:Extra ⊕ Pole → Submodule K (movingSupport → K)
   | Sum.inl (i,false) => LinearMap.ker (evU i)
   | Sum.inl (i,true) => LinearMap.ker ((KaehlerDifferential.D K (L i)).toLinearMap.comp (evJ i))
   | Sum.inr ⟨i,v,false⟩ => (cancellationSubmodule v.1.val
       (constant_value_le_one K (L i) v.1) (x i) linearSupport).comap restrictU
   | Sum.inr ⟨i,v,true⟩ => cancellationSubmodule v.1.val
       (constant_value_le_one K (L i) v.1) (movingCoordinates (x i) (w i)) movingSupport
 have hbad:∀ j,bad j≠⊤:=by
   rintro (⟨i,b⟩ | ⟨i,v,b⟩)
   · cases b
     · obtain ⟨c,hc⟩:=restrictU_surjective (K:=K)
         (deltaCoefficient linearSupport ⟨0,zero_mem_flagSupport _⟩)
       have hone:evU i c=1:=by
         change coefficientEvaluation (x i) linearSupport (restrictU c)=1
         rw [hc]
         change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _)=_
         rw [polynomialOfSupport_deltaCoefficient]
         simp
       intro ht
       have hz:evU i c=0:=LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,false));rw [ht];trivial)
       exact one_ne_zero (hone.symm.trans hz)
     · obtain ⟨c,hc⟩:=exists_coordinate_evaluation (K:=K) (x i) (w i) (index i)
       intro ht
       have hz:KaehlerDifferential.D K (L i) (evJ i c)=0:=
         LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,true));rw [ht];trivial)
       exact hd i (hc ▸ hz)
   · cases b
     · obtain ⟨d,hd⟩:=exists_exact_support_evaluation_of_downwardClosed (K:=K)
         v.1.val (x i) linearSupport (flagSupport_downwardClosed _) (zero_mem_flagSupport _)
       obtain ⟨c,hc⟩:=restrictU_surjective (K:=K) d
       intro ht
       have hm:c∈bad (Sum.inr ⟨i,v,false⟩):=by rw [ht];trivial
       change v.1.val (coefficientEvaluation (x i) linearSupport (restrictU c)) < _ at hm
       rw [hc,hd] at hm
       exact lt_irrefl _ hm
     · obtain ⟨c,hc⟩:=exists_exact_support_evaluation_of_downwardClosed (K:=K)
         v.1.val (movingCoordinates (x i) (w i)) movingSupport
         movingSupport_downwardClosed zero_mem_movingSupport
       exact cancellationSubmodule_ne_top_of_exact _ _ _ _ c hc
 obtain ⟨c,hc⟩:=exists_avoiding_finite_proper_submodules bad hbad
 refine ⟨c,fun i↦⟨?_,?_,?_⟩⟩
 · exact hc (Sum.inl (i,false))
 · exact hc (Sum.inl (i,true))
 · intro v hv
   have hj:=exact_of_avoids v (movingCoordinates (x i) (w i)) movingSupport c
     (hc (Sum.inr ⟨i,⟨v,hv⟩,true⟩))
   have hu:=exact_of_avoids v (x i) linearSupport (restrictU c)
     (hc (Sum.inr ⟨i,⟨v,hv⟩,false⟩))
   rw [exponentSetPoleWeight_moving] at hj
   rw [exponentSetPoleWeight_unitYZ] at hu
   exact ⟨hj,hu⟩
variable {K:Type} [Field K] [IsAlgClosed K]
def movingRelevantPlaces {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P) (w:CoordinateField K P):
   Finset (Place K (CoordinateField K P)):=by
 letI:=polynomialBaseAlgebra K P D.index
 letI:=rationalBaseAlgebra K P D.index D.transcendental
 letI:=polynomialBaseScalarTower K P D.index
 letI:=polynomialRationalScalarTower K P D.index D.transcendental
 letI:=rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=D.separable
 exact literalRelevantPlaces D ∪ if hw:w≠0 then
   RCN026.placesFor K (CoordinateField K P) w hw else ∅
theorem outside_movingRelevantPlaces {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P) (w:CoordinateField K P)
   (v:Place K (CoordinateField K P)) (hv:v∉movingRelevantPlaces D w):
   (∀ i,poleOrder v.val (coordinate K P i)=0)∧poleOrder v.val w=0:=by
 letI:=polynomialBaseAlgebra K P D.index
 letI:=rationalBaseAlgebra K P D.index D.transcendental
 letI:=polynomialBaseScalarTower K P D.index
 letI:=polynomialRationalScalarTower K P D.index D.transcendental
 letI:=rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=D.separable
 constructor
 · exact coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant D v
     (fun h↦hv (Finset.mem_union_left _ h))
 · by_cases hw:w=0
   · simp [hw,poleOrder]
   have horder:RCN026.order K (CoordinateField K P) v w=0:=by
     by_contra hn
     apply hv
     apply Finset.mem_union_right
     simp only [dif_pos hw]
     exact RCN026.placesFor_covers K (CoordinateField K P) w hw v hn
   simp only [RCN026.order] at horder
   simp [poleOrder,show (v.val w).log=0 by omega]
def movingRatio (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G:MvPolynomial (Fin 3) K):CoordinateField K P:=
 coordinateEvaluation K P G/coordinateEvaluation K P H
def movingPoleTarget (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G:MvPolynomial (Fin 3) K) (v:Place K (CoordinateField K P)):ℤ:=
 max (2*max (poleOrder v.val (coordinate K P 1))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))+
     poleOrder v.val (movingRatio P H G))
public theorem field_eval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (A:MvPolynomial (Fin 3) K):
   MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K P)) (coordinate K P) A=
     coordinateEvaluation K P A:=by
 rw [coordinateEvaluation_eq_aeval]
 exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm
theorem exists_common_original_projection (F A H G:MvPolynomial (Fin 3) K)
   (base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1):
   ∃ Q U:MvPolynomial (Fin 3) K,
     PolynomialInFlag (2 • unitAllFlag) Q∧PolynomialInFlag unitYZFlag U∧
     ∀ C:RegularComponent K F A H,
       U∉C.1∧KaehlerDifferential.D K (CoordinateField K C.1)
         (movingValue C.1 H G Q U)≠0∧
       (∀ v:Place K (CoordinateField K C.1),
         poleOrder v.val (movingValue C.1 H G Q U)=movingPoleTarget C.1 H G v)∧
       (∀ v∈movingRelevantPlaces (base C) (movingRatio C.1 H G),
         v.val (coordinateEvaluation K C.1 U)=
           WithZero.exp (max (poleOrder v.val (coordinate K C.1 0))
             (poleOrder v.val (coordinate K C.1 2)))):=by
 classical
 obtain ⟨c,hc⟩:=exists_common_coefficients (K:=K)
   (fun C:RegularComponent K F A H↦CoordinateField K C.1)
   (fun C↦coordinate K C.1) (fun C↦movingRatio C.1 H G)
   (fun C↦(base C).index) (fun C↦base_differential_ne_zero (base C))
   (fun C↦movingRelevantPlaces (base C) (movingRatio C.1 H G))
 let Q:=quadraticPolynomial c
 let U:=linearPolynomial c
 have hJ (C:RegularComponent K F A H):
     coefficientEvaluation (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G))
       movingSupport c=movingValue C.1 H G Q U:=by
   rw [coefficientEvaluation_eq,field_eval,field_eval]
   simp only [movingValue,movingRatio,Q,U,mul_div_assoc]
 have hU (C:RegularComponent K F A H):
     coefficientEvaluation (coordinate K C.1) linearSupport (restrictU c)=
       coordinateEvaluation K C.1 U:=field_eval C.1 U
 refine ⟨Q,U,quadraticPolynomial_inFlag c,linearPolynomial_inFlag c,fun C↦?_⟩
 have h:=hc C
 rw [hU C,hJ C] at h
 refine ⟨?_,h.2.1,?_,fun v hv↦(h.2.2 v hv).2⟩
 · intro hmem
   apply h.1
   apply RingHom.mem_ker.mp
   change U∈RingHom.ker (coordinateEvaluation K C.1).toRingHom
   rwa [coordinateEvaluation_ker]
 · intro v
   by_cases hv:v∈movingRelevantPlaces (base C) (movingRatio C.1 H G)
   · exact poleOrder_eq_of_valuation_eq_exp v.val _ _
       (by dsimp [movingPoleTarget,poleOrder];positivity) (h.2.2 v hv).1
   · obtain ⟨hcoord,hw⟩:=outside_movingRelevantPlaces (base C) (movingRatio C.1 H G) v hv
     have hz:exponentSetPoleWeight v.val
         (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G)) movingSupport=0:=by
       rw [exponentSetPoleWeight_moving]
       simp [hcoord,hw]
     have hp:=(poleOrder_eval_le_support v.val (algebraMap K (CoordinateField K C.1))
       (constant_value_le_one K (CoordinateField K C.1) v)
       (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G))
       (polynomialOfSupport movingSupport c)).trans
       (supportPoleWeight_le_exponentSetPoleWeight _ _ _ movingSupport
         (support_polynomialOfSupport_subset _ _))
     change poleOrder v.val (coefficientEvaluation _ _ c) ≤ _ at hp
     rw [hJ C,hz] at hp
     have hp0:=le_antisymm hp (le_max_left _ _)
     simpa [movingPoleTarget,hcoord,hw] using hp0
theorem moving_projection_gate {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (base:SeparableLiteralCoordinate P) (H G Q U:MvPolynomial (Fin 3) K)
   (hd:KaehlerDifferential.D K (CoordinateField K P) (movingValue P H G Q U)≠0):
   ∃ ht:Transcendental K (movingValue P H G Q U),
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       (elementEmbedding K (CoordinateField K P) (movingValue P H G Q U) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     IsScalarTower K (RatFunc K) (CoordinateField K P)∧
     algebraMap (RatFunc K) (CoordinateField K P)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=movingValue P H G Q U:=by
 obtain ⟨ht,hf,hs⟩:=element_transcendental_finite_separable_of_differential_ne_zero
   K (CoordinateField K P) (literalToSeparableCoordinate base) (movingValue P H G Q U) hd
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (movingValue P H G Q U) ht).toRingHom.toAlgebra
 refine ⟨ht,hf,hs,?_,elementEmbedding_variable K (CoordinateField K P) _ ht⟩
 exact IsScalarTower.of_algebraMap_eq fun c↦
   ((elementEmbedding K (CoordinateField K P) _ ht).commutes c).symm
end
end ProximityPrize.SubmissionLower.RCN064
end PackedLegacy_A9

/-! Packed from ProximityPrize.SubmissionLower.M8. -/
section PackedLegacy_M8
namespace ProximityPrize.SubmissionLower.RCN204
open scoped Classical BigOperators WithZero
open RCN095 RCN114 RCN207 RCN212 RCN295 RCN187 RCN002 RCN344 RCN064
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K L:Type*} [Field K] [Field L]
def flagPole (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):ℤ:=
 (p.zOnly:ℤ)*poleOrder v (x 2)+
 (p.yz:ℤ)*max (poleOrder v (x 0)) (poleOrder v (x 2))+
 (p.all:ℤ)*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2)))
theorem flagPole_nonneg (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):0 ≤ flagPole v x p:=by
 unfold flagPole poleOrder
 positivity
@[simp] theorem flagPole_add (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p q:FlagDegree):
   flagPole v x (p+q)=flagPole v x p+flagPole v x q:=by
 simp only [flagPole,add_zOnly,add_yz,add_all,Nat.cast_add]
 ring
@[simp] theorem flagPole_nsmul (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (k:ℕ) (p:FlagDegree):
   flagPole v x (k • p)=(k:ℤ)*flagPole v x p:=by
 simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,Nat.cast_mul]
 ring
@[simp] theorem flagPole_unitAll (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitAllFlag=
     max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 simp [flagPole,unitAllFlag]
@[simp] theorem flagPole_unitYZ (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitYZFlag=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 simp [flagPole,unitYZFlag]
theorem valuation_eval_le_flag (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (p:FlagDegree) (B:MvPolynomial (Fin 3) K) (hB:PolynomialInFlag p B):
   v (MvPolynomial.eval₂Hom coeff x B) ≤ WithZero.exp (flagPole v x p):=
 (valuation_eval_le_exp_exponentSet v coeff hcoeff x (flagSupport p) B
   ((support_subset_flagSupport_iff _ _).mpr hB)).trans
   (WithZero.exp_le_exp.mpr (exponentSetPoleWeight_flagSupport_le v x p))
end
end ProximityPrize.SubmissionLower.RCN204
end PackedLegacy_M8

/-! Packed from ProximityPrize.SubmissionLower.O3. -/
section PackedLegacy_O3
namespace ProximityPrize.SubmissionLower.RCN271
open scoped Classical
open RCN272 RCN094 RCN162 RCN165
noncomputable section
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN271.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev Ring3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def FiniteRegularZeroSetBound (P:Ideal (Ring3 K)) (H A:Ring3 K)
   (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → K),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v H≠0) →
   (∀ v∈points,MvPolynomial.aeval v A=0) → points.card ≤ cost
section Selected
open RCN136 RCN231 RCN319 RCN238 RCN243
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local instance _root_.ProximityPrize.SubmissionLower.RCN271.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
theorem agreement_fiber_card_le_of_regular_zero_bound
   (φ:Polynomial K →+*Ω) (P:Ideal (Ring3 Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:FiniteRegularZeroSetBound P (regularitySurface φ F)
     (agreementPolynomial φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hcount:points.card ≤ cost:=by
   apply hzero points
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     exact hpoint γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     change MvPolynomial.eval (selectedPoint φ selected γ)
       (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
     rw [selectedPoint_evaluation]
     exact hregular γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
     exact (selected_agreement_zero_iff φ F selected p w hchar γ
       (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rwa [hcard] at hcount
end Selected
end
end ProximityPrize.SubmissionLower.RCN271
end PackedLegacy_O3

/-! Packed from ProximityPrize.SubmissionLower.E3. -/
section PackedLegacy_E3
namespace ProximityPrize.SubmissionLower.RCN257
open scoped Classical BigOperators WithZero
open RCN344 RCN000 RCN002 RCN005 RCN006 RCN007 RCN271 RCN341
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
 (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
local instance _root_.ProximityPrize.SubmissionLower.RCN257.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
theorem model_regular_value_eq_one (ψ:A →ₐ[K] K) (h:A) (hψ:ψ h≠0):
   (modelPlace K L A ψ).val (algebraMap A L h)=1:=by
 apply le_antisymm
 · exact actual_model_value_le_one K A L ψ h
 · apply le_of_not_gt
   intro hlt
   exact hψ ((actual_model_value_lt_one_iff K A L ψ h).mp hlt)
theorem model_regular_quotient_zero_order
   (ψ:A →ₐ[K] K) (a h:A) (k:ℕ) (ha:a≠0)
   (hzero:ψ a=0) (hregular:ψ h≠0):
   1 ≤ RCN026.order K L (modelPlace K L A ψ)
     (algebraMap A L a/(algebraMap A L h)^k):=by
 have hv:=model_regular_value_eq_one K L A ψ h hregular
 change 1 ≤-((modelPlace K L A ψ).val
   (algebraMap A L a/(algebraMap A L h)^k)).log
 simp only [map_div₀,map_pow,hv,one_pow,div_one]
 exact actual_model_zero_order_ge_one K A L ψ a ha hzero
theorem finite_model_regular_zeros_le_poleMass
   (a h:A) (k cost:ℕ) (ha:a≠0) (hh:h≠0)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,RCN346.poleOrder K L v
       (algebraMap A L a/(algebraMap A L h)^k)) ≤ (cost:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hzero:∀ ψ∈S,ψ a=0) (hregular:∀ ψ∈S,ψ h≠0):
   S.card ≤ cost:=by
 classical
 let f:L:=algebraMap A L a/(algebraMap A L h)^k
 have hfa:algebraMap A L a≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne ha
 have hfh:algebraMap A L h≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne hh
 have hf:f≠0:=div_ne_zero hfa (pow_ne_zero k hfh)
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v f:=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   exact model_regular_quotient_zero_order K L A ψ a h k ha
     (hzero ψ hψ) (hregular ψ hψ)
 have hcount:=RCN026.finite_zero_places_le_poleMass K L f hf U hU
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hb:(S.card:ℤ) ≤ cost:=by
   rw [←hcard]
   exact hcount.trans (hpole _)
 exact_mod_cast hb
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem quotient_fraction_eq_field_eval (T:MvPolynomial (Fin 3) K):
   algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P T)=
     MvPolynomial.aeval (coordinate K P) T:=by
 exact (aeval_coordinate_eq_quotient K P T).symm
theorem finite_regular_zero_bound_of_separator
   (base:SeparableLiteralCoordinate P)
   (H F:MvPolynomial (Fin 3) K) (k cost:ℕ) (hF:F∉P) (hH:H∉P)
   (hpole:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P base.index base.transcendental
     ∀ W:Finset (Place K (CoordinateField K P)),
       (∑ v∈W,RCN346.poleOrder K (CoordinateField K P) v
         (MvPolynomial.aeval (coordinate K P) F/
           (MvPolynomial.aeval (coordinate K P) H)^k)) ≤ (cost:ℤ)):
   FiniteRegularZeroSetBound P H F cost:=by
 classical
 let i₀:=base.index
 let hi₀:=base.transcendental
 letI:Algebra (Polynomial K) (CoordinateRing K P):=
   quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (CoordinateField K P):=
   polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   rationalBaseAlgebra K P i₀ hi₀
 letI:=quotientBaseScalarTower K P i₀
 letI:=polynomialBaseScalarTower K P i₀
 letI:=quotientFractionScalarTower K P i₀
 letI:=polynomialRationalScalarTower K P i₀ hi₀
 letI:=rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=base.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=base.separable
 intro S hSP hSH hSF
 let liftPoint:{v:Fin 3 → K//v∈S} → (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) (pointHom_injective K P hvw)
 let points:=S.attach.image liftPoint
 have hzero:∀ ψ∈points,ψ (Ideal.Quotient.mk P F)=0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSF v.1 v.2
 have hregular:∀ ψ∈points,ψ (Ideal.Quotient.mk P H)≠0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSH v.1 v.2
 have hFq:Ideal.Quotient.mk P F≠0:=
   fun hz↦hF (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hHq:Ideal.Quotient.mk P H≠0:=
   fun hz↦hH (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hcount:=finite_model_regular_zeros_le_poleMass K (CoordinateField K P)
   (CoordinateRing K P) (Ideal.Quotient.mk P F) (Ideal.Quotient.mk P H)
   k cost hFq hHq (by simpa only [quotient_fraction_eq_field_eval] using hpole)
   points hzero hregular
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end ActualCurve
end
end ProximityPrize.SubmissionLower.RCN257
end PackedLegacy_E3

end Compact_PackedLegacyCore2


