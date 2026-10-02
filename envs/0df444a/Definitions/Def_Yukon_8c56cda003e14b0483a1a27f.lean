-- Prove2me | Definitions.Def_Yukon_8c56cda003e14b0483a1a27f
-- name    : Yukon_8c56cda003e14b0483a1a27f
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T18:54:35.868982+00:00
-- url     : https://prove2.me/theorems/65f7d3e5-01af-4bc4-98e8-4090d07d048b
-- title:
--   LowerFoundation source part 1/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-small-split-Yukon_8c56cda003e14b0483a1a27f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzZjY2FmMGVkZDJiMjQ0ZTcxYTQzNzdmZjZhYzAyNThjMWRkOTE2ODljYTVmY2Q3NGU4OWNhYjhiNTQ5MGMzOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tc21hbGwtc3BsaXQtWXVrb25fOGM1NmNkYTAwM2UxNGIwNDgzYTFhMjdmIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fOGM1NmNkYTAwM2UxNGIwNDgzYTFhMjdmIiwidiI6Mn0]

import Definitions.Def_Yukon_4703ffcd1429707f39aeab01
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
set_option linter.all false


section Compact_PackedLegacyCore1
/-! Packed from ProximityPrize.SubmissionLower.B5. -/
section PackedLegacy_B5
namespace ProximityPrize.SubmissionLower.RCN077
open RCN347
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section StableIdeals
variable {K A:Type*} [CommRing K] [CommRing A] [Algebra K A]
theorem derivation_preserves_span
   (D:Derivation K A A) (generators:Set A)
   (hgenerators:∀ x∈generators,D x∈Ideal.span generators):
   ∀ x∈Ideal.span generators,D x∈Ideal.span generators:=by
 intro x hx
 induction hx using Submodule.span_induction with
 | mem x hx => exact hgenerators x hx
 | zero => simpa only [map_zero] using (Ideal.span generators).zero_mem
 | add x y hx hy hDx hDy =>
   simpa only [map_add] using (Ideal.span generators).add_mem hDx hDy
 | smul c x hx hDx =>
   change D (c*x)∈Ideal.span generators
   rw [leibniz_product]
   exact (Ideal.span generators).add_mem
     ((Ideal.span generators).mul_mem_left (D c) hx)
     ((Ideal.span generators).mul_mem_left c hDx)
noncomputable def quotientDerivation
   (D:Derivation K A A) (I:Ideal A)
   (hstable:∀ x∈I,D x∈I):
   Derivation K (A ⧸ I) (A ⧸ I):=
 Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective K I)
   (d:=D) (fun x hx => by
     change Ideal.Quotient.mk I (D x)=0
     change Ideal.Quotient.mk I x=0 at hx
     exact Ideal.Quotient.eq_zero_iff_mem.mpr
       (hstable x (Ideal.Quotient.eq_zero_iff_mem.mp hx)))
theorem quotientDerivation_mk
   (D:Derivation K A A) (I:Ideal A)
   (hstable:∀ x∈I,D x∈I) (x:A):
   quotientDerivation D I hstable (Ideal.Quotient.mk I x)=
     Ideal.Quotient.mk I (D x):=by
 unfold quotientDerivation
 exact Derivation.liftOfSurjective_apply _ _ x
end StableIdeals
section PolynomialVectorField
variable (K:Type*) [CommRing K]
abbrev Poly4:=MvPolynomial (Fin 4) K
abbrev Poly5:=MvPolynomial (Fin 5) K
noncomputable def liftFour (F:Poly4 K):Poly5 K:=
 MvPolynomial.rename Fin.castSucc F
theorem partial_extra_liftFour (F:Poly4 K):
   MvPolynomial.pderiv (4:Fin 5) (liftFour K F)=0:=by
 induction F using MvPolynomial.induction_on with
 | C c => simp [liftFour]
 | add F G hF hG =>
   dsimp only [liftFour] at hF hG
   change MvPolynomial.pderiv (4:Fin 5)
     (MvPolynomial.rename Fin.castSucc (F+G))=0
   rw [map_add,map_add,hF,hG,add_zero]
 | mul_X F i hF =>
   dsimp only [liftFour] at hF
   have hne:(i.castSucc:Fin 5)≠4:=by
     intro h
     have hv:i.val=4:=congrArg Fin.val h
     have hi:=i.isLt
     omega
   change MvPolynomial.pderiv (4:Fin 5)
     (MvPolynomial.rename Fin.castSucc (F*MvPolynomial.X i))=0
   rw [map_mul,MvPolynomial.rename_X,leibniz_product,hF,
     MvPolynomial.pderiv_X_of_ne hne,zero_mul,mul_zero,add_zero]
theorem partial_liftFour (F:Poly4 K) (i:Fin 4):
   MvPolynomial.pderiv i.castSucc (liftFour K F)=
     liftFour K (MvPolynomial.pderiv i F):=by
 have hinj:Function.Injective (Fin.castSucc:Fin 4 → Fin 5):=by
   intro i j hij
   apply Fin.ext
   exact congrArg (fun x:Fin 5 => x.val) hij
 exact MvPolynomial.pderiv_rename hinj i F
noncomputable def inverseRelation (H:Poly5 K):Poly5 K:=
 H*MvPolynomial.X (4:Fin 5)-1
noncomputable def inverseDerivative (G H:Poly5 K):Poly5 K:=
 MvPolynomial.pderiv (0:Fin 5) H+
   MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) H+
   G*MvPolynomial.X (4:Fin 5)*MvPolynomial.pderiv (2:Fin 5) H
noncomputable def inverseVectorField (G H:Poly5 K):
   Derivation K (Poly5 K) (Poly5 K):=
 (MvPolynomial.pderiv (0:Fin 5):Derivation K (Poly5 K) (Poly5 K))+
   (MvPolynomial.X (2:Fin 5):Poly5 K) • MvPolynomial.pderiv (1:Fin 5)+
   (G*MvPolynomial.X (4:Fin 5)) • MvPolynomial.pderiv (2:Fin 5)-
   ((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H) •
     MvPolynomial.pderiv (4:Fin 5)
theorem inverseVectorField_apply (G H P:Poly5 K):
   inverseVectorField K G H P=
     MvPolynomial.pderiv (0:Fin 5) P+
       MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) P+
       G*MvPolynomial.X (4:Fin 5)*MvPolynomial.pderiv (2:Fin 5) P-
       ((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H)*
         MvPolynomial.pderiv (4:Fin 5) P:=by
 simp only [inverseVectorField,Derivation.add_apply,Derivation.sub_apply,
   Derivation.smul_apply,smul_eq_mul]
theorem inverseVectorField_X (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (0:Fin 5))=1:=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_Y (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (1:Fin 5))=
     MvPolynomial.X (2:Fin 5):=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_Z (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (3:Fin 5))=0:=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_U (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (4:Fin 5))=
     -((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H):=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_H (G H:Poly5 K)
   (hH:MvPolynomial.pderiv (4:Fin 5) H=0):
   inverseVectorField K G H H=inverseDerivative K G H:=by
 rw [inverseVectorField_apply,hH,mul_zero,sub_zero]
 rfl
theorem inverseVectorField_inverseRelation (G H:Poly5 K)
   (hH:MvPolynomial.pderiv (4:Fin 5) H=0):
   inverseVectorField K G H (inverseRelation K H)=
     -(inverseDerivative K G H*MvPolynomial.X (4:Fin 5))*
       inverseRelation K H:=by
 rw [inverseRelation,map_sub,(inverseVectorField K G H).map_one_eq_zero,
   sub_zero,leibniz_product,inverseVectorField_H K G H hH,inverseVectorField_U]
 ring
noncomputable def contactH (F:Poly4 K):Poly5 K:=
 MvPolynomial.pderiv (2:Fin 5) (liftFour K F)
noncomputable def contactG (F:Poly4 K):Poly5 K:=
 -(MvPolynomial.pderiv (0:Fin 5) (liftFour K F)+
     MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) (liftFour K F))
noncomputable def contactVectorField (F:Poly4 K):
   Derivation K (Poly5 K) (Poly5 K):=
 inverseVectorField K (contactG K F) (contactH K F)
theorem partial_extra_contactH (F:Poly4 K):
   MvPolynomial.pderiv (4:Fin 5) (contactH K F)=0:=by
 have h:=partial_liftFour K F (2:Fin 4)
 change contactH K F=liftFour K (MvPolynomial.pderiv (2:Fin 4) F) at h
 rw [h]
 exact partial_extra_liftFour K _
theorem contactVectorField_F (F:Poly4 K):
   contactVectorField K F (liftFour K F)=
     contactG K F*inverseRelation K (contactH K F):=by
 rw [contactVectorField,inverseVectorField_apply,partial_extra_liftFour,
   mul_zero,sub_zero]
 unfold contactG contactH inverseRelation
 ring
noncomputable def contactIdeal (F:Poly4 K):Ideal (Poly5 K):=
 Ideal.span ({liftFour K F,inverseRelation K (contactH K F)}:Set (Poly5 K))
theorem contactIdeal_stable (F:Poly4 K):
   ∀ P∈contactIdeal K F,contactVectorField K F P∈contactIdeal K F:=by
 apply derivation_preserves_span
 intro P hP
 have hrel:inverseRelation K (contactH K F)∈contactIdeal K F:=
   Ideal.subset_span (by simp)
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
 rcases hP with rfl | rfl
 · rw [contactVectorField_F]
   exact (contactIdeal K F).mul_mem_left _ hrel
 · rw [contactVectorField,
     inverseVectorField_inverseRelation K _ _ (partial_extra_contactH K F)]
   exact (contactIdeal K F).mul_mem_left _ hrel
abbrev ContactRing (F:Poly4 K):=Poly5 K ⧸ contactIdeal K F
noncomputable def contactDerivation (F:Poly4 K):
   Derivation K (ContactRing K F) (ContactRing K F):=
 quotientDerivation (contactVectorField K F) (contactIdeal K F) (contactIdeal_stable K F)
theorem contactDerivation_mk (F:Poly4 K) (P:Poly5 K):
   contactDerivation K F (Ideal.Quotient.mk (contactIdeal K F) P)=
     Ideal.Quotient.mk (contactIdeal K F) (contactVectorField K F P):=
 quotientDerivation_mk _ _ _ P
theorem contactRing_relation (F:Poly4 K):
   Ideal.Quotient.mk (contactIdeal K F) (liftFour K F)=0:=by
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 exact Ideal.subset_span (by simp)
theorem contactRing_inverse (F:Poly4 K):
   Ideal.Quotient.mk (contactIdeal K F) (contactH K F)*
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))=1:=by
 have hrel:Ideal.Quotient.mk (contactIdeal K F)
     (inverseRelation K (contactH K F))=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
 simpa only [inverseRelation,map_sub,map_mul,map_one,sub_eq_zero] using hrel
end PolynomialVectorField
end ProximityPrize.SubmissionLower.RCN077
end PackedLegacy_B5

/-! Packed from ProximityPrize.SubmissionLower.W. -/
section PackedLegacy_W
namespace ProximityPrize.SubmissionLower.RCN313
open RCN077 RCN347
noncomputable section
section AlgebraicStep
variable {K A B:Type*} [CommRing K] [CommRing A] [CommRing B] [Algebra K A]
def clearedStep (n:ℕ) (m mx my mr r g h hx hy hr:A):A:=
 h^2*mx+r*h^2*my+g*h*mr-
   (n:A)*m*(h*hx+r*h*hy+g*hr)
theorem map_clearedStep (φ:A →+*B) (n:ℕ) (m mx my mr r g h hx hy hr:A):
   φ (clearedStep n m mx my mr r g h hx hy hr)=
     clearedStep n (φ m) (φ mx) (φ my) (φ mr) (φ r) (φ g) (φ h)
       (φ hx) (φ hy) (φ hr):=by
 simp only [clearedStep,map_sub,map_add,map_mul,map_pow,map_natCast]
theorem derivation_inverse_power
   (D:Derivation K A A) (u a:A) (hU:D u= -(u^2*a)) (n:ℕ):
   D (u^n)= -(n:A)*u^(n+1)*a:=by
 induction n with
 | zero =>
     simp only [pow_zero,D.map_one_eq_zero,Nat.cast_zero,neg_zero,zero_mul]
 | succ n ih =>
     rw [pow_succ,leibniz_product,ih,hU]
     simp only [Nat.cast_succ,pow_succ]
     ring
theorem differentiated_fraction_step
   (D:Derivation K A A) (n:ℕ) (m mx my mr r g h hx hy hr u:A)
   (hHU:h*u=1)
   (hM:D m=mx+r*my+g*u*mr)
   (hU:D u= -(u^2*(hx+r*hy+g*u*hr))):
   D (m*u^n)=clearedStep n m mx my mr r g h hx hy hr*u^(n+2):=by
 rw [leibniz_product,hM,
   derivation_inverse_power D u (hx+r*hy+g*u*hr) hU n]
 simp only [pow_add,pow_one]
 unfold clearedStep
 linear_combination
   -(u^n)*((1+h*u)*(mx+r*my)+g*u*mr-
     (n:A)*m*u*(hx+r*hy))*hHU
end AlgebraicStep
section ContactQuotient
variable (K:Type*) [CommRing K]
def polyH (F:Poly4 K):Poly4 K:=MvPolynomial.pderiv (2:Fin 4) F
def polyG (F:Poly4 K):Poly4 K:=
 -(MvPolynomial.pderiv (0:Fin 4) F+
   MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) F)
theorem partial_liftFour_zero (P:Poly4 K):
   MvPolynomial.pderiv (0:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (0:Fin 4) P):=
 partial_liftFour K P (0:Fin 4)
theorem partial_liftFour_one (P:Poly4 K):
   MvPolynomial.pderiv (1:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (1:Fin 4) P):=
 partial_liftFour K P (1:Fin 4)
theorem partial_liftFour_two (P:Poly4 K):
   MvPolynomial.pderiv (2:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (2:Fin 4) P):=
 partial_liftFour K P (2:Fin 4)
theorem castSucc_two:(2:Fin 4).castSucc=(2:Fin 5):=rfl
theorem contactH_eq_lift (F:Poly4 K):
   contactH K F=liftFour K (polyH K F):=
 partial_liftFour K F (2:Fin 4)
theorem contactG_eq_lift (F:Poly4 K):
   contactG K F=liftFour K (polyG K F):=by
 unfold contactG polyG
 rw [partial_liftFour_zero,partial_liftFour_one]
 simp only [liftFour,map_neg,map_add,map_mul,MvPolynomial.rename_X,
   castSucc_two]
def polyImage (F:Poly4 K):Poly4 K →+*ContactRing K F:=
 (Ideal.Quotient.mk (contactIdeal K F)).comp
   (MvPolynomial.rename (R:=K) (Fin.castSucc:Fin 4 → Fin 5)).toRingHom
theorem polyImage_apply (F P:Poly4 K):
   polyImage K F P=Ideal.Quotient.mk (contactIdeal K F) (liftFour K P):=rfl
@[simp] theorem polyImage_X (F:Poly4 K) (i:Fin 4):
   polyImage K F (MvPolynomial.X i)=
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X i.castSucc):=by
 rw [polyImage_apply]
 simp only [liftFour,MvPolynomial.rename_X]
def inverseCoordinate (F:Poly4 K):ContactRing K F:=
 Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))
theorem polyImage_H_mul_inverse (F:Poly4 K):
   polyImage K F (polyH K F)*inverseCoordinate K F=1:=by
 change Ideal.Quotient.mk (contactIdeal K F) (liftFour K (polyH K F))*
   Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))=1
 rw [←contactH_eq_lift]
 exact contactRing_inverse K F
theorem contactDerivation_polyImage (F P:Poly4 K):
   contactDerivation K F (polyImage K F P)=
     polyImage K F (MvPolynomial.pderiv (0:Fin 4) P)+
       polyImage K F (MvPolynomial.X (2:Fin 4))*
         polyImage K F (MvPolynomial.pderiv (1:Fin 4) P)+
       polyImage K F (polyG K F)*inverseCoordinate K F*
         polyImage K F (MvPolynomial.pderiv (2:Fin 4) P):=by
 rw [polyImage_apply,contactDerivation_mk,contactVectorField,
   inverseVectorField_apply,partial_extra_liftFour,mul_zero,sub_zero]
 rw [partial_liftFour_zero,partial_liftFour_one,partial_liftFour_two,contactG_eq_lift]
 simp only [map_add,map_mul,polyImage_apply,inverseCoordinate,
   liftFour,MvPolynomial.rename_X,castSucc_two]
theorem contactDerivation_inverseCoordinate (F:Poly4 K):
   contactDerivation K F (inverseCoordinate K F)=
     -(inverseCoordinate K F^2*
       (polyImage K F (MvPolynomial.pderiv (0:Fin 4) (polyH K F))+
         polyImage K F (MvPolynomial.X (2:Fin 4))*
           polyImage K F (MvPolynomial.pderiv (1:Fin 4) (polyH K F))+
         polyImage K F (polyG K F)*inverseCoordinate K F*
           polyImage K F (MvPolynomial.pderiv (2:Fin 4) (polyH K F)))):=by
 rw [inverseCoordinate,contactDerivation_mk,contactVectorField,inverseVectorField_U]
 rw [contactG_eq_lift,contactH_eq_lift]
 unfold inverseDerivative
 rw [partial_liftFour_zero,partial_liftFour_one,partial_liftFour_two]
 simp only [map_neg,map_mul,map_pow,map_add,polyImage_apply,
   inverseCoordinate,liftFour,MvPolynomial.rename_X,castSucc_two]
def numeratorStep (F:Poly4 K) (b:ℕ) (M:Poly4 K):Poly4 K:=
 clearedStep (2*b) M
   (MvPolynomial.pderiv (0:Fin 4) M)
   (MvPolynomial.pderiv (1:Fin 4) M)
   (MvPolynomial.pderiv (2:Fin 4) M)
   (MvPolynomial.X (2:Fin 4)) (polyG K F) (polyH K F)
   (MvPolynomial.pderiv (0:Fin 4) (polyH K F))
   (MvPolynomial.pderiv (1:Fin 4) (polyH K F))
   (MvPolynomial.pderiv (2:Fin 4) (polyH K F))
def numerator (F:Poly4 K):ℕ → Poly4 K
 | 0 => MvPolynomial.X (1:Fin 4)
 | b+1 => numeratorStep K F b (numerator F b)
@[simp] theorem numerator_zero (F:Poly4 K):
   numerator K F 0=MvPolynomial.X (1:Fin 4):=rfl
@[simp] theorem numerator_succ (F:Poly4 K) (b:ℕ):
   numerator K F (b+1)=numeratorStep K F b (numerator K F b):=rfl
theorem iterate_Y_eq_numerator (F:Poly4 K) (b:ℕ):
   (contactDerivation K F)^[b] (polyImage K F (MvPolynomial.X (1:Fin 4)))=
     polyImage K F (numerator K F b)*inverseCoordinate K F^(2*b):=by
 induction b with
 | zero => simp
 | succ b ih =>
     rw [Function.iterate_succ_apply',ih,numerator_succ,numeratorStep,
       map_clearedStep]
     have hexp:2*(b+1)=2*b+2:=by omega
     rw [hexp]
     apply differentiated_fraction_step
     · exact polyImage_H_mul_inverse K F
     · exact contactDerivation_polyImage K F (numerator K F b)
     · exact contactDerivation_inverseCoordinate K F
end ContactQuotient
section DegreeBounds
variable {K:Type*} [Field K]
theorem support_before_pderiv (i:Fin 4) (P:Poly4 K) (d:Fin 4 →₀ ℕ)
   (hd:d∈(MvPolynomial.pderiv i P).support):
   d+Finsupp.single i 1∈P.support:=by
 apply MvPolynomial.mem_support_iff.mpr
 intro hzero
 have hne:=MvPolynomial.mem_support_iff.mp hd
 apply hne
 rw [MvPolynomial.coeff_pderiv,hzero,zero_mul]
theorem pderiv_degree_bound (i j:Fin 4) (P:Poly4 K) (a:ℕ)
   (hP:P.degreeOf j ≤ a):(MvPolynomial.pderiv i P).degreeOf j ≤ a:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply] at hh
 omega
theorem pderiv_same_degree_bound (i:Fin 4) (P:Poly4 K) (a:ℕ)
   (hP:P.degreeOf i ≤ a):(MvPolynomial.pderiv i P).degreeOf i ≤ a-1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
 omega
theorem pderiv_eq_zero_of_degree_bound_zero (i:Fin 4) (P:Poly4 K)
   (hP:P.degreeOf i ≤ 0):MvPolynomial.pderiv i P=0:=by
 ext d
 rw [MvPolynomial.coeff_zero,MvPolynomial.coeff_pderiv]
 have hzero:MvPolynomial.coeff (d+Finsupp.single i 1) P=0:=by
   by_contra hne
   have hh:=MvPolynomial.degreeOf_le_iff.mp hP
     (d+Finsupp.single i 1) (MvPolynomial.mem_support_iff.mpr hne)
   simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
   omega
 rw [hzero,zero_mul]
theorem degree_mul_bound (i:Fin 4) {P Q:Poly4 K} {a b:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ b):
   (P*Q).degreeOf i ≤ a+b:=
 (MvPolynomial.degreeOf_mul_le i P Q).trans (Nat.add_le_add hP hQ)
theorem degree_add_bound (i:Fin 4) {P Q:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ a):
   (P+Q).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_add_le i P Q).trans (max_le hP hQ)
theorem degree_sub_bound (i:Fin 4) {P Q:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ a):
   (P-Q).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_sub_le i P Q).trans (max_le hP hQ)
theorem degree_pow_bound (i:Fin 4) (n:ℕ) {P:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a):(P^n).degreeOf i ≤ n*a:=
 (MvPolynomial.degreeOf_pow_le i P n).trans (Nat.mul_le_mul_left n hP)
theorem degree_natCast_eq_zero (i:Fin 4) (n:ℕ):
   (n:Poly4 K).degreeOf i=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K) n]
 exact MvPolynomial.degreeOf_C (n:K) i
theorem polyG_degree_bound (i:Fin 4) (F:Poly4 K) (a r:ℕ)
   (hF:F.degreeOf i ≤ a) (hR:(MvPolynomial.X (2:Fin 4):Poly4 K).degreeOf i ≤ r):
   (polyG K F).degreeOf i ≤ a+r:=by
 unfold polyG
 rw [MvPolynomial.degreeOf_neg]
 apply degree_add_bound i
 · have hh:=pderiv_degree_bound (0:Fin 4) i F a hF
   omega
 · have hh:=degree_mul_bound i hR (pderiv_degree_bound (1:Fin 4) i F a hF)
   simpa only [Nat.add_comm] using hh
theorem numeratorStep_nonR_degree_bound
   (i:Fin 4) (hi:i≠2) (F M:Poly4 K) (b a c:ℕ)
   (hF:F.degreeOf i ≤ c) (hM:M.degreeOf i ≤ a):
   (numeratorStep K F b M).degreeOf i ≤ a+2*c:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf i ≤ 0:=by
   simp only [R,MvPolynomial.degreeOf_X_of_ne hi,le_refl]
 have hH:H.degreeOf i ≤ c:=pderiv_degree_bound (2:Fin 4) i F c hF
 have hG:G.degreeOf i ≤ c:=by
   simpa only [Nat.add_zero] using polyG_degree_bound i F c 0 hF hR
 have hH2:=degree_pow_bound i 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) i M a hM
 have hMY:=pderiv_degree_bound (1:Fin 4) i M a hM
 have hMR:=pderiv_degree_bound (2:Fin 4) i M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) i H c hH
 have hHY:=pderiv_degree_bound (1:Fin 4) i H c hH
 have hHR:=pderiv_degree_bound (2:Fin 4) i H c hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hG hH) hMR
   omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i hG hHR
   omega
 have hbrace:=degree_add_bound i (degree_add_bound i hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf i ≤ 0:=
   le_of_eq (degree_natCast_eq_zero i (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf i ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound i hn hM
 have h4:=degree_mul_bound i hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf i ≤ a+2*c
 exact degree_sub_bound i (degree_add_bound i (degree_add_bound i h1 h2) h3) h4
theorem numeratorStep_R_degree_bound
   (F M:Poly4 K) (b a s:ℕ) (hs:1 ≤ s)
   (hF:F.degreeOf (2:Fin 4) ≤ s) (hM:M.degreeOf (2:Fin 4) ≤ a):
   (numeratorStep K F b M).degreeOf (2:Fin 4) ≤ a+(2*s-1):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s-1:=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s+1:=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hH2:=degree_pow_bound (2:Fin 4) 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) M a hM
 have hMY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) M a hM
 have hMR:=pderiv_same_degree_bound (2:Fin 4) M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) H (s-1) hH
 have hHY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) H (s-1) hH
 have hHR:=pderiv_same_degree_bound (2:Fin 4) H (s-1) hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   have hh:=degree_mul_bound (2:Fin 4) hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   by_cases ha:a=0
   · have hz:MvPolynomial.pderiv (2:Fin 4) M=0:=
       pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) M (by simpa only [ha] using hM)
     rw [hz,mul_zero,MvPolynomial.degreeOf_zero]
     exact Nat.zero_le _
   · have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hG hH) hMR
     omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   have hh:=degree_mul_bound (2:Fin 4) hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   by_cases hsone:s=1
   · have hz:MvPolynomial.pderiv (2:Fin 4) H=0:=
       pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) H (by simpa [hsone] using hH)
     rw [hz,mul_zero,MvPolynomial.degreeOf_zero]
     exact Nat.zero_le _
   · have hh:=degree_mul_bound (2:Fin 4) hG hHR
     omega
 have hbrace:=degree_add_bound (2:Fin 4)
   (degree_add_bound (2:Fin 4) hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf (2:Fin 4) ≤ 0:=
   le_of_eq (degree_natCast_eq_zero (2:Fin 4) (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf (2:Fin 4) ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound (2:Fin 4) hn hM
 have h4:=degree_mul_bound (2:Fin 4) hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf (2:Fin 4) ≤ a+(2*s-1)
 exact degree_sub_bound (2:Fin 4)
   (degree_add_bound (2:Fin 4) (degree_add_bound (2:Fin 4) h1 h2) h3) h4
theorem numerator_nonR_degree_bound
   (i:Fin 4) (hi:i≠2) (F:Poly4 K) (c a₀:ℕ)
   (hF:F.degreeOf i ≤ c) (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (b:ℕ):(numerator K F b).degreeOf i ≤ a₀+2*b*c:=by
 induction b with
 | zero => simpa only [numerator_zero,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] using hbase
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_nonR_degree_bound i hi F (numerator K F b) b
       (a₀+2*b*c) c hF ih
     have heq:a₀+2*(b+1)*c=(a₀+2*b*c)+2*c:=by ring
     rw [heq]
     exact hh
theorem numerator_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) (b:ℕ):
   (numerator K F b).degreeOf (2:Fin 4) ≤ b*(2*s-1):=by
 induction b with
 | zero => simp [numerator_zero,MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4)≠1)]
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_R_degree_bound F (numerator K F b) b
       (b*(2*s-1)) s hs hF ih
     simpa only [Nat.add_mul,Nat.one_mul] using hh
end DegreeBounds
section AgreementNumerators
variable {K:Type*} [Field K]
def commonNumeratorTerm (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x:K) (j:ℕ):
   Poly4 K:=
 MvPolynomial.C (c j)*numerator K F j*
   polyH K F^(2*(w-j))*
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j
def clearedTaylorNumerator (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x:K):Poly4 K:=
 ∑ j∈Finset.range (w+1),commonNumeratorTerm F w c x j
def affineSeedPolynomial (u₀ u₁:K):Poly4 K:=
 MvPolynomial.C u₀+MvPolynomial.X (3:Fin 4)*MvPolynomial.C u₁
def agreementNumerator (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   Poly4 K:=
 clearedTaylorNumerator F w c x-affineSeedPolynomial u₀ u₁*polyH K F^(2*w)
theorem shiftedX_degree_bound (i:Fin 4) (hi:i≠0) (x:K):
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K).degreeOf i ≤ 0:=by
 apply degree_sub_bound i
 · simp only [MvPolynomial.degreeOf_C,le_refl]
 · simp only [MvPolynomial.degreeOf_X_of_ne hi,le_refl]
theorem degree_sum_bound (i:Fin 4) (I:Finset ℕ) (f:ℕ → Poly4 K) (a:ℕ)
   (hf:∀ j∈I,(f j).degreeOf i ≤ a):
   (∑ j∈I,f j).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_sum_le i I f).trans (Finset.sup_le hf)
theorem commonNumeratorTerm_nonR_degree_bound
   (i:Fin 4) (hi₀:i≠0) (hi₂:i≠2)
   (F:Poly4 K) (cap a₀:ℕ) (hF:F.degreeOf i ≤ cap)
   (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K):
   (commonNumeratorTerm F w c x j).degreeOf i ≤ a₀+2*w*cap:=by
 have hM:=numerator_nonR_degree_bound i hi₂ F cap a₀ hF hbase j
 have hCM:(MvPolynomial.C (c j)*numerator K F j).degreeOf i ≤ a₀+2*j*cap:=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) i (c j)).trans hM
 have hH:(polyH K F).degreeOf i ≤ cap:=
   pderiv_degree_bound (2:Fin 4) i F cap hF
 have hHP:=degree_pow_bound i (2*(w-j)) hH
 have hXP:((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j).degreeOf i ≤ 0:=by
   simpa only [Nat.mul_zero] using degree_pow_bound i j (shiftedX_degree_bound i hi₀ x)
 have hterm:=degree_mul_bound i (degree_mul_bound i hCM hHP) hXP
 have hw:j+(w-j)=w:=by omega
 have heq:(a₀+2*j*cap)+2*(w-j)*cap+0=a₀+2*w*cap:=by
   calc
     (a₀+2*j*cap)+2*(w-j)*cap+0=a₀+2*(j+(w-j))*cap:=by ring
     _=a₀+2*w*cap:=by rw [hw]
 exact hterm.trans (le_of_eq heq)
theorem commonNumeratorTerm_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K):
   (commonNumeratorTerm F w c x j).degreeOf (2:Fin 4) ≤ w*(2*s-1):=by
 have hM:=numerator_R_degree_bound F s hs hF j
 have hCM:(MvPolynomial.C (c j)*numerator K F j).degreeOf (2:Fin 4) ≤ j*(2*s-1):=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) (2:Fin 4) (c j)).trans hM
 have hH:(polyH K F).degreeOf (2:Fin 4) ≤ s-1:=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hHP:=degree_pow_bound (2:Fin 4) (2*(w-j)) hH
 have hXP:((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j).degreeOf (2:Fin 4) ≤ 0:=by
   simpa only [Nat.mul_zero] using
     degree_pow_bound (2:Fin 4) j (shiftedX_degree_bound (2:Fin 4) (by decide) x)
 have hterm:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hCM hHP) hXP
 have hw:j+(w-j)=w:=by omega
 have hs':2*s-1=2*(s-1)+1:=by omega
 have hcap:j*(2*s-1)+2*(w-j)*(s-1) ≤ w*(2*s-1):=by
   rw [hs']
   calc
     j*(2*(s-1)+1)+2*(w-j)*(s-1)=
         2*(j+(w-j))*(s-1)+j:=by ring
     _=2*w*(s-1)+j:=by rw [hw]
     _ ≤ 2*w*(s-1)+w:=Nat.add_le_add_left hj _
     _=w*(2*(s-1)+1):=by ring
 have hterm':(commonNumeratorTerm F w c x j).degreeOf (2:Fin 4) ≤
     j*(2*s-1)+2*(w-j)*(s-1):=by
   simpa only [commonNumeratorTerm,Nat.add_zero] using hterm
 exact hterm'.trans hcap
theorem clearedTaylorNumerator_nonR_degree_bound
   (i:Fin 4) (hi₀:i≠0) (hi₂:i≠2)
   (F:Poly4 K) (cap a₀:ℕ) (hF:F.degreeOf i ≤ cap)
   (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (w:ℕ) (c:ℕ → K) (x:K):
   (clearedTaylorNumerator F w c x).degreeOf i ≤ a₀+2*w*cap:=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound i
 intro j hj
 exact commonNumeratorTerm_nonR_degree_bound i hi₀ hi₂ F cap a₀ hF hbase w j
   (by have hh:=Finset.mem_range.mp hj;omega) c x
theorem clearedTaylorNumerator_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x:K):
   (clearedTaylorNumerator F w c x).degreeOf (2:Fin 4) ≤ w*(2*s-1):=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound (2:Fin 4)
 intro j hj
 exact commonNumeratorTerm_R_degree_bound F s hs hF w j
   (by have hh:=Finset.mem_range.mp hj;omega) c x
theorem affineSeedPolynomial_degree_bound (i:Fin 4) (cap:ℕ)
   (hZ:(MvPolynomial.X (3:Fin 4):Poly4 K).degreeOf i ≤ cap) (u₀ u₁:K):
   (affineSeedPolynomial u₀ u₁).degreeOf i ≤ cap:=by
 unfold affineSeedPolynomial
 apply degree_add_bound i
 · simp only [MvPolynomial.degreeOf_C,Nat.zero_le]
 · have hC:(MvPolynomial.C u₁:Poly4 K).degreeOf i ≤ 0:=by
     simp only [MvPolynomial.degreeOf_C,le_refl]
   simpa only [Nat.add_zero] using degree_mul_bound i hZ hC
theorem agreementNumerator_degree_bounds
   (F:Poly4 K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf (1:Fin 4) ≤ ell)
   (hR:F.degreeOf (2:Fin 4) ≤ s)
   (hZ:F.degreeOf (3:Fin 4) ≤ L)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   (agreementNumerator F w c x u₀ u₁).degreeOf (1:Fin 4) ≤ 1+2*w*ell∧
   (agreementNumerator F w c x u₀ u₁).degreeOf (2:Fin 4) ≤ w*(2*s-1)∧
   (agreementNumerator F w c x u₀ u₁).degreeOf (3:Fin 4) ≤ 2*w*L+1:=by
 unfold agreementNumerator
 refine ⟨?_,?_,?_⟩
 · apply degree_sub_bound (1:Fin 4)
   · exact clearedTaylorNumerator_nonR_degree_bound (1:Fin 4) (by decide) (by decide)
       F ell 1 hY (by simp) w c x
   · have ha:=affineSeedPolynomial_degree_bound (1:Fin 4) 0
       (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 4)≠3)]) u₀ u₁
     have hH:(polyH K F).degreeOf (1:Fin 4) ≤ ell:=
       pderiv_degree_bound (2:Fin 4) (1:Fin 4) F ell hY
     have hh:=degree_mul_bound (1:Fin 4) ha (degree_pow_bound (1:Fin 4) (2*w) hH)
     omega
 · apply degree_sub_bound (2:Fin 4)
   · exact clearedTaylorNumerator_R_degree_bound F s hs hR w c x
   · have ha:=affineSeedPolynomial_degree_bound (2:Fin 4) 0
       (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4)≠3)]) u₀ u₁
     have hH:=pderiv_same_degree_bound (2:Fin 4) F s hR
     have hh:=degree_mul_bound (2:Fin 4) ha (degree_pow_bound (2:Fin 4) (2*w) hH)
     have hs':2*s-1=2*(s-1)+1:=by omega
     have hcap:0+(2*w)*(s-1) ≤ w*(2*s-1):=by
       rw [hs']
       calc
         0+(2*w)*(s-1) ≤ 2*w*(s-1)+w:=by omega
         _=w*(2*(s-1)+1):=by ring
     exact hh.trans hcap
 · apply degree_sub_bound (3:Fin 4)
   · have hh:=clearedTaylorNumerator_nonR_degree_bound (3:Fin 4) (by decide) (by decide)
       F L 0 hZ
         (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(3:Fin 4)≠1)]) w c x
     omega
   · have ha:=affineSeedPolynomial_degree_bound (3:Fin 4) 1 (by simp) u₀ u₁
     have hH:(polyH K F).degreeOf (3:Fin 4) ≤ L:=
       pderiv_degree_bound (2:Fin 4) (3:Fin 4) F L hZ
     have hh:=degree_mul_bound (3:Fin 4) ha (degree_pow_bound (3:Fin 4) (2*w) hH)
     omega
end AgreementNumerators
end
end ProximityPrize.SubmissionLower.RCN313
end PackedLegacy_W

/-! Packed from ProximityPrize.SubmissionLower.O1. -/
section PackedLegacy_O1
namespace ProximityPrize.SubmissionLower.RCN269
open RCN077
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section Evaluation
variable {K L:Type*} [CommRing K] [Field L]
def extendPoint (v:Fin 4 → L) (inverseValue:L):Fin 5 → L:=
 ![v 0,v 1,v 2,v 3,inverseValue]
theorem extendPoint_castSucc (v:Fin 4 → L) (inverseValue:L) (i:Fin 4):
   extendPoint v inverseValue i.castSucc=v i:=by
 fin_cases i <;> rfl
theorem extendPoint_last (v:Fin 4 → L) (inverseValue:L):
   extendPoint v inverseValue (4:Fin 5)=inverseValue:=rfl
theorem eval_liftFour
   (coefficients:K →+*L) (v:Fin 4 → L) (inverseValue:L) (P:Poly4 K):
   MvPolynomial.eval₂Hom coefficients (extendPoint v inverseValue) (liftFour K P)=
     MvPolynomial.eval₂Hom coefficients v P:=by
 have hhom:
     (MvPolynomial.eval₂Hom coefficients (extendPoint v inverseValue)).comp
         (MvPolynomial.rename (Fin.castSucc:Fin 4 → Fin 5):
           Poly4 K →ₐ[K] Poly5 K).toRingHom=
       MvPolynomial.eval₂Hom coefficients v:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_C,MvPolynomial.eval₂Hom_C]
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_X,MvPolynomial.eval₂Hom_X',extendPoint_castSucc]
 exact RingHom.congr_fun hhom P
noncomputable def pointEvaluation
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):Poly5 K →+*L:=
 MvPolynomial.eval₂Hom coefficients
   (extendPoint v ((MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F))⁻¹))
theorem pointEvaluation_liftFour
   (coefficients:K →+*L) (F P:Poly4 K) (v:Fin 4 → L):
   pointEvaluation coefficients F v (liftFour K P)=
     MvPolynomial.eval₂Hom coefficients v P:=
 eval_liftFour coefficients v _ P
theorem pointEvaluation_H
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):
   pointEvaluation coefficients F v (contactH K F)=
     MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F):=by
 have h:=partial_liftFour K F (2:Fin 4)
 change contactH K F=liftFour K (MvPolynomial.pderiv (2:Fin 4) F) at h
 rw [h,pointEvaluation_liftFour]
theorem pointEvaluation_U
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):
   pointEvaluation coefficients F v (MvPolynomial.X (4:Fin 5))=
     (MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F))⁻¹:=by
 simp only [pointEvaluation,MvPolynomial.eval₂Hom_X',extendPoint_last]
theorem contactIdeal_le_ker_pointEvaluation
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   contactIdeal K F ≤ RingHom.ker (pointEvaluation coefficients F v):=by
 apply Ideal.span_le.mpr
 intro P hP
 change pointEvaluation coefficients F v P=0
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
 rcases hP with rfl | rfl
 · rw [pointEvaluation_liftFour,hF]
 · rw [inverseRelation,map_sub,map_mul,map_one,pointEvaluation_H,
     pointEvaluation_U,mul_inv_cancel₀ hregular,sub_self]
noncomputable def regularPointValue
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):ContactRing K F →+*L:=
 Ideal.Quotient.lift (contactIdeal K F) (pointEvaluation coefficients F v)
   (fun P hP => RingHom.mem_ker.mp
     (contactIdeal_le_ker_pointEvaluation coefficients F v hF hregular hP))
theorem regularPointValue_mk
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (P:Poly5 K):
   regularPointValue coefficients F v hF hregular
     (Ideal.Quotient.mk (contactIdeal K F) P)=pointEvaluation coefficients F v P:=rfl
theorem regularPointValue_algebraMap
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (c:K):
   regularPointValue coefficients F v hF hregular
     (algebraMap K (ContactRing K F) c)=coefficients c:=by
 change regularPointValue coefficients F v hF hregular
   (Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.C c))=coefficients c
 rw [regularPointValue_mk]
 simp only [pointEvaluation,MvPolynomial.eval₂Hom_C]
theorem regularPointValue_comp_algebraMap
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   (regularPointValue coefficients F v hF hregular).comp
     (algebraMap K (ContactRing K F))=coefficients:=by
 ext c
 exact regularPointValue_algebraMap coefficients F v hF hregular c
end Evaluation
section Coordinates
variable (K:Type*) [CommRing K]
noncomputable def contactCoordinate (F:Poly4 K) (i:Fin 4):ContactRing K F:=
 Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X i.castSucc)
theorem coordinate_relation (F:Poly4 K):
   MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F))
     (contactCoordinate K F) F=0:=by
 have hhom:
     (Ideal.Quotient.mk (contactIdeal K F)).comp
         (MvPolynomial.rename (Fin.castSucc:Fin 4 → Fin 5):
           Poly4 K →ₐ[K] Poly5 K).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F))
         (contactCoordinate K F):=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_C,MvPolynomial.eval₂Hom_C]
     rfl
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_X,MvPolynomial.eval₂Hom_X']
     rfl
 have hF:=RingHom.congr_fun hhom F
 change Ideal.Quotient.mk (contactIdeal K F) (liftFour K F)=
   MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F)) (contactCoordinate K F) F at hF
 rw [contactRing_relation] at hF
 exact hF.symm
theorem derivation_coordinate_X (F:Poly4 K):
   contactDerivation K F (contactCoordinate K F (0:Fin 4))=1:=by
 rw [contactCoordinate,contactDerivation_mk]
 change Ideal.Quotient.mk (contactIdeal K F)
   (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (0:Fin 5)))=1
 rw [inverseVectorField_X,map_one]
theorem derivation_coordinate_Y (F:Poly4 K):
   contactDerivation K F (contactCoordinate K F (1:Fin 4))=
     contactCoordinate K F (2:Fin 4):=by
 rw [contactCoordinate,contactDerivation_mk]
 change Ideal.Quotient.mk (contactIdeal K F)
   (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (1:Fin 5)))=
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (2:Fin 5))
 rw [inverseVectorField_Y]
theorem derivation_coordinate_Z (F:Poly4 K):
   contactDerivation K F (contactCoordinate K F (3:Fin 4))=0:=by
 rw [contactCoordinate,contactDerivation_mk]
 change Ideal.Quotient.mk (contactIdeal K F)
   (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (3:Fin 5)))=0
 rw [inverseVectorField_Z,map_zero]
variable {L:Type*} [Field L]
theorem regularPointValue_coordinate
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (i:Fin 4):
   regularPointValue coefficients F v hF hregular (contactCoordinate K F i)=v i:=by
 rw [contactCoordinate,regularPointValue_mk]
 simp only [pointEvaluation,MvPolynomial.eval₂Hom_X',extendPoint_castSucc]
end Coordinates
end ProximityPrize.SubmissionLower.RCN269
end PackedLegacy_O1

/-! Packed from ProximityPrize.SubmissionLower.E0. -/
section PackedLegacy_E0
namespace ProximityPrize.SubmissionLower.RCN233
open RCN347 RCN348 RCN077 RCN269
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section GeneralTaylorCoordinates
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem iterate_affine_coordinate_ge_two
   (D:Derivation K A A) (a:A) (ha:D a=1) (j:ℕ):
   D^[j+2] a=0:=by
 rw [Function.iterate_add_apply]
 change D^[j] (D (D a))=0
 rw [ha,D.map_one_eq_zero]
 exact iterate_zero D j
theorem jetPolynomial_affine_coordinate
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:2 ≤ bound) (a:A) (ha:D a=1):
   jetPolynomial D value bound a=Polynomial.C (value a)+Polynomial.X:=by
 ext j
 cases j with
 | zero =>
   have hb:0 < bound:=by omega
   simp [jetPolynomial_coeff,jetCoefficient,hb]
 | succ j =>
   cases j with
   | zero =>
     have hb:1 < bound:=by omega
     simp [jetPolynomial_coeff,jetCoefficient,hb,ha]
   | succ j =>
     have hz:jetCoefficient D value a (j+2)=0:=by
       simp only [jetCoefficient,iterate_affine_coordinate_ge_two D a ha j,
         map_zero,zero_div]
     have hn0:j+2≠0:=by omega
     have hn1:j+2≠1:=by omega
     change (jetPolynomial D value bound a).coeff (j+2)=
       (Polynomial.C (value a)+Polynomial.X).coeff (j+2)
     simp [jetPolynomial_coeff,hz,Polynomial.coeff_C,Polynomial.coeff_X,hn0,hn1]
theorem jetPolynomial_natDegree_le
   (D:Derivation K A A) (value:A →+*L) (w:ℕ) (a:A):
   (jetPolynomial D value (w+1) a).natDegree ≤ w:=by
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 rw [jetPolynomial_coeff,if_neg (by omega)]
end GeneralTaylorCoordinates
section ActualRegularPoint
variable {K L:Type*} [CommRing K] [Field L]
noncomputable def reconstructedPolynomial
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 jetPolynomial (contactDerivation K F)
   (regularPointValue coefficients F v hF hregular) (w+1)
   (contactCoordinate K F (1:Fin 4))
noncomputable def reconstructionSubstitution
   (v:Fin 4 → L) (P:Polynomial L):Fin 4 → Polynomial L:=
 ![Polynomial.C (v 0)+Polynomial.X,P,P.derivative,Polynomial.C (v 3)]
noncomputable def reconstructedEquation
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
   (reconstructionSubstitution v (reconstructedPolynomial coefficients F v hF hregular w)) F
theorem reconstructedPolynomial_natDegree_le
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hregular w).natDegree ≤ w:=
 jetPolynomial_natDegree_le _ _ _ _
theorem reconstructedPolynomial_coeff_zero
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hregular w).coeff 0=v 1:=by
 simp [reconstructedPolynomial,jetPolynomial_coeff,jetCoefficient,
   regularPointValue_coordinate]
theorem reconstructedPolynomial_coeff_one
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (hw:1 ≤ w):
   (reconstructedPolynomial coefficients F v hF hregular w).coeff 1=v 2:=by
 have hb:1 < w+1:=by omega
 simp [reconstructedPolynomial,jetPolynomial_coeff,jetCoefficient,hb,
   derivation_coordinate_Y,regularPointValue_coordinate]
theorem coordinate_taylor_eq_reconstruction
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0):
   ∀ i:Fin 4,
     jetPolynomial (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular) bound
       (contactCoordinate K F i)=
     reconstructionSubstitution v
       (reconstructedPolynomial coefficients F v hF hregular w) i:=by
 let D:=contactDerivation K F
 let value:=regularPointValue coefficients F v hF hregular
 let P:=reconstructedPolynomial coefficients F v hF hregular w
 have hbound:0 < bound:=by omega
 have hfull:jetPolynomial D value bound (contactCoordinate K F (1:Fin 4))=P:=by
   apply jetPolynomial_eq_shorter_of_tails_zero D value (w+1) bound
     (contactCoordinate K F (1:Fin 4)) hshort
   intro j hj hjbound
   exact htails j (by omega) hjbound.le
 have hlast:jetCoefficient D value (contactCoordinate K F (1:Fin 4)) bound=0:=
   htails bound (by omega) le_rfl
 have hdr:=jetPolynomial_derivation_eq_derivative_of_char D value p bound hchar
   (contactCoordinate K F (1:Fin 4)) hlast
 have hDy:D (contactCoordinate K F (1:Fin 4))=
     contactCoordinate K F (2:Fin 4):=derivation_coordinate_Y K F
 rw [hDy,hfull] at hdr
 have hx:=jetPolynomial_affine_coordinate D value bound (by omega)
   (contactCoordinate K F (0:Fin 4)) (derivation_coordinate_X K F)
 have hvalueX:value (contactCoordinate K F (0:Fin 4))=v 0:=
   regularPointValue_coordinate K coefficients F v hF hregular 0
 rw [hvalueX] at hx
 have hz:=jetPolynomial_of_derivation_eq_zero D value bound hbound
   (contactCoordinate K F (3:Fin 4)) (derivation_coordinate_Z K F)
 have hvalueZ:value (contactCoordinate K F (3:Fin 4))=v 3:=
   regularPointValue_coordinate K coefficients F v hF hregular 3
 rw [hvalueZ] at hz
 intro i
 fin_cases i
 · exact hx
 · exact hfull
 · exact hdr
 · exact hz
theorem polynomiality_of_all_tails
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0)
   (hdegree:(reconstructedEquation coefficients F v hF hregular w).natDegree < bound):
   reconstructedEquation coefficients F v hF hregular w=0:=by
 let D:=contactDerivation K F
 let value:=regularPointValue coefficients F v hF hregular
 let sigmaPolys:=reconstructionSubstitution v
   (reconstructedPolynomial coefficients F v hF hregular w)
 have hcoeff:value.comp (algebraMap K (ContactRing K F))=coefficients:=
   regularPointValue_comp_algebraMap coefficients F v hF hregular
 have hcoordinates:∀ i:Fin 4,
     jetPolynomial D value bound (contactCoordinate K F i)=sigmaPolys i:=
   coordinate_taylor_eq_reconstruction coefficients F v hF hregular p bound w
     hw hshort hchar htails
 have hfactorial:∀ j < bound,(j.factorial:L)≠0:=by
   intro j hj
   exact factorial_cast_ne_zero_below_characteristic p j (hj.trans hchar)
 have hdeg:(MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K (ContactRing K F)))) sigmaPolys F).natDegree <
       bound:=by
   rw [hcoeff]
   exact hdegree
 have hzero:=polynomial_relation_of_taylor_substitution D value bound (by omega)
   hfactorial (contactCoordinate K F) sigmaPolys hcoordinates F
   (coordinate_relation K F) hdeg
 rw [hcoeff] at hzero
 exact hzero
end ActualRegularPoint
end ProximityPrize.SubmissionLower.RCN233
end PackedLegacy_E0

/-! Packed from ProximityPrize.SubmissionLower.A4. -/
section PackedLegacy_A4
namespace ProximityPrize.SubmissionLower.RCN047
open RCN077 RCN269 RCN233 RCN313 RCN347
noncomputable section
section ScalarClearing
variable {A:Type*} [CommRing A]
theorem common_denominator_power (h u:A) (hHU:h*u=1)
   (w j:ℕ) (hj:j ≤ w):
   h^(2*w)*u^(2*j)=h^(2*(w-j)):=by
 have hexp:2*w=2*(w-j)+2*j:=by omega
 rw [hexp,pow_add,mul_assoc, ←mul_pow,hHU,one_pow,mul_one]
theorem common_denominator_term (h u:A) (hHU:h*u=1)
   (w j:ℕ) (hj:j ≤ w) (c m z:A):
   c*m*h^(2*(w-j))*z^j=
     h^(2*w)*(c*m*u^(2*j)*z^j):=by
 rw [←common_denominator_power h u hHU w j hj]
 ring
theorem common_denominator_sum (h u:A) (hHU:h*u=1)
   (w:ℕ) (c m:ℕ → A) (z a:A):
   (∑ j∈Finset.range (w+1),c j*m j*h^(2*(w-j))*z^j)-
       a*h^(2*w)=
     h^(2*w)*
       ((∑ j∈Finset.range (w+1),c j*m j*u^(2*j)*z^j)-a):=by
 calc
   (∑ j∈Finset.range (w+1),c j*m j*h^(2*(w-j))*z^j)-
       a*h^(2*w)=
     (∑ j∈Finset.range (w+1),
       h^(2*w)*(c j*m j*u^(2*j)*z^j))-a*h^(2*w):=by
         congr 1
         apply Finset.sum_congr rfl
         intro j hj
         exact common_denominator_term h u hHU w j
           (by have hh:=Finset.mem_range.mp hj;omega) (c j) (m j) z
   _=h^(2*w)*
       ((∑ j∈Finset.range (w+1),c j*m j*u^(2*j)*z^j)-a):=by
         rw [mul_sub,Finset.mul_sum]
         ring
end ScalarClearing
section PolynomialClearing
variable {K A:Type*} [Field K] [CommRing A]
theorem map_agreementNumerator
   (φ:Poly4 K →+*A) (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K)
   (u:A) (hHU:φ (polyH K F)*u=1):
   φ (agreementNumerator F w c x u₀ u₁)=
     φ (polyH K F)^(2*w)*
       ((∑ j∈Finset.range (w+1),
           φ (MvPolynomial.C (c j))*φ (numerator K F j)*u^(2*j)*
             (φ (MvPolynomial.C x)-φ (MvPolynomial.X (0:Fin 4)))^j)-
         (φ (MvPolynomial.C u₀)+
           φ (MvPolynomial.X (3:Fin 4))*φ (MvPolynomial.C u₁))):=by
 simp only [agreementNumerator,clearedTaylorNumerator,commonNumeratorTerm,
   affineSeedPolynomial,map_sub,map_sum,map_mul,map_pow,map_add]
 exact common_denominator_sum (φ (polyH K F)) u hHU w
   (fun j => φ (MvPolynomial.C (c j))) (fun j => φ (numerator K F j))
   (φ (MvPolynomial.C x)-φ (MvPolynomial.X (0:Fin 4)))
   (φ (MvPolynomial.C u₀)+
     φ (MvPolynomial.X (3:Fin 4))*φ (MvPolynomial.C u₁))
end PolynomialClearing
section ActualPoint
variable {K L:Type*} [Field K] [Field L]
theorem polyImage_eq_coordinate (F:Poly4 K) (i:Fin 4):
   polyImage K F (MvPolynomial.X i)=contactCoordinate K F i:=
 polyImage_X K F i
theorem regularPointValue_polyImage
   (coefficients:K →+*L) (F P:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   regularPointValue coefficients F v hF hregular (polyImage K F P)=
     MvPolynomial.eval₂Hom coefficients v P:=by
 rw [polyImage_apply,regularPointValue_mk,pointEvaluation_liftFour]
theorem regularPointValue_inverseCoordinate
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   regularPointValue coefficients F v hF hregular (inverseCoordinate K F)=
     (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹:=by
 rw [inverseCoordinate,regularPointValue_mk]
 exact pointEvaluation_U coefficients F v
theorem evaluated_iterate_Y
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (b:ℕ):
   regularPointValue coefficients F v hF hregular
       ((contactDerivation K F)^[b] (contactCoordinate K F (1:Fin 4)))=
     MvPolynomial.eval₂Hom coefficients v (numerator K F b)*
       (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*b):=by
 rw [←polyImage_eq_coordinate F (1:Fin 4),iterate_Y_eq_numerator,
   map_mul,map_pow,regularPointValue_polyImage,regularPointValue_inverseCoordinate]
theorem jetCoefficient_eq_evaluated_numerator
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (b:ℕ):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=
     MvPolynomial.eval₂Hom coefficients v (numerator K F b)*
       (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*b)/
         (b.factorial:L):=by
 rw [jetCoefficient,evaluated_iterate_Y]
theorem numerator_eval_zero_iff_jetCoefficient_zero
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (b:ℕ) (hfactorial:(b.factorial:L)≠0):
   MvPolynomial.eval₂Hom coefficients v (numerator K F b)=0 ↔
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=0:=by
 have hH:MvPolynomial.eval₂Hom coefficients v (polyH K F)≠0:=hregular
 have hU:(MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*b)≠0:=
   pow_ne_zero _ (inv_ne_zero hH)
 have hfac:((b.factorial:L)⁻¹)≠0:=inv_ne_zero hfactorial
 rw [jetCoefficient_eq_evaluated_numerator]
 simp only [div_eq_mul_inv,mul_eq_zero,hU,hfac,or_false]
theorem numerator_eval_zero_iff_jetCoefficient_zero_of_char
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p b:ℕ) [CharP L p] (hb:b < p):
   MvPolynomial.eval₂Hom coefficients v (numerator K F b)=0 ↔
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=0:=
 numerator_eval_zero_iff_jetCoefficient_zero coefficients F v hF hregular b
   (factorial_cast_ne_zero_below_characteristic p b hb)
theorem all_tail_numerators_iff_all_tail_jets
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hchar:bound < p):
   (∀ b,w < b → b ≤ bound →
     MvPolynomial.eval₂Hom coefficients v (numerator K F b)=0) ↔
   (∀ b,w < b → b ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=0):=by
 constructor
 · intro h b hwb hbb
   exact (numerator_eval_zero_iff_jetCoefficient_zero_of_char
     coefficients F v hF hregular p b (hbb.trans_lt hchar)).mp (h b hwb hbb)
 · intro h b hwb hbb
   exact (numerator_eval_zero_iff_jetCoefficient_zero_of_char
     coefficients F v hF hregular p b (hbb.trans_lt hchar)).mpr (h b hwb hbb)
theorem reconstructedPolynomial_eval
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (z:L):
   (reconstructedPolynomial coefficients F v hF hregular w).eval z=
     ∑ j∈Finset.range (w+1),
       jetCoefficient (contactDerivation K F)
         (regularPointValue coefficients F v hF hregular)
         (contactCoordinate K F (1:Fin 4)) j*z^j:=by
 simp only [reconstructedPolynomial,jetPolynomial,Polynomial.eval_finsetSum,
   Polynomial.eval_monomial]
theorem eval_agreementNumerator_clearing
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients v (agreementNumerator F w c x u₀ u₁)=
     MvPolynomial.eval₂Hom coefficients v (polyH K F)^(2*w)*
       ((∑ j∈Finset.range (w+1),
           coefficients (c j)*MvPolynomial.eval₂Hom coefficients v (numerator K F j)*
             (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*j)*
               (coefficients x-v 0)^j)-
         (coefficients u₀+v 3*coefficients u₁)):=by
 have hH:MvPolynomial.eval₂Hom coefficients v (polyH K F)≠0:=hregular
 simpa only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X'] using
   map_agreementNumerator (MvPolynomial.eval₂Hom coefficients v) F w c x u₀ u₁
     (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹ (mul_inv_cancel₀ hH)
theorem eval_factorial_agreementNumerator
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients v
       (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) x u₀ u₁)=
     MvPolynomial.eval₂Hom coefficients v (polyH K F)^(2*w)*
       ((reconstructedPolynomial coefficients F v hF hregular w).eval
           (coefficients x-v 0)-coefficients u₀-v 3*coefficients u₁):=by
 rw [eval_agreementNumerator_clearing coefficients F v hregular]
 have hsum:
     (∑ j∈Finset.range (w+1),
       coefficients ((j.factorial:K)⁻¹)*
         MvPolynomial.eval₂Hom coefficients v (numerator K F j)*
         (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*j)*
         (coefficients x-v 0)^j)=
     (reconstructedPolynomial coefficients F v hF hregular w).eval
       (coefficients x-v 0):=by
   rw [reconstructedPolynomial_eval]
   apply Finset.sum_congr rfl
   intro j hj
   rw [jetCoefficient_eq_evaluated_numerator]
   simp only [map_inv₀,map_natCast,div_eq_mul_inv]
   ring
 rw [hsum]
 ring
theorem factorial_agreement_zero_iff_actual_agreement
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients v
       (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) x u₀ u₁)=0 ↔
     (reconstructedPolynomial coefficients F v hF hregular w).eval
       (coefficients x-v 0)=coefficients u₀+v 3*coefficients u₁:=by
 rw [eval_factorial_agreementNumerator coefficients F v hF hregular w x u₀ u₁]
 have hH:MvPolynomial.eval₂Hom coefficients v (polyH K F)^(2*w)≠0:=
   pow_ne_zero _ hregular
 constructor
 · intro h
   have hz:=(mul_eq_zero.mp h).resolve_left hH
   linear_combination hz
 · intro h
   rw [h]
   ring
end ActualPoint
end
end ProximityPrize.SubmissionLower.RCN047
end PackedLegacy_A4

/-! Packed from ProximityPrize.SubmissionLower.N4. -/
section PackedLegacy_N4
namespace ProximityPrize.SubmissionLower.RCN256
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def slopeDifference:Poly K:=MvPolynomial.X 0-MvPolynomial.X 1
private def plusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
def shiftPlus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (plusVariables K)
def monomialRemainder (d:Fin 3 →₀ ℕ):Poly K →ₗ[K] Poly K where
 toFun f:=f.modMonomial d
 map_add' f g:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
 map_smul' c f:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
def contactJet (h:ℕ):Poly K →ₗ[K] Poly K:=
 (monomialRemainder K (Finsupp.single 0 h)).comp (shiftPlus K).toLinearMap
def boxExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 2 ≤ L∧d 1 ≤ s}
def coefficientBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (boxExponents M L s)
theorem coefficientBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈coefficientBox K M L s)
   (hg:g∈coefficientBox K M' L' s'):
   f*g∈coefficientBox K (M+M') (L+L') (s+s'):=by
 have hset:boxExponents M L s+boxExponents M' L' s' ⊆
     boxExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hd2,hd1⟩
   rcases he with ⟨he0,he2,he1⟩
   simp only [boxExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   omega
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
private def exponentTriple (i j z:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j+Finsupp.single 2 z
@[simp] private theorem exponentTriple_zero (i j z:ℕ):
   exponentTriple i j z 0=i:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_one (i j z:ℕ):
   exponentTriple i j z 1=j:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_two (i j z:ℕ):
   exponentTriple i j z 2=z:=by simp [exponentTriple]
private theorem exponentTriple_eta (d:Fin 3 →₀ ℕ):
   exponentTriple (d 0) (d 1) (d 2)=d:=by
 ext i
 fin_cases i <;> simp
abbrev BoxIndex (M L s:ℕ):=
 (i:Fin (min M L+1)) × (Fin (s+1) × Fin (L-i.val+1))
private theorem finPair_heq_of_val_eq
   {n a b:ℕ} {i j:Fin n} {u:Fin a} {v:Fin b}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (i,u) (j,v):=by
 subst b
 have hi:i=j:=Fin.ext hij
 have hu:u=v:=Fin.ext huv
 cases hi
 cases hu
 rfl
def boxExponentsEquivIndex (M L s:ℕ):
   boxExponents M L s ≃ BoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,by
       rcases d.property with ⟨hM,hL,hs⟩
       omega⟩,
     ⟨⟨d.val 1,by
         rcases d.property with ⟨hM,hL,hs⟩
         omega⟩,
       ⟨d.val 2,by
         change d.val 2 < L-d.val 0+1
         rcases d.property with ⟨hM,hL,hs⟩
         omega⟩⟩⟩
 invFun q:=
   ⟨exponentTriple q.1.val q.2.1.val q.2.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.1.isLt
     have hz:=q.2.2.isLt
     simp only [boxExponents,Set.mem_setOf_eq,exponentTriple_zero,
       exponentTriple_one,exponentTriple_two]
     omega⟩
 left_inv d:=Subtype.ext (exponentTriple_eta d.val)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨⟨j,hj⟩,⟨z,hz⟩⟩⟩
   simp
   apply finPair_heq_of_val_eq
   · simp [exponentTriple]
   · rfl
   · rfl
instance boxExponentsFintype (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (boxExponentsEquivIndex M L s).symm
instance coefficientBoxFinite (M L s:ℕ):
   Module.Finite K (coefficientBox K M L s):=
 Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))
def blockJet (M L s h:ℕ):coefficientBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (coefficientBox K M L s).subtype
end
end ProximityPrize.SubmissionLower.RCN256
end PackedLegacy_N4

/-! Packed from ProximityPrize.SubmissionLower.Y2. -/
section PackedLegacy_Y2
namespace ProximityPrize.SubmissionLower.RCN051
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq
def mixed (a b c:DegreeVector):ℕ:=
 a.y*b.r*c.z+a.y*b.z*c.r+
 a.r*b.y*c.z+a.r*b.z*c.y+
 a.z*b.y*c.r+a.z*b.r*c.y
def unitY:DegreeVector:=⟨1,0,0⟩
def unitR:DegreeVector:=⟨0,1,0⟩
def unitZ:DegreeVector:=⟨0,0,1⟩
end ProximityPrize.SubmissionLower.RCN051
end PackedLegacy_Y2

/-! Packed from ProximityPrize.SubmissionLower.Q. -/
section PackedLegacy_Q
namespace ProximityPrize.SubmissionLower.RCN174
open RCN256 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
theorem coefficientBox_mono {M L s M' L' s':ℕ}
   (hM:M ≤ M') (hL:L ≤ L') (hs:s ≤ s'):
   coefficientBox K M L s ≤ coefficientBox K M' L' s':=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 exact ⟨hd.1.trans hM,hd.2.1.trans hL,hd.2.2.trans hs⟩
def localMonomial (f j z:ℕ):Poly K:=
 MvPolynomial.monomial
   (Finsupp.single 0 f+Finsupp.single 1 j+Finsupp.single 2 z) 1
theorem localMonomial_mem (f j z:ℕ):
   localMonomial K f j z∈coefficientBox K f (f+z) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [boxExponents]
def seedAffine (u₀ u₁:K):Poly K:=
 MvPolynomial.C u₀+MvPolynomial.monomial (Finsupp.single 2 1) u₁
theorem seedAffine_mem (u₀ u₁:K):
   seedAffine K u₀ u₁∈coefficientBox K 0 1 0:=by
 apply (coefficientBox K 0 1 0).add_mem
 · change MvPolynomial.monomial 0 u₀∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem seedAffine_pow_mem (u₀ u₁:K) (t:ℕ):
   seedAffine K u₀ u₁^t∈coefficientBox K 0 t 0:=by
 induction t with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ t ih =>
     simpa only [pow_succ,Nat.zero_add] using
       coefficientBox_mul K ih (seedAffine_mem K u₀ u₁)
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (L+1-i.val) × Fin (D-w*i.val-(w-1)*j.val))
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 3 ≤ L∧d 2 ≤ s∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):
   Submodule K (MvPolynomial (Fin 4) K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
def blockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):Poly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     (((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)) •
         (seedAffine K u₀ u₁^(c.1.val-f.val)*
           localMonomial K f.val c.2.1.val c.2.2.1.val)
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u₀ u₁ c r∈
     coefficientBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (coefficientBox K (min r L) L s).smul_mem
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have hz:=c.2.2.1.isLt
   have hfi:=f.isLt
   have hmul:=coefficientBox_mul K
     (seedAffine_pow_mem K u₀ u₁ (c.1.val-f.val))
     (localMonomial_mem K f.val c.2.1.val c.2.2.1.val)
   apply coefficientBox_mono K (show 0+f.val ≤ min r L by omega)
     (show c.1.val-f.val+(f.val+c.2.2.1.val) ≤ L by omega)
     (show 0+c.2.1.val ≤ s by omega)
   exact hmul
 · exact (coefficientBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   coefficientBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u₀ u₁ c r,
   blockEntry_mem K D w L s x u₀ u₁ c r⟩
def extractBlock (D w L s:ℕ) (x u₀ u₁:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     coefficientBox K (min r L) L s where
 toFun θ:=∑ c:CoefficientIndex D w L s,
   θ c • boundedBlockEntry K D w L s x u₀ u₁ c r
 map_add' θ η:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a θ:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))
end
end ProximityPrize.SubmissionLower.RCN174
end PackedLegacy_Q

/-! Packed from ProximityPrize.SubmissionLower.DC. -/
section PackedLegacy_DC
namespace ProximityPrize.SubmissionLower
namespace BCHKSSubstitutionVanish
theorem mul_card_le_natDegree_of_rootMultiplicity
   {F ι:Type*} [Field F] [DecidableEq F] [DecidableEq ι]
   (R:Polynomial F) (ω:ι ↪ F) (A:Finset ι) (m:Nat)
   (hmult:∀ i∈A,m ≤ R.rootMultiplicity (ω i)):
   m*A.card ≤ R.natDegree:=by
 let xs:Finset F:=A.map ω
 have hselected:
     ∑ x∈xs,Multiset.count x R.roots ≤ R.roots.card:=by
   let all:=xs ∪ R.roots.toFinset
   calc
     ∑ x∈xs,Multiset.count x R.roots ≤
         ∑ x∈all,Multiset.count x R.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ x∈R.roots.toFinset,Multiset.count x R.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro x hxall hxroots
       exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
     _=R.roots.card:=Multiset.toFinset_sum_count_eq R.roots
 calc
   m*A.card=∑ i∈A,m:=by simp [Nat.mul_comm]
   _ ≤ ∑ i∈A,R.rootMultiplicity (ω i):=
     Finset.sum_le_sum fun i hi => hmult i hi
   _=∑ x∈xs,R.rootMultiplicity x:=by
     symm
     exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
   _=∑ x∈xs,Multiset.count x R.roots:=by
     apply Finset.sum_congr rfl
     intro x hx
     exact (Polynomial.count_roots R).symm
   _ ≤ R.roots.card:=hselected
   _ ≤ R.natDegree:=Polynomial.card_roots' R
end BCHKSSubstitutionVanish
end ProximityPrize.SubmissionLower
end PackedLegacy_DC

/-! Packed from ProximityPrize.SubmissionLower.C6. -/
section PackedLegacy_C6
namespace ProximityPrize.SubmissionLower.RCN185
open Polynomial
section LocalRing
variable {F:Type*} [CommRing F]
theorem shifted_power_dvd_iff_taylor_coeff_zero
   (P:F[X]) (x:F) (h:ℕ):
   (Polynomial.X-Polynomial.C x)^h∣P ↔
     ∀ j < h,(taylor x P).coeff j=0:=by
 have hshift:taylor x ((Polynomial.X-Polynomial.C x)^h)=
     (Polynomial.X:F[X])^h:=by
   rw [taylor_pow,map_sub,taylor_X,taylor_C,add_sub_cancel_right]
 have hdiv:=map_dvd_iff (taylorEquiv x)
   (a:=((Polynomial.X:F[X])-Polynomial.C x)^h) (b:=P)
 change taylor x ((Polynomial.X-Polynomial.C x)^h)∣taylor x P ↔
   (Polynomial.X-Polynomial.C x)^h∣P at hdiv
 rw [hshift] at hdiv
 exact hdiv.symm.trans (Polynomial.X_pow_dvd_iff (f:=taylor x P) (n:=h))
noncomputable def contactResidual (P:F[X]) (x:F):F[X]:=
 taylor x P-Polynomial.C (P.eval x)-
   Polynomial.X*taylor x P.derivative
theorem X_sq_dvd_contactResidual (P:F[X]) (x:F):
   (Polynomial.X:F[X])^2∣contactResidual P x:=by
 rw [X_pow_dvd_iff]
 intro j hj
 have hcases:j=0∨j=1:=by omega
 rcases hcases with rfl | rfl
 · simp [contactResidual]
 · simp [contactResidual,coeff_X_mul]
end LocalRing
section GlobalVanishing
variable {F I J:Type*} [Field F] [DecidableEq F] [DecidableEq I]
end GlobalVanishing
end ProximityPrize.SubmissionLower.RCN185
end PackedLegacy_C6

/-! Packed from ProximityPrize.SubmissionLower.K. -/
section PackedLegacy_K
namespace ProximityPrize.SubmissionLower.RCN319
open RCN256 RCN174 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
abbrev LocalPolynomial:=Polynomial (Poly K)
def translationVariables (x u₀ u₁:K):Fin 4 → LocalPolynomial K:=
 ![Polynomial.X+Polynomial.C (MvPolynomial.C x),
   Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
     Polynomial.C (seedAffine K u₀ u₁),
   Polynomial.C (MvPolynomial.X 1),
   Polynomial.C (MvPolynomial.X 2)]
def homogenizedTranslation (x u₀ u₁:K):
   MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K:=
 MvPolynomial.aeval (translationVariables K x u₀ u₁)
def contactEvaluation (R B:Polynomial K) (γ:K):Poly K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![R+Polynomial.X*B,R,Polynomial.C γ]
def outerEvaluation (R B:Polynomial K) (γ:K):
   LocalPolynomial K →+*Polynomial K:=
 Polynomial.eval₂RingHom (contactEvaluation K R B γ).toRingHom Polynomial.X
@[simp] theorem contactEvaluation_slopeDifference (R B:Polynomial K) (γ:K):
   contactEvaluation K R B γ (slopeDifference K)=Polynomial.X*B:=by
 simp [contactEvaluation,slopeDifference]
theorem outerEvaluation_contact_dvd
   (H:LocalPolynomial K) (m:ℕ) (R B:Polynomial K) (γ:K)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣H.coeff r):
   (Polynomial.X:Polynomial K)^m∣outerEvaluation K R B γ H:=by
 classical
 change (Polynomial.X:Polynomial K)^m∣
   H.eval₂ (contactEvaluation K R B γ).toRingHom Polynomial.X
 rw [Polynomial.eval₂_eq_sum]
 change (Polynomial.X:Polynomial K)^m∣
   ∑ r∈H.support,contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r
 apply Finset.dvd_sum
 intro r hr
 have hlocal:(Polynomial.X:Polynomial K)^(m-r)∣
     contactEvaluation K R B γ (H.coeff r):=by
   obtain ⟨q,hq⟩:=hcoeff r
   refine ⟨B^(m-r)*contactEvaluation K R B γ q,?_⟩
   simp only [hq,map_mul,map_pow,contactEvaluation_slopeDifference,
     mul_pow,mul_assoc]
 have hprod:=mul_dvd_mul hlocal
   (dvd_refl ((Polynomial.X:Polynomial K)^r))
 have htotal:(Polynomial.X:Polynomial K)^((m-r)+r)∣
     contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r:=by
   simpa only [pow_add] using hprod
 exact (pow_dvd_pow Polynomial.X (show m ≤ (m-r)+r by omega)).trans htotal
def specialization (P:Polynomial K) (γ:K):
   MvPolynomial (Fin 4) K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![Polynomial.X,P,P.derivative,Polynomial.C γ]
theorem outerEvaluation_translation
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (B:Polynomial K)
   (hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B)):
   outerEvaluation K (Polynomial.taylor x P.derivative) B γ
       (homogenizedTranslation K x u₀ u₁ Q)=
     Polynomial.taylor x (specialization K P γ Q):=by
 have hhom:
     (outerEvaluation K (Polynomial.taylor x P.derivative) B γ).comp
       (homogenizedTranslation K x u₀ u₁).toRingHom=
     (Polynomial.taylorAlgHom x).toRingHom.comp
       (specialization K P γ).toRingHom:=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
       homogenizedTranslation,specialization,Polynomial.algebraMap_apply,
       MvPolynomial.algebraMap_eq]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
         homogenizedTranslation,translationVariables,specialization,
         seedAffine,MvPolynomial.aeval_monomial,Polynomial.algebraMap_apply,
         MvPolynomial.algebraMap_eq,hP] <;> ring
 exact DFunLike.congr_fun hhom Q
theorem X_pow_dvd_taylor_specialization
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (m:ℕ)
   (hvalue:P.eval x=u₀+γ*u₁)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K x u₀ u₁ Q).coeff r):
   (Polynomial.X:Polynomial K)^m∣
     Polynomial.taylor x (specialization K P γ Q):=by
 obtain ⟨B,hB⟩:=RCN185.X_sq_dvd_contactResidual P x
 have hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B):=by
   change Polynomial.taylor x P-Polynomial.C (P.eval x)-
     Polynomial.X*Polynomial.taylor x P.derivative=Polynomial.X^2*B at hB
   rw [hvalue] at hB
   linear_combination hB
 have hh:=outerEvaluation_contact_dvd K
   (homogenizedTranslation K x u₀ u₁ Q) m (Polynomial.taylor x P.derivative) B γ hcoeff
 rw [outerEvaluation_translation K Q P x u₀ u₁ γ B hP] at hh
 exact hh
theorem specialization_eq_zero_of_contact_and_degree
   [DecidableEq K] {I:Type*} [DecidableEq I]
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (nodes:I ↪ K) (u₀ u₁:I → K) (support:Finset I) (m:ℕ)
   (hcontact:∀ i∈support,∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K (nodes i) (u₀ i) (u₁ i) Q).coeff r)
   (hvalues:∀ i∈support,P.eval (nodes i)=u₀ i+γ*u₁ i)
   (hdegree:(specialization K P γ Q).natDegree < m*support.card):
   specialization K P γ Q=0:=by
 by_contra hnonzero
 have hmult:∀ i∈support,
     m ≤ (specialization K P γ Q).rootMultiplicity (nodes i):=by
   intro i hi
   have hlocal:=X_pow_dvd_taylor_specialization K Q P
     (nodes i) (u₀ i) (u₁ i) γ m (hvalues i hi) (hcontact i hi)
   have hshifted:(Polynomial.X-Polynomial.C (nodes i))^m∣
       specialization K P γ Q:=
     (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
       (specialization K P γ Q) (nodes i) m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)
   exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
 have hh:=BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
   (specialization K P γ Q) nodes support m hmult
 exact (Nat.not_le_of_gt hdegree) hh
theorem monomial_eq (d:Fin 4 →₀ ℕ) (a:K):
   MvPolynomial.monomial d a=
     MvPolynomial.C a*MvPolynomial.X 0^d 0*MvPolynomial.X 1^d 1*
       MvPolynomial.X 2^d 2*MvPolynomial.X 3^d 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem specialization_monomial
   (P:Polynomial K) (γ:K) (d:Fin 4 →₀ ℕ) (a:K):
   specialization K P γ (MvPolynomial.monomial d a)=
     Polynomial.C a*Polynomial.X^d 0*P^d 1*P.derivative^d 2*
       Polynomial.C γ^d 3:=by
 rw [monomial_eq K d a]
 simp [specialization,Polynomial.algebraMap_eq]
theorem specialization_monomial_natDegree_le
   (P:Polynomial K) (γ:K) (w:ℕ) (hP:P.natDegree ≤ w)
   (d:Fin 4 →₀ ℕ) (a:K):
   (specialization K P γ (MvPolynomial.monomial d a)).natDegree ≤
     d 0+w*d 1+(w-1)*d 2:=by
 rw [specialization_monomial]
 have hc:(Polynomial.C a:Polynomial K).natDegree ≤ 0:=by simp
 have hx:((Polynomial.X:Polynomial K)^d 0).natDegree ≤ d 0:=by simp
 have hy:(P^d 1).natDegree ≤ d 1*w:=
   Polynomial.natDegree_pow_le_of_le (d 1) hP
 have hderiv:P.derivative.natDegree ≤ w-1:=
   (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
 have hr:(P.derivative^d 2).natDegree ≤ d 2*(w-1):=
   Polynomial.natDegree_pow_le_of_le (d 2) hderiv
 have hz:((Polynomial.C γ:Polynomial K)^d 3).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 3)
     (show (Polynomial.C γ:Polynomial K).natDegree ≤ 0 by simp)
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le
     (Polynomial.natDegree_mul_le_of_le
       (Polynomial.natDegree_mul_le_of_le hc hx) hy) hr) hz
 simpa only [Nat.zero_add,Nat.add_zero,Nat.mul_comm] using hh
theorem specialization_natDegree_lt
   (D w L s:ℕ) (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (hD:0 < D) (hcaps:Q∈globalCoefficientBox K D w L s)
   (hP:P.natDegree ≤ w):
   (specialization K P γ Q).natDegree < D:=by
 classical
 have hsupport:∀ d∈Q.support,
     d 1+d 3 ≤ L∧d 2 ≤ s∧d 0+w*d 1+(w-1)*d 2 < D:=hcaps
 have hterms:∀ d∈Q.support,
     (specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))).natDegree ≤
       D-1:=by
   intro d hd
   have hweight:=(hsupport d hd).2.2
   have hh:=specialization_monomial_natDegree_le K P γ w hP d (MvPolynomial.coeff d Q)
   omega
 rw [MvPolynomial.as_sum Q,map_sum]
 have hh:=Polynomial.natDegree_sum_le_of_forall_le Q.support
   (fun d => specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))) hterms
 exact lt_of_le_of_lt hh (by omega)
end
end ProximityPrize.SubmissionLower.RCN319
end PackedLegacy_K

/-! Packed from ProximityPrize.SubmissionLower.BJ. -/
section PackedLegacy_BJ
namespace ProximityPrize.SubmissionLower.RCN139
open RCN077 RCN269 RCN233 RCN347 RCN174 RCN319
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {K L:Type*} [Field K] [Field L]
theorem derivative_taylor (r:L) (P:Polynomial L):
   (Polynomial.taylor r P).derivative=Polynomial.taylor r P.derivative:=by
 simp [Polynomial.taylor_apply,Polynomial.derivative_comp]
theorem taylor_reconstruction_eq_specialization
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L) (P:Polynomial L):
   Polynomial.taylor (-(v 0))
       (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
         (reconstructionSubstitution v P) F)=
     specialization L (Polynomial.taylor (-(v 0)) P) (v 3)
       (MvPolynomial.map coefficients F):=by
 have hhom:
     (Polynomial.taylorAlgHom (-(v 0))).toRingHom.comp
         (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
           (reconstructionSubstitution v P))=
       (specialization L (Polynomial.taylor (-(v 0)) P) (v 3)).toRingHom.comp
         (MvPolynomial.map coefficients):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,reconstructionSubstitution,specialization]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,reconstructionSubstitution,specialization,
         derivative_taylor]
 exact DFunLike.congr_fun hhom F
theorem map_mem_globalCoefficientBox
   (coefficients:K →+*L) (F:Poly4 K) (bound w seedCap slopeCap:ℕ)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap):
   MvPolynomial.map coefficients F∈globalCoefficientBox L bound w seedCap slopeCap:=by
 intro d hd
 exact hcaps (MvPolynomial.support_map_subset coefficients F hd)
noncomputable def globalPolynomial
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 Polynomial.taylor (-(v 0)) (reconstructedPolynomial coefficients F v hF hregular w)
theorem globalPolynomial_natDegree_le
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hregular w).natDegree ≤ w:=by
 simpa only [globalPolynomial,Polynomial.natDegree_taylor] using
   reconstructedPolynomial_natDegree_le coefficients F v hF hregular w
theorem globalPolynomial_eval
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (x:L):
   (globalPolynomial coefficients F v hF hregular w).eval x=
     (reconstructedPolynomial coefficients F v hF hregular w).eval (x-v 0):=by
 simp only [globalPolynomial,Polynomial.taylor_eval,sub_eq_add_neg]
theorem globalPolynomial_initial_value
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hregular w).eval (v 0)=v 1:=by
 rw [globalPolynomial_eval,sub_self, ←Polynomial.taylor_coeff_zero (0:L),
   Polynomial.taylor_zero]
 exact reconstructedPolynomial_coeff_zero coefficients F v hF hregular w
theorem globalPolynomial_initial_slope
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (hw:1 ≤ w):
   (globalPolynomial coefficients F v hF hregular w).derivative.eval (v 0)=v 2:=by
 rw [globalPolynomial,derivative_taylor,Polynomial.taylor_eval,add_neg_cancel]
 rw [←Polynomial.taylor_coeff_one (0:L),Polynomial.taylor_zero]
 exact reconstructedPolynomial_coeff_one coefficients F v hF hregular w hw
theorem reconstructedEquation_natDegree_lt
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (bound w seedCap slopeCap:ℕ) (hbound:0 < bound)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap):
   (reconstructedEquation coefficients F v hF hregular w).natDegree < bound:=by
 have hdeg:=specialization_natDegree_lt L bound w seedCap slopeCap
   (MvPolynomial.map coefficients F) (globalPolynomial coefficients F v hF hregular w)
   (v 3) hbound (map_mem_globalCoefficientBox coefficients F bound w seedCap slopeCap hcaps)
   (globalPolynomial_natDegree_le coefficients F v hF hregular w)
 have heq:=taylor_reconstruction_eq_specialization coefficients F v
   (reconstructedPolynomial coefficients F v hF hregular w)
 change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w)=
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F) at heq
 rw [←heq,Polynomial.natDegree_taylor] at hdeg
 exact hdeg
theorem global_polynomiality_of_all_tails
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0):
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 have hdegree:=reconstructedEquation_natDegree_lt coefficients F v hF hregular
   bound w seedCap slopeCap (by omega) hcaps
 have hzero:=polynomiality_of_all_tails coefficients F v hF hregular p bound w
   hw hshort hchar htails hdegree
 have heq:=taylor_reconstruction_eq_specialization coefficients F v
   (reconstructedPolynomial coefficients F v hF hregular w)
 change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w)=
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F) at heq
 rw [←heq,hzero,map_zero]
end
end ProximityPrize.SubmissionLower.RCN139
end PackedLegacy_BJ

/-! Packed from ProximityPrize.SubmissionLower.D9. -/
section PackedLegacy_D9
namespace ProximityPrize.SubmissionLower.RCN231
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN319 RCN347
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section PolynomialIdentities
variable (K:Type*) [Field K]
theorem derivative_specialization (P:Polynomial K) (γ:K) (Q:Poly4 K):
   (specialization K P γ Q).derivative=
     specialization K P γ (MvPolynomial.pderiv (0:Fin 4) Q)+
     P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) Q)+
     P.derivative.derivative*
       specialization K P γ (MvPolynomial.pderiv (2:Fin 4) Q):=by
 induction Q using MvPolynomial.induction_on with
 | C a => simp [specialization]
 | add Q S hQ hS =>
     simp only [map_add,hQ,hS]
     ring
 | mul_X Q i hQ =>
     simp only [MvPolynomial.pderiv_mul,map_add,map_mul,
       Polynomial.derivative_mul,hQ]
     fin_cases i <;> simp [specialization] <;> ring
theorem solution_slope_identity (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0):
   specialization K P γ (polyH K F)*P.derivative.derivative=
     specialization K P γ (polyG K F):=by
 have hchain:=derivative_specialization K P γ F
 rw [hsolution,Polynomial.derivative_zero] at hchain
 have hG:specialization K P γ (polyG K F)=
     -(specialization K P γ (MvPolynomial.pderiv (0:Fin 4) F)+
       P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) F)):=by
   simp [polyG,specialization]
 rw [hG]
 change specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)*
     P.derivative.derivative=_
 linear_combination-hchain
theorem specialization_numeratorStep
   (F M:Poly4 K) (P:Polynomial K) (γ:K) (b:ℕ)
   (hsolution:specialization K P γ F=0):
   specialization K P γ (numeratorStep K F b M)=
     specialization K P γ (polyH K F)^2*
       (specialization K P γ M).derivative-
     (2*b:Polynomial K)*specialization K P γ M*
       specialization K P γ (polyH K F)*
       (specialization K P γ (polyH K F)).derivative:=by
 simp only [numeratorStep,clearedStep,map_sub,map_add,map_mul,
   map_pow,map_natCast]
 have hR:specialization K P γ (MvPolynomial.X (2:Fin 4))=P.derivative:=by
   simp [specialization]
 rw [hR, ←solution_slope_identity K F P γ hsolution,
   derivative_specialization K P γ M,
   derivative_specialization K P γ (polyH K F)]
 push_cast
 ring
theorem derivative_power_cancellation (H A:Polynomial K) (n:ℕ):
   H^2*(H^n*A).derivative-
     (n:Polynomial K)*(H^n*A)*H*H.derivative=
     H^(n+2)*A.derivative:=by
 cases n with
 | zero => simp [pow_two]
 | succ n =>
     rw [Polynomial.derivative_mul,Polynomial.derivative_pow_succ]
     simp only [Polynomial.C_add,Polynomial.C_1,Polynomial.C_eq_natCast,
       Nat.cast_add,Nat.cast_one,pow_succ]
     ring
theorem specialization_numerator_eq
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0) (b:ℕ):
   specialization K P γ (numerator K F b)=
     specialization K P γ (polyH K F)^(2*b)*Polynomial.derivative^[b] P:=by
 induction b with
 | zero => simp [numerator_zero,specialization]
 | succ b ih =>
     rw [numerator_succ,specialization_numeratorStep K F (numerator K F b) P γ b
       hsolution,ih]
     have hexp:2*(b+1)=2*b+2:=by omega
     rw [hexp,Function.iterate_succ_apply']
     simpa only [Nat.cast_mul,Nat.cast_ofNat] using
       derivative_power_cancellation K (specialization K P γ (polyH K F))
         (Polynomial.derivative^[b] P) (2*b)
theorem specialization_numerator_zero_of_degree
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0) (b:ℕ) (hb:P.natDegree < b):
   specialization K P γ (numerator K F b)=0:=by
 rw [specialization_numerator_eq K F P γ hsolution b,
   Polynomial.iterate_derivative_eq_zero hb,mul_zero]
end PolynomialIdentities
section ActualPoints
variable {K L:Type*} [Field K] [Field L]
def polynomialPoint (coefficients:K →+*L) (P:Polynomial K) (γ:K) (ξ:L):
   Fin 4 → L:=
 ![ξ,P.eval₂ coefficients ξ,P.derivative.eval₂ coefficients ξ,coefficients γ]
theorem eval_polynomialPoint_eq_specialization
   (coefficients:K →+*L) (P:Polynomial K) (γ:K) (ξ:L) (Q:Poly4 K):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ) Q=
     (specialization K P γ Q).eval₂ coefficients ξ:=by
 have hhom:
     (Polynomial.eval₂RingHom coefficients ξ).comp (specialization K P γ).toRingHom=
       MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,specialization]
   · intro i
     fin_cases i <;> simp [RingHom.comp_apply,specialization,polynomialPoint]
 exact (DFunLike.congr_fun hhom Q).symm
theorem polynomialPoint_relation
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ) F=0:=by
 rw [eval_polynomialPoint_eq_specialization,hsolution]
 simp
theorem polynomialPoint_numerator_zero
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0) (b:ℕ) (hb:P.natDegree < b):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (numerator K F b)=0:=by
 rw [eval_polynomialPoint_eq_specialization,
   specialization_numerator_zero_of_degree K F P γ hsolution b hb]
 simp
end ActualPoints
end
end ProximityPrize.SubmissionLower.RCN231
end PackedLegacy_D9

/-! Packed from ProximityPrize.SubmissionLower.T. -/
section PackedLegacy_T
namespace ProximityPrize.SubmissionLower.RCN229
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN319 RCN347
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {K L:Type*} [Field K] [Field L]
theorem taylor_coeff_eq_derivative_div_factorial
   (P:Polynomial L) (ξ:L) (j:ℕ) (hfactorial:(j.factorial:L)≠0):
   (Polynomial.taylor ξ P).coeff j=
     (Polynomial.derivative^[j] P).eval ξ/(j.factorial:L):=by
 have hpoly:(j.factorial:Polynomial L)*Polynomial.hasseDeriv j P=
     Polynomial.derivative^[j] P:=by
   have h:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=L) j) P
   change j.factorial • (Polynomial.hasseDeriv j P)=
     Polynomial.derivative^[j] P at h
   simpa only [nsmul_eq_mul] using h
 have hvalue:=congrArg (Polynomial.evalRingHom ξ) hpoly
 simp only [map_mul,map_natCast] at hvalue
 change (j.factorial:L)*(Polynomial.hasseDeriv j P).eval ξ=
   (Polynomial.derivative^[j] P).eval ξ at hvalue
 rw [Polynomial.taylor_coeff]
 apply (eq_div_iff hfactorial).mpr
 simpa only [mul_comm] using hvalue
theorem polynomialPoint_jetCoefficient_eq
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (j:ℕ):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F (polynomialPoint coefficients P γ ξ)
         (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular)
       (contactCoordinate K F (1:Fin 4)) j=
     (Polynomial.derivative^[j] P).eval₂ coefficients ξ/(j.factorial:L):=by
 let v:=polynomialPoint coefficients P γ ξ
 let h:=MvPolynomial.eval₂Hom coefficients v (polyH K F)
 have hH:h≠0:=hregular
 have hnum:MvPolynomial.eval₂Hom coefficients v (numerator K F j)=
     h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by
   rw [eval_polynomialPoint_eq_specialization,
     specialization_numerator_eq K F P γ hsolution j,
     Polynomial.eval₂_mul,Polynomial.eval₂_pow]
   rw [←eval_polynomialPoint_eq_specialization coefficients P γ ξ (polyH K F)]
 have hcancel:h^(2*j)*h⁻¹^(2*j)=1:=by
   rw [←mul_pow,mul_inv_cancel₀ hH,one_pow]
 rw [jetCoefficient_eq_evaluated_numerator,hnum]
 change (h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ)*
     h⁻¹^(2*j)/(j.factorial:L)=_
 congr 1
 calc
   (h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ)*h⁻¹^(2*j)=
       (h^(2*j)*h⁻¹^(2*j))*
         (Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by ring
   _=(Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by rw [hcancel,one_mul]
theorem polynomialPoint_jetCoefficient_eq_taylor_coeff
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (j:ℕ)
   (hfactorial:(j.factorial:L)≠0):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F (polynomialPoint coefficients P γ ξ)
         (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular)
       (contactCoordinate K F (1:Fin 4)) j=
     (Polynomial.taylor ξ (P.map coefficients)).coeff j:=by
 rw [polynomialPoint_jetCoefficient_eq coefficients F P γ ξ hsolution hregular j,
   Polynomial.eval₂_eq_eval_map, ←Polynomial.iterate_derivative_map]
 exact (taylor_coeff_eq_derivative_div_factorial (P.map coefficients) ξ j hfactorial).symm
theorem reconstructedPolynomial_eq_taylor_of_solution
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w):
   reconstructedPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w=
     Polynomial.taylor ξ (P.map coefficients):=by
 ext j
 simp only [reconstructedPolynomial,jetPolynomial_coeff]
 by_cases hj:j < w+1
 · rw [if_pos hj]
   exact polynomialPoint_jetCoefficient_eq_taylor_coeff coefficients F P γ ξ
     hsolution hregular j
     (factorial_cast_ne_zero_below_characteristic p j (by omega))
 · rw [if_neg hj]
   have hmap:(P.map coefficients).natDegree ≤ w:=
     Polynomial.natDegree_map_le.trans hdegree
   symm
   apply Polynomial.coeff_eq_zero_of_natDegree_lt
   rw [Polynomial.natDegree_taylor]
   omega
theorem globalPolynomial_eq_map_of_solution
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w):
   globalPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w=
     P.map coefficients:=by
 change Polynomial.taylor (-ξ)
   (reconstructedPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w)=_
 rw [reconstructedPolynomial_eq_taylor_of_solution coefficients F P γ ξ hsolution
   hregular p w hchar hdegree,Polynomial.taylor_taylor,neg_add_cancel,
   Polynomial.taylor_zero]
theorem factorial_agreement_zero_iff_original_agreement
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w)
   (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
       (agreementNumerator F w (fun j:ℕ => (j.factorial:K)⁻¹) x u₀ u₁)=0 ↔
     P.eval x=u₀+γ*u₁:=by
 have heq:=factorial_agreement_zero_iff_actual_agreement coefficients F
   (polynomialPoint coefficients P γ ξ)
   (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w x u₀ u₁
 rw [←globalPolynomial_eval coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w (coefficients x),
   globalPolynomial_eq_map_of_solution coefficients F P γ ξ hsolution hregular
     p w hchar hdegree] at heq
 have hvalue:(P.map coefficients).eval (coefficients x)=coefficients (P.eval x):=by
   rw [←Polynomial.eval₂_eq_eval_map,Polynomial.eval₂_at_apply]
 have hseed:polynomialPoint coefficients P γ ξ (3:Fin 4)=coefficients γ:=rfl
 rw [hvalue,hseed, ←map_mul, ←map_add] at heq
 exact heq.trans coefficients.injective.eq_iff
end
end ProximityPrize.SubmissionLower.RCN229
end PackedLegacy_T

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier07 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.B0. -/
section PackedLegacy_B0
namespace ProximityPrize.SubmissionLower.RCN065
open RCN002 RCN136 RCN224 RCN139 RCN233 RCN231 RCN229 RCN313 RCN047 RCN147 RCN319
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
def componentCoefficients:K →+*CoordinateField Ω P:=
 (algebraMap Ω (CoordinateField Ω P)).comp (φ.comp Polynomial.C)
def componentPoint:Fin 4 → CoordinateField Ω P:=
 Fin.cases (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X)) (coordinate Ω P)
theorem component_evaluation (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=
     coordinateEvaluation Ω P (surfaceMap φ F):=by
 have hhom:MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P)=
     (coordinateEvaluation Ω P).toRingHom.comp (surfaceMap φ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [componentCoefficients,RingHom.comp_apply]
   · intro i
     refine Fin.cases ?_ (fun j => ?_) i
     · simp [componentPoint,RingHom.comp_apply]
     · simp only [MvPolynomial.eval₂Hom_X',RingHom.comp_apply,surfaceMap_X_succ]
       rfl
 exact RingHom.congr_fun hhom F
theorem component_evaluation_zero_iff (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=0 ↔
     surfaceMap φ F∈P:=by
 rw [component_evaluation]
 change surfaceMap φ F∈RingHom.ker (coordinateEvaluation Ω P).toRingHom ↔ _
 rw [coordinateEvaluation_ker]
variable (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
include hF in
theorem component_relation:
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=0:=
 (component_evaluation_zero_iff φ P F).mpr hF
include hH in
theorem component_regular:
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0:=
 (component_evaluation_zero_iff φ P _).not.mpr hH
def truncatedPolynomial (w:ℕ):Polynomial (CoordinateField Ω P):=
 globalPolynomial (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w
theorem truncatedPolynomial_natDegree_le (w:ℕ):
   (truncatedPolynomial φ P F hF hH w).natDegree ≤ w:=
 globalPolynomial_natDegree_le _ _ _ _ _ _
theorem truncatedPolynomial_initial_value (w:ℕ):
   (truncatedPolynomial φ P F hF hH w).eval
     (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X))=coordinate Ω P 0:=
 globalPolynomial_initial_value (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w
theorem truncatedPolynomial_initial_slope (w:ℕ) (hw:1 ≤ w):
   (truncatedPolynomial φ P F hF hH w).derivative.eval
     (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X))=coordinate Ω P 1:=
 globalPolynomial_initial_slope (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w hw
theorem agreement_mem_iff_truncated_value (w:ℕ) (x u₀ u₁:K):
   surfaceMap φ (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) x u₀ u₁)∈P ↔
     (truncatedPolynomial φ P F hF hH w).eval (componentCoefficients φ P x)=
       componentCoefficients φ P u₀+coordinate Ω P 2*componentCoefficients φ P u₁:=by
 rw [←component_evaluation_zero_iff]
 rw [factorial_agreement_zero_iff_actual_agreement (componentCoefficients φ P) F
   (componentPoint φ P) (component_relation φ P F hF) (component_regular φ P F hH)]
 rw [←globalPolynomial_eval]
 rfl
def identityNodes {ι:Type*} (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ):Finset ι:=by
 classical
 exact nodes.filter (fun i => surfaceMap φ
   (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i))∈P)
theorem identityNodes_subset {ι:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ):
   identityNodes φ P F nodes x u₀ u₁ w ⊆ nodes:=by
 classical
 exact Finset.filter_subset _ _
theorem exists_common_pencil_of_many_identities {ι τ:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ)
   (hinj:Set.InjOn x nodes)
   (hcard:w < (identityNodes φ P F nodes x u₀ u₁ w).card)
   (seed:τ → K) (selected:τ → Polynomial K)
   (hdegree:∀ t,(selected t).natDegree ≤ w)
   (hvalues:∀ t i,i∈identityNodes φ P F nodes x u₀ u₁ w →
     (selected t).eval (x i)=u₀ i+seed t*u₁ i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     truncatedPolynomial φ P F hF hH w=
       P₀.map (componentCoefficients φ P)+Polynomial.C (coordinate Ω P 2)*
         P₁.map (componentCoefficients φ P)∧
     ∀ t,selected t=P₀+Polynomial.C (seed t)*P₁:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let seeds:Option τ → CoordinateField Ω P:=fun
   | none => coordinate Ω P 2
   | some t => componentCoefficients φ P (seed t)
 let polys:Option τ → Polynomial (CoordinateField Ω P):=fun
   | none => truncatedPolynomial φ P F hF hH w
   | some t => (selected t).map (componentCoefficients φ P)
 have hI:Set.InjOn x I:=hinj.mono (identityNodes_subset φ P F nodes x u₀ u₁ w)
 have hd:∀ t,(polys t).natDegree ≤ w:=by
   intro t
   cases t with
   | none => exact truncatedPolynomial_natDegree_le φ P F hF hH w
   | some t => exact Polynomial.natDegree_map_le.trans (hdegree t)
 have hv:∀ t i,i∈I → (polys t).eval (componentCoefficients φ P (x i))=
     componentCoefficients φ P (u₀ i)+seeds t*componentCoefficients φ P (u₁ i):=by
   intro t i hi
   cases t with
   | none =>
     apply (agreement_mem_iff_truncated_value φ P F hF hH w (x i) (u₀ i) (u₁ i)).mp
     exact (Finset.mem_filter.mp hi).2
   | some t =>
     change ((selected t).map (componentCoefficients φ P)).eval _=_
     rw [Polynomial.eval_map_apply,hvalues t i hi,map_add,map_mul]
 obtain ⟨P₀,P₁,h₀,h₁,hp⟩:=exists_basefield_affine_pencil_of_identity_nodes
   (componentCoefficients φ P) I x u₀ u₁ w hcard hI seeds polys hd hv
 refine ⟨P₀,P₁,h₀,h₁,hp none,?_⟩
 intro t
 apply Polynomial.map_injective (componentCoefficients φ P) (componentCoefficients φ P).injective
 simpa only [polys,seeds,Polynomial.map_add,Polynomial.map_mul,
   Polynomial.map_C] using hp (some t)
theorem coordinates_affine_of_basefield_pencil (w:ℕ) (hw:1 ≤ w)
   (P₀ P₁:Polynomial K)
   (hp:truncatedPolynomial φ P F hF hH w=
     P₀.map (componentCoefficients φ P)+Polynomial.C (coordinate Ω P 2)*
       P₁.map (componentCoefficients φ P)):
   coordinate Ω P 0=algebraMap Ω (CoordinateField Ω P)
       ((P₀.map (φ.comp Polynomial.C)).eval (φ Polynomial.X))+
     coordinate Ω P 2*algebraMap Ω (CoordinateField Ω P)
       ((P₁.map (φ.comp Polynomial.C)).eval (φ Polynomial.X))∧
   coordinate Ω P 1=algebraMap Ω (CoordinateField Ω P)
       ((P₀.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X))+
     coordinate Ω P 2*algebraMap Ω (CoordinateField Ω P)
       ((P₁.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X)):=by
 apply affine_coordinates_of_polynomial_pencil Ω P (φ Polynomial.X)
   (truncatedPolynomial φ P F hF hH w)
   (P₀.map (φ.comp Polynomial.C)) (P₁.map (φ.comp Polynomial.C))
 · simpa only [Polynomial.map_map,componentCoefficients] using hp
 · exact truncatedPolynomial_initial_value φ P F hF hH w
 · exact truncatedPolynomial_initial_slope φ P F hF hH w hw
include hF hH in
theorem seed_transcendental_of_many_identities {ι:Type*} [IsAlgClosed Ω]
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ) (hw:1 ≤ w)
   (hinj:Set.InjOn x nodes)
   (hcard:w < (identityNodes φ P F nodes x u₀ u₁ w).card)
   (hnonpoint:∀ v:Fin 3 → Ω,P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   Transcendental Ω (coordinate Ω P 2):=by
 obtain ⟨P₀,P₁,_,_,hp,_⟩:=
   exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hcard
     (fun t:Empty => t.elim) (fun t:Empty => t.elim)
     (fun t => t.elim) (fun t => t.elim)
 obtain ⟨hy,hr⟩:=coordinates_affine_of_basefield_pencil φ P F hF hH w hw P₀ P₁ hp
 exact seed_transcendental_of_affine_coordinates Ω P hnonpoint _ _ _ _ hy hr
theorem selected_agrees_on_identity_nodes {ι:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (p w:ℕ) [CharP Ω p]
   (hw:w < p) (S:Polynomial K) (γ:K) (hdegree:S.natDegree ≤ w)
   (hsolution:specialization K S γ F=0)
   (hregular:MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:P ≤ RingHom.ker (MvPolynomial.aeval
     (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)).toRingHom):
   ∀ i∈identityNodes φ P F nodes x u₀ u₁ w,
     S.eval (x i)=u₀ i+γ*u₁ i:=by
 classical
 intro i hi
 have hmem:=(Finset.mem_filter.mp hi).2
 have hz:=hpoint hmem
 change MvPolynomial.eval
   (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)
   (surfaceMap φ (agreementNumerator F w (fun j => (j.factorial:K)⁻¹)
     (x i) (u₀ i) (u₁ i)))=0 at hz
 rw [eval_surfaceMap] at hz
 have hv:Fin.cases (φ Polynomial.X)
     (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)=
     polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv] at hz
 exact (factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F S γ
   (φ Polynomial.X) hsolution hregular p w hw hdegree (x i) (u₀ i) (u₁ i)).mp hz
end
end ProximityPrize.SubmissionLower.RCN065
end PackedLegacy_B0

/- Library component HJ is loaded from Mathlib.Combinatorics.Enumerative.DoubleCounting. -/

/-! Packed from ProximityPrize.SubmissionLower.BX. -/
section PackedLegacy_BX
namespace ProximityPrize.SubmissionLower.RCN173
theorem enlarge_exempt_card_bound
   {q n a i w M:ℕ}
   (hiw:i ≤ w) (hwa:w ≤ a) (han:a ≤ n)
   (hcount:q*(a-i) ≤ (n-i)*M):
   q*(a-w) ≤ (n-w)*M:=by
 by_cases hqM:q ≤ M
 · calc
     q*(a-w) ≤ M*(a-w):=Nat.mul_le_mul_right _ hqM
     _ ≤ M*(n-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _=(n-w)*M:=Nat.mul_comm _ _
 · have hMq:M ≤ q:=(Nat.lt_of_not_ge hqM).le
   have ha:a-i=(a-w)+(w-i):=by omega
   have hn:n-i=(n-w)+(w-i):=by omega
   have hcount':
       q*(a-w)+q*(w-i) ≤
         (n-w)*M+(w-i)*M:=by
     simpa only [ha,hn,Nat.mul_add,Nat.add_mul] using hcount
   have hcancel:(w-i)*M ≤ q*(w-i):=by
     calc
       (w-i)*M ≤ (w-i)*q:=Nat.mul_le_mul_left _ hMq
       _=q*(w-i):=Nat.mul_comm _ _
   omega
section FiniteIncidence
variable {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
 (relation:Seed → Node → Prop)
 [∀ seed node,Decidable (relation seed node)]
theorem incidence_after_exempt_nodes
   (seeds:Finset Seed) (nodes identities:Finset Node) (a M:ℕ)
   (hidentities:identities ⊆ nodes)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-identities.card) ≤
     (nodes.card-identities.card)*M:=by
 have hremaining (seed:Seed) (hseed:seed∈seeds):
     a-identities.card ≤ ((nodes \ identities).filter (relation seed)).card:=by
   have hsub:(nodes.filter (relation seed)) \ identities ⊆
       (nodes \ identities).filter (relation seed):=by
     intro node hnode
     obtain ⟨hfiltered,hnot⟩:=Finset.mem_sdiff.mp hnode
     obtain ⟨hnodes,hagree⟩:=Finset.mem_filter.mp hfiltered
     exact Finset.mem_filter.mpr
       ⟨Finset.mem_sdiff.mpr ⟨hnodes,hnot⟩,hagree⟩
   calc
     a-identities.card ≤
         (nodes.filter (relation seed)).card-identities.card:=
       Nat.sub_le_sub_right (hagreement seed hseed) identities.card
     _ ≤ ((nodes.filter (relation seed)) \ identities).card:=
       Finset.le_card_sdiff identities (nodes.filter (relation seed))
     _ ≤ ((nodes \ identities).filter (relation seed)).card:=
       Finset.card_le_card hsub
 have hdouble:seeds.card • (a-identities.card) ≤
     (nodes \ identities).card • M:=
   Finset.card_nsmul_le_card_nsmul (R:=ℕ) (r:=relation)
     (s:=seeds) (t:=nodes \ identities) hremaining hfiber
 simpa [nsmul_eq_mul,Finset.card_sdiff_of_subset hidentities] using hdouble
theorem sharp_incidence_bound
   (seeds:Finset Seed) (nodes identities:Finset Node) (a w M:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-w) ≤ (nodes.card-w)*M:=by
 exact enlarge_exempt_card_bound hcard hwa.le han
   (incidence_after_exempt_nodes relation seeds nodes identities a M
     hidentities hagreement hfiber)
end FiniteIncidence
end ProximityPrize.SubmissionLower.RCN173
end PackedLegacy_BX

/-! Packed from ProximityPrize.SubmissionLower.J. -/
section PackedLegacy_J
namespace ProximityPrize.SubmissionLower.RCN238
open scoped Classical BigOperators
open RCN002 RCN005 RCN007 RCN136 RCN231 RCN229 RCN313 RCN065 RCN319
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
local instance _root_.ProximityPrize.SubmissionLower.RCN238.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN238.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
def selectedPoint (selected:K → Polynomial K) (γ:K):Fin 3 → Ω:=
 fun i↦polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) i.succ
theorem selectedPoint_seed (selected:K → Polynomial K) (γ:K):
   selectedPoint φ selected γ (2:Fin 3)=(φ.comp Polynomial.C) γ:=rfl
theorem selectedPoint_injective (selected:K → Polynomial K):
   Function.Injective (selectedPoint φ selected):=by
 intro γ η h
 apply (φ.comp Polynomial.C).injective
 simpa only [selectedPoint_seed] using congrFun h (2:Fin 3)
def agreementPolynomial (F:MvPolynomial (Fin 4) K) (w:ℕ) (x u₀ u₁:K):
   MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁)
theorem selected_agreement_zero_iff
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (γ:K) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:specialization K (selected γ) γ F=0)
   (hregular:MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (x u₀ u₁:K):
   MvPolynomial.aeval (selectedPoint φ selected γ)
     (agreementPolynomial φ F w x u₀ u₁)=0 ↔
       (selected γ).eval x=u₀+γ*u₁:=by
 change MvPolynomial.eval (selectedPoint φ selected γ)
   (surfaceMap φ (agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁))=0 ↔ _
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
 exact factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F
   (selected γ) γ (φ Polynomial.X) hsolution hregular p w hchar hdegree x u₀ u₁
variable [IsAlgClosed Ω]
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
def componentCost (cap:Fin 3 → ℕ):ℕ:=
 ∑ j,cap j*actualCoordinateDegree Ω P j
theorem agreement_fiber_card_le
   (hproj:ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (hproper:agreementPolynomial φ F w x u₀ u₁∉P)
   (cap:Fin 3 → ℕ)
   (hcap:∀ j,(agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ componentCost P cap:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hpointsP:∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint γ (Finset.mem_filter.mp hγ).1
 have hpointsF:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁)=0:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcount:=RCN007.finite_zero_points_le_box Ω P hproj hnonpoint
   (agreementPolynomial φ F w x u₀ u₁) hproper cap hcap points hpointsP hpointsF
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rw [hcard] at hcount
 unfold componentCost
 exact_mod_cast hcount
theorem coordinateDegree_pos_of_transcendental
   (hproj:ProjectionsFiniteSeparable Ω P) (j:Fin 3)
   (hj:Transcendental Ω (coordinate Ω P j)):
   1 ≤ actualCoordinateDegree Ω P j:=by
 letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=rationalBaseAlgebra Ω P j hj
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω P):=(hproj j hj).1
 rw [actualCoordinateDegree_of_transcendental Ω P j hj]
 exact Module.finrank_pos
def NoLargeSelectedPencil (selected:K → Polynomial K) (Γ:Finset K) (w e:ℕ):Prop:=
 ∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
   (Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)).card ≤ e+1
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN238.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp
   (hproj:ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap φ F∈P)
   (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤ (nodes.card-w)*componentCost P cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hfiber:∀ i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card ≤ componentCost P cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact agreement_fiber_card_le φ P hproj hnonpoint F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u₀ i) (u₁ i) hproper cap (hcap i hinodes)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     (componentCost P cap) (identityNodes_subset φ P F nodes x u₀ u₁ w) hI hwa han
     hagreement hfiber
   omega
 · have hc:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u₀ i+t.1*u₁ i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P₀,P₁,h₀,h₁,_,hpencil⟩:=
     exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
       (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
       (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH nodes x u₀ u₁ w hw
     hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental P hproj (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
end
end ProximityPrize.SubmissionLower.RCN238
end PackedLegacy_J

/-! Packed from ProximityPrize.SubmissionLower.X2. -/
section PackedLegacy_X2
namespace ProximityPrize.SubmissionLower.RCN371
open RCN002
noncomputable section
variable (K:Type) [Field K]
abbrev Original:=MvPolynomial (Fin 3) K
abbrev Collected:=MvPolynomial (Fin 2) (Polynomial K)
abbrev RationalPolynomials:=MvPolynomial (Fin 2) (RatFunc K)
def collectFirst:Original K ≃ₐ[K] Collected K:=
 (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)).trans
   (MvPolynomial.optionEquivRight K (Fin 2))
def collect (order:Fin 3 ≃ Fin 3):Original K ≃ₐ[K] Collected K:=
 (MvPolynomial.renameEquiv K order.symm).trans (collectFirst K)
@[simp] theorem collect_C (order:Fin 3 ≃ Fin 3) (a:K):
   collect K order (MvPolynomial.C a)=MvPolynomial.C (Polynomial.C a):=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem collect_X_first (order:Fin 3 ≃ Fin 3):
   collect K order (MvPolynomial.X (order 0))=MvPolynomial.C Polynomial.X:=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem collect_X_other (order:Fin 3 ≃ Fin 3) (j:Fin 2):
   collect K order (MvPolynomial.X (order j.succ))=MvPolynomial.X j:=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
def coefficientLift (order:Fin 3 ≃ Fin 3):Polynomial K →+*Original K:=
 (collect K order).symm.toRingHom.comp MvPolynomial.C
@[simp] theorem coefficientLift_C (order:Fin 3 ≃ Fin 3) (a:K):
   coefficientLift K order (Polynomial.C a)=MvPolynomial.C a:=by
 apply (collect K order).injective
 simp [coefficientLift]
@[simp] theorem coefficientLift_X (order:Fin 3 ≃ Fin 3):
   coefficientLift K order Polynomial.X=MvPolynomial.X (order 0):=by
 apply (collect K order).injective
 simp [coefficientLift]
def rationalMap (order:Fin 3 ≃ Fin 3):Original K →+*RationalPolynomials K:=
 (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K))).comp
   (collect K order).toRingHom
theorem rationalMap_injective (order:Fin 3 ≃ Fin 3):
   Function.Injective (rationalMap K order):=
 (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).comp
   (collect K order).injective
theorem rationalMap_ne_zero (order:Fin 3 ≃ Fin 3) (F:Original K) (hF:F≠0):
   rationalMap K order F≠0:=by
 intro h
 apply hF
 apply rationalMap_injective K order
 simpa only [map_zero] using h
attribute [local instance] MvPolynomial.algebraMvPolynomial
def coefficientDenominators:Submonoid (Collected K):=
 (nonZeroDivisors (Polynomial K)).map MvPolynomial.C
local instance _root_.ProximityPrize.SubmissionLower.RCN371.instIsLocalizationCollectedCoefficientDenominatorsRationalPolynomials :IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
theorem rationalMap_eq (order:Fin 3 ≃ Fin 3) (F:Original K):
   rationalMap K order F=
     algebraMap (Collected K) (RationalPolynomials K) (collect K order F):=rfl
theorem collected_principal_isPrime (order:Fin 3 ≃ Fin 3)
   (G:Original K) (hG:Irreducible G):
   (Ideal.span ({collect K order G}:Set (Collected K))).IsPrime:=by
 have hi:Irreducible (collect K order G):=
   (MulEquiv.irreducible_iff (collect K order)).mpr hG
 exact Ideal.isPrime_span_singleton_of_prime hi.prime
section ActualComponent
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
def collectedEvaluation:Collected K →+*CoordinateField K P:=
 (coordinateEvaluation K P).toRingHom.comp (collect K order).symm.toRingHom
@[simp] theorem collectedEvaluation_collect (F:Original K):
   collectedEvaluation K order P (collect K order F)=coordinateEvaluation K P F:=by
 simp [collectedEvaluation]
@[simp] theorem collectedEvaluation_C (H:Polynomial K):
   collectedEvaluation K order P (MvPolynomial.C H)=
     Polynomial.aeval (coordinate K P (order 0)) H:=by
 have hhom:(coordinateEvaluation K P).toRingHom.comp (coefficientLift K order)=
     (Polynomial.aeval (coordinate K P (order 0))).toRingHom:=by
   apply Polynomial.ringHom_ext
   · intro a
     change coordinateEvaluation K P (coefficientLift K order (Polynomial.C a))=
       Polynomial.aeval (coordinate K P (order 0)) (Polynomial.C a)
     rw [coefficientLift_C,Polynomial.aeval_C]
     exact MvPolynomial.algHom_C (coordinateEvaluation K P) a
   · change coordinateEvaluation K P (coefficientLift K order Polynomial.X)=
       Polynomial.aeval (coordinate K P (order 0)) Polynomial.X
     rw [coefficientLift_X,Polynomial.aeval_X]
     rfl
 exact RingHom.congr_fun hhom H
theorem coefficientDenominators_disjoint_of_component
   (G:Original K) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collect K order G}:Set (Collected K)):Set (Collected K)):=by
 have hGzero:coordinateEvaluation K P G=0:=by
   change G∈RingHom.ker (coordinateEvaluation K P).toRingHom
   rw [coordinateEvaluation_ker]
   exact hmem
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨H,hH,rfl⟩:=Submonoid.mem_map.mp ha
 have hH0:H≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hH
 obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hI
 have hroot:Polynomial.aeval (coordinate K P (order 0)) H=0:=by
   have heval:=congrArg (collectedEvaluation K order P) hU
   simpa only [map_mul,collectedEvaluation_collect,collectedEvaluation_C,
     hGzero,zero_mul] using heval
 exact hH0 (transcendental_iff.mp ht H hroot)
theorem localized_principal_isPrime_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   (Ideal.span ({rationalMap K order G}:Set (RationalPolynomials K))).IsPrime:=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collect K order G}:Set (Collected K)))
   (collected_principal_isPrime K order G hG)
   (coefficientDenominators_disjoint_of_component K order P G hmem ht)
 simpa only [Ideal.map_span,Set.image_singleton, ←rationalMap_eq] using hp
theorem rationalMap_irreducible_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   Irreducible (rationalMap K order G):=by
 exact ((Ideal.span_singleton_prime (rationalMap_ne_zero K order G hG.ne_zero)).mp
   (localized_principal_isPrime_of_component K order P G hG hmem ht)).irreducible
theorem rationalMap_dvd_iff_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
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
     (coefficientDenominators_disjoint_of_component K order P G hmem ht)] at hu
   obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collect K order).symm U,?_⟩
   apply (collect K order).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
 · intro hdiv
   exact map_dvd (rationalMap K order) hdiv
end ActualComponent
end
end ProximityPrize.SubmissionLower.RCN371
end PackedLegacy_X2
end Compact_PackedLegacyCore1


