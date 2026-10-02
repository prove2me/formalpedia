-- Prove2me | Definitions.Def_Yukon_baa5877344aa01c8873b10a8
-- name    : Yukon_baa5877344aa01c8873b10a8
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T22:10:20.700917+00:00
-- url     : https://prove2.me/theorems/a58ca0c8-44c2-4383-8efd-32fd8c8a1d36
-- title:
--   LowerFoundation source part 3/5
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-compact-module-Yukon_baa5877344aa01c8873b10a8
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMjBlNDQwMGU1MWI3NjdjZDkyN2U4ZmNlNDc1YjM3ZWMxNDNmZjZmYzQxOGQxYmE3NmMwZmU4OTI0ZjExMDhmNSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tY29tcGFjdC1tb2R1bGUtWXVrb25fYmFhNTg3NzM0NGFhMDFjODg3M2IxMGE4IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fYmFhNTg3NzM0NGFhMDFjODg3M2IxMGE4IiwidiI6Mn0]

import Definitions.Def_Yukon_1af791eb6f6293537a7eba7b
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


/-! Packed from ProximityPrize.SubmissionLower.M9. -/
section PackedLegacy_M9
namespace ProximityPrize.SubmissionLower.RCN209
open scoped Classical BigOperators WithZero
open RCN002 RCN264 RCN344 RCN341 RCN022 RCN207 RCN208 RCN064 RCN202 RCN095 RCN187
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K
theorem exists_separable_moving_coordinates (F A H G:Poly)
   (base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1):
   ∃ (Q U:Poly) (J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1)),
     PolynomialInFlag (2 • unitAllFlag) Q∧PolynomialInFlag unitYZFlag U∧
     ∀ C:RegularComponent K F A H,
       U∉C.1∧SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U∧
       (∀ v:Place K (CoordinateField K C.1),
         poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
           movingPoleTarget C.1 H G v)∧
       (∀ v∈movingRelevantPlaces (base C) (movingRatio C.1 H G),
         v.val (coordinateEvaluation K C.1 U)=WithZero.exp
           (max (poleOrder v.val (coordinate K C.1 0)) (poleOrder v.val (coordinate K C.1 2)))):=by
 obtain ⟨Q,U,hQ,hU,h⟩:=exists_common_original_projection F A H G base
 have gate (C:RegularComponent K F A H):=moving_projection_gate (base C) H G Q U (h C).2.1
 let J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1):=
   fun C↦{
     embedding:=elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) (gate C).choose
     finite:=(gate C).choose_spec.1
     separable:=(gate C).choose_spec.2.1}
 have hv (C:RegularComponent K F A H):
     SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U:=
   elementEmbedding_variable K (CoordinateField K C.1) _ (gate C).choose
 refine ⟨Q,U,J,hQ,hU,fun C↦⟨(h C).1,hv C,?_,(h C).2.2.2⟩⟩
 intro v
 rw [hv C]
 exact (h C).2.2.1 v
variable {E:Type} [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
theorem exists_moving_projection_family (F H G:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (base:∀ C:RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (p:FlagDegree) (hFp:PolynomialInFlag p F) (a b s:ℕ) (C0:FlagDegree)
   (hH:PolynomialInFlag (⟨a,b+1,s+1⟩:FlagDegree) H)
   (hG:PolynomialInFlag (⟨a,b,s+3⟩:FlagDegree) G)
   (c:Fin (k+1) → FlagDegree) (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar):
   ∃ J:∀ C:RegularComponent K F (filteredCut k B H G) H,
       SeparableCoordinate K (CoordinateField K C.1),
     (∀ (C:RegularComponent K F (filteredCut k B H G) H)
         (v:Place K (CoordinateField K C.1)),
       poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
         movingPoleTarget C.1 H G v)∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,
       SeparableCoordinate.degree K (CoordinateField K C.1) (J C)) ≤
       flagMixed p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree)):=by
 classical
 obtain ⟨Q,U,J,hQ,hU,hJ⟩:=exists_separable_moving_coordinates F (filteredCut k B H G) H G base
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).embedding.toRingHom.toAlgebra
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     IsScalarTower K (RatFunc K) (CoordinateField K C.1):=fun C↦
       IsScalarTower.of_algebraMap_eq fun a↦((J C).embedding.commutes a).symm
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     FiniteDimensional (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).finite
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).separable
 have hj (C:RegularComponent K F (filteredCut k B H G) H):
     algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=movingValue C.1 H G Q U:=
   (hJ C).2.1
 have hdeg:p.zOnly+p.yz+p.all < pchar:=by
   nlinarith
 obtain ⟨hN,hA⟩:=fiber_small_flags (E:=E) a b s k C0 H G Q U B c hH hG hQ hU hB hc
 have hcount:=sum_moving_degrees_le (E:=E) F H G Q U k B hj (fun C↦(hJ C).1)
   hF hderiv p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree))
   hFp hN hA pchar hdeg hmix
 refine ⟨J,fun C v↦(hJ C).2.2.1 v,?_⟩
 simpa only [SeparableCoordinate.degree] using hcount
end
end ProximityPrize.SubmissionLower.RCN209
end PackedLegacy_M9

/-! Packed from ProximityPrize.SubmissionLower.M4. -/
section PackedLegacy_M4
namespace ProximityPrize.SubmissionLower.RCN200
open scoped Classical BigOperators WithZero
open RCN002 RCN264 RCN344 RCN341 RCN046 RCN095 RCN295 RCN187 RCN207 RCN064 RCN209 RCN199
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K
def budgetOfProjections (F A H G:Poly)
   {base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (unit:AdaptiveUnitProjectionFamily base p q)
   (J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1))
   (hJ:∀ (C:RegularComponent K F A H) (v:Place K (CoordinateField K C.1)),
     poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
       movingPoleTarget C.1 H G v) (C:RegularComponent K F A H):
   MovingPoleBudget C.1 H G where
 zCost:=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)
 yzCost:=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)
 allCost:=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C)
 movingCost:=SeparableCoordinate.degree K (CoordinateField K C.1) (J C)
 zPole:=unit.toAdaptiveUnitPoleBudget.zPole C
 yzPole:=unit.toAdaptiveUnitPoleBudget.yzPole C
 allPole:=unit.toAdaptiveUnitPoleBudget.allPole C
 movingPole:=by
   intro W
   calc
     (∑ v∈W,movingPoleTarget C.1 H G v)=
         ∑ v∈W,RCN346.poleOrder K (CoordinateField K C.1) v
           (SeparableCoordinate.value K (CoordinateField K C.1) (J C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact (hJ C v).symm
     _ ≤ (SeparableCoordinate.degree K (CoordinateField K C.1) (J C):ℤ):=
       SeparableCoordinate.finite_sum_pole_le_degree K (CoordinateField K C.1) (J C) W
variable {E:Type} [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
theorem exists_moving_pole_budget_family (F H G:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (base:∀ C:RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
   (p firstCutFlag:FlagDegree) (unit:AdaptiveUnitProjectionFamily base p firstCutFlag)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (hFp:PolynomialInFlag p F) (a b s:ℕ) (C0:FlagDegree)
   (hH:PolynomialInFlag (⟨a,b+1,s+1⟩:FlagDegree) H)
   (hG:PolynomialInFlag (⟨a,b,s+3⟩:FlagDegree) G)
   (c:Fin (k+1) → FlagDegree) (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar):
   ∃ budget:∀ C:RegularComponent K F (filteredCut k B H G) H,MovingPoleBudget C.1 H G,
     (∀ C,(budget C).zCost=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)∧
       (budget C).yzCost=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)∧
       (budget C).allCost=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C))∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).zCost) ≤
       flagMixed p firstCutFlag unitZFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).yzCost) ≤
       flagMixed p firstCutFlag unitYZFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).allCost) ≤
       flagMixed p firstCutFlag unitAllFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).movingCost) ≤
       flagMixed p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree)):=by
 obtain ⟨J,hJ,hdegree⟩:=exists_moving_projection_family (E:=E) F H G k B base
   hF hderiv p hFp a b s C0 hH hG c hB hc pchar hmix
 refine ⟨budgetOfProjections F (filteredCut k B H G) H G unit J hJ,?_,?_,?_,?_,?_⟩
 · exact fun C↦⟨rfl,rfl,rfl⟩
 · exact unit.sum_zDegree_le
 · exact unit.sum_yzDegree_le
 · exact unit.sum_allDegree_le
 · exact hdegree
end
end ProximityPrize.SubmissionLower.RCN200
end PackedLegacy_M4

/-! Packed from ProximityPrize.SubmissionLower.M5. -/
section PackedLegacy_M5
namespace ProximityPrize.SubmissionLower.RCN201
open scoped Classical
open RCN198 RCN136 RCN313 RCN095 RCN234 RCN156 RCN057 RCN055
noncomputable section
set_option maxHeartbeats 3000000
variable {K Ω:Type} [Field K] [Field Ω]
public theorem mapped_flag (φ:Polynomial K →+*Ω)
   (Q:MvPolynomial (Fin 4) K) (a b s:ℕ)
   (hR:wt residualSWeights Q ≤ s)
   (hM:wt residualYSWeights Q ≤ b+s)
   (hT:wt residualTotalWeights Q ≤ a+b+s):
   PolynomialInFlag ⟨a,b,s⟩ (surfaceMap φ Q):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
 have hr:=(MvPolynomial.le_weightedTotalDegree residualSWeights hq).trans hR
 have hm:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hM
 have ht:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hT
 simp [RCN081.weight_fin4,residualSWeights] at hr
 simp [RCN081.weight_fin4,residualYSWeights] at hm
 simp [RCN081.weight_fin4,residualTotalWeights] at ht
 exact ⟨hr,hm,ht⟩
public theorem G_weight (w:Fin 4 → ℕ) (t:ℕ)
   (h0:w 0=0) (h1:w 1=t) (h2:w 2=1) (ht:t≤1)
   (F:MvPolynomial (Fin 4) K) (C:ℕ)
   (hC:1≤C) (hF:wt w F≤C):wt w (polyG K F)≤C+1-t:=by
 have hf:WeightBound w F (C:ℤ):=Or.inr (by exact_mod_cast hF)
 have hg:WeightBound w (polyG K F) ((C:ℤ)+1-t):=by
   simpa only [polyG,horizontalDerivation,Derivation.add_apply,
     Derivation.smul_apply,smul_eq_mul] using (hf.horizontal t h0 h1 h2 ht).neg
 rcases hg with hz | hb
 · simp [hz,wt,MvPolynomial.weightedTotalDegree]
 · have htc:t≤C+1:=by omega
   have hb':(wt w (polyG K F):ℤ) ≤ ((C+1-t:ℕ):ℤ):=by
     rw [Nat.cast_sub htc]
     push_cast
     exact hb
   exact_mod_cast hb'
theorem surfaceMap_HG_flags (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3):
   PolynomialInFlag ⟨a,b+1,s+1⟩ (surfaceMap φ (polyH K F))∧
   PolynomialInFlag ⟨a,b,s+3⟩ (surfaceMap φ (polyG K F)):=by
 have hS:=support_data a b s F hR hYR hAll
 have hr:=hS.s_weight
 have hm:=hS.ys_weight
 have ha:=hS.total_weight
 change wt residualSWeights F≤s+2 at hr
 change wt residualYSWeights F≤b+s+3 at hm
 change wt residualTotalWeights F≤a+b+s+3 at ha
 constructor
 · apply mapped_flag φ (polyH K F) a (b+1) (s+1)
   · simpa [residualSWeights] using wt_polyH_le residualSWeights F (s+2) hr
   · have h:=wt_polyH_le residualYSWeights F (b+s+3) hm
     change wt residualYSWeights (polyH K F) ≤ b+s+3-1 at h
     omega
   · have h:=wt_polyH_le residualTotalWeights F (a+b+s+3) ha
     change wt residualTotalWeights (polyH K F) ≤ a+b+s+3-1 at h
     omega
 · apply mapped_flag φ (polyG K F) a b (s+3)
   · simpa using G_weight residualSWeights 0 rfl rfl rfl (by omega) F
       (s+2) (by omega) hr
   · simpa [Nat.add_assoc] using G_weight residualYSWeights 1 rfl rfl rfl (by omega) F
       (b+s+3) (by omega) hm
   · have h:=G_weight residualTotalWeights 1 rfl rfl rfl (by omega) F
       (a+b+s+3) (by omega) ha
     omega
end
end ProximityPrize.SubmissionLower.RCN201
end PackedLegacy_M5

/-! Packed from ProximityPrize.SubmissionLower.M7. -/
section PackedLegacy_M7
namespace ProximityPrize.SubmissionLower.RCN203
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN201 RCN275 RCN287
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
 [IsScalarTower Ω (RatFunc Ω) E]
def paddedCut (a b s d:ℕ):FlagDegree:=
 RCN206.centreFlag a b s+
   d • RCN206.directionFlag a b s
theorem mixed_add_second (p q r t:FlagDegree):
   flagMixed p (q+r) t=flagMixed p q t+flagMixed p r t:=by
 simp only [flagMixed,add_zOnly,add_yz,add_all]
 ring
theorem mixed_affine_third (p q C R:FlagDegree) (k:ℕ):
   flagMixed p q (C+k • R)=flagMixed p q C+k*flagMixed p q R:=by
 simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
 ring
theorem mixed_sharp_le_padded (a b s d:ℕ) (p r:FlagDegree):
   flagMixed p (sharpResidualAgreementFlag (support a b s) d) r ≤
     flagMixed p (paddedCut a b s d) r:=by
 have he:paddedCut a b s d=
     sharpResidualAgreementFlag (support a b s) d+direction a b s:=by
   rw [sharp_flag_eq]
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1 <;> simp [paddedCut,RCN206.centreFlag,
     RCN206.directionFlag,direction,unitYZFlag] <;> ring
 rw [he,mixed_add_second]
 exact Nat.le_add_right _ _
end
end ProximityPrize.SubmissionLower.RCN203
end PackedLegacy_M7
end Compact_PackedLegacy


