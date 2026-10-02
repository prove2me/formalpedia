-- Prove2me | Definitions.Def_Yukon_4328c3a3fc53bf96b4a2a518
-- name    : Yukon_4328c3a3fc53bf96b4a2a518
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T19:04:18.013134+00:00
-- url     : https://prove2.me/theorems/62e33a6a-62be-4e5c-a5f4-044fce0be846
-- title:
--   LowerFoundation source part 2/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-small-split-Yukon_4328c3a3fc53bf96b4a2a518
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNDlhN2Q4NjkwZmU1ZDBlZjRmYWJlOTcxOWI1MjYyOTE5OTg5MmRkNTRkY2MwMzZiZjk4Mzg3YzgzOTZlMzRjZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tc21hbGwtc3BsaXQtWXVrb25fNDMyOGMzYTNmYzUzYmY5NmI0YTJhNTE4IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNDMyOGMzYTNmYzUzYmY5NmI0YTJhNTE4IiwidiI6Mn0]

import Definitions.Def_Yukon_8c56cda003e14b0483a1a27f
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


/-! Packed from ProximityPrize.SubmissionLower.AX. -/
section PackedLegacy_AX
namespace ProximityPrize.SubmissionLower.RCN011
open RCN002 RCN005 RCN371
noncomputable section
def bivariateEquiv (A:Type) [Field A]:
   MvPolynomial (Fin 2) A ≃ₐ[A] Polynomial (Polynomial A):=
 (MvPolynomial.finSuccEquiv A 1).trans
   (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1)))
@[simp] theorem bivariateEquiv_C (A:Type) [Field A] (a:A):
   bivariateEquiv A (MvPolynomial.C a)=Polynomial.C (Polynomial.C a):=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_zero (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (0:Fin 2))=Polynomial.X:=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_one (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (1:Fin 2))=Polynomial.C Polynomial.X:=by
 change Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
   ((MvPolynomial.finSuccEquiv A 1) (MvPolynomial.X (0:Fin 1).succ))=
     Polynomial.C Polynomial.X
 rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
 simp [MvPolynomial.uniqueAlgEquiv]
variable (K:Type) [Field K]
abbrev PlaneRing:=Polynomial (Polynomial (RatFunc K))
def planeMap (order:Fin 3 ≃ Fin 3):Original K →+*PlaneRing K:=
 (bivariateEquiv (RatFunc K)).toRingHom.comp (rationalMap K order)
@[simp] theorem planeMap_C (order:Fin 3 ≃ Fin 3) (a:K):
   planeMap K order (MvPolynomial.C a)=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_first (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 0))=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_outer (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 1))=Polynomial.X:=by
 have h:=collect_X_other K order (0:Fin 2)
 change collect K order (MvPolynomial.X (order 1))=MvPolynomial.X 0 at h
 simp [planeMap,rationalMap,h]
@[simp] theorem planeMap_X_inner (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 2))=Polynomial.C Polynomial.X:=by
 have h:=collect_X_other K order (1:Fin 2)
 change collect K order (MvPolynomial.X (order 2))=MvPolynomial.X 1 at h
 simp [planeMap,rationalMap,h]
theorem planeMap_injective (order:Fin 3 ≃ Fin 3):
   Function.Injective (planeMap K order):=
 (bivariateEquiv (RatFunc K)).injective.comp (rationalMap_injective K order)
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
include ht in
theorem planeMap_irreducible_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P):
   Irreducible (planeMap K order G):=by
 exact (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_component K order P G hG hmem ht)
include ht in
theorem planeMap_dvd_iff_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_component K order P G H hG hmem ht).mp hrat
 · intro hdiv
   exact map_dvd (planeMap K order) hdiv
def actualPlaneEvaluation:PlaneRing K →+*CoordinateField K P:=
 (Polynomial.evalRingHom (coordinate K P (order 1))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom (rationalBaseEmbedding K P (order 0) ht).toRingHom
       (coordinate K P (order 2))))
@[simp] theorem actualPlaneEvaluation_C_C (a:RatFunc K):
   actualPlaneEvaluation K order P ht (Polynomial.C (Polynomial.C a))=
     rationalBaseEmbedding K P (order 0) ht a:=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_X:
   actualPlaneEvaluation K order P ht Polynomial.X=coordinate K P (order 1):=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_C_X:
   actualPlaneEvaluation K order P ht (Polynomial.C Polynomial.X)=
     coordinate K P (order 2):=by
 simp [actualPlaneEvaluation]
theorem actualPlaneEvaluation_comp_planeMap:
   (actualPlaneEvaluation K order P ht).comp (planeMap K order)=
     (coordinateEvaluation K P).toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,actualPlaneEvaluation_C_C,
     rationalBaseEmbedding_polynomial,Polynomial.aeval_C]
   exact (MvPolynomial.algHom_C (coordinateEvaluation K P) a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,actualPlaneEvaluation_C_C,
       rationalBaseEmbedding_polynomial,Polynomial.aeval_X]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,actualPlaneEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h => hj (Fin.ext h)
     have hjone:j.val≠1:=fun h => hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,actualPlaneEvaluation_C_X]
   rfl
def actualRelationKernel:Ideal (PlaneRing K):=
 RingHom.ker (actualPlaneEvaluation K order P ht)
theorem actualRelationKernel_contract:
   (actualRelationKernel K order P ht).comap (planeMap K order)=P:=by
 rw [actualRelationKernel,RingHom.comap_ker,actualPlaneEvaluation_comp_planeMap]
 exact coordinateEvaluation_ker K P
theorem actualPlane_root_iff (F:Original K):
   actualPlaneEvaluation K order P ht (planeMap K order F)=0 ↔ F∈P:=by
 change ((actualPlaneEvaluation K order P ht).comp (planeMap K order)) F=0 ↔ F∈P
 rw [actualPlaneEvaluation_comp_planeMap]
 change F∈RingHom.ker (coordinateEvaluation K P).toRingHom ↔ F∈P
 rw [coordinateEvaluation_ker]
end Component
theorem prime_eq_of_actualRelationKernel_eq
   (order:Fin 3 ≃ Fin 3) (P Q:Ideal (Original K)) [P.IsPrime] [Q.IsPrime]
   (hP:Transcendental K (coordinate K P (order 0)))
   (hQ:Transcendental K (coordinate K Q (order 0)))
   (heq:actualRelationKernel K order P hP=actualRelationKernel K order Q hQ):
   P=Q:=by
 have h:=congrArg (Ideal.comap (planeMap K order)) heq
 simpa only [actualRelationKernel_contract] using h
theorem actualRelationKernel_family_injective
   (order:Fin 3 ≃ Fin 3) {I:Type} (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P):
   Function.Injective (fun i => actualRelationKernel K order (P i) (ht i)):=by
 intro i j hij
 apply hinj
 exact prime_eq_of_actualRelationKernel_eq K order (P i) (P j) (ht i) (ht j) hij
end
end ProximityPrize.SubmissionLower.RCN011
end PackedLegacy_AX

/-! Packed from ProximityPrize.SubmissionLower.DA. -/
section PackedLegacy_DA
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate
open scoped BigOperators
set_option linter.constructorNameAsVariable false
local instance concreteFieldChar:
   CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433:=
 charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem derivative_ne_zero_of_pos_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hpos:0 < R.natDegree) (hlt:R.natDegree < p):R.derivative≠0:=by
 intro hzero
 have hc:=congrArg (fun f:K[X] => f.coeff (R.natDegree-1)) hzero
 rw [coeff_derivative] at hc
 have hsucc:R.natDegree-1+1=R.natDegree:=by omega
 rw [hsucc] at hc
 have hcastSucc:((R.natDegree-1:ℕ):K)+1=(R.natDegree:K):=by
   simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z:ℕ => (z:K)) hsucc
 rw [hcastSucc,coeff_natDegree] at hc
 simp only [coeff_zero] at hc
 have hcast:(R.natDegree:K)≠0:=by
   intro hz
   have hdvd:p∣R.natDegree:=(CharP.cast_eq_zero_iff K p R.natDegree).mp hz
   exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd
 have hR:R≠0:=by
   intro hz
   simp [hz] at hpos
 exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hR) hcast) hc
theorem irreducible_isCoprime_derivative_of_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hirr:Irreducible R) (hpos:0 < R.natDegree) (hlt:R.natDegree < p):
   IsCoprime R R.derivative:=by
 have hdne:=derivative_ne_zero_of_pos_natDegree_lt_char p R hpos hlt
 have hddeg:R.derivative.natDegree < R.natDegree:=
   natDegree_derivative_lt (ne_of_gt hpos)
 have hnotdvd:¬ R∣R.derivative:=by
   intro hdvd
   have hle:=natDegree_le_of_dvd hdvd hdne
   omega
 by_contra hnot
 exact hnotdvd ((hirr.dvd_iff_not_isCoprime).2 hnot)
end ProximityPrize.SubmissionLower
end PackedLegacy_DA

/-! Packed from ProximityPrize.SubmissionLower.X8. -/
section PackedLegacy_X8
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate
variable {F:Type} [Field F]
theorem bivariate_resultant_natDegree_le (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree ≤
     m*degreeX B+n*degreeX H:=by
 exact ps_nat_degree_resultant_le H B m n
end ProximityPrize.SubmissionLower
end PackedLegacy_X8

/-! Packed from ProximityPrize.SubmissionLower.W2. -/
section PackedLegacy_W2
namespace ProximityPrize.SubmissionLower.RCN355
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_eval_columns_eq_zero
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (columns:Finset ι)
   (hzero:∀ j∈columns,∀ i,(M i j).eval alpha=0):
   (Polynomial.X-Polynomial.C alpha)^columns.card∣M.det:=by
 classical
 rw [Matrix.det_apply']
 apply Finset.dvd_sum
 intro permutation _
 have hpart:
     (∏ j∈columns,(Polynomial.X-Polynomial.C alpha))∣
       ∏ j∈columns,M (permutation j) j:=by
   apply Finset.prod_dvd_prod_of_dvd
   intro j hj
   exact Polynomial.dvd_iff_isRoot.mpr (hzero j hj (permutation j))
 have hfull:
     (∏ j∈columns,M (permutation j) j)∣
       ∏ j:ι,M (permutation j) j:=
   Finset.prod_dvd_prod_of_subset columns Finset.univ
     (fun j => M (permutation j) j) (Finset.subset_univ columns)
 have hproduct:
     (Polynomial.X-Polynomial.C alpha)^columns.card∣
       ∏ j:ι,M (permutation j) j:=by
   simpa using hpart.trans hfull
 exact dvd_mul_of_dvd_right hproduct _
theorem pow_corank_dvd_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K):
   (Polynomial.X-Polynomial.C alpha)^
       (Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank)∣
     M.det:=by
 classical
 let evalMatrix:Matrix ι ι (Polynomial K) →+*Matrix ι ι K:=
   (Polynomial.evalRingHom alpha).mapMatrix
 let constMatrix:Matrix ι ι K →+*Matrix ι ι (Polynomial K):=
   (Polynomial.C:K →+*Polynomial K).mapMatrix
 let evaluated:Matrix ι ι K:=evalMatrix M
 obtain ⟨V,U,e,hV,hU,hnormal⟩:=Matrix.exists_rank_normal_form evaluated
 let transformed:Matrix ι ι (Polynomial K):=constMatrix V*M*constMatrix U
 have heval_const (B:Matrix ι ι K):evalMatrix (constMatrix B)=B:=by
   ext i j
   simp [evalMatrix,constMatrix,RingHom.mapMatrix_apply,Matrix.map_apply]
 have heval:evalMatrix transformed=
     (Matrix.fromBlocks 1 0 0 0).submatrix e e:=by
   change evalMatrix (constMatrix V*M*constMatrix U)=_
   rw [map_mul,map_mul,heval_const,heval_const]
   exact hnormal
 let zeroEmbedding:Fin (Fintype.card ι-evaluated.rank) ↪ ι:={
   toFun:=fun j => e.symm (Sum.inr j)
   inj':=by
     intro i j hij
     exact Sum.inr.inj (e.symm.injective hij)
 }
 let zeroColumns:Finset ι:=Finset.univ.map zeroEmbedding
 have hcard:zeroColumns.card=Fintype.card ι-evaluated.rank:=by
   simp [zeroColumns]
 have hzero:∀ j∈zeroColumns,∀ i,(transformed i j).eval alpha=0:=by
   intro j hj i
   obtain ⟨j0,_,rfl⟩:=Finset.mem_map.mp hj
   change evalMatrix transformed i (e.symm (Sum.inr j0))=0
   rw [heval]
   simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
   cases e i <;> rfl
 have hVdet:IsUnit (constMatrix V).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hV.map constMatrix)
 have hUdet:IsUnit (constMatrix U).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hU.map constMatrix)
 have hdiv:=pow_card_dvd_det_of_eval_columns_eq_zero
   transformed alpha zeroColumns hzero
 rw [hcard] at hdiv
 change (Polynomial.X-Polynomial.C alpha)^
     (Fintype.card ι-evaluated.rank)∣
       (constMatrix V*M*constMatrix U).det at hdiv
 rw [Matrix.det_mul,Matrix.det_mul] at hdiv
 exact hVdet.dvd_mul_left.mp (hUdet.dvd_mul_right.mp hdiv)
theorem corank_le_rootMultiplicity_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (hdet:M.det≠0):
   Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank ≤
     M.det.rootMultiplicity alpha:=by
 exact (Polynomial.le_rootMultiplicity_iff hdet).mpr
   (pow_corank_dvd_det M alpha)
theorem sum_rootMultiplicity_le_natDegree
   (P:Polynomial K) (points:Finset K):
   (∑ alpha∈points,P.rootMultiplicity alpha) ≤ P.natDegree:=by
 classical
 have hselected:
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤ P.roots.card:=by
   let all:=points ∪ P.roots.toFinset
   calc
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤
         ∑ alpha∈all,Multiset.count alpha P.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ alpha∈P.roots.toFinset,Multiset.count alpha P.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro alpha _ hnot
       exact Multiset.count_eq_zero.mpr (by simpa using hnot)
     _=P.roots.card:=Multiset.toFinset_sum_count_eq P.roots
 calc
   (∑ alpha∈points,P.rootMultiplicity alpha)=
       ∑ alpha∈points,Multiset.count alpha P.roots:=by
     apply Finset.sum_congr rfl
     intro alpha _
     exact (Polynomial.count_roots P).symm
   _ ≤ P.roots.card:=hselected
   _ ≤ P.natDegree:=Polynomial.card_roots' P
theorem sylvester_corank_le_rootMultiplicity_resultant
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank ≤
     (Polynomial.resultant P Q m n).rootMultiplicity alpha:=by
 simpa only [Fintype.card_fin,Polynomial.resultant,
   ←Polynomial.sylvester_map_map] using
   corank_le_rootMultiplicity_det (Polynomial.sylvester P Q m n) alpha hresultant
theorem sum_sylvester_coranks_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ alpha∈points,(m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(Polynomial.resultant P Q m n).rootMultiplicity alpha:=
     Finset.sum_le_sum fun alpha _ =>
       sylvester_corank_le_rootMultiplicity_resultant P Q m n alpha hresultant
   _ ≤ (Polynomial.resultant P Q m n).natDegree:=
     sum_rootMultiplicity_le_natDegree (Polynomial.resultant P Q m n) points
end
end ProximityPrize.SubmissionLower.RCN355
end PackedLegacy_W2

/-! Packed from ProximityPrize.SubmissionLower.G5. -/
section PackedLegacy_G5
namespace ProximityPrize.SubmissionLower.RCN363
open scoped BigOperators
noncomputable section
variable {K:Type} [Field K] [DecidableEq K]
def evaluationOn (N:ℕ) (roots:Finset K):
   Polynomial.degreeLT K N →ₗ[K] (roots → K) where
 toFun P x:=(P:Polynomial K).eval (x:K)
 map_add' _ _:=funext fun _ => Polynomial.eval_add
 map_smul' _ _:=funext <| by simp
theorem evaluationOn_surjective (N:ℕ) (roots:Finset K)
   (hcard:roots.card ≤ N):Function.Surjective (evaluationOn N roots):=by
 let E:=Lagrange.funEquivDegreeLT (s:=roots) (v:=fun x:K => x)
   (Set.injOn_id (roots:Set K))
 intro values
 let small:=E.symm values
 have hsmall:(small:Polynomial K).degree < (roots.card:WithBot ℕ):=
   Polynomial.mem_degreeLT.mp small.property
 have hlarge:(small:Polynomial K).degree < (N:WithBot ℕ):=
   hsmall.trans_le (by exact_mod_cast hcard)
 refine ⟨⟨(small:Polynomial K),Polynomial.mem_degreeLT.mpr hlarge⟩,?_⟩
 change E small=values
 exact E.apply_symm_apply values
theorem finrank_degreeLT (N:ℕ):
   Module.finrank K (Polynomial.degreeLT K N)=N:=by
 simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K N)
theorem sylvester_rank_eq_finrank_range
   (p q:Polynomial K) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n):
   (Polynomial.sylvester p q m n).rank=
     Module.finrank K (LinearMap.range (Polynomial.sylvesterMap p q hp hq)):=by
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd K m n)
     (Polynomial.degreeLT.basis K (m+n))
     (Polynomial.sylvesterMap p q hp hq)=Polynomial.sylvester p q m n:=
   Polynomial.toMatrix_sylvesterMap' p q hp hq
 rw [Matrix.rank_eq_finrank_range_toLin _
   (Polynomial.degreeLT.basis K (m+n)) (Polynomial.degreeLT.basisProd K m n)]
 rw [←hmatrix,Matrix.toLin_toMatrix]
theorem common_roots_card_le_cap
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n:=by
 rcases hnonzero with hp0 | hq0
 · have hcard:roots.card ≤ p.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hp0).mpr (hroots x hx).1
   omega
 · have hcard:roots.card ≤ q.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hq0).mpr (hroots x hx).2
   omega
theorem common_roots_card_le_sylvester_corank
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n-(Polynomial.sylvester p q m n).rank:=by
 let E:=evaluationOn (m+n) roots
 let L:=Polynomial.sylvesterMap p q hp hq
 have hsurj:Function.Surjective E:=
   evaluationOn_surjective (m+n) roots
     (common_roots_card_le_cap p q m n roots hp hq hnonzero hroots)
 have hcontain:LinearMap.range L ≤ LinearMap.ker E:=by
   rintro P ⟨input,rfl⟩
   rw [LinearMap.mem_ker]
   ext x
   change (p*(input.2:Polynomial K)+q*(input.1:Polynomial K)).eval
     (x:K)=0
   simp only [Polynomial.eval_add,Polynomial.eval_mul,
     (hroots x x.property).1,(hroots x x.property).2,zero_mul,zero_add]
 have hevalrank:Module.finrank K (LinearMap.range E)=roots.card:=by
   rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,
     Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
 have hnull:=LinearMap.finrank_range_add_finrank_ker E
 rw [hevalrank,finrank_degreeLT] at hnull
 have hmono:=Submodule.finrank_mono hcontain
 have hmatrix:=sylvester_rank_eq_finrank_range p q m n hp hq
 change (Polynomial.sylvester p q m n).rank=
   Module.finrank K (LinearMap.range L) at hmatrix
 omega
theorem common_fiber_card_le_sylvester_corank
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K) (roots:Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hnonzero:P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ beta∈roots,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   roots.card ≤ m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank:=by
 apply common_roots_card_le_sylvester_corank
 · exact Polynomial.natDegree_map_le.trans hP
 · exact Polynomial.natDegree_map_le.trans hQ
 · exact hnonzero
 · exact hroots
theorem sum_common_fiber_cards_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(m+n-(Polynomial.sylvester
       (P.map (Polynomial.evalRingHom alpha))
       (Q.map (Polynomial.evalRingHom alpha)) m n).rank):=by
     apply Finset.sum_le_sum
     intro alpha halpha
     exact common_fiber_card_le_sylvester_corank P Q m n alpha (fibers alpha)
       hP hQ (hnonzero alpha halpha) (hroots alpha halpha)
   _ ≤ _:=RCN355.sum_sylvester_coranks_le_resultant_natDegree
     P Q m n points hresultant
theorem sum_common_fiber_cards_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 exact Nat.le_trans
   (sum_common_fiber_cards_le_resultant_natDegree P Q m n points fibers
     hP hQ hresultant hnonzero hroots)
   (bivariate_resultant_natDegree_le (F:=K) P Q m n)
def pointFiber (points:Finset (K × K)) (alpha:K):Finset K:=
 (points.filter (fun point => point.1=alpha)).image Prod.snd
theorem card_eq_sum_pointFiber (points:Finset (K × K)):
   points.card=∑ alpha∈points.image Prod.fst,(pointFiber points alpha).card:=by
 rw [Finset.card_eq_sum_card_image Prod.fst points]
 apply Finset.sum_congr rfl
 intro alpha _
 change (points.filter (fun point => point.1=alpha)).card=
   ((points.filter (fun point => point.1=alpha)).image Prod.snd).card
 symm
 apply Finset.card_image_of_injOn
 intro u hu v hv huv
 apply Prod.ext
 · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
 · exact huv
theorem common_points_card_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset (K × K))
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ point∈points,
     P.map (Polynomial.evalRingHom point.1)≠0∨
     Q.map (Polynomial.evalRingHom point.1)≠0)
   (hroots:∀ point∈points,
     (P.map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     (Q.map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 rw [card_eq_sum_pointFiber points]
 apply sum_common_fiber_cards_le_bidegree_bound P Q m n
   (points.image Prod.fst) (pointFiber points) hP hQ hresultant
 · intro alpha halpha
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp halpha
   exact hnonzero point hpoint
 · intro alpha _ beta hbeta
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp hbeta
   obtain ⟨hpoint,hfirst⟩:=Finset.mem_filter.mp hpoint
   simpa only [hfirst] using hroots point hpoint
end
end ProximityPrize.SubmissionLower.RCN363
end PackedLegacy_G5

/-! Packed from ProximityPrize.SubmissionLower.W6. -/
section PackedLegacy_W6
namespace ProximityPrize.SubmissionLower.RCN362
noncomputable section
variable {K:Type} [Field K] [DecidableEq K]
theorem inner_linear_C_dvd_of_specialization_eq_zero
   (P:Polynomial (Polynomial K)) (alpha:K)
   (hzero:P.map (Polynomial.evalRingHom alpha)=0):
   Polynomial.C (Polynomial.X-Polynomial.C alpha)∣P:=by
 rw [Polynomial.C_dvd_iff_dvd_coeff]
 intro i
 apply Polynomial.dvd_iff_isRoot.mpr
 have hcoeff:=congrArg (fun Q:Polynomial K => Q.coeff i) hzero
 simpa using hcoeff
theorem primitive_specialization_ne_zero
   (P:Polynomial (Polynomial K)) (hprimitive:P.IsPrimitive) (alpha:K):
   P.map (Polynomial.evalRingHom alpha)≠0:=by
 intro hzero
 exact Polynomial.not_isUnit_X_sub_C alpha
   (hprimitive _ (inner_linear_C_dvd_of_specialization_eq_zero P alpha hzero))
theorem primitive_irreducible_dvd_of_resultant_eq_zero
   (P Q:Polynomial (Polynomial K))
   (hprimitive:P.IsPrimitive) (hirreducible:Irreducible P)
   (hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree=0):P∣Q:=by
 classical
 let F:=FractionRing (Polynomial K)
 let f:Polynomial K →+*F:=algebraMap (Polynomial K) F
 have hf:Function.Injective f:=IsFractionRing.injective (Polynomial K) F
 have hPdegree:(P.map f).natDegree=P.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf P
 have hQdegree:(Q.map f).natDegree=Q.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf Q
 have hfixed:Polynomial.resultant (P.map f) (Q.map f)
     P.natDegree Q.natDegree=0:=by
   rw [Polynomial.resultant_map_map,hresultant,map_zero]
 have hresF:Polynomial.resultant (P.map f) (Q.map f)=0:=by
   simpa only [hPdegree,hQdegree] using hfixed
 have hnotCoprime:¬ IsCoprime (P.map f) (Q.map f):=
   (Polynomial.resultant_eq_zero_iff.mp hresF).2
 have hirreducibleF:Irreducible (P.map f):=
   hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirreducible
 have hdivF:P.map f∣Q.map f:=
   (Irreducible.dvd_iff_not_isCoprime hirreducibleF).mpr hnotCoprime
 exact hprimitive.dvd_of_fraction_map_dvd_fraction_map hdivF
theorem irreducible_resultant_ne_zero_of_not_dvd
   (P Q:Polynomial (Polynomial K)) (hirreducible:Irreducible P)
   (hdegree:0 < P.natDegree) (hproper:¬ P∣Q):
   Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=by
 intro hresultant
 exact hproper (primitive_irreducible_dvd_of_resultant_eq_zero P Q
   (hirreducible.isPrimitive (Nat.ne_of_gt hdegree)) hirreducible hresultant)
end
end ProximityPrize.SubmissionLower.RCN362
end PackedLegacy_W6

/- Library component IT is loaded from Mathlib.RingTheory.Polynomial.ContentIdeal. -/

/-! Packed from ProximityPrize.SubmissionLower.G3. -/
section PackedLegacy_G3
namespace ProximityPrize.SubmissionLower.RCN360
noncomputable section
variable {K L:Type} [Field K] [Field L]
local instance _root_.ProximityPrize.SubmissionLower.RCN360.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN360.instDecidableEq_proximityPrize_1 :DecidableEq L:=Classical.decEq L
def bimap (f:K →+*L) (P:Polynomial (Polynomial K)):
   Polynomial (Polynomial L):=P.map (Polynomial.mapRingHom f)
theorem bimap_primitive (f:K →+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive):
   (bimap f P).IsPrimitive:=by
 apply Polynomial.isPrimitive_of_contentIdeal_eq_top
 rw [bimap,Polynomial.contentIdeal_map_eq_map_contentIdeal,
   (Polynomial.isPrimitive_iff_contentIdeal_eq_top P).mp hP,Ideal.map_top]
theorem bimap_natDegree_le (f:K →+*L) (P:Polynomial (Polynomial K)):
   (bimap f P).natDegree ≤ P.natDegree:=
 Polynomial.natDegree_map_le
theorem bimap_degreeX_le (f:K →+*L) (P:Polynomial (Polynomial K)):
   Polynomial.Bivariate.degreeX (bimap f P) ≤ Polynomial.Bivariate.degreeX P:=by
 classical
 unfold Polynomial.Bivariate.degreeX
 apply Finset.sup_le
 intro j _
 rw [show (bimap f P).coeff j=(P.coeff j).map f by simp [bimap]]
 exact Polynomial.natDegree_map_le.trans
   (Polynomial.Bivariate.coeff_natDegree_le_degreeX P j)
theorem bimap_specialization (f:K →+*L)
   (P:Polynomial (Polynomial K)) (x:L):
   (bimap f P).map (Polynomial.evalRingHom x)=
     P.map (Polynomial.eval₂RingHom f x):=by
 ext j
 simp [bimap,Polynomial.eval_map]
theorem bimap_eval_natural (f:K →+*L)
   (P:Polynomial (Polynomial K)) (x y:K):
   ((bimap f P).map (Polynomial.evalRingHom (f x))).eval (f y)=
     f ((P.map (Polynomial.evalRingHom x)).eval y):=by
 have h:(bimap f P).map (Polynomial.evalRingHom (f x))=
     (P.map (Polynomial.evalRingHom x)).map f:=by
   ext j
   simp [bimap,Polynomial.eval_map,Polynomial.eval₂_at_apply]
 rw [h,Polynomial.eval_map_apply]
theorem bimap_comp {M:Type} [Field M]
   (f:K →+*L) (g:L →+*M) (P:Polynomial (Polynomial K)):
   bimap g (bimap f P)=bimap (g.comp f) P:=by
 ext j i
 simp [bimap]
theorem bimap_resultant_ne_zero (f:K →+*L)
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hres:Polynomial.resultant P Q m n≠0):
   Polynomial.resultant (bimap f P) (bimap f Q) m n≠0:=by
 unfold bimap
 rw [Polynomial.resultant_map_map]
 intro hzero
 apply hres
 apply Polynomial.map_injective f f.injective
 simpa only [Polynomial.coe_mapRingHom,Polynomial.map_zero] using hzero
theorem bimap_specialization_ne_zero (f:K →+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive) (x:L):
   (bimap f P).map (Polynomial.evalRingHom x)≠0:=by
 classical
 exact RCN362.primitive_specialization_ne_zero
   (bimap f P) (bimap_primitive f P hP) x
theorem common_points_card_le_after_extension (f:K →+*L)
   (P Q:Polynomial (Polynomial K)) (points:Finset (L × L))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (hroots:∀ point∈points,
     ((bimap f P).map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     ((bimap f Q).map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hcount:=RCN363.common_points_card_le_bidegree_bound
   (bimap f P) (bimap f Q) P.natDegree Q.natDegree points
   (bimap_natDegree_le f P) (bimap_natDegree_le f Q)
   (bimap_resultant_ne_zero f P Q P.natDegree Q.natDegree
     (RCN362.irreducible_resultant_ne_zero_of_not_dvd
       P Q hP hdeg hproper))
   (fun point _ => Or.inl (bimap_specialization_ne_zero f P
     (hP.isPrimitive (Nat.ne_of_gt hdeg)) point.1)) hroots
 exact hcount.trans (Nat.add_le_add
   (Nat.mul_le_mul_left _ (bimap_degreeX_le f P))
   (Nat.mul_le_mul_left _ (bimap_degreeX_le f Q)))
end
end ProximityPrize.SubmissionLower.RCN360
end PackedLegacy_G3

/-! Packed from ProximityPrize.SubmissionLower.G6. -/
section PackedLegacy_G6
namespace ProximityPrize.SubmissionLower.RCN364
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
local instance _root_.ProximityPrize.SubmissionLower.RCN364.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN364.instDecidableEq_proximityPrize_1 :DecidableEq L:=Classical.decEq L
theorem integral_and_separable_of_small_annihilator
   (p:ℕ) [CharP K p] (f:Polynomial K) (x:L)
   (hf:f≠0) (hx:Polynomial.aeval x f=0) (hdegree:f.natDegree < p):
   IsIntegral K x∧IsSeparable K x:=by
 have hint:IsIntegral K x:=IsAlgebraic.isIntegral ⟨f,hf,hx⟩
 have hmin:(minpoly K x).natDegree ≤ f.natDegree:=
   Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hx) hf
 refine ⟨hint,?_⟩
 change (minpoly K x).Separable
 apply (Polynomial.separable_def _).mpr
 exact irreducible_isCoprime_derivative_of_natDegree_lt_char p (minpoly K x)
   (minpoly.irreducible hint) (minpoly.natDegree_pos hint) (hmin.trans_lt hdegree)
theorem resultant_aeval_eq_zero_of_common_root
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPdegree:P.natDegree ≤ m) (hQdegree:Q.natDegree ≤ n)
   (hpositive:m≠0∨n≠0) (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0):
   Polynomial.aeval y (Polynomial.resultant P Q m n)=0:=by
 obtain ⟨U,V,_,_,hidentity⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
   P Q hPdegree hQdegree hpositive
 have heval:=congrArg
   (fun F:Polynomial (Polynomial K) =>
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r F) hidentity
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
   hP,hQ,zero_mul,zero_add] at heval
 exact heval.symm
theorem finite_separable_of_two_generators (y r:L)
   (hy:IsSeparable K y) (hr:IsSeparable K r)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 letI:FiniteDimensional K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.finiteDimensional_adjoin_pair hy.isIntegral hr.isIntegral
 letI:Algebra.IsSeparable K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.isSeparable_adjoin_pair_of_isSeparable K L hy hr
 letI:FiniteDimensional K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hsepTop:Algebra.IsSeparable K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hfinite:FiniteDimensional K L:=Module.Finite.of_surjective
   (IntermediateField.topEquiv (F:=K) (E:=L)).toLinearMap
   (IntermediateField.topEquiv (F:=K) (E:=L)).surjective
 exact ⟨hfinite,(IntermediateField.isSeparable_top (F:=K) (E:=L)).mp hsepTop⟩
theorem finite_separable_of_proper_plane_roots
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 classical
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=resultant_aeval_eq_zero_of_common_root P Q
   P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive)) y r hP hQ
 obtain ⟨_,hySeparable⟩:=integral_and_separable_of_small_annihilator p
   (Polynomial.resultant P Q P.natDegree Q.natDegree) y hresne hresroot hresultantDegree
 let S:IntermediateField K L:=IntermediateField.adjoin K {y}
 let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
 letI:DecidableEq S:=Classical.decEq S
 letI:CharP S p:=charP_of_injective_algebraMap (algebraMap K S).injective p
 let g:Polynomial K →+*S:=Polynomial.eval₂RingHom (algebraMap K S) yS
 let Py:Polynomial S:=P.map g
 have hPyne:Py≠0:=by
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K S) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.bimap_specialization] at h
   exact h
 have hPydegree:Py.natDegree < p:=Polynomial.natDegree_map_le.trans_lt hRdegree
 have hcoefficient:(algebraMap S L).comp g=
     Polynomial.eval₂RingHom (algebraMap K L) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
       Polynomial.eval₂ (algebraMap K L) y (Polynomial.C c)
     rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
     exact (IsScalarTower.algebraMap_apply K S L c).symm
   · change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
       Polynomial.eval₂ (algebraMap K L) y Polynomial.X
     rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
     rfl
 have hPyroot:Polynomial.aeval r Py=0:=by
   change Polynomial.eval₂ (algebraMap S L) r (P.map g)=0
   rw [Polynomial.eval₂_map,hcoefficient]
   exact hP
 obtain ⟨_,hrSeparable⟩:=integral_and_separable_of_small_annihilator p
   Py r hPyne hPyroot hPydegree
 letI:Algebra.IsSeparable K S:=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mpr hySeparable
 have hrOverK:IsSeparable K r:=
   IsSeparable.of_algebra_isSeparable_of_isSeparable K hrSeparable
 exact finite_separable_of_two_generators y r hySeparable hrOverK hgenerate
end
end ProximityPrize.SubmissionLower.RCN364
end PackedLegacy_G6

/-! Packed from ProximityPrize.SubmissionLower.G4. -/
section PackedLegacy_G4
namespace ProximityPrize.SubmissionLower.RCN361
open RCN360
noncomputable section
section Evaluation
variable (K E:Type) [Field K] [Field E] [Algebra K E]
def planeEval (y r:E):Polynomial (Polynomial K) →+*E:=
 (Polynomial.evalRingHom r).comp
   (Polynomial.mapRingHom (Polynomial.eval₂RingHom (algebraMap K E) y))
def relationIdeal (y r:E):Ideal (Polynomial (Polynomial K)):=
 RingHom.ker (planeEval K E y r)
theorem planeEval_eq (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     ((bimap (algebraMap K E) P).map (Polynomial.evalRingHom y)).eval r:=by
 simp only [planeEval,RingHom.comp_apply,Polynomial.coe_mapRingHom,
   Polynomial.coe_evalRingHom]
 rw [bimap_specialization]
variable (Ω:Type) [Field Ω] [Algebra K Ω]
theorem algHom_planeEval (φ:E →ₐ[K] Ω) (y r:E)
   (P:Polynomial (Polynomial K)):
   φ (planeEval K E y r P)=planeEval K Ω (φ y) (φ r) P:=by
 rw [planeEval_eq,planeEval_eq]
 have h:=bimap_eval_natural φ.toRingHom
   (bimap (algebraMap K E) P) y r
 have hcomp:φ.toRingHom.comp (algebraMap K E)=algebraMap K Ω:=by
   ext a
   exact φ.commutes a
 rw [bimap_comp,hcomp] at h
 exact h.symm
theorem algHom_eq_of_generating_pair (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (φ ψ:E →ₐ[K] Ω) (hy:φ y=ψ y) (hr:φ r=ψ r):φ=ψ:=by
 apply AlgHom.ext
 intro x
 have hx:x∈IntermediateField.adjoin K ({y,r}:Set E):=by
   rw [hgen]
   trivial
 exact IntermediateField.adjoin_induction K
   (p:=fun a _ => φ a=ψ a)
   (fun a ha => by
     rcases Set.mem_insert_iff.mp ha with h | h
     · simpa only [h] using hy
     · simpa only [Set.mem_singleton_iff.mp h] using hr)
   (fun a => by rw [φ.commutes,ψ.commutes])
   (fun a b _ _ ha hb => by simp only [map_add,ha,hb])
   (fun a _ ha => by simp only [map_inv₀,ha])
   (fun a b _ _ ha hb => by simp only [map_mul,ha,hb]) hx
theorem embedding_pair_injective (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤):
   Function.Injective (fun φ:E →ₐ[K] Ω => (φ y,φ r)):=by
 intro φ ψ h
 exact algHom_eq_of_generating_pair K E Ω y r hgen φ ψ
   (congrArg Prod.fst h) (congrArg Prod.snd h)
variable (E':Type) [Field E'] [Algebra K E']
theorem relationIdeal_eq_of_embedding_pairs_eq
   (y r:E) (y' r':E') (φ:E →ₐ[K] Ω) (ψ:E' →ₐ[K] Ω)
   (hy:φ y=ψ y') (hr:φ r=ψ r'):
   relationIdeal K E y r=relationIdeal K E' y' r':=by
 apply Ideal.ext
 intro P
 change planeEval K E y r P=0 ↔ planeEval K E' y' r' P=0
 have heq:φ (planeEval K E y r P)=ψ (planeEval K E' y' r' P):=by
   rw [algHom_planeEval,algHom_planeEval,hy,hr]
 constructor
 · intro h
   apply ψ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq.symm
 · intro h
   apply φ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq
end Evaluation
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
 [FiniteDimensional K E] [Algebra.IsSeparable K E]
theorem finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:E) (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hPy:planeEval K E y r P=0) (hQy:planeEval K E y r Q=0):
   Module.finrank K E ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure E
 letI:Fintype (E →ₐ[K] Ω):=Fintype.ofFinite _
 let points:Finset (Ω × Ω):=Finset.univ.image (fun φ:E →ₐ[K] Ω => (φ y,φ r))
 have hcard:points.card=Module.finrank K E:=by
   rw [Finset.card_image_of_injective _ (embedding_pair_injective K E Ω y r hgen),
     Finset.card_univ,Fintype.card_eq_nat_card]
   exact Field.finSepDegree_eq_finrank_of_isSeparable K E
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨φ,_,rfl⟩:=Finset.mem_image.mp hp
 constructor
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r P,hPy,map_zero]
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r Q,hQy,map_zero]
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 [∀ i,FiniteDimensional K (E i)] [∀ i,Algebra.IsSeparable K (E i)]
theorem sum_finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
   (hPy:∀ i,planeEval K (E i) (y i) (r i) P=0)
   (hQy:∀ i,planeEval K (E i) (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i)) ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure K
 letI:∀ i,Fintype (E i →ₐ[K] Ω):=fun i => Fintype.ofFinite _
 let pair:(Σ i,E i →ₐ[K] Ω) → Ω × Ω:=
   fun a => (a.2 (y a.1),a.2 (r a.1))
 have hinj:Function.Injective pair:=by
   rintro ⟨i,φ⟩ ⟨j,ψ⟩ h
   have hij:i=j:=hkernels
     (relationIdeal_eq_of_embedding_pairs_eq K (E i) Ω (E j)
       (y i) (r i) (y j) (r j) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h))
   subst j
   have heq:φ=ψ:=algHom_eq_of_generating_pair K (E i) Ω
     (y i) (r i) (hgen i) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h)
   exact congrArg (Sigma.mk i) heq
 let points:Finset (Ω × Ω):=Finset.univ.image pair
 have hcard:points.card=∑ i,Module.finrank K (E i):=by
   rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_sigma]
   apply Finset.sum_congr rfl
   intro i _
   rw [Fintype.card_eq_nat_card,
     ←Field.finSepDegree_eq_of_isAlgClosed K (E i) Ω,
     Field.finSepDegree_eq_finrank_of_isSeparable]
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨⟨i,φ⟩,_,rfl⟩:=Finset.mem_image.mp hp
 change
   ((bimap (algebraMap K Ω) P).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0∧
   ((bimap (algebraMap K Ω) Q).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0
 constructor
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) P,hPy i,map_zero]
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) Q,hQy i,map_zero]
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN361
end PackedLegacy_G4

/-! Packed from ProximityPrize.SubmissionLower.W7. -/
section PackedLegacy_W7
namespace ProximityPrize.SubmissionLower.RCN365
open RCN361
noncomputable section
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
theorem planeEval_eq_eval₂ (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K E) y) r P:=by
 change (P.map (Polynomial.eval₂RingHom (algebraMap K E) y)).eval r=_
 rw [Polynomial.eval_map]
theorem finite_separable_finrank_le_planar_bound
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:E)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hP:planeEval K E y r P=0) (hQ:planeEval K E y r Q=0):
   FiniteDimensional K E∧Algebra.IsSeparable K E∧
     Module.finrank K E ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hPeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r P=0:=by
   rw [←planeEval_eq_eval₂]
   exact hP
 have hQeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r Q=0:=by
   rw [←planeEval_eq_eval₂]
   exact hQ
 have hfields:=RCN364.finite_separable_of_proper_plane_roots
   p P Q hirreducible hpositive hproper hRdegree hresultantDegree y r hPeval hQeval hgenerate
 letI:FiniteDimensional K E:=hfields.1
 letI:Algebra.IsSeparable K E:=hfields.2
 exact ⟨hfields.1,hfields.2,
   RCN361.finrank_le_planar_bound K E P Q
     hirreducible hpositive hproper y r hgenerate hP hQ⟩
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
theorem finite_separable_sum_finrank_le_planar_bound
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:∀ i,E i)
   (hgenerate:∀ i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
   (hP:∀ i,planeEval K (E i) (y i) (r i) P=0)
   (hQ:∀ i,planeEval K (E i) (y i) (r i) Q=0):
   (∀ i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i))∧
     (∑ i,Module.finrank K (E i)) ≤
       Q.natDegree*Polynomial.Bivariate.degreeX P+
         P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hfields:∀ i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i):=by
   intro i
   have h:=finite_separable_finrank_le_planar_bound K (E i)
     p P Q hirreducible hpositive hproper hRdegree hresultantDegree
     (y i) (r i) (hgenerate i) (hP i) (hQ i)
   exact ⟨h.1,h.2.1⟩
 letI:∀ i,FiniteDimensional K (E i):=fun i => (hfields i).1
 letI:∀ i,Algebra.IsSeparable K (E i):=fun i => (hfields i).2
 exact ⟨hfields,
   RCN361.sum_finrank_le_planar_bound K E P Q
     hirreducible hpositive hproper y r hgenerate hkernels hP hQ⟩
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN365
end PackedLegacy_W7

/-! Packed from ProximityPrize.SubmissionLower.X4. -/
section PackedLegacy_X4
namespace ProximityPrize.SubmissionLower.RCN010
open RCN002 RCN005
 RCN371 RCN011
noncomputable section
theorem order_cover (order:Fin 3 ≃ Fin 3) (l:Fin 3):
   l=order 0∨l=order 2∨l=order 1:=by
 have h:∀ i:Fin 3,i=0∨i=2∨i=1:=by decide
 rcases h (order.symm l) with hl | hl | hl
 · exact Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl)
 · exact Or.inr (Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
 · exact Or.inr (Or.inr (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
variable (K:Type) [Field K]
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem actual_generators:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P (order 2),coordinate K P (order 1)}:Set (CoordinateField K P))=⊤:=
 adjoin_two_coordinates_over_ratFunc_eq_top K P (order 0) (order 2) (order 1) ht
   (order_cover order)
theorem actual_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
 letI:CharP (RatFunc K) p:=
   charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
 have hirr:=planeMap_irreducible_of_component
   (K:=K) (order:=order) (P:=P) (ht:=ht) G hG hGmem
 have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
   intro h
   exact hproper ((planeMap_dvd_iff_of_component
     (K:=K) (order:=order) (P:=P) (ht:=ht) G H hG hGmem).mp h)
 have hGroots:RCN361.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order G)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order G)=0
   exact (actualPlane_root_iff K order P ht G).mpr hGmem
 have hHroots:RCN361.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order H)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order H)=0
   exact (actualPlane_root_iff K order P ht H).mpr hHmem
 exact RCN365.finite_separable_finrank_le_planar_bound
   (RatFunc K) (CoordinateField K P) p (planeMap K order G) (planeMap K order H)
   hirr hpositive hproperPlane hRdegree hresultantDegree
   (coordinate K P (order 2)) (coordinate K P (order 1))
   (actual_generators K order P ht) hGroots hHroots
end Component
section FiniteFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem actual_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
   fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   letI:CharP (RatFunc K) p:=
     charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
   have hirr:=planeMap_irreducible_of_component
     (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G hG (hGmem i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro h
     exact hproper ((planeMap_dvd_iff_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G H hG (hGmem i₀)).mp h)
   have hkernels:Function.Injective (fun i =>
       RCN361.relationIdeal (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))):=by
     change Function.Injective (fun i => actualRelationKernel K order (P i) (ht i))
     exact actualRelationKernel_family_injective K order P ht hinj
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order G)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order G)=0
     exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order H)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order H)=0
     exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
   exact RCN365.finite_separable_sum_finrank_le_planar_bound
     (RatFunc K) (fun i => CoordinateField K (P i)) p
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     hRdegree hresultantDegree
     (fun i => coordinate K (P i) (order 2)) (fun i => coordinate K (P i) (order 1))
     (fun i => actual_generators K order (P i) (ht i)) hkernels hGroots hHroots
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN010
end PackedLegacy_X4

/-! Packed from ProximityPrize.SubmissionLower.H1. -/
section PackedLegacy_H1
namespace ProximityPrize.SubmissionLower.RCN009
open RCN371 RCN011
noncomputable section
variable (K:Type) [Field K]
section FirstCoordinate
variable {A:Type} [Field A]
def firstMap (φ:Polynomial K →+*A):
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 2) A:=
 (MvPolynomial.map φ).comp (collectFirst K).toRingHom
@[simp] theorem firstMap_C (φ:Polynomial K →+*A) (a:K):
   firstMap K φ (MvPolynomial.C a)=MvPolynomial.C (φ (Polynomial.C a)):=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem firstMap_X_zero (φ:Polynomial K →+*A):
   firstMap K φ (MvPolynomial.X (0:Fin 3))=MvPolynomial.C (φ Polynomial.X):=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem firstMap_X_succ (φ:Polynomial K →+*A) (i:Fin 2):
   firstMap K φ (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
theorem firstMap_eq_eval₂Hom (φ:Polynomial K →+*A):
   firstMap K φ=
     MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
       (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem firstMap_monomial (φ:Polynomial K →+*A)
   (d:Fin 3 →₀ ℕ) (a:K):
   firstMap K φ (MvPolynomial.monomial d a)=
     MvPolynomial.monomial d.tail (φ (Polynomial.C a)*(φ Polynomial.X)^d 0):=by
 rw [firstMap_eq_eval₂Hom,MvPolynomial.eval₂Hom_monomial]
 simp only [RingHom.comp_apply,Finsupp.prod_pow,Fin.prod_univ_succ,Fin.cases_zero,
   Fin.cases_succ,MvPolynomial.monomial_eq,Finsupp.tail_apply,map_mul,map_pow]
 ring
theorem support_firstMap_subset (φ:Polynomial K →+*A)
   (F:MvPolynomial (Fin 3) K):
   (firstMap K φ F).support ⊆ F.support.image Finsupp.tail:=by
 classical
 have hsum:firstMap K φ F=
     ∑ d∈F.support,firstMap K φ (MvPolynomial.monomial d (MvPolynomial.coeff d F)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 intro e he
 rw [hsum] at he
 obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
 rw [firstMap_monomial] at hed
 have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
 exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
theorem firstMap_degreeOf_le (φ:Polynomial K →+*A)
   (F:MvPolynomial (Fin 3) K) (i:Fin 2):
   (firstMap K φ F).degreeOf i ≤ F.degreeOf i.succ:=by
 classical
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro e he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_firstMap_subset K φ F he)
 exact MvPolynomial.monomial_le_degreeOf i.succ hd
end FirstCoordinate
theorem rationalMap_eq_firstMap (order:Fin 3 ≃ Fin 3) (F:Original K):
   rationalMap K order F=firstMap K (algebraMap (Polynomial K) (RatFunc K))
     (MvPolynomial.rename order.symm F):=rfl
theorem rationalMap_degreeOf_le (order:Fin 3 ≃ Fin 3) (F:Original K) (i:Fin 2):
   (rationalMap K order F).degreeOf i ≤ F.degreeOf (order i.succ):=by
 rw [rationalMap_eq_firstMap]
 calc
   _ ≤ (MvPolynomial.rename order.symm F).degreeOf i.succ:=
     firstMap_degreeOf_le K _ _ i
   _=F.degreeOf (order i.succ):=by
     simpa only [Equiv.symm_apply_apply] using
       (MvPolynomial.degreeOf_rename_of_injective (p:=F) order.symm.injective
         (order i.succ))
section NestedDegrees
variable (A:Type) [Field A]
theorem bivariateEquiv_natDegree (f:MvPolynomial (Fin 2) A):
   (bivariateEquiv A f).natDegree=f.degreeOf 0:=by
 change (Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
   (MvPolynomial.finSuccEquiv A 1 f)).natDegree=f.degreeOf 0
 rw [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.uniqueAlgEquiv A (Fin 1)).injective]
 exact MvPolynomial.natDegree_finSuccEquiv f
theorem uniqueAlgEquiv_natDegree_le (f:MvPolynomial (Fin 1) A):
   (MvPolynomial.uniqueAlgEquiv A (Fin 1) f).natDegree ≤ f.degreeOf 0:=by
 classical
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 rw [MvPolynomial.coeff_uniqueAlgEquiv]
 by_contra hne
 have hd:=MvPolynomial.monomial_le_degreeOf (0:Fin 1)
   (MvPolynomial.mem_support_iff.mpr hne)
 have hdefault:(default:Fin 1)=0:=Subsingleton.elim _ _
 simp only [hdefault,Finsupp.single_eq_same] at hd
 omega
theorem bivariateEquiv_degreeX_le (f:MvPolynomial (Fin 2) A):
   Polynomial.Bivariate.degreeX (bivariateEquiv A f) ≤ f.degreeOf 1:=by
 classical
 unfold Polynomial.Bivariate.degreeX
 apply Finset.sup_le
 intro j _
 rw [show (bivariateEquiv A f).coeff j=
   MvPolynomial.uniqueAlgEquiv A (Fin 1) ((MvPolynomial.finSuccEquiv A 1 f).coeff j) by
   simp [bivariateEquiv]]
 exact (uniqueAlgEquiv_natDegree_le A _).trans
   (MvPolynomial.degreeOf_coeff_finSuccEquiv f (0:Fin 1) j)
end NestedDegrees
theorem planeMap_natDegree_le (order:Fin 3 ≃ Fin 3) (F:Original K):
   (planeMap K order F).natDegree ≤ F.degreeOf (order 1):=by
 change (bivariateEquiv (RatFunc K) (rationalMap K order F)).natDegree ≤ _
 rw [bivariateEquiv_natDegree]
 exact rationalMap_degreeOf_le K order F (0:Fin 2)
theorem planeMap_degreeX_le (order:Fin 3 ≃ Fin 3) (F:Original K):
   Polynomial.Bivariate.degreeX (planeMap K order F) ≤ F.degreeOf (order 2):=by
 exact (bivariateEquiv_degreeX_le (RatFunc K) (rationalMap K order F)).trans
   (rationalMap_degreeOf_le K order F (1:Fin 2))
theorem planeMap_resultant_natDegree_le (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree ≤
     H.degreeOf (order 1)*G.degreeOf (order 2)+
       G.degreeOf (order 1)*H.degreeOf (order 2):=by
 exact (bivariate_resultant_natDegree_le (planeMap K order G) (planeMap K order H)
   (planeMap K order G).natDegree (planeMap K order H).natDegree).trans
     (Nat.add_le_add
       (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
       (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H)))
theorem original_characteristic_gates (order:Fin 3 ≃ Fin 3) (G H:Original K) (p:ℕ)
   (houter:G.degreeOf (order 1) < p)
   (hmixed:H.degreeOf (order 1)*G.degreeOf (order 2)+
     G.degreeOf (order 1)*H.degreeOf (order 2) < p):
   (planeMap K order G).natDegree < p∧
     (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree < p:=
 ⟨(planeMap_natDegree_le K order G).trans_lt houter,
   (planeMap_resultant_natDegree_le K order G H).trans_lt hmixed⟩
end
end ProximityPrize.SubmissionLower.RCN009
end PackedLegacy_H1

/-! Packed from ProximityPrize.SubmissionLower.X5. -/
section PackedLegacy_X5
namespace ProximityPrize.SubmissionLower.RCN013
open RCN002 RCN371 RCN011 RCN009
noncomputable section
variable (K:Type) [Field K]
def swapOtherOrder (order:Fin 3 ≃ Fin 3):Fin 3 ≃ Fin 3:=
 (Equiv.swap (1:Fin 3) 2).trans order
@[simp] theorem swapOtherOrder_zero (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 0=order 0:=by
 simp [swapOtherOrder,Equiv.swap_apply_def]
@[simp] theorem swapOtherOrder_one (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 1=order 2:=by
 simp [swapOtherOrder]
@[simp] theorem swapOtherOrder_two (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 2=order 1:=by
 simp [swapOtherOrder]
theorem rationalMap_first (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 0))=
     MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X):=by
 simp [rationalMap]
theorem rationalMap_outer (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 1))=MvPolynomial.X 0:=by
 have h:=collect_X_other K order (0:Fin 2)
 change collect K order (MvPolynomial.X (order 1))=MvPolynomial.X 0 at h
 simp [rationalMap,h]
theorem rationalMap_inner (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 2))=MvPolynomial.X 1:=by
 have h:=collect_X_other K order (1:Fin 2)
 change collect K order (MvPolynomial.X (order 2))=MvPolynomial.X 1 at h
 simp [rationalMap,h]
theorem rationalMap_swapOtherOrder (order:Fin 3 ≃ Fin 3):
   rationalMap K (swapOtherOrder order)=
     (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)).toRingHom.comp
       (rationalMap K order):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp [rationalMap]
 · intro j
   obtain ⟨i,rfl⟩:=order.surjective j
   have hi:i=0∨i=1∨i=2:=by omega
   rcases hi with rfl | rfl | rfl
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 0))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 0)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 0))=
         MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) by
       simpa only [swapOtherOrder_zero] using rationalMap_first K (swapOtherOrder order)]
     rw [rationalMap_first]
     simp
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 1))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 1)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 1))=
         MvPolynomial.X 1 by
       simpa only [swapOtherOrder_two] using rationalMap_inner K (swapOtherOrder order)]
     rw [rationalMap_outer]
     simp
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 2))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 2)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 2))=
         MvPolynomial.X 0 by
       simpa only [swapOtherOrder_one] using rationalMap_outer K (swapOtherOrder order)]
     rw [rationalMap_inner]
     simp
theorem swapped_outer_degree (order:Fin 3 ≃ Fin 3) (F:Original K):
   (planeMap K (swapOtherOrder order) F).natDegree=
     (rationalMap K order F).degreeOf 1:=by
 change (bivariateEquiv (RatFunc K) (rationalMap K (swapOtherOrder order) F)).natDegree=_
 rw [bivariateEquiv_natDegree,rationalMap_swapOtherOrder]
 change (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1) (rationalMap K order F)).degreeOf 0=_
 simpa only [Equiv.swap_apply_right] using
   (MvPolynomial.degreeOf_rename_of_injective (p:=rationalMap K order F)
     (Equiv.swap (0:Fin 2) 1).injective (1:Fin 2))
theorem positive_degree_of_irreducible {A:Type} [Field A]
   (f:MvPolynomial (Fin 2) A) (hf:Irreducible f):
   0 < f.degreeOf 0∨0 < f.degreeOf 1:=by
 classical
 by_cases h0:0 < f.degreeOf 0
 · exact Or.inl h0
 by_cases h1:0 < f.degreeOf 1
 · exact Or.inr h1
 exfalso
 have hdeg:∀ i:Fin 2,f.degreeOf i=0:=by
   intro i
   have hi:i=0∨i=1:=by omega
   rcases hi with rfl | rfl <;> omega
 have hconst:f=MvPolynomial.C (MvPolynomial.coeff 0 f):=by
   apply MvPolynomial.ext
   intro d
   by_cases hd:d=0
   · subst d
     simp
   · have hzero:MvPolynomial.coeff d f=0:=by
       by_contra hne
       have hm:d∈f.support:=MvPolynomial.mem_support_iff.mpr hne
       apply hd
       apply Finsupp.ext
       intro i
       have hle:=MvPolynomial.monomial_le_degreeOf i hm
       rw [hdeg i] at hle
       exact Nat.eq_zero_of_le_zero hle
     simp [hzero,Ne.symm hd]
 have ha:MvPolynomial.coeff 0 f≠0:=by
   intro h
   apply hf.ne_zero
   rw [hconst,h,map_zero]
 apply hf.not_isUnit
 rw [hconst]
 exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
theorem exists_positive_outer_order (order:Fin 3 ≃ Fin 3)
   (P:Ideal (Original K)) [P.IsPrime] (G:Original K)
   (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   ∃ order':Fin 3 ≃ Fin 3,
     (order'=order∨order'=swapOtherOrder order)∧
     order' 0=order 0∧0 < (planeMap K order' G).natDegree:=by
 have hirr:=rationalMap_irreducible_of_component K order P G hG hmem ht
 rcases positive_degree_of_irreducible (rationalMap K order G) hirr with h0 | h1
 · refine ⟨order,Or.inl rfl,rfl,?_⟩
   change 0 < (bivariateEquiv (RatFunc K) (rationalMap K order G)).natDegree
   rwa [bivariateEquiv_natDegree]
 · exact ⟨swapOtherOrder order,Or.inr rfl,swapOtherOrder_zero order,
     by rwa [swapped_outer_degree]⟩
def originalMixedDegree (order:Fin 3 ≃ Fin 3) (G H:Original K):ℕ:=
 H.degreeOf (order 1)*G.degreeOf (order 2)+
   G.degreeOf (order 1)*H.degreeOf (order 2)
@[simp] theorem originalMixedDegree_swap (order:Fin 3 ≃ Fin 3) (G H:Original K):
   originalMixedDegree K (swapOtherOrder order) G H=originalMixedDegree K order G H:=by
 simp only [originalMixedDegree,swapOtherOrder_one,swapOtherOrder_two]
 ring
theorem exists_positive_characteristic_order (order:Fin 3 ≃ Fin 3)
   (P:Ideal (Original K)) [P.IsPrime] (G H:Original K) (p:ℕ)
   (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   ∃ order':Fin 3 ≃ Fin 3,
     order' 0=order 0∧
     originalMixedDegree K order' G H=originalMixedDegree K order G H∧
     0 < (planeMap K order' G).natDegree∧
     (planeMap K order' G).natDegree < p∧
     (Polynomial.resultant (planeMap K order' G) (planeMap K order' H)).natDegree < p:=by
 obtain ⟨order',hor,hbase,hpos⟩:=exists_positive_outer_order K order P G hG hmem ht
 have hbudget:originalMixedDegree K order' G H=originalMixedDegree K order G H:=by
   rcases hor with rfl | rfl
   · rfl
   · exact originalMixedDegree_swap K order G H
 have hout:G.degreeOf (order' 1) < p:=by
   rcases hor with rfl | rfl
   · exact h1
   · simpa only [swapOtherOrder_one] using h2
 have hmix':H.degreeOf (order' 1)*G.degreeOf (order' 2)+
     G.degreeOf (order' 1)*H.degreeOf (order' 2) < p:=by
   change originalMixedDegree K order' G H < p
   rwa [hbudget]
 exact ⟨order',hbase,hbudget,hpos,
   original_characteristic_gates K order' G H p hout hmix'⟩
end
end ProximityPrize.SubmissionLower.RCN013
end PackedLegacy_X5

/-! Packed from ProximityPrize.SubmissionLower.G9. -/
section PackedLegacy_G9
namespace ProximityPrize.SubmissionLower.RCN004
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
noncomputable section
variable (K:Type) [Field K]
theorem rationalBaseAlgebra_congr (P:Ideal (Original K)) [P.IsPrime]
   (i j:Fin 3) (hij:i=j)
   (hi:Transcendental K (coordinate K P i))
   (hj:Transcendental K (coordinate K P j)):
   rationalBaseAlgebra K P i hi=rationalBaseAlgebra K P j hj:=by
 subst j
 rfl
public def singleSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)) (B:ℕ):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
   Module.finrank (RatFunc K) (CoordinateField K P) ≤ B
public def fieldsSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
public def familySummary {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem plane_budget_le_original (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
     (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H) ≤
       originalMixedDegree K order G H:=
 Nat.add_le_add
   (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
   (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H))
section Single
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem original_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order G H:=by
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
   exists_positive_characteristic_order K order P G H p hG hGmem ht h1 h2 hmixed
 have ht':Transcendental K (coordinate K P (order' 0)):=by
   simpa only [hbase] using ht
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
       Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order' G H:=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
   obtain ⟨hfd,hsep,hbound⟩:=actual_finite_separable_finrank_bound
     K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfd,hsep,hbound.trans (plane_budget_le_original K order' G H)⟩
 change singleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
   (originalMixedDegree K order' G H) at hresult
 rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,hbudget] at hresult
 exact hresult
end Single
section Family
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem original_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
     exists_positive_characteristic_order K order (P i₀) G H p
       hG (hGmem i₀) (ht i₀) h1 h2 hmixed
   have ht':∀ i,Transcendental K (coordinate K (P i) (order' 0)):=by
     intro i
     simpa only [hbase] using ht i
   have hresult:
       letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
         fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
       (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
         Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
         (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
           originalMixedDegree K order' G H:=by
     letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
       fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     obtain ⟨hfields,hbound⟩:=actual_finite_separable_sum_finrank_bound
       K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
     exact ⟨hfields,hbound.trans (plane_budget_le_original K order' G H)⟩
   have halg:(fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
       (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
     funext i
     exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0) hbase (ht' i) (ht i)
   change familySummary K P (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
     (originalMixedDegree K order' G H) at hresult
   rw [halg,hbudget] at hresult
   exact hresult
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end Family
theorem all_transcendental_coordinates_finite_separable
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:∀ j k:Fin 3,j≠k →
     H.degreeOf j*G.degreeOf k+G.degreeOf j*H.degreeOf k < p):
   ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 intro i hi
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hneq:order 1≠order 2:=by
   intro h
   have heq:=order.injective h
   exact (by decide:(1:Fin 3)≠2) heq
 have hbudget:originalMixedDegree K order G H < p:=
   hmixed (order 1) (order 2) hneq
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hbudget
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end ProximityPrize.SubmissionLower.RCN004
end PackedLegacy_G9

/-! Packed from ProximityPrize.SubmissionLower.AV. -/
section PackedLegacy_AV
namespace ProximityPrize.SubmissionLower.RCN001
open RCN002 RCN005
 RCN371 RCN007 RCN013
 RCN004
noncomputable section
variable (K:Type) [Field K]
section Family
variable {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem sum_actualCoordinateDegree_le_original
   (order:Fin 3 ≃ Fin 3) (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   (∑ i,actualCoordinateDegree K (P i) (order 0)) ≤ originalMixedDegree K order G H:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) (order 0))}
 let D:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (CoordinateField K (P i)):=
     rationalBaseAlgebra K (P i) (order 0) i.2
   Module.finrank (RatFunc K) (CoordinateField K (P i))
 have hinj':Function.Injective (fun i:s => P i):=by
   intro i j h
   apply Subtype.ext
   exact hinj h
 have hbound:(∑ i:s,D i) ≤ originalMixedDegree K order G H:=by
   have h:=original_finite_separable_sum_finrank_bound K order (fun i:s => P i)
     (fun i => i.2) hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
     hproper h1 h2 hmixed
   exact h.2
 calc
   _=∑ i:s,D i:=by
     apply Finset.sum_congr_set s (fun i => actualCoordinateDegree K (P i) (order 0)) D
     · intro i hi
       exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
     · intro i hi
       change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
       exact dif_neg hi
   _ ≤ _:=hbound
end Family
def coordinateMixedDegree (G H:Original K) (i:Fin 3):ℕ:=
 originalMixedDegree K (Equiv.swap 0 i) G H
@[simp] theorem coordinateMixedDegree_zero (G H:Original K):
   coordinateMixedDegree K G H 0=
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_one (G H:Original K):
   coordinateMixedDegree K G H 1=
     H.degreeOf 0*G.degreeOf 2+G.degreeOf 0*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_two (G H:Original K):
   coordinateMixedDegree K G H 2=
     H.degreeOf 0*G.degreeOf 1+G.degreeOf 0*H.degreeOf 1:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def] <;> ring
theorem sum_actualCoordinateDegree_at_le
   {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (hinj:Function.Injective P) (j:Fin 3) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ k:Fin 3,G.degreeOf k < p)
   (hmixed:coordinateMixedDegree K G H j < p):
   (∑ i,actualCoordinateDegree K (P i) j) ≤ coordinateMixedDegree K G H j:=by
 have h:=sum_actualCoordinateDegree_le_original K P (Equiv.swap 0 j) hinj p G H
   hG hGmem hHmem hproper (hdegree ((Equiv.swap 0 j) 1))
     (hdegree ((Equiv.swap 0 j) 2)) hmixed
 simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using h
end
end ProximityPrize.SubmissionLower.RCN001
end PackedLegacy_AV

/-! Packed from ProximityPrize.SubmissionLower.F. -/
section PackedLegacy_F
namespace ProximityPrize.SubmissionLower.RCN243
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN319 RCN238 RCN264
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance _root_.ProximityPrize.SubmissionLower.RCN243.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN243.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
def regularitySurface (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)
theorem selectedPoint_evaluation (selected:K → Polynomial K) (γ:K)
   (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ Q)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) Q:=by
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
theorem noLargeSelectedPencil_mono
   (selected:K → Polynomial K) (Γ Δ:Finset K) (w e:ℕ)
   (hsub:Δ ⊆ Γ) (hno:NoLargeSelectedPencil selected Γ w e):
   NoLargeSelectedPencil selected Δ w e:=by
 intro P₀ P₁ h₀ h₁
 apply le_trans (Finset.card_le_card ?_) (hno P₀ P₁ h₀ h₁)
 intro γ hγ
 obtain ⟨hΔ,hp⟩:=Finset.mem_filter.mp hγ
 exact Finset.mem_filter.mpr ⟨hsub hΔ,hp⟩
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN243.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
theorem proper_cut_seed_bound_of_projection_sum
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i):
   Γ.card*(a-w) ≤ (nodes.card-w)*(∑ i,cap i*budget i)+
     (e+1)*(a-w)*budget 2:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let degree:RegularComponent Ω G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Ω C.1 i
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have htmem:=regularComponent_T_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Ω C.1:=
     all_transcendental_coordinates_finite_separable Ω C.1 p G T hG hgmem htmem
       hproper hGdegree hcutDegree
   have hcount:=prime_seed_incidence_sharp φ C.1 hproj
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ => hdegree γ (hsub hγ))
     (fun γ hγ => hsolution γ (hsub hγ))
     (fun γ hγ => hregular γ (hsub hγ))
     (fun γ hγ => componentSeeds_on_prime Ω G T H Γ (selectedPoint φ selected) C γ hγ)
     (fun γ hγ => hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil) cap hcap
   exact hcount
 exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   cap budget degree hcomponent hbudget
theorem regularComponents_degree_budget
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (p:ℕ) [CharP Ω p] (hG:Irreducible G) (hproper:¬ G∣T)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p):
   ∀ i,(∑ C:RegularComponent Ω G T (regularitySurface φ F),
     actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i:=by
 intro i
 letI:∀ C:RegularComponent Ω G T (regularitySurface φ F),C.1.IsPrime:=
   fun C => regularComponent_isPrime Ω G T (regularitySurface φ F) C
 have hneq:(Equiv.swap (0:Fin 3) i) 1≠(Equiv.swap (0:Fin 3) i) 2:=
   (Equiv.swap (0:Fin 3) i).injective.ne (by decide)
 have hmixed:coordinateMixedDegree Ω G T i < p:=
   hcutDegree ((Equiv.swap (0:Fin 3) i) 1) ((Equiv.swap (0:Fin 3) i) 2) hneq
 exact sum_actualCoordinateDegree_at_le Ω
   (fun C:RegularComponent Ω G T (regularitySurface φ F) => C.1)
   Subtype.val_injective i p G T hG
   (regularComponent_G_mem Ω G T (regularitySurface φ F))
   (regularComponent_T_mem Ω G T (regularitySurface φ F))
   hproper hGdegree hmixed
theorem proper_cut_seed_bound
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,cap i*coordinateMixedDegree Ω G T i)+
     (e+1)*(a-w)*coordinateMixedDegree Ω G T 2:=
 proper_cut_seed_bound_of_projection_sum φ F G T hG hdiv hproper selected Γ
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree hcutDegree
   hdegree hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
   (coordinateMixedDegree Ω G T) hcap
   (regularComponents_degree_budget φ F G T p hG hproper hGdegree hcutDegree)
end
end ProximityPrize.SubmissionLower.RCN243
end PackedLegacy_F

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier08 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.AI. -/
section PackedLegacy_AI
namespace ProximityPrize.SubmissionLower.RCN301
open RCN174 RCN256
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def prime:ℕ:=2130706433
namespace Profile
end Profile
end ProximityPrize.SubmissionLower.RCN301
end PackedLegacy_AI

/-! Packed from ProximityPrize.SubmissionLower.H. -/
section PackedLegacy_H
namespace ProximityPrize.SubmissionLower.RCN213
open scoped BigOperators
end ProximityPrize.SubmissionLower.RCN213
end PackedLegacy_H

/-! Packed from ProximityPrize.SubmissionLower.R. -/
section PackedLegacy_R
namespace ProximityPrize.SubmissionLower.RCN223
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def prime:ℕ:=2130706433
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq
end ProximityPrize.SubmissionLower.RCN223
end PackedLegacy_R

/-! Packed from ProximityPrize.SubmissionLower.CB. -/
section PackedLegacy_CB
namespace ProximityPrize.SubmissionLower.RCN294
open scoped BigOperators
open RCN223
def sumVector {I:Type} [Fintype I] (v:I-> DegreeVector):DegreeVector:=
 ⟨∑ i,(v i).y,∑ i,(v i).r,∑ i,(v i).z⟩
def vectorLE (a b:DegreeVector):Prop:=
 a.y ≤ b.y∧a.r ≤ b.r∧a.z ≤ b.z
def dot (a b:DegreeVector):Nat:=
 a.y*b.y+a.r*b.r+a.z*b.z
theorem dot_mono_left {a b:DegreeVector} (c:DegreeVector)
   (h:vectorLE a b):dot a c ≤ dot b c:=
 Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1)
     (Nat.mul_le_mul_right c.r h.2.1))
   (Nat.mul_le_mul_right c.z h.2.2)
theorem dot_sum_left {I:Type} [Fintype I]
   (v:I-> DegreeVector) (a:DegreeVector):
   dot (sumVector v) a=∑ i,dot (v i) a:=by
 simp only [dot,sumVector,Finset.sum_add_distrib,Finset.sum_mul]
end ProximityPrize.SubmissionLower.RCN294
end PackedLegacy_CB

/-! Packed from ProximityPrize.SubmissionLower.AK. -/
section PackedLegacy_AK
namespace ProximityPrize.SubmissionLower.RCN318
open scoped BigOperators
open RCN223 RCN294
structure TightParameters where
 n:ℕ
 w:ℕ
 a:ℕ
 D:ℕ
 L:ℕ
 s:ℕ
 deriving DecidableEq
namespace TightParameters
def errors (P:TightParameters):ℕ:=P.n-P.a
def gap (P:TightParameters):ℕ:=P.a-P.w
def kappa (P:TightParameters):ℕ:=2*P.s-1
def implicitYCap (P:TightParameters):ℕ:=(P.kappa*P.D-1)/P.w
def algebraicCap (P:TightParameters):ℕ:=P.kappa*P.L
def agreement (P:TightParameters):DegreeVector:=
 ⟨1+2*P.w*P.implicitYCap,
   P.w,
   2*P.w*P.algebraicCap+1⟩
def aggregateCost (P:TightParameters):DegreeVector:=
 ⟨P.algebraicCap,
   2*P.implicitYCap*P.algebraicCap,
   P.implicitYCap⟩
def coefficients (P:TightParameters):DegreeVector:=
 ⟨(P.n-P.w)*P.agreement.y,
   (P.n-P.w)*P.agreement.r,
   (P.n-P.w)*P.agreement.z+(P.errors+1)*P.gap⟩
def coreNumerator (P:TightParameters):ℕ:=
 (P.n-P.w)*dot P.agreement P.aggregateCost+
   (P.errors+1)*P.gap*P.implicitYCap
def tightNumerator (P:TightParameters):ℕ:=
 P.coreNumerator+2*P.algebraicCap^2*P.gap
def countCap (P:TightParameters):ℕ:=P.tightNumerator/P.gap
theorem bound_eq_dot (P:TightParameters) (v:DegreeVector):
   (P.n-P.w)*dot P.agreement v+
       (P.errors+1)*P.gap*v.z=
     dot v P.coefficients:=by
 simp only [coefficients,errors,gap,dot]
 ring
theorem aggregate_eq_core (P:TightParameters):
   dot P.aggregateCost P.coefficients=P.coreNumerator:=by
 simp only [aggregateCost,coefficients,coreNumerator,dot]
 ring
theorem sum_counts_bound (P:TightParameters) {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector)
   (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
   (hcount:∀ i,count i*P.gap ≤
     (P.n-P.w)*dot P.agreement (cost i)+
       (P.errors+1)*P.gap*(cost i).z):
   (∑ i,count i)*P.gap ≤ P.coreNumerator:=by
 calc
   _=∑ i,count i*P.gap:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (cost i) P.coefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←P.bound_eq_dot]
     exact hcount i
   _=dot (sumVector cost) P.coefficients:=
     (dot_sum_left cost P.coefficients).symm
   _ ≤ dot P.aggregateCost P.coefficients:=
     dot_mono_left P.coefficients ⟨hy,hr,hz⟩
   _=P.coreNumerator:=P.aggregate_eq_core
theorem with_exceptions_bound (P:TightParameters) {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
   (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
   (hcount:∀ i,count i*P.gap ≤
     (P.n-P.w)*dot P.agreement (cost i)+
       (P.errors+1)*P.gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*P.algebraicCap^2):
   ((∑ i,count i)+exceptions)*P.gap ≤ P.tightNumerator:=by
 have hmain:=P.sum_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*P.gap+exceptions*P.gap:=Nat.add_mul _ _ _
   _ ≤ P.coreNumerator+2*P.algebraicCap^2*P.gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right P.gap hexceptions)
   _=P.tightNumerator:=rfl
theorem count_le_countCap (P:TightParameters) (count:ℕ)
   (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.tightNumerator):
   count ≤ P.countCap:=by
 exact (Nat.le_div_iff_mul_le hgap).mpr hcount
end TightParameters
end ProximityPrize.SubmissionLower.RCN318
end PackedLegacy_AK

/-! Packed from ProximityPrize.SubmissionLower.N5. -/
section PackedLegacy_N5
namespace ProximityPrize.SubmissionLower.RCN260
open scoped BigOperators
open RCN318 RCN223 RCN294
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
structure UnequalParameters where
 n:ℕ
 w:ℕ
 a:ℕ
 leftY:ℕ
 leftR:ℕ
 leftZ:ℕ
 rightY:ℕ
 rightR:ℕ
 rightZ:ℕ
 deriving DecidableEq
namespace UnequalParameters
def errors (P:UnequalParameters):ℕ:=P.n-P.a
def gap (P:UnequalParameters):ℕ:=P.a-P.w
def leftAgreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.leftY,
   P.w*(2*P.leftR-1),
   2*P.w*P.leftZ+1⟩
def rightAgreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.rightY,
   P.w*(2*P.rightR-1),
   2*P.w*P.rightZ+1⟩
def agreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨max P.leftAgreement.y P.rightAgreement.y,
   max P.leftAgreement.r P.rightAgreement.r,
   max P.leftAgreement.z P.rightAgreement.z⟩
def mixedCost (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨P.leftR*P.rightZ+P.leftZ*P.rightR,
   P.leftY*P.rightZ+P.leftZ*P.rightY,
   P.leftY*P.rightR+P.leftR*P.rightY⟩
def regularNumerator (P:UnequalParameters):ℕ:=
 (P.n-P.w)*dot P.agreement P.mixedCost+
   (P.errors+1)*P.gap*P.mixedCost.z
def regularCountCap (P:UnequalParameters):ℕ:=P.regularNumerator/P.gap
theorem regular_count_le (P:UnequalParameters) (count:ℕ)
   (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.regularNumerator):
   count ≤ P.regularCountCap:=
 (Nat.le_div_iff_mul_le hgap).mpr hcount
end UnequalParameters
end ProximityPrize.SubmissionLower.RCN260
end PackedLegacy_N5

/-! Packed from ProximityPrize.SubmissionLower.C. -/
section PackedLegacy_C
namespace ProximityPrize.SubmissionLower.RCN081
open RCN174
noncomputable section
def weightEmbed (weights:Fin 4 → ℕ):(Fin 4 →₀ ℕ) →+(Fin 5 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+
   Finsupp.single 4 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ) (i:Fin 4):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   weightEmbed weights d (4:Fin 5)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 5 →₀ ℕ => a i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
variable {K:Type*} [Field K]
def weightedLift (K:Type*) [Field K] (weights:Fin 4 → ℕ):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 5) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem weightedLift_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightedLift K weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)
theorem weightedLift_ne_zero (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K)
   (hP:P≠0):weightedLift K weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).support=P.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).degreeOf (4:Fin 5)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift K weights P).degreeOf (4:Fin 5)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
 funext d
 exact weightEmbed_last weights d
theorem weightedTotalDegree_mul (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift K weights (P*Q)).degreeOf (4:Fin 5):=
     (degree_weightedLift weights (P*Q)).symm
   _=(weightedLift K weights P*weightedLift K weights Q).degreeOf (4:Fin 5):=by
     rw [map_mul]
   _=(weightedLift K weights P).degreeOf (4:Fin 5)+
       (weightedLift K weights Q).degreeOf (4:Fin 5):=
     MvPolynomial.degreeOf_mul_eq (weightedLift_ne_zero weights P hP)
       (weightedLift_ne_zero weights Q hQ)
   _=MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
     rw [degree_weightedLift,degree_weightedLift]
theorem weightedTotalDegree_le_of_dvd (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_le_iff (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (cap:ℕ):
   MvPolynomial.weightedTotalDegree weights P ≤ cap ↔
     ∀ d∈P.support,Finsupp.weight weights d ≤ cap:=by
 simp only [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
theorem weight_fin4 (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2+d 3*weights 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 calc
   Finsupp.weight weights d=Finsupp.weight weights
       (Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
         Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)):=congrArg _ hd
   _=_:=by simp only [map_add,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id]
def seedWeights:Fin 4 → ℕ:=![0,1,0,1]
def slopeWeights:Fin 4 → ℕ:=![0,0,1,0]
def contactWeights (w:ℕ):Fin 4 → ℕ:=![1,w,w-1,0]
theorem seed_weight (d:Fin 4 →₀ ℕ):Finsupp.weight seedWeights d=d 1+d 3:=by
 rw [weight_fin4]
 simp [seedWeights]
theorem slope_weight (d:Fin 4 →₀ ℕ):Finsupp.weight slopeWeights d=d 2:=by
 rw [weight_fin4]
 simp [slopeWeights]
theorem contact_weight (w:ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight (contactWeights w) d=d 0+w*d 1+(w-1)*d 2:=by
 rw [weight_fin4]
 simp [contactWeights,Nat.mul_comm]
theorem mem_globalCoefficientBox_iff (P:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hD:0 < D):
   P∈globalCoefficientBox K D w L s ↔
     MvPolynomial.weightedTotalDegree seedWeights P ≤ L∧
     MvPolynomial.weightedTotalDegree slopeWeights P ≤ s∧
     MvPolynomial.weightedTotalDegree (contactWeights w) P ≤ D-1:=by
 constructor
 · intro h
   refine ⟨?_,?_,?_⟩
   · apply (weightedTotalDegree_le_iff seedWeights P L).mpr
     intro d hd
     rw [seed_weight]
     exact (h hd).1
   · apply (weightedTotalDegree_le_iff slopeWeights P s).mpr
     intro d hd
     rw [slope_weight]
     exact (h hd).2.1
   · apply (weightedTotalDegree_le_iff (contactWeights w) P (D-1)).mpr
     intro d hd
     rw [contact_weight]
     have hh:=(h hd).2.2
     omega
 · rintro ⟨hseed,hslope,hcontact⟩ d hd
   have hs:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hseed
   have hr:=(MvPolynomial.le_weightedTotalDegree slopeWeights hd).trans hslope
   have hc:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hcontact
   rw [seed_weight] at hs
   rw [slope_weight] at hr
   rw [contact_weight] at hc
   exact ⟨hs,hr,by omega⟩
theorem mem_globalCoefficientBox_of_dvd
   (F Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
   (hQ:Q≠0) (hdiv:F∣Q)
   (hbox:Q∈globalCoefficientBox K D w L s):
   F∈globalCoefficientBox K D w L s:=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have hh:=(hbox hd).2.2
   omega
 have hcaps:=(mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
 apply (mem_globalCoefficientBox_iff F D w L s hD).mpr
 exact ⟨(weightedTotalDegree_le_of_dvd seedWeights F Q hdiv hQ).trans hcaps.1,
   (weightedTotalDegree_le_of_dvd slopeWeights F Q hdiv hQ).trans hcaps.2.1,
   (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hcaps.2.2⟩
theorem degreeOf_le_of_dvd (i:Fin 4) (F Q:MvPolynomial (Fin 4) K)
   (hdiv:F∣Q) (hQ:Q≠0):F.degreeOf i ≤ Q.degreeOf i:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hF,hG⟩
 rw [MvPolynomial.degreeOf_mul_eq hF hG]
 exact Nat.le_add_right _ _
theorem sum_degreeOf_le_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q) (i:Fin 4):
   (∑ j∈I,(f j).degreeOf i) ≤ Q.degreeOf i:=by
 classical
 have hprod:(∏ j∈I,f j)≠0:=by
   intro hz
   rcases hdiv with ⟨G,hG⟩
   apply hQ
   rw [hG,hz,zero_mul]
 have hf:∀ j∈I,f j≠0:=Finset.prod_ne_zero_iff.mp hprod
 calc
   (∑ j∈I,(f j).degreeOf i)=(∏ j∈I,f j).degreeOf i:=
     (MvPolynomial.degreeOf_prod_eq (n:=i) I f hf).symm
   _ ≤ Q.degreeOf i:=degreeOf_le_of_dvd i _ Q hdiv hQ
theorem separated_degree_budgets_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q):
   (∑ j∈I,(f j).degreeOf (1:Fin 4)) ≤ Q.degreeOf (1:Fin 4)∧
   (∑ j∈I,(f j).degreeOf (2:Fin 4)) ≤ Q.degreeOf (2:Fin 4)∧
   (∑ j∈I,(f j).degreeOf (3:Fin 4)) ≤ Q.degreeOf (3:Fin 4):=
 ⟨sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 1,
   sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 2,
   sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 3⟩
theorem degreeOf_Y_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (1:Fin 4) ≤ (D-1)/w:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 apply (Nat.le_div_iff_mul_le hw).mpr
 have hc:=(hbox hd).2.2
 have hm:d 1*w=w*d 1:=Nat.mul_comm _ _
 omega
theorem degreeOf_R_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (2:Fin 4) ≤ s:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hbox hd).2.1
theorem degreeOf_Z_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (3:Fin 4) ≤ L:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=(hbox hd).1
 omega
theorem degree_bounds_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (1:Fin 4) ≤ (D-1)/w∧
   Q.degreeOf (2:Fin 4) ≤ s∧Q.degreeOf (3:Fin 4) ≤ L:=
 ⟨degreeOf_Y_le_of_mem_box Q D w L s hw hbox,
   degreeOf_R_le_of_mem_box Q D w L s hbox,
   degreeOf_Z_le_of_mem_box Q D w L s hbox⟩
theorem separated_factor_caps_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K D w L s) (hdiv:(∏ j∈I,f j)∣Q):
   (∑ j∈I,(f j).degreeOf (1:Fin 4)) ≤ (D-1)/w∧
   (∑ j∈I,(f j).degreeOf (2:Fin 4)) ≤ s∧
   (∑ j∈I,(f j).degreeOf (3:Fin 4)) ≤ L:=by
 have hsum:=separated_degree_budgets_of_prod_dvd I f Q hQ hdiv
 have hcaps:=degree_bounds_of_mem_box Q D w L s hw hbox
 exact ⟨hsum.1.trans hcaps.1,hsum.2.1.trans hcaps.2.1,hsum.2.2.trans hcaps.2.2⟩
end
end ProximityPrize.SubmissionLower.RCN081
end PackedLegacy_C

/-! Packed from ProximityPrize.SubmissionLower.J1. -/
section PackedLegacy_J1
namespace ProximityPrize.SubmissionLower.RCN082
open UniqueFactorizationMonoid RCN136 RCN174
noncomputable section
variable {K L:Type*} [Field K] [Field L]
local instance _root_.ProximityPrize.SubmissionLower.RCN082.instStrongNormalizationMonoidMvPolynomialFinOfNatNat_proximityPrize :StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
 UniqueFactorizationMonoid.strongNormalizationMonoid
def activeFactors (Q:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (normalizedFactors Q).toFinset.filter
   (fun F => 0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
theorem activeFactors_spec (Q F:MvPolynomial (Fin 4) K)
   (hF:F∈activeFactors Q):
   Irreducible F∧F∣Q∧0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 classical
 obtain ⟨hm,hp⟩:=Finset.mem_filter.mp hF
 have hmem:F∈normalizedFactors Q:=Multiset.mem_toFinset.mp hm
 exact ⟨irreducible_of_normalized_factor F hmem,
   dvd_of_mem_normalizedFactors hmem,hp⟩
theorem exists_normalized_factor_of_map_zero
   {A:Type*} [CommRing A] [IsDomain A]
   (ψ:MvPolynomial (Fin 4) K →+*A)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hzero:ψ Q=0):
   ∃ F∈normalizedFactors Q,ψ F=0:=by
 have hassoc:=Associated.map ψ (prod_normalizedFactors hQ)
 rw [hzero] at hassoc
 have hp:ψ (normalizedFactors Q).prod=0:=
   (associated_zero_iff_eq_zero _).mp hassoc
 rw [map_multiset_prod] at hp
 exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
theorem eq_C_of_all_degreeOf_zero (P:MvPolynomial (Fin 3) L)
   (h:∀ i,P.degreeOf i=0):P=MvPolynomial.C (P.coeff 0):=by
 classical
 apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
 apply Nat.eq_zero_of_le_zero
 rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
 intro d hd
 have hd0:d=0:=by
   ext i
   have hi:=MvPolynomial.monomial_le_degreeOf i hd
   rw [h i] at hi
   exact Nat.eq_zero_of_le_zero hi
 simp [hd0]
theorem positive_seed_degree_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ F)=0):
   0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 by_contra hn
 have hy:F.degreeOf 1 ≤ 0:=by omega
 have hr:F.degreeOf 2 ≤ 0:=by omega
 have hz:F.degreeOf 3 ≤ 0:=by omega
 have hc:=surfaceMap_separated_caps φ F 0 0 0 hy hr hz
 have hconst:surfaceMap φ F=MvPolynomial.C ((surfaceMap φ F).coeff 0):=by
   apply eq_C_of_all_degreeOf_zero
   intro i
   fin_cases i
   · exact Nat.eq_zero_of_le_zero hc.1
   · exact Nat.eq_zero_of_le_zero hc.2.1
   · exact Nat.eq_zero_of_le_zero hc.2.2
 have hvalue:=hzero
 rw [hconst,MvPolynomial.eval_C] at hvalue
 apply surfaceMap_ne_zero φ hφ F hF
 rw [hconst,hvalue,map_zero]
theorem exists_active_factor_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
   ∃ F∈activeFactors Q,MvPolynomial.eval v (surfaceMap φ F)=0:=by
 classical
 obtain ⟨F,hmem,hz⟩:=exists_normalized_factor_of_map_zero
   ((MvPolynomial.eval v).comp (surfaceMap φ)) Q hQ hzero
 have hF:=ne_zero_of_mem_normalizedFactors hmem
 have hpos:=positive_seed_degree_of_surface_zero φ hφ F hF v hz
 exact ⟨F,Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem,hpos⟩,hz⟩
theorem activeFactors_product_dvd (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
   (∏ F∈activeFactors Q,F)∣Q:=by
 classical
 apply (Finset.prod_dvd_prod_of_subset (activeFactors Q)
   (normalizedFactors Q).toFinset id (Finset.filter_subset _ _)).trans
 exact (normalizedFactors Q).toFinset_prod_dvd_prod.trans (prod_normalizedFactors hQ).dvd
end
end ProximityPrize.SubmissionLower.RCN082
end PackedLegacy_J1

/-! Packed from ProximityPrize.SubmissionLower.BH. -/
section PackedLegacy_BH
namespace ProximityPrize.SubmissionLower.RCN132
open RCN136 RCN082
noncomputable section
variable (K:Type*) [Field K]
abbrev Collected:=MvPolynomial (Fin 3) (Polynomial K)
abbrev RationalCoefficients:=FractionRing (Polynomial K)
abbrev RationalPolynomials:=MvPolynomial (Fin 3) (RationalCoefficients K)
attribute [local instance] MvPolynomial.algebraMvPolynomial
def coefficientDenominators:Submonoid (Collected K):=
 (nonZeroDivisors (Polynomial K)).map MvPolynomial.C
local instance _root_.ProximityPrize.SubmissionLower.RCN132.instIsLocalizationCollectedCoefficientDenominatorsRationalPolynomials :IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RationalCoefficients K)
def rationalSurfaceMap:
   MvPolynomial (Fin 4) K →+*RationalPolynomials K:=
 surfaceMap (algebraMap (Polynomial K) (RationalCoefficients K))
theorem rationalSurfaceMap_eq (F:MvPolynomial (Fin 4) K):
   rationalSurfaceMap K F=
     algebraMap (Collected K) (RationalPolynomials K) (collectX K F):=rfl
def xLift (P:Polynomial K):MvPolynomial (Fin 4) K:=
 (collectX K).symm (MvPolynomial.C P)
theorem xLift_add (P Q:Polynomial K):xLift K (P+Q)=xLift K P+xLift K Q:=by
 simp [xLift]
theorem xLift_monomial (n:ℕ) (a:K):
   xLift K (Polynomial.monomial n a)=
     MvPolynomial.C a*MvPolynomial.X (0:Fin 4)^n:=by
 apply (collectX K).injective
 simp [xLift, ←Polynomial.C_mul_X_pow_eq_monomial]
theorem xLift_ne_zero (P:Polynomial K) (hP:P≠0):xLift K P≠0:=by
 intro h
 have hh:=congrArg (collectX K) h
 have hc:(MvPolynomial.C P:Collected K)=0:=by
   simpa only [xLift,AlgEquiv.apply_symm_apply,map_zero] using hh
 apply hP
 apply MvPolynomial.C_injective
 simpa only [map_zero] using hc
theorem xLift_degreeOf_succ (P:Polynomial K) (i:Fin 3):
   (xLift K P).degreeOf i.succ=0:=by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ =>
     rw [xLift_add]
     apply Nat.eq_zero_of_le_zero
     simpa only [hP,hQ,max_self] using
       MvPolynomial.degreeOf_add_le i.succ (xLift K P) (xLift K Q)
 | monomial n a =>
     rw [xLift_monomial]
     have hx:(MvPolynomial.X (0:Fin 4):MvPolynomial (Fin 4) K).degreeOf i.succ=0:=by
       simp [MvPolynomial.degreeOf_X,Fin.succ_ne_zero]
     have hp:=MvPolynomial.degreeOf_pow_le i.succ
       (MvPolynomial.X (0:Fin 4):MvPolynomial (Fin 4) K) n
     rw [hx,Nat.mul_zero] at hp
     have hm:=MvPolynomial.degreeOf_mul_le i.succ
       (MvPolynomial.C a:MvPolynomial (Fin 4) K) (MvPolynomial.X (0:Fin 4)^n)
     rw [MvPolynomial.degreeOf_C,Nat.zero_add] at hm
     exact Nat.eq_zero_of_le_zero (hm.trans hp)
theorem not_dvd_xLift_of_positive_degree
   (F:MvPolynomial (Fin 4) K) (P:Polynomial K) (hP:P≠0)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   ¬ F∣xLift K P:=by
 intro hdiv
 have hi:∃ i:Fin 3,0 < F.degreeOf i.succ:=by
   by_cases hy:0 < F.degreeOf 1
   · exact ⟨0,hy⟩
   by_cases hr:0 < F.degreeOf 2
   · exact ⟨1,hr⟩
   exact ⟨2,by change 0 < F.degreeOf (3:Fin 4);omega⟩
 obtain ⟨i,hi⟩:=hi
 have hb:=RCN081.degreeOf_le_of_dvd i.succ F (xLift K P)
   hdiv (xLift_ne_zero K P hP)
 rw [xLift_degreeOf_succ] at hb
 omega
theorem collected_principal_isPrime (F:MvPolynomial (Fin 4) K) (hF:Irreducible F):
   (Ideal.span ({collectX K F}:Set (Collected K))).IsPrime:=by
 have hi:Irreducible (collectX K F):=(MulEquiv.irreducible_iff (collectX K)).mpr hF
 exact Ideal.isPrime_span_singleton_of_prime hi.prime
theorem coefficientDenominators_disjoint (F:MvPolynomial (Fin 4) K)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collectX K F}:Set (Collected K)):Set (Collected K)):=by
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨P,hP,rfl⟩:=Submonoid.mem_map.mp ha
 have hP0:P≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hP
 obtain ⟨G,hG⟩:=Ideal.mem_span_singleton.mp hI
 have hdiv:F∣xLift K P:=by
   refine ⟨(collectX K).symm G,?_⟩
   apply (collectX K).injective
   simpa only [xLift,AlgEquiv.apply_symm_apply,map_mul] using hG
 exact not_dvd_xLift_of_positive_degree K F P hP0 hpos hdiv
theorem localized_principal_isPrime (F:MvPolynomial (Fin 4) K)
   (hF:Irreducible F) (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   (Ideal.span ({rationalSurfaceMap K F}:Set (RationalPolynomials K))).IsPrime:=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collectX K F}:Set (Collected K)))
   (collected_principal_isPrime K F hF) (coefficientDenominators_disjoint K F hpos)
 simpa only [Ideal.map_span,Set.image_singleton, ←rationalSurfaceMap_eq] using hp
theorem rationalSurfaceMap_irreducible (F:MvPolynomial (Fin 4) K)
   (hF:Irreducible F) (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   Irreducible (rationalSurfaceMap K F):=by
 have hne:rationalSurfaceMap K F≠0:=
   surfaceMap_ne_zero (algebraMap (Polynomial K) (RationalCoefficients K))
     (IsFractionRing.injective (Polynomial K) (RationalCoefficients K)) F hF.ne_zero
 exact ((Ideal.span_singleton_prime hne).mp
   (localized_principal_isPrime K F hF hpos)).irreducible
theorem rationalSurfaceMap_dvd_iff
   (F M:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   rationalSurfaceMap K F∣rationalSurfaceMap K M ↔ F∣M:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collectX K M)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collectX K F}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalSurfaceMap_eq] using hdiv
   have hu:collectX K M∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collectX K F}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K F hF)
     (coefficientDenominators_disjoint K F hpos)] at hu
   obtain ⟨G,hG⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collectX K).symm G,?_⟩
   apply (collectX K).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hG
 · intro hdiv
   exact map_dvd (rationalSurfaceMap K) hdiv
end
end ProximityPrize.SubmissionLower.RCN132
end PackedLegacy_BH

/-! Packed from ProximityPrize.SubmissionLower.R6. -/
section PackedLegacy_R6
namespace ProximityPrize.SubmissionLower.RCN350
noncomputable section
section FlatPrincipal
variable {A B:Type*} [CommRing A] [IsDomain A]
 [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra A B]
 [Module.Flat A B]
theorem prime_eq_span_of_le (g:B) (hg:Prime g)
   (Q:Ideal B) [Q.IsPrime] (hQ:Q≠⊥)
   (hle:Q ≤ Ideal.span {g}):Q=Ideal.span {g}:=by
 let P:Ideal B:=Ideal.span {g}
 haveI:P.IsPrime:=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
 have hheight:P.height ≤ 1:=Ideal.height_span_singleton_le_one hg.not_unit
 by_contra hne
 have hlt:Q < P:=lt_of_le_of_ne hle hne
 have hsmall:=(Ideal.height_le_iff (p:=P) (n:=1)).mp hheight Q
   inferInstance hlt
 have hzero:Q.height=0:=Order.lt_one_iff.mp hsmall
 exact hQ (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
theorem under_prime_factor_eq
   (hinjective:Function.Injective (algebraMap A B))
   (F:A) (hF:Prime F) (g:B) (hg:Prime g)
   (hdiv:g∣algebraMap A B F):
   (Ideal.span {g}).under A=Ideal.span {F}:=by
 let P:Ideal B:=Ideal.span {g}
 let p:Ideal A:=Ideal.span {F}
 haveI:P.IsPrime:=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
 haveI:p.IsPrime:=(Ideal.span_singleton_prime hF.ne_zero).mpr hF
 have hp:p ≤ P.under A:=by
   apply Ideal.span_le.mpr
   intro x hx
   obtain rfl:=Set.mem_singleton_iff.mp hx
   exact Ideal.mem_span_singleton.mpr hdiv
 obtain ⟨Q,hQP,hQprime,hQover⟩:=
   P.exists_ideal_le_liesOver_of_le (p:=p) (q:=P.under A) hp
 letI:Q.IsPrime:=hQprime
 letI:Q.LiesOver p:=hQover
 have hFQ:algebraMap A B F∈Q:=by
   change F∈Q.under A
   rw [←Q.over_def p]
   exact Ideal.subset_span (Set.mem_singleton F)
 have hQ:Q≠⊥:=by
   intro hbot
   rw [hbot,Ideal.mem_bot] at hFQ
   exact hF.ne_zero (hinjective (by simpa only [map_zero] using hFQ))
 have heq:Q=P:=prime_eq_span_of_le g hg Q hQ hQP
 have hover:Q.under A=p:=(Q.over_def p).symm
 simpa only [heq] using hover
end FlatPrincipal
section CoefficientExtension
variable {K L σ:Type*} [Field K] [Field L] [Algebra K L]
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem coefficient_extension_flat:
   Module.Flat (MvPolynomial σ K) (MvPolynomial σ L):=by
 exact Module.Flat.of_linearEquiv
   (Algebra.IsPushout.equiv K (MvPolynomial σ K) L
     (MvPolynomial σ L)).symm.toLinearEquiv
variable [Finite σ]
theorem geometric_factor_contraction
   (F:MvPolynomial σ K) (hF:Irreducible F)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdiv:g∣MvPolynomial.map (algebraMap K L) F):
   Ideal.comap (MvPolynomial.map (algebraMap K L)) (Ideal.span {g})=
     Ideal.span {F}:=by
 letI:=coefficient_extension_flat (K:=K) (L:=L) (σ:=σ)
 have hinj:Function.Injective
     (algebraMap (MvPolynomial σ K) (MvPolynomial σ L)):=
   MvPolynomial.map_injective _ (algebraMap K L).injective
 exact under_prime_factor_eq hinj F hF.prime g hg.prime hdiv
theorem original_dvd_of_geometric_factor_dvd
   (F M:MvPolynomial σ K) (hF:Irreducible F)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdivF:g∣MvPolynomial.map (algebraMap K L) F)
   (hdivM:g∣MvPolynomial.map (algebraMap K L) M):
   F∣M:=by
 have hm:M∈Ideal.comap (MvPolynomial.map (algebraMap K L))
     (Ideal.span {g}):=Ideal.mem_span_singleton.mpr hdivM
 rw [geometric_factor_contraction F hF g hg hdivF] at hm
 exact Ideal.mem_span_singleton.mp hm
end CoefficientExtension
end
end ProximityPrize.SubmissionLower.RCN350
end PackedLegacy_R6

/-! Packed from ProximityPrize.SubmissionLower.CG. -/
section PackedLegacy_CG
namespace ProximityPrize.SubmissionLower.RCN311
open RCN077 RCN313 RCN047 RCN269 RCN233 RCN139 RCN347 RCN174 RCN319
noncomputable section
variable (K:Type*) [CommRing K]
theorem numeratorStep_mul_equation (F A:Poly4 K) (b:ℕ):
   numeratorStep K F b (F*A)=F*numeratorStep K F b A:=by
 unfold numeratorStep clearedStep
 simp only [leibniz_product]
 unfold polyG polyH
 ring
theorem equation_dvd_numeratorStep (F M:Poly4 K) (b:ℕ) (h:F∣M):
   F∣numeratorStep K F b M:=by
 rcases h with ⟨A,rfl⟩
 rw [numeratorStep_mul_equation]
 exact dvd_mul_right F _
theorem equation_dvd_all_later_numerators (F:Poly4 K) (b:ℕ)
   (h:F∣numerator K F b):
   ∀ j,b ≤ j → F∣numerator K F j:=by
 intro j hbj
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hbj
 clear hbj
 induction d with
 | zero => simpa using h
 | succ d ih =>
     simpa only [Nat.add_succ,numerator_succ] using
       equation_dvd_numeratorStep K F (numerator K F (b+d)) (b+d) ih
variable {L:Type*} [CommRing L]
theorem all_later_numerators_vanish (coefficients:K →+*L)
   (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (b:ℕ) (h:F∣numerator K F b):
   ∀ j,b ≤ j →
     MvPolynomial.eval₂Hom coefficients v (numerator K F j)=0:=by
 intro j hbj
 rcases equation_dvd_all_later_numerators K F b h j hbj with ⟨A,hA⟩
 rw [hA,map_mul,hF,zero_mul]
end
section PolynomialFamily
variable {K L:Type*} [Field K] [Field L]
theorem all_tail_jets_zero_of_first_tail_dvd
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hdiv:F∣numerator K F (w+1)):
   ∀ j,w < j →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hreg)
       (contactCoordinate K F (1:Fin 4)) j=0:=by
 intro j hj
 rw [jetCoefficient_eq_evaluated_numerator coefficients F v hF hreg]
 rw [all_later_numerators_vanish K coefficients F v hF (w+1) hdiv j (by omega)]
 simp
end PolynomialFamily
end ProximityPrize.SubmissionLower.RCN311
end PackedLegacy_CG

/-! Packed from ProximityPrize.SubmissionLower.EK. -/
section PackedLegacy_EK
namespace ProximityPrize.SubmissionLower.RCN135
open RCN077 RCN269 RCN233 RCN231 RCN229 RCN139 RCN313 RCN319
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable (K:Type*) [Field K]
abbrev RationalBase:=FractionRing (Polynomial K)
abbrev GenericField:=AlgebraicClosure (RationalBase K)
def polynomialEmbedding:Polynomial K →+*GenericField K:=
 (algebraMap (RationalBase K) (GenericField K)).comp
   (algebraMap (Polynomial K) (RationalBase K))
def coefficientEmbedding:K →+*GenericField K:=
 (polynomialEmbedding K).comp Polynomial.C
def initialCoordinate:GenericField K:=polynomialEmbedding K Polynomial.X
theorem polynomialEmbedding_injective:Function.Injective (polynomialEmbedding K):=
 (algebraMap (RationalBase K) (GenericField K)).injective.comp
   (IsFractionRing.injective (Polynomial K) (RationalBase K))
theorem coefficientEmbedding_injective:Function.Injective (coefficientEmbedding K):=
 (coefficientEmbedding K).injective
theorem genericField_charP (p:ℕ) [CharP K p]:CharP (GenericField K) p:=by
 infer_instance
theorem generic_eval_eq (P:Polynomial K):
   P.eval₂ (coefficientEmbedding K) (initialCoordinate K)=polynomialEmbedding K P:=by
 have hhom:Polynomial.eval₂RingHom (coefficientEmbedding K) (initialCoordinate K)=
     polynomialEmbedding K:=by
   apply Polynomial.ringHom_ext
   · intro a
     simp [coefficientEmbedding,RingHom.comp_apply]
   · simp [initialCoordinate]
 exact DFunLike.congr_fun hhom P
@[simp] theorem polynomialEmbedding_eq_zero_iff (P:Polynomial K):
   polynomialEmbedding K P=0 ↔ P=0:=by
 constructor
 · intro h
   apply polynomialEmbedding_injective K
   simpa only [map_zero] using h
 · rintro rfl
   exact map_zero _
def initialPoint (P:Polynomial K) (γ:K):Fin 4 → GenericField K:=
 polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)
@[simp] theorem initialPoint_X (P:Polynomial K) (γ:K):
   initialPoint K P γ 0=initialCoordinate K:=rfl
@[simp] theorem initialPoint_Z (P:Polynomial K) (γ:K):
   initialPoint K P γ 3=coefficientEmbedding K γ:=rfl
theorem evaluation_at_initialPoint (P:Polynomial K) (γ:K) (Q:Poly4 K):
   MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ) Q=
     polynomialEmbedding K (specialization K P γ Q):=by
 change MvPolynomial.eval₂Hom (coefficientEmbedding K)
     (polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)) Q=_
 rw [eval_polynomialPoint_eq_specialization,generic_eval_eq]
theorem initialPoint_regular_iff (F:Poly4 K) (P:Polynomial K) (γ:K):
   MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ)
       (MvPolynomial.pderiv (2:Fin 4) F)≠0 ↔
     specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0:=by
 simp only [evaluation_at_initialPoint,ne_eq,polynomialEmbedding_eq_zero_iff]
end
end ProximityPrize.SubmissionLower.RCN135
end PackedLegacy_EK

/-! Packed from ProximityPrize.SubmissionLower.EM. -/
section PackedLegacy_EM
namespace ProximityPrize.SubmissionLower.RCN138
open RCN136 RCN132 RCN313 RCN311 RCN174 RCN319 RCN135
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra (RationalCoefficients K) L]
def geometricPolynomialEmbedding:Polynomial K →+*L:=
 (algebraMap (RationalCoefficients K) L).comp
   (algebraMap (Polynomial K) (RationalCoefficients K))
def geometricSurfaceMap:MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 3) L:=
 (MvPolynomial.map (algebraMap (RationalCoefficients K) L)).comp (rationalSurfaceMap K)
theorem geometricSurfaceMap_eq_surfaceMap:
   geometricSurfaceMap K L=surfaceMap (geometricPolynomialEmbedding K L):=by
 apply RingHom.ext
 intro F
 change MvPolynomial.map (algebraMap (RationalCoefficients K) L)
     (MvPolynomial.map (algebraMap (Polynomial K) (RationalCoefficients K)) (collectX K F))=
   MvPolynomial.map ((algebraMap (RationalCoefficients K) L).comp
     (algebraMap (Polynomial K) (RationalCoefficients K))) (collectX K F)
 exact MvPolynomial.map_map _ _ _
theorem geometric_factor_dvd_iff
   (F M:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   g∣geometricSurfaceMap K L M ↔ F∣M:=by
 constructor
 · intro hdivM
   have hfrac:rationalSurfaceMap K F∣rationalSurfaceMap K M:=
     RCN350.original_dvd_of_geometric_factor_dvd
       (rationalSurfaceMap K F) (rationalSurfaceMap K M)
       (rationalSurfaceMap_irreducible K F hF hpos) g hg hdivF hdivM
   exact (rationalSurfaceMap_dvd_iff K F M hF hpos).mp hfrac
 · intro hdiv
   exact hdivF.trans (map_dvd (geometricSurfaceMap K L) hdiv)
section CanonicalGenericField
theorem canonical_geometricPolynomialEmbedding:
   geometricPolynomialEmbedding K (GenericField K)=polynomialEmbedding K:=rfl
theorem canonical_geometricSurfaceMap:
   geometricSurfaceMap K (GenericField K)=surfaceMap (polynomialEmbedding K):=by
 rw [geometricSurfaceMap_eq_surfaceMap,canonical_geometricPolynomialEmbedding]
theorem eval_at_actual_generic_initial_point
   (P:Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (fun i:Fin 3 => initialPoint K P γ i.succ)
     (geometricSurfaceMap K (GenericField K) F)=
     polynomialEmbedding K (specialization K P γ F):=by
 rw [canonical_geometricSurfaceMap,eval_surfaceMap]
 change MvPolynomial.eval₂Hom (coefficientEmbedding K)
     (Fin.cases (initialCoordinate K) (fun i:Fin 3 => initialPoint K P γ i.succ)) F=_
 have hv:Fin.cases (initialCoordinate K) (fun i:Fin 3 => initialPoint K P γ i.succ)=
     initialPoint K P γ:=by
   funext i
   refine Fin.cases ?_ (fun j => ?_) i <;> rfl
 rw [hv]
 exact evaluation_at_initialPoint K P γ F
theorem actual_generic_initial_zero_iff
   (P:Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (fun i:Fin 3 => initialPoint K P γ i.succ)
     (geometricSurfaceMap K (GenericField K) F)=0 ↔ specialization K P γ F=0:=by
 rw [eval_at_actual_generic_initial_point,polynomialEmbedding_eq_zero_iff]
end CanonicalGenericField
end
end ProximityPrize.SubmissionLower.RCN138
end PackedLegacy_EM

/-! Packed from ProximityPrize.SubmissionLower.EL. -/
section PackedLegacy_EL
namespace ProximityPrize.SubmissionLower.RCN137
open UniqueFactorizationMonoid RCN136 RCN082 RCN135 RCN138 RCN174 RCN319
noncomputable section
section ArbitraryVariables
variable {σ A:Type*} [Field A]
local instance _root_.ProximityPrize.SubmissionLower.RCN137.instStrongNormalizationMonoidMvPolynomial_proximityPrize :StrongNormalizationMonoid (MvPolynomial σ A):=
 UniqueFactorizationMonoid.strongNormalizationMonoid
def normalizedFactorSet (Q:MvPolynomial σ A):Finset (MvPolynomial σ A):=by
 classical
 exact (normalizedFactors Q).toFinset
theorem normalizedFactorSet_spec (Q F:MvPolynomial σ A)
   (hF:F∈normalizedFactorSet Q):Irreducible F∧F∣Q:=by
 classical
 have hm:F∈normalizedFactors Q:=Multiset.mem_toFinset.mp hF
 exact ⟨irreducible_of_normalized_factor F hm,dvd_of_mem_normalizedFactors hm⟩
theorem normalizedFactorSet_product_dvd (Q:MvPolynomial σ A) (hQ:Q≠0):
   (∏ F∈normalizedFactorSet Q,F)∣Q:=by
 classical
 exact (normalizedFactors Q).toFinset_prod_dvd_prod.trans (prod_normalizedFactors hQ).dvd
theorem coordinate_degree_le_of_dvd (i:σ) (F Q:MvPolynomial σ A)
   (hdiv:F∣Q) (hQ:Q≠0):F.degreeOf i ≤ Q.degreeOf i:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hF,hG⟩
 rw [MvPolynomial.degreeOf_mul_eq hF hG]
 exact Nat.le_add_right _ _
theorem sum_coordinate_degrees_le_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial σ A) (Q:MvPolynomial σ A)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q) (i:σ):
   (∑ j∈I,(f j).degreeOf i) ≤ Q.degreeOf i:=by
 classical
 have hprod:(∏ j∈I,f j)≠0:=by
   intro hz
   rcases hdiv with ⟨G,hG⟩
   apply hQ
   rw [hG,hz,zero_mul]
 have hf:∀ j∈I,f j≠0:=Finset.prod_ne_zero_iff.mp hprod
 calc
   (∑ j∈I,(f j).degreeOf i)=(∏ j∈I,f j).degreeOf i:=
     (MvPolynomial.degreeOf_prod_eq (n:=i) I f hf).symm
   _ ≤ Q.degreeOf i:=coordinate_degree_le_of_dvd i _ Q hdiv hQ
theorem normalizedFactorSet_degree_budget
   (Q:MvPolynomial σ A) (hQ:Q≠0) (i:σ):
   (∑ F∈normalizedFactorSet Q,F.degreeOf i) ≤ Q.degreeOf i:=
 sum_coordinate_degrees_le_of_prod_dvd (normalizedFactorSet Q) id Q hQ
   (normalizedFactorSet_product_dvd Q hQ) i
theorem exists_normalizedFactorSet_zero
   {B:Type*} [CommRing B] [IsDomain B]
   (ψ:MvPolynomial σ A →+*B) (Q:MvPolynomial σ A)
   (hQ:Q≠0) (hzero:ψ Q=0):
   ∃ F∈normalizedFactorSet Q,ψ F=0:=by
 classical
 have ha:=Associated.map ψ (prod_normalizedFactors hQ)
 rw [hzero] at ha
 have hp:ψ (normalizedFactors Q).prod=0:=(associated_zero_iff_eq_zero _).mp ha
 rw [map_multiset_prod] at hp
 obtain ⟨F,hm,hz⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
 exact ⟨F,Multiset.mem_toFinset.mpr hm,hz⟩
end ArbitraryVariables
section SurfaceFamilies
variable {K L:Type*} [Field K] [Field L]
def surfaceFactors (φ:Polynomial K →+*L) (F:MvPolynomial (Fin 4) K):
   Finset (MvPolynomial (Fin 3) L):=normalizedFactorSet (surfaceMap φ F)
theorem surfaceFactors_spec (φ:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K) (g:MvPolynomial (Fin 3) L)
   (hg:g∈surfaceFactors φ F):Irreducible g∧g∣surfaceMap φ F:=
 normalizedFactorSet_spec (surfaceMap φ F) g hg
theorem exists_surfaceFactor_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ F)=0):
   ∃ g∈surfaceFactors φ F,MvPolynomial.eval v g=0:=
 exists_normalizedFactorSet_zero (MvPolynomial.eval v) (surfaceMap φ F)
   (surfaceMap_ne_zero φ hφ F hF) hzero
theorem surfaceFactors_degree_budget
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (i:Fin 3):
   (∑ g∈surfaceFactors φ F,g.degreeOf i) ≤ F.degreeOf i.succ:=
 (normalizedFactorSet_degree_budget (surfaceMap φ F)
   (surfaceMap_ne_zero φ hφ F hF) i).trans (surfaceMap_degreeOf_le φ F i)
end SurfaceFamilies
section CanonicalPoints
variable (K:Type*) [Field K]
end CanonicalPoints
end
end ProximityPrize.SubmissionLower.RCN137
end PackedLegacy_EL
end Compact_PackedLegacyCore1


