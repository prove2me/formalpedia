-- Prove2me | Definitions.Def_Yukon_1af791eb6f6293537a7eba7b
-- name    : Yukon_1af791eb6f6293537a7eba7b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T22:03:32.366699+00:00
-- url     : https://prove2.me/theorems/d1945200-64e7-44e0-8ab0-ebd4aeb1d8b3
-- title:
--   LowerFoundation source part 2/5
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-compact-module-Yukon_1af791eb6f6293537a7eba7b
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMmNmMDM1ZGQ1ODViMTEwNmRmMDE0ZDUyYTdjN2E5MzA1MWE2NDE4YjZkYTNkMGU2YjY1NWNkZmExNzQ2YmIyMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tY29tcGFjdC1tb2R1bGUtWXVrb25fMWFmNzkxZWI2ZjYyOTM1MzdhN2ViYTdiIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMWFmNzkxZWI2ZjYyOTM1MzdhN2ViYTdiIiwidiI6Mn0]

import Definitions.Def_Yukon_74e50608097e19dffcbac46b
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


/-! Packed from ProximityPrize.SubmissionLower.M6. -/
section PackedLegacy_M6
namespace ProximityPrize.SubmissionLower.RCN202
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084 RCN095 RCN341 RCN037 RCN076
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" => MvPolynomial (Fin 3) K
local notation "PE" => MvPolynomial (Fin 3) E
def rationalVariable (K:Type) [Field K]:RatFunc K:=
 algebraMap (Polynomial K) (RatFunc K) Polynomial.X
theorem eliminated_not_mem_nonpoint
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (C:RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=
     movingValue C.1 H G Q U)
   (D:Ideal PE) [D.IsPrime]
   (hnonpoint:∀ v:Fin 3 → E,D≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hF:scalarPolynomialMap K E F∈D)
   (hN:movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (rationalVariable K))∈D)
   (hH:scalarPolynomialMap K E H∉D) (hU:scalarPolynomialMap K E U∉D)
   (hbelow:D.comap (scalarPolynomialMap K E) ≤ C.1):
   eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (rationalVariable K))∉D:=by
 intro hA
 let mu:=scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (rationalVariable K)
 let evD:=coordinateEvaluation E D
 let ev:=evD.toRingHom.comp mu
 have hTor:mu (filteredCut k B H G)∈D:=by
   rw [map_filteredCut]
   exact original_mem_of_eliminated_mem D k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hA hU
 have hcut:cutIdeal K F (filteredCut k B H G) ≤ D.comap mu:=by
   apply Ideal.span_le.mpr
   intro A hA
   rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hA) with rfl | rfl
   · exact hF
   · exact hTor
 have hmin:=(mem_componentFamily K F (filteredCut k B H G) C.1).mp
   (regularComponent_mem K _ _ _ C)
 have hcontract:D.comap mu=C.1:=
   le_antisymm hbelow (hmin.2 ⟨inferInstance,hcut⟩ hbelow)
 have hker:RingHom.ker ev=C.1:=by
   rw [show RingHom.ker ev=(RingHom.ker evD.toRingHom).comap mu from rfl,
     coordinateEvaluation_ker E D]
   exact hcontract
 let phi:=coordinateFieldMap C.1 ev hker
 have hphi (A:Poly):phi (coordinateEvaluation K C.1 A)=ev A:=
   coordinateFieldMap_eval _ _ _ A
 have hscalar (c:K):phi (algebraMap K (CoordinateField K C.1) c)=
     algebraMap E (CoordinateField E D) (algebraMap K E c):=by
   simpa [ev,mu,scalarPolynomialMap] using hphi (MvPolynomial.C c)
 have hHne:ev H≠0:=by
   intro hz
   have:mu H∈RingHom.ker evD.toRingHom:=hz
   rw [coordinateEvaluation_ker E D] at this
   exact hH this
 have hNzero:evD (movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   apply RingHom.mem_ker.mp
   change _∈RingHom.ker (coordinateEvaluation E D).toRingHom
   rwa [coordinateEvaluation_ker E D]
 have hrel:ev H*(algebraMap E (CoordinateField E D) t-ev Q)=ev U*ev G:=by
   have hconst:evD (MvPolynomial.C t)=algebraMap E (CoordinateField E D) t:=evD.commutes t
   apply sub_eq_zero.mp
   simpa only [movingEquation,map_sub,map_mul,hconst,
     ev,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hNzero
 have hjmap:phi (movingValue C.1 H G Q U)=algebraMap E (CoordinateField E D) t:=by
   unfold movingValue
   rw [map_add,map_div₀,map_mul,hphi Q,hphi U,hphi G,hphi H]
   have hd:ev U*ev G/ev H=algebraMap E (CoordinateField E D) t-ev Q:=by
     apply (div_eq_iff hHne).mpr
     simpa only [mul_comm] using hrel.symm
   rw [hd];ring
 have hdiag:(algebraMap E (CoordinateField E D)).comp (algebraMap (RatFunc K) E)=
     phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1)):=by
   apply IsFractionRing.ringHom_ext (A:=Polynomial K)
   intro p
   have hp:((algebraMap E (CoordinateField E D)).comp (algebraMap (RatFunc K) E)).comp
       (algebraMap (Polynomial K) (RatFunc K))=
       (phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1))).comp
         (algebraMap (Polynomial K) (RatFunc K)):=by
     apply Polynomial.ringHom_ext
     · intro c
       change algebraMap E (CoordinateField E D)
         (algebraMap (RatFunc K) E (algebraMap K (RatFunc K) c))=
         phi (algebraMap (RatFunc K) (CoordinateField K C.1) (algebraMap K (RatFunc K) c))
       rw [←IsScalarTower.algebraMap_apply K (RatFunc K) E,
         ←IsScalarTower.algebraMap_apply K (RatFunc K) (CoordinateField K C.1),hscalar]
     · change algebraMap E (CoordinateField E D) t=
         phi (algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K))
       rw [hj];exact hjmap.symm
   exact RingHom.congr_fun hp p
 have halg:∀ i,IsAlgebraic E (coordinate E D i):=by
   intro i
   have hint:=IsIntegral.map_of_comp_eq (algebraMap (RatFunc K) E) phi hdiag
     (IsIntegral.of_finite (RatFunc K) (coordinate K C.1 i))
   have hcoord:phi (coordinate K C.1 i)=coordinate E D i:=by
     simpa only [coordinate,ev,evD,RingHom.comp_apply,mu,scalarPolynomialMap,
       MvPolynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hphi (MvPolynomial.X i)
   rw [hcoord] at hint
   exact hint.isAlgebraic
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic E D halg
 exact hnonpoint v hv
theorem embedding_point_certificate
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (C:RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=
     movingValue C.1 H G Q U) (hU:U∉C.1)
   (f:CoordinateField K C.1 →ₐ[RatFunc K] E):
   let mu:=scalarPolynomialMap K E
   let t:=algebraMap (RatFunc K) E (rationalVariable K)
   let v:=embeddingPoint C.1 (f.restrictScalars K)
   let N:=movingEquation (mu H) (mu G) (mu Q) (mu U) t
   let A:=eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t
   MvPolynomial.eval v (mu F)=0∧MvPolynomial.eval v N=0∧
     MvPolynomial.aeval v A=0∧MvPolynomial.eval v (mu H*mu U)≠0∧
     IsolatedPoint (mu F) N A v:=by
 dsimp only
 let mu:=scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (rationalVariable K)
 let v:=embeddingPoint C.1 (f.restrictScalars K)
 let ev:=MvPolynomial.eval v
 have hev (A:Poly):ev (mu A)=f (coordinateEvaluation K C.1 A):=by
   have h:=AlgHom.congr_fun (embeddingPoint_aeval C.1 (f.restrictScalars K)) A
   change MvPolynomial.eval v (MvPolynomial.map (algebraMap K E) A)=_
   rw [MvPolynomial.eval_map]
   exact h
 have hz (A:Poly) (hA:A∈C.1):ev (mu A)=0:=by
   rw [hev]
   have ha:coordinateEvaluation K C.1 A=0:=by
     apply RingHom.mem_ker.mp
     change A∈RingHom.ker (coordinateEvaluation K C.1).toRingHom
     rwa [coordinateEvaluation_ker K C.1]
   rw [ha,map_zero]
 have hne (A:Poly) (hA:A∉C.1):ev (mu A)≠0:=by
   rw [hev]
   exact fun h↦hA (by
     rw [←coordinateEvaluation_ker K C.1]
     exact (map_eq_zero_iff f f.injective).mp h)
 have hHne:=hne H (regularComponent_H_not_mem K _ _ _ C)
 have hUne:=hne U hU
 have hjval:ev (mu Q)+ev (mu U)*ev (mu G)/ev (mu H)=t:=by
   simp only [hev]
   have h:=f.commutes (rationalVariable K)
   rw [hj] at h
   simpa only [movingValue,map_add,map_div₀,map_mul] using h
 have hN:ev (movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   have hevC:ev (MvPolynomial.C t)=t:=by simp [ev]
   simp only [movingEquation,map_sub,map_mul,hevC]
   have h:=(div_eq_iff hHne).mp (show ev (mu U)*ev (mu G)/ev (mu H)=t-ev (mu Q) by
     linear_combination hjval)
   linear_combination-h
 have hA:ev (eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t)=0:=by
   apply (eliminatedCut_zero_iff ev k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hHne hUne).mpr
   rw [←map_filteredCut]
   exact hz _ (regularComponent_T_mem K _ _ _ C)
 refine ⟨hz F (regularComponent_G_mem K _ _ _ C),hN,hA,?_,?_⟩
 · simpa only [map_mul] using mul_ne_zero hHne hUne
 · intro D hD hn hp hDF hDN
   letI:=hD
   apply eliminated_not_mem_nonpoint F H G Q U k B C hj D hn hDF hDN
   · exact fun h↦hHne (hp h)
   · exact fun h↦hUne (hp h)
   · exact comap_le_of_embedding_point C.1 (f.restrictScalars K) D hp
abbrev fiberEquation (H G Q U:Poly):PE:=
 movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
   (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
   (algebraMap (RatFunc K) E (rationalVariable K))
abbrev fiberCut (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly):PE:=
 eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
   (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
   (algebraMap (RatFunc K) E (rationalVariable K))
theorem sum_moving_degrees_le
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1)]
   (hj:∀ C:RegularComponent K F (filteredCut k B H G) H,
     algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=movingValue C.1 H G Q U)
   (hU:∀ C:RegularComponent K F (filteredCut k B H G) H,U∉C.1)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (p q r:FlagDegree) (hFp:PolynomialInFlag p F)
   (hNq:PolynomialInFlag q (fiberEquation (E:=E) H G Q U))
   (hAr:PolynomialInFlag r (fiberCut (E:=E) k B Q U))
   (c:ℕ) [CharP E c] (hdeg:p.zOnly+p.yz+p.all < c)
   (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c):
   (∑ C:RegularComponent K F (filteredCut k B H G) H,
     Module.finrank (RatFunc K) (CoordinateField K C.1)) ≤ flagMixed p q r:=by
 classical
 let mu:=scalarPolynomialMap K E
 let N:=fiberEquation (E:=E) H G Q U
 let A:=fiberCut (E:=E) k B Q U
 let R:=mu H*mu U
 let P:=fun C:RegularComponent K F (filteredCut k B H G) H↦C.1
 let points:=genericFiberPoints (B:=RatFunc K) (L:=E) P
 have hc:∀ v∈points,MvPolynomial.eval v (mu F)=0∧MvPolynomial.eval v N=0∧
     MvPolynomial.aeval v A=0∧MvPolynomial.eval v R≠0∧IsolatedPoint (mu F) N A v:=by
   intro v hv
   obtain ⟨⟨C,f⟩,_,rfl⟩:=Finset.mem_image.mp hv
   exact embedding_point_certificate F H G Q U k B C (hj C) (hU C) f
 have hinj:Function.Injective mu:=
   MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective
 have hMF:mu F≠0:=fun h↦hF (hinj (h.trans (map_zero mu).symm))
 have hMFp:=inFlag_map (algebraMap K E) hFp
 obtain ⟨base,hY,hZ⟩:=exists_small_projection_data (mu F) N R hMF p q hMFp hNq c hdeg hmix
 rw [←genericFiberPoints_card (B:=RatFunc K) (L:=E) P Subtype.val_injective]
 apply isolated_points_card_le (mu F) N A R p q r hMF
   hMFp hNq hAr base hY hZ points
 · intro v hv
   have hv:=hc v hv
   apply exists_active_factor_of_isolated (mu F) N A R hMF v hv.1 hv.2.2.1 hv.2.2.2.1
   · have hH:MvPolynomial.eval v (mu H)≠0:=
       (mul_ne_zero_iff.mp (by simpa only [R,map_mul] using hv.2.2.2.1)).1
     exact map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval v) (mu F) (mu H)
       (scalar_derivative_span F H hderiv) hv.1 hH
   · exact hv.2.2.2.2
 · exact fun v hv↦(hc v hv).2.1
 · exact fun v hv↦(hc v hv).2.2.1
 · exact fun v hv↦(hc v hv).2.2.2.1
 · intro g C v hv hp
   have hCF:=C.1.mem_of_dvd (activeFactors_spec (mu F) N g).2.1
     (regularComponent_G_mem E g.1 N R C)
   exact (hc v hv).2.2.2.2 C.1 inferInstance (regularComponent_ne_point E g.1 N R C)
     hp hCF (regularComponent_T_mem E g.1 N R C)
theorem fiber_small_flags (a b s k:ℕ) (C:FlagDegree)
   (H G Q U:Poly) (B:Fin (k+1) → Poly) (c:Fin (k+1) → FlagDegree)
   (hH:PolynomialInFlag ⟨a,b+1,s+1⟩ H) (hG:PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q) (hU:PolynomialInFlag unitYZFlag U)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   PolynomialInFlag ⟨a,b+1,s+3⟩ (fiberEquation (E:=E) H G Q U)∧
   PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (fiberCut (E:=E) k B Q U):=by
 constructor
 · exact movingEquation_inFlag a b s _ _ _ _ _
     (inFlag_map (algebraMap K E) hH) (inFlag_map (algebraMap K E) hG)
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU)
 · exact eliminatedCut_small_flag a b s k C _ _ _ _ c
     (fun j↦inFlag_map (algebraMap K E) (hB j))
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU) hc
end
end ProximityPrize.SubmissionLower.RCN202
end PackedLegacy_M6
end Compact_PackedLegacy


