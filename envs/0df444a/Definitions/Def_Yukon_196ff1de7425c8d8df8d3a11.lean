-- Prove2me | Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
-- name    : Yukon_196ff1de7425c8d8df8d3a11
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T19:23:10.730025+00:00
-- url     : https://prove2.me/theorems/f024009e-6c6e-4c50-ba78-9d670ba9f12c
-- title:
--   LowerFoundation source part 4/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-small-split-Yukon_196ff1de7425c8d8df8d3a11
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYWM4NWM0ZDYwMjc4YWUzNjBhZGI2NWJmN2E4ODk5MWUyMzliMjYzNDYzZDAxMzExNGZjMTJmM2E5NzZmNWRjNSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tc21hbGwtc3BsaXQtWXVrb25fMTk2ZmYxZGU3NDI1YzhkOGRmOGQzYTExIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMTk2ZmYxZGU3NDI1YzhkOGRmOGQzYTExIiwidiI6Mn0]

import Definitions.Def_Yukon_cc09659938447005331d9581
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


/-! Packed from ProximityPrize.SubmissionLower.DW. -/
section PackedLegacy_DW
namespace ProximityPrize.SubmissionLower.RCN052
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN052.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev RegularIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(positiveRFactors Q)
abbrev ImplicitIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(implicitPairSet (singularAuxiliary Q))
def regularPairSeeds (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RegularIndex Q):Finset K:=
 Gamma.filter fun gamma↦
   RegularSolution F.1 (selected gamma) gamma∧
     specialization K (selected gamma) gamma T=0
def implicitSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):Finset K:=
 Gamma.filter fun gamma↦LiftedSolutionPair q.1 (selected gamma) gamma
def singularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K):Finset K:=
 Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
   exceptionalSeeds (singularAuxiliary Q) Gamma selected
theorem regularPairSeeds_subset (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (F:RegularIndex Q):
   regularPairSeeds Q T selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
theorem regularPairSeeds_data (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (F:RegularIndex Q)
   (gamma:K) (hgamma:gamma∈regularPairSeeds Q T selected Gamma F):
   RegularSolution F.1 (selected gamma) gamma∧
     specialization K (selected gamma) gamma T=0:=
 (Finset.mem_filter.mp hgamma).2
theorem card_le_regular_sum_add_singular
   (Q T:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p]
   (hs:1 ≤ s) (hsmall:s < p) (hw:1 ≤ w)
   (hDw:w < (2*s-1)*D)
   (hj:1 ≤ (2*s-1)*L) (hjSmall:(2*s-1)*L < p)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hQsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hTsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma T=0):
   Gamma.card ≤
     (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ D w L s p hs hsmall hw
   hDw hj hjSmall hbox Gamma selected hQsolution
 let regularUnion:=Finset.univ.biUnion (regularPairSeeds Q T selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   by_cases hexc:gamma∈exceptionalSeeds (singularAuxiliary Q) Gamma selected
   · exact Finset.mem_union_right _ (Finset.mem_union_right _ hexc)
   · obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩:=hdecomp.2.1 gamma hgamma hexc
     · apply Finset.mem_union_left
       exact Finset.mem_biUnion.mpr ⟨⟨F,hF⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,hreg,hTsolution gamma hgamma⟩⟩
     · apply Finset.mem_union_right
       apply Finset.mem_union_left
       exact Finset.mem_biUnion.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RegularIndex Q,
         (regularPairSeeds Q T selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
theorem regularFactor_not_dvd_second
   (Q T:MvPolynomial (Fin 4) K) (hrel:IsRelPrime Q T)
   (F:RegularIndex Q):¬ F.1∣T:=by
 obtain ⟨hirr,hdiv,_⟩:=positiveRFactors_spec Q F.1 F.2
 intro hFT
 exact hirr.not_isUnit (hrel hdiv hFT)
theorem geometricFactor_not_dvd_second
   (Q T:MvPolynomial (Fin 4) K) (hrel:IsRelPrime Q T)
   (F:RegularIndex Q)
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hg:g∈surfaceFactors (polynomialEmbedding K) F.1):
   ¬ g∣surfaceMap (polynomialEmbedding K) T:=by
 obtain ⟨hFirr,_hFdiv,hFRpos⟩:=positiveRFactors_spec Q F.1 F.2
 obtain ⟨hgirred,hgdiv⟩:=
   surfaceFactors_spec (polynomialEmbedding K) F.1 g hg
 have hpos:0 < F.1.degreeOf 1+F.1.degreeOf 2+F.1.degreeOf 3:=by
   omega
 have hgeo:g∣geometricSurfaceMap K (GenericField K) F.1:=by
   simpa only [canonical_geometricSurfaceMap] using hgdiv
 intro hgT
 apply regularFactor_not_dvd_second Q T hrel F
 apply (geometric_factor_dvd_iff K (GenericField K) F.1 T hFirr hpos
   g hgirred hgeo).mp
 simpa only [canonical_geometricSurfaceMap] using hgT
def regularVector (P:UnequalParameters)
   (F:MvPolynomial (Fin 4) K):RCN223.DegreeVector:=
 ⟨F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR,
   F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY,
   F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY⟩
def regularCapAt (v:RCN223.DegreeVector):Fin 3 → ℕ:=
 ![v.y,v.r,v.z]
theorem sum_coordinateMixedDegree_geometricFactors_le
   (P:UnequalParameters) (F T:MvPolynomial (Fin 4) K) (hF:F≠0)
   (hTY:T.degreeOf 1 ≤ P.rightY) (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ) (i:Fin 3):
   (∑ g:GeometricFactor K F,
     coordinateMixedDegree (GenericField K) g.1
       (surfaceMap (polynomialEmbedding K) T) i) ≤
     regularCapAt (regularVector P F) i:=by
 classical
 have hsum (j:Fin 3):
     (∑ g:GeometricFactor K F,g.1.degreeOf j) ≤ F.degreeOf j.succ:=
   geometricFactor_sum_degree_le K F hF j
 have hsum0:(∑ g:GeometricFactor K F,g.1.degreeOf 0) ≤ F.degreeOf 1:=by
   simpa using hsum 0
 have hsum1:(∑ g:GeometricFactor K F,g.1.degreeOf 1) ≤ F.degreeOf 2:=by
   simpa using hsum 1
 have hsum2:(∑ g:GeometricFactor K F,g.1.degreeOf 2) ≤ F.degreeOf 3:=by
   have h:=hsum 2
   rw [show (2:Fin 3).succ=(3:Fin 4) by decide] at h
   exact h
 have hT0:(surfaceMap (polynomialEmbedding K) T).degreeOf 0 ≤ P.rightY:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 0).trans hTY
 have hT1:(surfaceMap (polynomialEmbedding K) T).degreeOf 1 ≤ P.rightR:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 1).trans hTR
 have hT2:(surfaceMap (polynomialEmbedding K) T).degreeOf 2 ≤ P.rightZ:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 2).trans hTZ
 have hi:i=0∨i=1∨i=2:=by omega
 rcases hi with rfl | rfl | rfl
 · change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 1*geom.1.degreeOf 2+
         geom.1.degreeOf 1*(surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
       F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT1 hsum2)
       (Nat.mul_le_mul hsum1 hT2)
 · change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 2+
         geom.1.degreeOf 0*(surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
       F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum2)
       (Nat.mul_le_mul hsum0 hT2)
 · simp only [RCN001.coordinateMixedDegree_two,
     regularCapAt,regularVector,Matrix.cons_val_two]
   change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 1+
         geom.1.degreeOf 0*(surfaceMap (polynomialEmbedding K) T).degreeOf 1)) ≤
       F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum1)
       (Nat.mul_le_mul hsum0 hT1)
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN052.instDecidableEq_proximityPrize_1 :DecidableEq ι:=Classical.decEq ι
theorem regularPairSeeds_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hrel:IsRelPrime Q T) (F:RegularIndex Q)
   (p:ℕ) [CharP K p]
   (hFY:F.1.degreeOf 1 ≤ P.leftY)
   (hFR:F.1.degreeOf 2 ≤ P.leftR)
   (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
     (P.n-P.w)*dot P.agreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 classical
 let phi:=polynomialEmbedding K
 let Delta:=regularPairSeeds Q T selected Gamma F
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFspec:=positiveRFactors_spec Q F.1 F.2
 have hFne:F.1≠0:=hFspec.1.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=regularPairSeeds_subset Q T selected Gamma F
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RegularSolution F.1 (selected gamma) gamma∧
       specialization K (selected gamma) gamma T=0:=
   regularPairSeeds_data Q T selected Gamma F gamma hgamma
 have hcover:=card_le_sum_geometricSeeds K F.1 hFne selected Delta
   (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=genericField_charP K p
 have hsingle (g:GeometricFactor K F.1):
     (geometricSeeds K F.1 selected Delta g).card*P.gap ≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.agreement i*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=surfaceFactors_spec phi F.1 g.1 g.2
   have hsub:=geometricSeeds_subset K F.1 selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=geometricFactor_degree_le K F.1 hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (surfaceMap_degreeOf_le phi T 0).trans hTY
     · exact (surfaceMap_degreeOf_le phi T 1).trans hTR
     · exact (surfaceMap_degreeOf_le phi T 2).trans hTZ
   have hcarrierSmall:∀ i,capAt carrierCap i < p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=actual_characteristic_gates g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F.1)≠0:=by
     intro gamma hgamma
     exact selectedPoint_regular_of_specialization K F.1 selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [selectedPoint_surface_evaluation,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀ j,
       (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
         regularCapAt P.agreement j:=by
     have h:=surface_agreement_caps phi F.1 P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j => (j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
           capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [agreementPolynomial] using h j
     fin_cases j
     · apply hj.trans
       change P.leftAgreement.y ≤ max P.leftAgreement.y P.rightAgreement.y
       exact le_max_left _ _
     · apply hj.trans
       change P.leftAgreement.r ≤ max P.leftAgreement.r P.rightAgreement.r
       exact le_max_left _ _
     · apply hj.trans
       change P.leftAgreement.z ≤ max P.leftAgreement.z P.rightAgreement.z
       exact le_max_left _ _
   have hcount:=proper_cut_seed_bound phi F.1 g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (geometricFactor_not_dvd_second Q T hrel F g.1 g.2)
     selected (geometricSeeds K F.1 selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma => hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma => (hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma => (Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma => hagreement gamma (hDeltaSub (hsub hgamma)))
     (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
       (fun _ hgamma => hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.agreement) (fun node _ => hcap node)
   simpa [hnodes,UnequalParameters.gap] using hcount
 have hbudget (i:Fin 3):=
   sum_coordinateMixedDegree_geometricFactors_le P F.1 T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:GeometricFactor K F.1,∑ i:Fin 3,
         regularCapAt P.agreement i*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.agreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap ≤
       (∑ g:GeometricFactor K F.1,
         (geometricSeeds K F.1 selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:GeometricFactor K F.1,
       (geometricSeeds K F.1 selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F.1,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.agreement i*
         coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _ => hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.agreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.agreement i*regularCapAt (regularVector P F.1) i)+
       (P.errors+1)*P.gap*regularCapAt (regularVector P F.1) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.agreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]
theorem all_regularPairSeeds_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hrel:IsRelPrime Q T)
   (D w L s p:ℕ) [CharP K p]
   (hbox:Q∈globalCoefficientBox K D w L s) (hwBox:1 ≤ w)
   (hY:(D-1)/w ≤ P.leftY)
   (hR:s ≤ P.leftR) (hZ:L ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   ∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 intro F
 have hFbox:=(directFactor_data Q F.1 hQ D w L s hbox F.2).2.2
 have hFcaps:=degree_bounds_of_mem_box F.1 D w L s hwBox hFbox
 exact regularPairSeeds_bound P Q T hrel F p
   (hFcaps.1.trans (by simpa using hY))
   (hFcaps.2.1.trans hR) (hFcaps.2.2.trans hZ)
   hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall
   hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u₀ u₁
   hinj hnodes hw hchar hwa han hdegree hagreement hnoPencil
theorem regularVector_budgets
   (P:UnequalParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (hY:(D-1)/w ≤ P.leftY)
   (hR:s ≤ P.leftR) (hZ:L ≤ P.leftZ):
   (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z:=by
 classical
 have hb:=directFactor_input_budgets Q hQ D w L s hw hbox
 have hbY:(∑ F:RegularIndex Q,F.1.degreeOf (1:Fin 4)) ≤ (D-1)/w:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.1
 have hbR:(∑ F:RegularIndex Q,F.1.degreeOf (2:Fin 4)) ≤ s:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.2.1
 have hbZ:(∑ F:RegularIndex Q,F.1.degreeOf (3:Fin 4)) ≤ L:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.2.2
 simp only [regularVector,Finset.sum_add_distrib]
 constructor
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightZ (hbR.trans hR))
     (Nat.mul_le_mul_right P.rightR (hbZ.trans hZ))
 constructor
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightZ (hbY.trans hY))
     (Nat.mul_le_mul_right P.rightY (hbZ.trans hZ))
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightR (hbY.trans hY))
     (Nat.mul_le_mul_right P.rightY (hbR.trans hR))
theorem dot_sum_right {I:Type} [Fintype I]
   (v:I → RCN223.DegreeVector)
   (a:RCN223.DegreeVector):
   dot a (RCN294.sumVector v)=∑ i,dot a (v i):=by
 calc
   _=dot (RCN294.sumVector v) a:=by
     simp only [dot]
     ring
   _=∑ i,dot (v i) a:=
     RCN294.dot_sum_left v a
   _=_:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [dot]
     ring
theorem sum_regular_counts_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hcost:
     (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z)
   (hcount:∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):
   (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)*
       P.gap ≤ P.regularNumerator:=by
 calc
   _=∑ F:RegularIndex Q,
       (regularPairSeeds Q T selected Gamma F).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F:RegularIndex Q,
       ((P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):=
     Finset.sum_le_sum fun F _↦hcount F
   _=(P.n-P.w)*dot P.agreement
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1)+
       (P.errors+1)*P.gap*
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1).z:=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,
       ←dot_sum_right]
     simp only [RCN294.sumVector]
   _ ≤ (P.n-P.w)*dot P.agreement P.mixedCost+
       (P.errors+1)*P.gap*P.mixedCost.z:=by
     apply Nat.add_le_add
     · exact Nat.mul_le_mul_left _ (Nat.add_le_add
         (Nat.add_le_add
           (Nat.mul_le_mul_left P.agreement.y hcost.1)
           (Nat.mul_le_mul_left P.agreement.r hcost.2.1))
         (Nat.mul_le_mul_left P.agreement.z hcost.2.2))
     · exact Nat.mul_le_mul_left _ hcost.2.2
   _=P.regularNumerator:=rfl
end
end ProximityPrize.SubmissionLower.RCN052
end PackedLegacy_DW

/-! Packed from ProximityPrize.SubmissionLower.BP. -/
section PackedLegacy_BP
namespace ProximityPrize.SubmissionLower.RCN157
open RCN136 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
end
end ProximityPrize.SubmissionLower.RCN157
end PackedLegacy_BP

/-! Packed from ProximityPrize.SubmissionLower.AA. -/
section PackedLegacy_AA
namespace ProximityPrize.SubmissionLower.RCN234
open scoped BigOperators
open RCN081 RCN167 RCN313
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def wt (weights:Fin 4 → ℕ) (P:Poly4 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights P
theorem wt_mul_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P*Q) ≤ wt weights P+wt weights Q:=
 weighted_mul_le weights P Q
theorem wt_add_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P+Q) ≤ max (wt weights P) (wt weights Q):=
 weighted_add_le weights P Q
theorem wt_sub_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P-Q) ≤ max (wt weights P) (wt weights Q):=by
 unfold wt
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (4:Fin 5)
     (weightedLift K weights P) (weightedLift K weights Q)
theorem wt_neg (weights:Fin 4 → ℕ) (P:Poly4 K):
   wt weights (-P)=wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_neg,MvPolynomial.degreeOf_neg,
   degree_weightedLift]
theorem wt_pow_le (weights:Fin 4 → ℕ) (P:Poly4 K) (n:ℕ):
   wt weights (P^n) ≤ n*wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (4:Fin 5) (weightedLift K weights P) n
theorem wt_C (weights:Fin 4 → ℕ) (c:K):
   wt weights (MvPolynomial.C c:Poly4 K)=0:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp
theorem wt_X (weights:Fin 4 → ℕ) (i:Fin 4):
   wt weights (MvPolynomial.X i:Poly4 K)=weights i:=by
 unfold wt
 exact weighted_X weights i
theorem wt_natCast (weights:Fin 4 → ℕ) (n:ℕ):
   wt weights (n:Poly4 K)=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K),wt_C]
theorem wt_sum_le (weights:Fin 4 → ℕ) (I:Finset ℕ)
   (f:ℕ → Poly4 K) (a:ℕ) (hf:∀ i∈I,wt weights (f i) ≤ a):
   wt weights (∑ i∈I,f i) ≤ a:=by
 unfold wt
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem wt_pderiv_le (weights:Fin 4 → ℕ) (P:Poly4 K)
   (i:Fin 4) (A:ℕ) (hP:wt weights P ≤ A):
   wt weights (MvPolynomial.pderiv i P) ≤ A-weights i:=
 pderiv_weight_sub_bound weights P i A hP
theorem wt_polyH_le (weights:Fin 4 → ℕ) (F:Poly4 K)
   (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyH K F) ≤ C-weights 2:=
 wt_pderiv_le weights F 2 C hF
theorem wt_polyG_le (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyG K F) ≤ C+weights 2:=by
 have hx:=wt_pderiv_le weights F 0 C hF
 have hy:=wt_pderiv_le weights F 1 C hF
 have hR:wt weights (MvPolynomial.X (2:Fin 4):Poly4 K)=weights 2:=
   weighted_X weights 2
 have hm:=wt_mul_le weights (MvPolynomial.X (2:Fin 4):Poly4 K)
   (MvPolynomial.pderiv 1 F)
 have hsum:=wt_add_le weights (MvPolynomial.pderiv 0 F)
   (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)
 unfold polyG
 rw [wt_neg]
 exact hsum.trans (max_le (by omega) (by omega))
theorem shiftedX_wt_eq_zero (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (x:K):
   wt weights (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)=0:=by
 apply Nat.eq_zero_of_le_zero
 apply (wt_sub_le weights _ _).trans
 rw [wt_C,wt_X,hX]
 simp
theorem affineSeedPolynomial_wt_le (weights:Fin 4 → ℕ) (u₀ u₁:K):
   wt weights (affineSeedPolynomial u₀ u₁) ≤ weights 3:=by
 unfold affineSeedPolynomial
 apply (wt_add_le weights _ _).trans
 apply max_le
 · rw [wt_C]
   exact Nat.zero_le _
 · have hm:=wt_mul_le weights (MvPolynomial.X (3:Fin 4):Poly4 K)
     (MvPolynomial.C u₁)
   rw [wt_X,wt_C,Nat.add_zero] at hm
   exact hm
end
end ProximityPrize.SubmissionLower.RCN234
end PackedLegacy_AA

/-! Packed from ProximityPrize.SubmissionLower.FO. -/
section PackedLegacy_FO
namespace ProximityPrize.SubmissionLower.RCN235
open scoped BigOperators Matrix
open ProximityPrize.SubmissionLower.RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←RCN081.degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => RCN081.weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [RCN081.degree_weightedLift]
 exact hf i hi
end
end ProximityPrize.SubmissionLower.RCN235
end PackedLegacy_FO

/-! Packed from ProximityPrize.SubmissionLower.AH. -/
section PackedLegacy_AH
namespace ProximityPrize.SubmissionLower.RCN295
open scoped Classical BigOperators WithZero
open RCN187
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
local instance _root_.ProximityPrize.SubmissionLower.RCN295.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
def exponentPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*poleOrder v (x i)
def exponentValuationWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*(v (x i)).log
def ExponentSetDownwardClosed (E:Finset (σ →₀ ℕ)):Prop:=
 ∀ d∈E,∀ e:σ →₀ ℕ,e ≤ d → e∈E
def exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):ℤ:=
 (insert (0:ℤ) (E.image (exponentPoleWeight v x))).max'
   ⟨0,Finset.mem_insert_self (0:ℤ) _⟩
def supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):ℤ:=
 exponentSetPoleWeight v x F.support
theorem supportPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):
   0 ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem exponentPoleWeight_le_supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support):
   exponentPoleWeight v x d ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
theorem exponentSetPoleWeight_mono
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) {E D:Finset (σ →₀ ℕ)} (hED:E ⊆ D):
   exponentSetPoleWeight v x E ≤ exponentSetPoleWeight v x D:=by
 unfold exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   apply Finset.le_max'
   exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hED hd,rfl⟩)
theorem supportPoleWeight_le_exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K) (E:Finset (σ →₀ ℕ))
   (hFE:F.support ⊆ E):
   supportPoleWeight v x F ≤ exponentSetPoleWeight v x E:=
 exponentSetPoleWeight_mono v x hFE
theorem valuation_monomial_le_exp_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support) (c:K):
   v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
     WithZero.exp (supportPoleWeight v x F):=by
 classical
 apply WithZero.le_exp_of_log_le
 calc
   (v (MvPolynomial.eval₂Hom coeff x
       (MvPolynomial.monomial d c))).log ≤
       poleOrder v (MvPolynomial.eval₂Hom coeff x
         (MvPolynomial.monomial d c)):=
     le_max_right _ _
   _ ≤ exponentPoleWeight v x d:=by
     by_cases hc:c=0
     · subst c
       simp [exponentPoleWeight,poleOrder]
       positivity
     · have hmono:=poleOrder_eval_le_box v coeff hcoeff x
         (fun i↦d i) (MvPolynomial.monomial d c) (fun i↦by
           rw [MvPolynomial.degreeOf_monomial_eq d i hc])
       simpa only [exponentPoleWeight] using hmono
   _ ≤ supportPoleWeight v x F:=
     exponentPoleWeight_le_supportPoleWeight v x F d hd
theorem valuation_eval_le_exp_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     WithZero.exp (supportPoleWeight v x F):=by
 classical
 conv_lhs => rw [MvPolynomial.as_sum F,map_sum]
 apply v.map_sum_le
 intro d hd
 exact valuation_monomial_le_exp_support v coeff hcoeff x F d hd
   (F.coeff d)
theorem valuation_eval_le_exp_exponentSet
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (F:MvPolynomial σ K)
   (hFE:F.support ⊆ E):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     WithZero.exp (exponentSetPoleWeight v x E):=by
 exact (valuation_eval_le_exp_support v coeff hcoeff x F).trans
   ((WithZero.exp_le_exp).2
     (supportPoleWeight_le_exponentSetPoleWeight v x F E hFE))
theorem poleOrder_eval_le_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K):
   poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
     supportPoleWeight v x F:=by
 classical
 have heval:=valuation_eval_le_exp_support v coeff hcoeff x F
 have hone:(1:WithZero (Multiplicative ℤ)) ≤
     WithZero.exp (supportPoleWeight v x F):=by
   rw [←WithZero.exp_zero,WithZero.exp_le_exp]
   exact supportPoleWeight_nonneg v x F
 have hmax:max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
     WithZero.exp (supportPoleWeight v x F):=max_le hone heval
 have hleft0:max 1 (v (MvPolynomial.eval₂Hom coeff x F))≠0:=
   ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
 have hlog:=(WithZero.log_le_log hleft0 WithZero.exp_ne_zero).2 hmax
 rw [log_max_one,WithZero.log_exp] at hlog
 simpa only [poleOrder] using hlog
theorem weighted_poleOrder_eval_le_exponentSet
   {τ:Type*} (S:Finset τ) (weight:τ → ℕ)
   (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L)
   (hcoeff:∀ t∈S,∀ c:K,v t (coeff c) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (F:MvPolynomial σ K)
   (hFE:F.support ⊆ E):
   (∑ t∈S,(weight t:ℤ)*
     poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∑ t∈S,(weight t:ℤ)*exponentSetPoleWeight (v t) x E:=by
 classical
 apply Finset.sum_le_sum
 intro t ht
 apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
 exact (poleOrder_eval_le_support (v t) coeff (hcoeff t ht) x F).trans
   (supportPoleWeight_le_exponentSetPoleWeight (v t) x F E hFE)
end
end ProximityPrize.SubmissionLower.RCN295
end PackedLegacy_AH

/-! Packed from ProximityPrize.SubmissionLower.D. -/
section PackedLegacy_D
namespace ProximityPrize.SubmissionLower.RCN095
open scoped BigOperators
open ProximityPrize.SubmissionLower.RCN295
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
structure FlagDegree where
 zOnly:ℕ
 yz:ℕ
 all:ℕ
 deriving DecidableEq,Repr
instance _root_.ProximityPrize.SubmissionLower.RCN095.instAddFlagDegree :Add FlagDegree:=⟨fun p q↦
 ⟨p.zOnly+q.zOnly,p.yz+q.yz,p.all+q.all⟩⟩
instance _root_.ProximityPrize.SubmissionLower.RCN095.instSMulNatFlagDegree :SMul ℕ FlagDegree:=⟨fun n p↦
 ⟨n*p.zOnly,n*p.yz,n*p.all⟩⟩
@[simp] theorem add_zOnly (p q:FlagDegree):
   (p+q).zOnly=p.zOnly+q.zOnly:=rfl
@[simp] theorem add_yz (p q:FlagDegree):
   (p+q).yz=p.yz+q.yz:=rfl
@[simp] theorem add_all (p q:FlagDegree):
   (p+q).all=p.all+q.all:=rfl
@[simp] theorem nsmul_zOnly (n:ℕ) (p:FlagDegree):
   (n • p).zOnly=n*p.zOnly:=rfl
@[simp] theorem nsmul_yz (n:ℕ) (p:FlagDegree):
   (n • p).yz=n*p.yz:=rfl
@[simp] theorem nsmul_all (n:ℕ) (p:FlagDegree):
   (n • p).all=n*p.all:=rfl
def InFlag (p:FlagDegree) (d:Fin 3 →₀ ℕ):Prop:=
 d 1 ≤ p.all∧
   d 0+d 1 ≤ p.yz+p.all∧
   d 0+d 1+d 2 ≤ p.zOnly+p.yz+p.all
theorem inFlag_zero (p:FlagDegree):InFlag p 0:=by
 simp [InFlag]
theorem inFlag_add {p q:FlagDegree} {d e:Fin 3 →₀ ℕ}
   (hd:InFlag p d) (he:InFlag q e):InFlag (p+q) (d+e):=by
 rcases hd with ⟨hdS,hdYS,hdTot⟩
 rcases he with ⟨heS,heYS,heTot⟩
 simp only [InFlag,Finsupp.add_apply,add_zOnly,add_yz,add_all]
 omega
noncomputable def exponentOfTriple (t:ℕ × ℕ × ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 t.1+Finsupp.single 1 t.2.1+
   Finsupp.single 2 t.2.2
noncomputable def flagSupport (p:FlagDegree):Finset (Fin 3 →₀ ℕ):=
 by
   classical
   exact (((((Finset.range (p.zOnly+p.yz+p.all+1)).product
       (Finset.range (p.all+1))).product
       (Finset.range (p.zOnly+p.yz+p.all+1))).image
         (fun t↦exponentOfTriple (t.1.1,t.1.2,t.2))).filter (InFlag p))
theorem mem_flagSupport_iff (p:FlagDegree) (d:Fin 3 →₀ ℕ):
   d∈flagSupport p ↔ InFlag p d:=by
 classical
 constructor
 · intro hd
   unfold flagSupport at hd
   exact (Finset.mem_filter.mp hd).2
 · intro hd
   unfold flagSupport
   rw [Finset.mem_filter]
   refine ⟨?_,hd⟩
   apply Finset.mem_image.mpr
   rcases hd with ⟨hS,hYS,htotal⟩
   refine ⟨((d 0,d 1),d 2),?_,?_⟩
   · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
       ⟨Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega),
         Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩,
       Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩
   · ext i
     fin_cases i <;> simp [exponentOfTriple]
theorem zero_mem_flagSupport (p:FlagDegree):
   (0:Fin 3 →₀ ℕ)∈flagSupport p:=by
 rw [mem_flagSupport_iff]
 exact inFlag_zero p
theorem flagSupport_downwardClosed (p:FlagDegree):
   ExponentSetDownwardClosed (flagSupport p):=by
 intro d hd e he
 rw [mem_flagSupport_iff] at hd ⊢
 rcases hd with ⟨hdS,hdYS,hdtotal⟩
 have h0:=he 0
 have h1:=he 1
 have h2:=he 2
 exact ⟨h1.trans hdS,by omega,by omega⟩
def PolynomialInFlag {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):Prop:=
 ∀ d∈A.support,InFlag p d
theorem support_subset_flagSupport_iff {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):
   A.support ⊆ flagSupport p ↔ PolynomialInFlag p A:=by
 simp only [PolynomialInFlag,Finset.subset_iff,mem_flagSupport_iff]
def flagSWeights:Fin 3 → ℕ:=![0,1,0]
def flagYSWeights:Fin 3 → ℕ:=![1,1,0]
def flagTotalWeights:Fin 3 → ℕ:=![1,1,1]
theorem flag_weight_fin3 (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
def flagMixed (p q r:FlagDegree):ℕ:=
 p.all*q.all*r.all+
 (p.zOnly*q.all*r.all+q.zOnly*p.all*r.all+
   r.zOnly*p.all*q.all)+
 (p.yz*q.all*r.all+q.yz*p.all*r.all+
   r.yz*p.all*q.all)+
 (p.all*q.yz*r.yz+q.all*p.yz*r.yz+
   r.all*p.yz*q.yz)+
 (p.zOnly*q.yz*r.all+p.zOnly*r.yz*q.all+
   q.zOnly*p.yz*r.all+q.zOnly*r.yz*p.all+
   r.zOnly*p.yz*q.all+r.zOnly*q.yz*p.all)
def unitZFlag:FlagDegree:=⟨1,0,0⟩
def unitYZFlag:FlagDegree:=⟨0,1,0⟩
def unitAllFlag:FlagDegree:=⟨0,0,1⟩
def seedFlag:FlagDegree:=unitYZFlag
public def legacyW:ℕ:=131071
def shearedSurfaceFlag:FlagDegree:=⟨350,21,5⟩
def shearedDerivativeFlag:FlagDegree:=⟨350,21,4⟩
def shearedAgreementFlag:FlagDegree:=
 seedFlag+legacyW • (shearedSurfaceFlag+shearedDerivativeFlag)
theorem shearedAgreementFlag_value:
   shearedAgreementFlag=⟨91749700,5504983,1179639⟩:=by
 change (⟨0+131071*(350+350),
     1+131071*(21+21),
     0+131071*(5+4)⟩:FlagDegree)=_
 norm_num
def flagWholeMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag shearedAgreementFlag
def flagZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitZFlag
def flagYZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitYZFlag
def flagAllMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitAllFlag
theorem flag_mixed_values:
   flagWholeMixedCap=16236998221509765∧
     flagZMixedCap=58195529∧
     flagYZMixedCap=929817679∧
     flagAllMixedCap=4898910072:=by
 norm_num [flagWholeMixedCap,flagZMixedCap,flagMixed,
   flagYZMixedCap,flagAllMixedCap,
   shearedSurfaceFlag,shearedAgreementFlag,shearedDerivativeFlag,
   seedFlag,unitZFlag,unitYZFlag,unitAllFlag,legacyW]
end ProximityPrize.SubmissionLower.RCN095
end PackedLegacy_D

/-! Packed from ProximityPrize.SubmissionLower.BO. -/
section PackedLegacy_BO
namespace ProximityPrize.SubmissionLower.RCN156
open scoped Classical BigOperators
open RCN157 RCN234 RCN235 RCN095 RCN136 RCN313
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
def residualSWeights:Fin 4 → ℕ:=![0,0,1,0]
def residualYSWeights:Fin 4 → ℕ:=![0,1,1,0]
def residualTotalWeights:Fin 4 → ℕ:=![0,1,1,1]
end
end ProximityPrize.SubmissionLower.RCN156
end PackedLegacy_BO

/-! Packed from ProximityPrize.SubmissionLower.D5. -/
section PackedLegacy_D5
namespace ProximityPrize.SubmissionLower.RCN215
open RCN095 RCN156 RCN213
end ProximityPrize.SubmissionLower.RCN215
end PackedLegacy_D5

/-! Packed from ProximityPrize.SubmissionLower.D4. -/
section PackedLegacy_D4
namespace ProximityPrize.SubmissionLower.RCN214
open scoped BigOperators
open RCN095 RCN213 RCN215
set_option maxHeartbeats 1000000
end ProximityPrize.SubmissionLower.RCN214
end PackedLegacy_D4

/-! Packed from ProximityPrize.SubmissionLower.AC. -/
section PackedLegacy_AC
namespace ProximityPrize.SubmissionLower.RCN266
open scoped BigOperators
open RCN223 RCN286 RCN167 RCN174 RCN136 RCN095
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
abbrev RegularIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(positiveRFactors Q)
end
end ProximityPrize.SubmissionLower.RCN266
end PackedLegacy_AC

/-! Packed from ProximityPrize.SubmissionLower.I3. -/
section PackedLegacy_I3
namespace ProximityPrize.SubmissionLower.RCN069
open RCN223 RCN174 RCN136 RCN068 RCN238
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
end
end ProximityPrize.SubmissionLower.RCN069
end PackedLegacy_I3

/-! Packed from ProximityPrize.SubmissionLower.K6. -/
section PackedLegacy_K6
namespace ProximityPrize.SubmissionLower.RCN171
open scoped Classical BigOperators
open RCN223 RCN294 RCN069 RCN068 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001
noncomputable section
variable {K:Type} [Field K]
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN171.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN171.instDecidableEq_proximityPrize_1 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN171
end PackedLegacy_K6

/-! Packed from ProximityPrize.SubmissionLower.F1. -/
section PackedLegacy_F1
namespace ProximityPrize.SubmissionLower.RCN291
open scoped BigOperators
open RCN223 RCN294 RCN286 RCN169 RCN167 RCN290 RCN293 RCN174 RCN319 RCN171 RCN081 RCN238 RCN243
noncomputable section
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN291.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev ImplicitIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(implicitPairSet (singularAuxiliary Q))
def implicitSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):Finset K:=by
 classical
 exact Gamma.filter (fun gamma => LiftedSolutionPair q.1 (selected gamma) gamma)
def implicitVector (Q:MvPolynomial (Fin 4) K)
   (q:ImplicitIndex Q):DegreeVector:=
 ⟨pairYCost q.1,pairRCost q.1,pairZCost q.1⟩
def singularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K):Finset K:=by
 classical
 exact Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
   exceptionalSeeds (singularAuxiliary Q) Gamma selected
theorem implicitSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):implicitSeeds Q selected Gamma q ⊆ Gamma:=by
 classical
 exact Finset.filter_subset _ _
theorem implicitSeeds_solution (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q) (gamma:K)
   (hgamma:gamma∈implicitSeeds Q selected Gamma q):
   LiftedSolutionPair q.1 (selected gamma) gamma:=by
 classical
 exact (Finset.mem_filter.mp hgamma).2
theorem singularSeeds_card_le_sum
   (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K):
   (singularSeeds Q selected Gamma).card ≤
     (∑ q:ImplicitIndex Q,(implicitSeeds Q selected Gamma q).card)+
       (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card:=by
 classical
 unfold singularSeeds
 exact (Finset.card_union_le _ _).trans
   (Nat.add_le_add_right Finset.card_biUnion_le _)
variable {Iota:Type}
local instance _root_.ProximityPrize.SubmissionLower.RCN291.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN291
end PackedLegacy_F1

/-! Packed from ProximityPrize.SubmissionLower.Z4. -/
section PackedLegacy_Z4
namespace ProximityPrize.SubmissionLower.RCN140
open scoped Classical BigOperators
open RCN223 RCN286 RCN167 RCN174 RCN319 RCN081 RCN266 RCN291 RCN214 RCN238
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN140.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
def regularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):Finset K:=
 Gamma.filter (fun gamma↦RegularSolution F.1 (selected gamma) gamma)
theorem regularSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):
   regularSeeds Q selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
end
end ProximityPrize.SubmissionLower.RCN140
end PackedLegacy_Z4

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier11 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.BC. -/
section PackedLegacy_BC
namespace ProximityPrize.SubmissionLower.RCN119
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def slopeDifference:Poly K:=MvPolynomial.X 0-MvPolynomial.X 1
public def plusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
public def minusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0-MvPolynomial.X 1 else MvPolynomial.X i
def shiftPlus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (plusVariables K)
def shiftMinus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (minusVariables K)
theorem shiftMinus_comp_shiftPlus:
   (shiftMinus K).comp (shiftPlus K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i <;> simp [shiftPlus,shiftMinus,plusVariables,minusVariables]
@[simp] theorem shiftMinus_shiftPlus (f:Poly K):
   shiftMinus K (shiftPlus K f)=f:=
 DFunLike.congr_fun (shiftMinus_comp_shiftPlus K) f
@[simp] theorem shiftPlus_slopeDifference:
   shiftPlus K (slopeDifference K)=MvPolynomial.X 0:=by
 simp [slopeDifference,shiftPlus,plusVariables]
@[simp] theorem shiftMinus_X_zero:
   shiftMinus K (MvPolynomial.X 0)=slopeDifference K:=by
 simp [shiftMinus,minusVariables,slopeDifference]
theorem slopeDifference_ne_zero:slopeDifference K≠0:=by
 intro h
 have hh:=congrArg (shiftPlus K) h
 simpa using hh
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
theorem contactJet_apply (h:ℕ) (f:Poly K):
   contactJet K h f=(shiftPlus K f).modMonomial (Finsupp.single 0 h):=rfl
theorem contactJet_eq_zero_iff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔ slopeDifference K^h∣f:=by
 rw [contactJet_apply,
   ←MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero,
   ←MvPolynomial.X_pow_eq_monomial]
 constructor
 · rintro ⟨q,hq⟩
   refine ⟨shiftMinus K q,?_⟩
   have hh:=congrArg (shiftMinus K) hq
   simpa only [shiftMinus_shiftPlus,map_mul,map_pow,shiftMinus_X_zero] using hh
 · rintro ⟨q,rfl⟩
   exact ⟨shiftPlus K q,by simp⟩
theorem contactJet_mul_slopeDifference (h:ℕ) (q:Poly K):
   contactJet K h (slopeDifference K^h*q)=0:=
 (contactJet_eq_zero_iff K h _).2 ⟨q,rfl⟩
theorem contactJet_eq_zero_iff_coeff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔
     ∀ d:Fin 3 →₀ ℕ,d 0 < h → MvPolynomial.coeff d (shiftPlus K f)=0:=by
 constructor
 · intro hf d hd
   have hnot:¬ Finsupp.single (0:Fin 3) h ≤ d:=by
     intro hle
     have hh:=hle 0
     simp only [Finsupp.single_eq_same] at hh
     omega
   have hh:=congrArg (MvPolynomial.coeff d) hf
   simpa [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hnot] using hh
 · intro hf
   ext d
   by_cases hle:Finsupp.single (0:Fin 3) h ≤ d
   · simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_le _ hle]
   · have hd:d 0 < h:=by
       by_contra hnot
       apply hle
       intro i
       by_cases hi:i=0
       · subst i
         simp only [Finsupp.single_eq_same]
         omega
       · simp [Finsupp.single_eq_of_ne hi]
     simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hle,hf d hd]
def boxExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 1+d 2 ≤ L∧d 1 ≤ s}
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
   rcases hd with ⟨hd0,hdTotal,hd1⟩
   rcases he with ⟨he0,heTotal,he1⟩
   simp only [boxExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   omega
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_coefficientBox:
   slopeDifference K∈coefficientBox K 1 1 1:=by
 apply (coefficientBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem slopeDifference_pow_mem_coefficientBox (h:ℕ):
   slopeDifference K^h∈coefficientBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ h ih =>
     simpa only [pow_succ] using coefficientBox_mul K ih (slopeDifference_mem_coefficientBox K)
theorem slopeDifference_mul_mem_coefficientBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈coefficientBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈coefficientBox K M L s:=by
 have hh:=coefficientBox_mul K (slopeDifference_pow_mem_coefficientBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,Nat.add_sub_of_le hs] using hh
public def exponentTriple (i j z:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j+Finsupp.single 2 z
@[simp] public theorem exponentTriple_zero (i j z:ℕ):
   exponentTriple i j z 0=i:=by simp [exponentTriple]
@[simp] public theorem exponentTriple_one (i j z:ℕ):
   exponentTriple i j z 1=j:=by simp [exponentTriple]
@[simp] public theorem exponentTriple_two (i j z:ℕ):
   exponentTriple i j z 2=z:=by simp [exponentTriple]
public theorem exponentTriple_eta (d:Fin 3 →₀ ℕ):
   exponentTriple (d 0) (d 1) (d 2)=d:=by
 ext i
 fin_cases i <;> simp
public theorem finSigma_heq_of_val_eq
   {n:ℕ} {a b:Fin n → ℕ}
   {i j:Fin n} {u:Fin (a i)} {v:Fin (b j)}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (⟨i,u⟩:(k:Fin n) × Fin (a k))
     (⟨j,v⟩:(k:Fin n) × Fin (b k)):=by
 subst b
 have hi:i=j:=Fin.ext hij
 subst j
 have hu:u=v:=Fin.ext huv
 subst v
 rfl
abbrev BoxIndex (M L s:ℕ):=
 (i:Fin (M+1)) ×
   (j:Fin (s+1)) × Fin (L+1-i.val-j.val)
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
       rcases d.property with ⟨hM,hL,hs⟩
       change d.val 2 < L+1-d.val 0-d.val 1
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
   apply Sigma.ext
   · apply Fin.ext
     exact exponentTriple_zero i j z
   · dsimp only
     apply @finSigma_heq_of_val_eq (s+1)
       (fun k↦L+1-(exponentTriple i j z) 0-k.val)
       (fun k↦L+1-i-k.val) _ _ _ _
     · funext k
       simp only [exponentTriple_zero]
     · exact exponentTriple_one i j z
     · exact exponentTriple_two i j z
instance boxExponentsFintype (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (boxExponentsEquivIndex M L s).symm
instance coefficientBoxFinite (M L s:ℕ):
   Module.Finite K (coefficientBox K M L s):=
 Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))
theorem coefficientBox_finrank (M L s:ℕ):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 change Module.finrank K (MvPolynomial.restrictSupport K (boxExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (boxExponents M L s))]
 rw [Fintype.card_congr (boxExponentsEquivIndex M L s)]
 simp [BoxIndex,Fintype.card_sigma]
theorem coefficientBox_finrank_of_le (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 exact coefficientBox_finrank K M L s
def multiplyIntoBox {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     coefficientBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_coefficientBox K hM hL hs q.property⟩
 map_add' q r:=by
   apply Subtype.ext
   simp [mul_add]
 map_smul' c q:=by
   apply Subtype.ext
   simp [mul_smul_comm]
theorem multiplyIntoBox_injective
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=slopeDifference K^h*r.val:=
   congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def blockJet (M L s h:ℕ):coefficientBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (coefficientBox K M L s).subtype
def kernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (blockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (blockJet K M L s h))
   (multiplyIntoBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem kernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (kernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoBox_injective K hM hL hs
 exact congrArg Subtype.val heq
theorem blockJet_rank_add_quotient_finrank_le {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h))+
       Module.finrank K (coefficientBox K (M-h) (L-h) (s-h)) ≤
     Module.finrank K (coefficientBox K M L s):=by
 have hker:=LinearMap.finrank_le_finrank_of_injective
   (kernelEmbedding_injective K hM hL hs)
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 omega
theorem blockJet_rank_le_input (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 rw [coefficientBox_finrank_of_le K M L s hML] at hsum
 omega
theorem coefficientBox_finrank_range (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i∈Finset.range (M+1),
       ∑ j∈Finset.range (s+1),(L+1-i-j):=by
 rw [coefficientBox_finrank_of_le K M L s hML]
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro i hi
 rw [Finset.sum_range]
def blockInputCount (M L s:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1),
   ∑ j∈Finset.range (s+1),(L+1-i-j)
def blockKernelLowerBound (M L s h:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1-h),
   ∑ j∈Finset.range (s+1-h),(L+1-h-i-j)
def contactRankBound (M L s h:ℕ):ℕ:=
 blockInputCount M L s-blockKernelLowerBound M L s h
theorem blockJet_rank_le_contactRankBound (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     contactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hineq:=blockJet_rank_add_quotient_finrank_le K hM hL hs
     rw [coefficientBox_finrank_range K M L s hML,
       coefficientBox_finrank_range K (M-h) (L-h) (s-h)
         (Nat.sub_le_sub_right hML h)] at hineq
     have hMeq:M-h+1=M+1-h:=by omega
     have hLeq:L-h+1=L+1-h:=by omega
     have hseq:s-h+1=s+1-h:=by omega
     rw [hMeq,hLeq,hseq] at hineq
     unfold contactRankBound blockInputCount blockKernelLowerBound
     omega
   · have hzero:s+1-h=0:=by omega
     have hinput:=blockJet_rank_le_input K M L s h hML
     simpa [contactRankBound,blockKernelLowerBound,blockInputCount,
       hzero,Finset.sum_range] using hinput
 · have hzero:M+1-h=0:=by omega
   have hinput:=blockJet_rank_le_input K M L s h hML
   simpa [contactRankBound,blockKernelLowerBound,blockInputCount,
     hzero,Finset.sum_range] using hinput
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   contactRankBound (min r L) L s (min (r+1) (m-r))
end
end ProximityPrize.SubmissionLower.RCN119
end PackedLegacy_BC

/-! Packed from ProximityPrize.SubmissionLower.C1. -/
section PackedLegacy_C1
namespace ProximityPrize.SubmissionLower.RCN100
open RCN119 ProximityPrize.Benchmark
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
   localMonomial K f j z∈coefficientBox K f (f+j+z) j:=by
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
   (Fin (L+1-i.val-j.val) ×
     Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ} (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val+Finsupp.single 3 c.2.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 0=c.2.2.2.val:=by simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 1=c.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 2=c.2.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 3=c.2.2.1.val:=by simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 have hz:=congrArg (fun e:Fin 4 →₀ ℕ => e 3) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 simp only [columnExponent_z] at hz
 subst di
 subst dj
 subst dz
 subst de
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):
   Submodule K (MvPolynomial (Fin 4) K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have hz:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 simp only [globalExponents,Set.mem_setOf_eq,columnExponent_x,
   columnExponent_y,columnExponent_r,columnExponent_z]
 omega
def reconstruct (D w L s:ℕ) (θ:CoefficientIndex D w L s → K):
   MvPolynomial (Fin 4) K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (θ c)
theorem reconstruct_coeff (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s θ)=θ c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro θ η h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (hθ:θ≠0):
   reconstruct K D w L s θ≠0:=by
 intro hzero
 apply hθ
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hzero
theorem reconstruct_mem_globalCoefficientBox (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   reconstruct K D w L s θ∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (θ c)
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     (L+1-i-j)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,Finset.sum_range]
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
     (show c.1.val-f.val+
         (f.val+c.2.1.val+c.2.2.1.val) ≤ L by omega)
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
theorem full_contactRankBound_eq (r m L s:ℕ):
   contactRankBound (min r L) L s (m-r)=
     contactRankBound (min r L) L s (min (r+1) (m-r)):=by
 by_cases h:r+1 ≤ m-r
 · have hM:min r L ≤ r:=min_le_left r L
   have hzero:min r L+1-(m-r)=0:=by omega
   have hzero':min r L+1-(r+1)=0:=by omega
   simp only [Nat.min_eq_left h,contactRankBound,blockKernelLowerBound,
     hzero,hzero',Finset.range_zero,Finset.sum_empty,mul_zero,Nat.sub_zero]
 · have h':m-r ≤ r+1:=by omega
   rw [Nat.min_eq_right h']
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 have hh:=blockJet_rank_le_contactRankBound K (min r.val L) L s (m-r.val)
   (min_le_right r.val L)
 rw [full_contactRankBound_eq] at hh
 exact hh
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
theorem globalTarget_finrank_le {I:Type*} [Fintype I] (m L s:ℕ):
   Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
 change Module.finrank K (I → LocalTarget K m L s) ≤ _
 rw [Module.finrank_pi_fintype]
 calc
   (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
       ∑ _i:I,localRankBound m L s:=by
     apply Finset.sum_le_sum
     intro i hi
     exact localTarget_finrank_le K m L s
   _=Fintype.card I*localRankBound m L s:=by simp
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val)
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,
     θ≠0∧constraintMap K D w L s m nodes u₀ u₁ θ=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective (constraintMap K D w L s m nodes u₀ u₁):=by
   intro θ η heq
   by_contra hne
   apply hnone
   refine ⟨θ-η,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have hupper:=globalTarget_finrank_le K (I:=I) m L s
 exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)
theorem all_blocks_divisible_of_equations
   (D w L s m:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K)
   (h:∀ r:Fin m,contactJet K (m-r.val)
     ((extractBlock K D w L s x u₀ u₁ r.val θ):Poly K)=0):
   ∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 intro r
 by_cases hr:r < m
 · exact (contactJet_eq_zero_iff K (m-r) _).mp (h ⟨r,hr⟩)
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
end
end ProximityPrize.SubmissionLower.RCN100
end PackedLegacy_C1

/-! Packed from ProximityPrize.SubmissionLower.BD. -/
section PackedLegacy_BD
namespace ProximityPrize.SubmissionLower.RCN122
open RCN119 RCN100 ProximityPrize.Benchmark
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
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val*
       MvPolynomial.X 3^c.2.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j z:ℕ):
   localMonomial K f j z=
     MvPolynomial.X 0^f*MvPolynomial.X 1^j*MvPolynomial.X 2^z:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.X_pow_eq_monomial]
theorem coeff_shifted_affine_product
   {A:Type*} [CommRing A] (x a y b:A) (e i r:ℕ):
   (((Polynomial.X+Polynomial.C x)^e*
       (Polynomial.X*Polynomial.C y+Polynomial.C a)^i*
       Polynomial.C b):Polynomial A).coeff r=
     ∑ f:Fin (i+1),if f.val ≤ r then
       (x^(e-(r-f.val))*(e.choose (r-f.val):A))*
         (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b)
     else 0:=by
 rw [add_pow (Polynomial.X*Polynomial.C y) (Polynomial.C a) i,
   Finset.mul_sum,Finset.sum_mul,Polynomial.finsetSum_coeff]
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro f hf
 have hfactor:
     (((Polynomial.X+Polynomial.C x)^e*
       ((Polynomial.X*Polynomial.C y)^f.val*
         Polynomial.C a^(i-f.val)*(i.choose f.val:Polynomial A)))*
         Polynomial.C b)=
       (((Polynomial.X+Polynomial.C x)^e*
         Polynomial.C (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b))*
         Polynomial.X^f.val):=by
   simp only [mul_pow,map_mul,map_pow,map_natCast]
   ring
 rw [hfactor,Polynomial.coeff_mul_X_pow']
 split_ifs with hfr
 · rw [Polynomial.coeff_mul_C,Polynomial.coeff_X_add_C_pow]
 · rfl
theorem translation_column (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K):
   homogenizedTranslation K x u₀ u₁ (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       (Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
       (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
         Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
       Polynomial.C (MvPolynomial.X 1)^c.2.1.val*
       Polynomial.C (MvPolynomial.X 2)^c.2.2.1.val:=by
 rw [columnMonomial_eq K D w L s c a]
 simp [homogenizedTranslation,translationVariables,
   Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
theorem translation_column_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u₀ u₁ c r:=by
 have hfactor:
     homogenizedTranslation K x u₀ u₁
       (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       ((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
         (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
           Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
         Polynomial.C (MvPolynomial.X 1^c.2.1.val*
           MvPolynomial.X 2^c.2.2.1.val)):=by
   rw [translation_column K D w L s x u₀ u₁ c a]
   simp only [map_mul,map_pow]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,
     map_mul,map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁ (reconstruct K D w L s θ)).coeff r=
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
   θ c • blockEntry K D w L s x u₀ u₁ c r)=
     (((∑ c:CoefficientIndex D w L s,
       θ c • boundedBlockEntry K D w L s x u₀ u₁ c r):
         coefficientBox K (min r L) L s):Poly K)
 simp [boundedBlockEntry]
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
     d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
       d 0+w*d 1+(w-1)*d 2 < D:=hcaps
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
end ProximityPrize.SubmissionLower.RCN122
end PackedLegacy_BD

/-! Packed from ProximityPrize.SubmissionLower.C2. -/
section PackedLegacy_C2
namespace ProximityPrize.SubmissionLower.RCN101
open ProximityPrize.Benchmark RCN100 RCN119 RCN122
noncomputable section
variable (K:Type*) [Field K]
theorem block_equations_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:Fin m),
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
         Poly K)=0:=by
 intro i r
 have hzero:constraintMap K D w L s m nodes u0 u1 theta=0:=
   LinearMap.mem_ker.mp htheta
 have happ:=congrArg
   (fun target:GlobalTarget K I m L s => ((target i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
     Poly K)=0 at happ
 exact happ
theorem translated_contact_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:ℕ),
     slopeDifference K^(m-r)∣
       (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
         (reconstruct K D w L s theta)).coeff r:=by
 intro i r
 rw [translation_reconstruct_coeff]
 exact all_blocks_divisible_of_equations K D w L s m
   (nodes i) (u0 i) (u1 i) theta
   (block_equations_of_mem_ker K D w L s m nodes u0 u1 theta htheta i) r
theorem specialization_eq_zero_of_mem_ker
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hD:0 < D) (hP:P.natDegree ≤ w)
   (hcapacity:D ≤ m*support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_contact_and_degree K
   (reconstruct K D w L s theta) P gamma nodes u0 u1 support m
 · intro i hi r
   exact translated_contact_of_mem_ker K D w L s m nodes u0 u1 theta
     htheta i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt K D w L s
     (reconstruct K D w L s theta) P gamma hD
     (reconstruct_mem_globalCoefficientBox K D w L s theta) hP
   exact hdegree.trans_le hcapacity
theorem specialization_eq_zero_of_agreements
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a)
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hP:P.natDegree ≤ w) (hcard:a ≤ support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_mem_ker K D w L s m nodes u0 u1 theta
   htheta P gamma support hD hP
 · rw [hDa]
   exact Nat.mul_le_mul_left m hcard
 · exact hvalues
theorem flag_box_to_ordinary (D w L s:ℕ)
   (Q:MvPolynomial (Fin 4) K)
   (hQ:Q∈globalCoefficientBox K D w L s):
   Q∈RCN174.globalCoefficientBox K D w L s:=by
 intro d hd
 obtain ⟨hT,hR,hD⟩:=hQ hd
 exact ⟨by omega,hR,hD⟩
theorem specialization_eq_ordinary (P:Polynomial K) (gamma:K):
   specialization K P gamma=RCN319.specialization K P gamma:=rfl
end
end ProximityPrize.SubmissionLower.RCN101
end PackedLegacy_C2

/-! Packed from ProximityPrize.SubmissionLower.I4. -/
section PackedLegacy_I4
namespace ProximityPrize.SubmissionLower.RCN071
open scoped BigOperators
open RCN081
noncomputable section
variable {K:Type*} [Field K]
theorem weightedTotalDegree_prod_eq
   {I:Type*} [DecidableEq I] (weights:Fin 4 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 4) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=
       Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul weights (f a) (∏ i∈s,f i) hfa hprod,
       ih hfs]
def weightEmbed3 (weights:Fin 3 → ℕ):
   (Fin 3 →₀ ℕ) →+(Fin 4 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+
   Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed3_original (weights:Fin 3 → ℕ)
   (d:Fin 3 →₀ ℕ) (i:Fin 3):
   weightEmbed3 weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed3]
theorem weightEmbed3_last (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   weightEmbed3 weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed3]
theorem weightEmbed3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightEmbed3 weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 4 →₀ ℕ↦a i.castSucc) h
 simpa only [weightEmbed3_original] using hi
def weightedLift3 (weights:Fin 3 → ℕ):
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed3 weights)
theorem weightedLift3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightedLift3 (K:=K) weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed3_injective weights)
theorem weightedLift3_ne_zero (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K) (hP:P≠0):
   weightedLift3 weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift3_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).support=
     P.support.image (weightEmbed3 weights):=by
 change (Finsupp.mapDomain (weightEmbed3 weights)
     (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed3 weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective
   (weightEmbed3_injective weights) _
theorem degree_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift3 weights P).degreeOf (3:Fin 4)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift3,Finset.sup_image]
 apply congrArg (fun f:(Fin 3 →₀ ℕ) → ℕ↦P.support.sup f)
 funext d
 exact weightEmbed3_last weights d
theorem weightedTotalDegree_mul_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift3 weights (P*Q)).degreeOf (3:Fin 4):=
     (degree_weightedLift3 weights (P*Q)).symm
   _=(weightedLift3 weights P*weightedLift3 weights Q).degreeOf
       (3:Fin 4):=by rw [map_mul]
   _=(weightedLift3 weights P).degreeOf (3:Fin 4)+
       (weightedLift3 weights Q).degreeOf (3:Fin 4):=
     MvPolynomial.degreeOf_mul_eq
       (weightedLift3_ne_zero weights P hP)
       (weightedLift3_ne_zero weights Q hQ)
   _=_:=by rw [degree_weightedLift3,degree_weightedLift3]
theorem weightedTotalDegree_le_of_dvd_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul_fin3 weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_prod_eq_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul_fin3 weights (f a) (∏ i∈s,f i)
         hfa hprod,ih hfs]
theorem sum_weightedTotalDegree_le_of_prod_dvd_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K) (Q:MvPolynomial (Fin 3) K)
   (hQ:Q≠0) (hdiv:(∏ i∈s,f i)∣Q):
   (∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈s,f i)≠0:=by
   intro hzero
   obtain ⟨R,hR⟩:=hdiv
   apply hQ
   rw [hR,hzero,zero_mul]
 have hf:∀ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [←weightedTotalDegree_prod_eq_fin3 weights s f hf]
 exact weightedTotalDegree_le_of_dvd_fin3 weights _ Q hdiv hQ
end
end ProximityPrize.SubmissionLower.RCN071
end PackedLegacy_I4

/-! Packed from ProximityPrize.SubmissionLower.X3. -/
section PackedLegacy_X3
namespace ProximityPrize.SubmissionLower.RCN372
open scoped Classical BigOperators
noncomputable section
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN372.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def shearImage (a:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1-MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def unshearImage (a:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1+MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def shearAlgHom (a:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (shearImage a)
def unshearAlgHom (a:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (unshearImage a)
theorem unshear_comp_shear (a:K):
   (unshearAlgHom a).comp (shearAlgHom a)=AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;> simp [shearImage,unshearImage,shearAlgHom,unshearAlgHom] <;> ring
theorem shear_comp_unshear (a:K):
   (shearAlgHom a).comp (unshearAlgHom a)=AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;> simp [shearImage,unshearImage,shearAlgHom,unshearAlgHom] <;> ring
def shearEquiv (a:K):Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom (shearAlgHom a) (unshearAlgHom a)
   (shear_comp_unshear a) (unshear_comp_shear a)
@[simp] theorem shearEquiv_apply (a:K) (F:Poly3 K):
   shearEquiv a F=shearAlgHom a F:=rfl
section WeightedDegree
def weightEmbed (weights:Fin 3 → ℕ):(Fin 3 →₀ ℕ) →+(Fin 4 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ) (i:Fin 3):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   weightEmbed weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun b:Fin 4 →₀ ℕ↦b i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
def weightedLift (weights:Fin 3 → ℕ):Poly3 K →+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem support_weightedLift (weights:Fin 3 → ℕ) (F:Poly3 K):
   (weightedLift weights F).support=F.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff F)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff F).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 3 → ℕ) (F:Poly3 K):
   (weightedLift weights F).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights F:=by
 change (weightedLift weights F).degreeOf (3:Fin 4)=
   F.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 3 →₀ ℕ) → ℕ↦F.support.sup f)
 funext d
 exact weightEmbed_last weights d
def wt (weights:Fin 3 → ℕ) (F:Poly3 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights F
theorem wt_mul_le (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F*G) ≤ wt weights F+wt weights G:=by
 unfold wt
 rw [←degree_weightedLift,map_mul]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_mul_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem wt_sub_le (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F-G) ≤ max (wt weights F) (wt weights G):=by
 unfold wt
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem wt_pow_le (weights:Fin 3 → ℕ) (F:Poly3 K) (n:ℕ):
   wt weights (F^n) ≤ n*wt weights F:=by
 unfold wt
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (3:Fin 4) (weightedLift weights F) n
theorem wt_C (weights:Fin 3 → ℕ) (c:K):
   wt weights (MvPolynomial.C c:Poly3 K)=0:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp
theorem wt_X (weights:Fin 3 → ℕ) (i:Fin 3):
   wt weights (MvPolynomial.X i:Poly3 K)=weights i:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp [MvPolynomial.support_X,Finsupp.weight_single]
theorem wt_finset_prod_le_sum {ι:Type*} [DecidableEq ι]
   (weights:Fin 3 → ℕ) (I:Finset ι) (f:ι → Poly3 K):
   wt weights (∏ i∈I,f i) ≤ ∑ i∈I,wt weights (f i):=by
 induction I using Finset.induction_on with
 | empty => simp [wt,MvPolynomial.weightedTotalDegree]
 | @insert i I hi ih =>
     simp only [Finset.prod_insert hi,Finset.sum_insert hi]
     exact (wt_mul_le weights (f i) (∏ j∈I,f j)).trans
       (Nat.add_le_add le_rfl ih)
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 3 → ℕ) (I:Finset ι) (f:ι → Poly3 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (3:Fin 4) I
   (fun i↦weightedLift weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem weight_fin3 (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
end WeightedDegree
end
end ProximityPrize.SubmissionLower.RCN372
end PackedLegacy_X3

/-! Packed from ProximityPrize.SubmissionLower.Z3. -/
section PackedLegacy_Z3
namespace ProximityPrize.SubmissionLower.RCN125
open scoped Classical BigOperators
open RCN095 RCN372 RCN003 RCN002 RCN011 RCN371 RCN012 RCN013
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN125.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def flagImage (lam μ ν:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0-MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1-
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def unflagImage (lam μ ν:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0+MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1+MvPolynomial.C μ*MvPolynomial.X 0+
     MvPolynomial.C ν*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def flagAlgHom (lam μ ν:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (flagImage lam μ ν)
def unflagAlgHom (lam μ ν:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (unflagImage lam μ ν)
@[simp] theorem flagAlgHom_X (lam μ ν:K) (i:Fin 3):
   flagAlgHom lam μ ν (MvPolynomial.X i)=flagImage lam μ ν i:=by
 simp [flagAlgHom]
theorem unflag_comp_flag (lam μ ν:K):
   (unflagAlgHom lam μ ν).comp (flagAlgHom lam μ ν)=
     AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [flagImage,unflagImage,flagAlgHom,unflagAlgHom] <;> ring
theorem flag_comp_unflag (lam μ ν:K):
   (flagAlgHom lam μ ν).comp (unflagAlgHom lam μ ν)=
     AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [flagImage,unflagImage,flagAlgHom,unflagAlgHom] <;> ring
def flagEquiv (lam μ ν:K):Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom (flagAlgHom lam μ ν) (unflagAlgHom lam μ ν)
   (flag_comp_unflag lam μ ν) (unflag_comp_flag lam μ ν)
@[simp] theorem flagEquiv_apply (lam μ ν:K) (F:Poly3 K):
   flagEquiv lam μ ν F=flagAlgHom lam μ ν F:=rfl
theorem flag_irreducible_iff (lam μ ν:K) (F:Poly3 K):
   Irreducible (flagAlgHom lam μ ν F) ↔ Irreducible F:=by
 simpa only [flagEquiv_apply] using
   (MulEquiv.irreducible_iff (flagEquiv lam μ ν))
theorem flag_dvd_iff (lam μ ν:K) (F G:Poly3 K):
   flagAlgHom lam μ ν F∣flagAlgHom lam μ ν G ↔ F∣G:=by
 simpa only [flagEquiv_apply] using
   (map_dvd_iff (flagEquiv lam μ ν))
theorem flag_ne_zero (lam μ ν:K) {F:Poly3 K} (hF:F≠0):
   flagAlgHom lam μ ν F≠0:=
 (flagEquiv lam μ ν).injective.ne hF
theorem eval₂Hom_flag
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (u v z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]
       (flagAlgHom lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![u-algebraMap K A lam*z,
         v-algebraMap K A μ*u+
           algebraMap K A (μ*lam-ν)*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]).comp
         (flagAlgHom lam μ ν).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![u-algebraMap K A lam*z,
           v-algebraMap K A μ*u+
             algebraMap K A (μ*lam-ν)*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,flagAlgHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,flagAlgHom,flagImage] <;> ring
 exact RingHom.congr_fun hhom F
theorem eval₂Hom_flag_at_affine
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (y s z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A)
       ![y+algebraMap K A lam*z,
         s+algebraMap K A μ*y+algebraMap K A ν*z,
         z] (flagAlgHom lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z] F:=by
 rw [eval₂Hom_flag]
 congr 2
 funext i
 fin_cases i <;> simp <;> ring
def flagPullWeights (weights:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![max (weights 0) (weights 2),
   max (weights 1) (max (weights 0) (weights 2)),
   weights 2]
theorem flagImage_wt_le (weights:Fin 3 → ℕ) (lam μ ν:K) (i:Fin 3):
   wt weights (flagImage lam μ ν i) ≤ flagPullWeights weights i:=by
 fin_cases i
 · dsimp [flagImage,flagPullWeights]
   have hm:=wt_mul_le weights (MvPolynomial.C lam:Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hm
   exact (wt_sub_le weights (MvPolynomial.X 0)
     (MvPolynomial.C lam*MvPolynomial.X 2)).trans
       (max_le_max (by rw [wt_X]) hm)
 · dsimp [flagImage,flagPullWeights]
   have hμ:=wt_mul_le weights (MvPolynomial.C μ:Poly3 K)
     (MvPolynomial.X 0)
   have hν:=wt_mul_le weights (MvPolynomial.C (μ*lam-ν):Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hμ hν
   have hinner:=wt_sub_le weights
     (MvPolynomial.C μ*MvPolynomial.X 0)
     (MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   have houter:=wt_sub_le weights (MvPolynomial.X 1)
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   exact houter.trans (max_le_max (by rw [wt_X])
     (hinner.trans (max_le_max hμ hν)))
 · simp [flagImage,flagPullWeights,wt_X]
theorem flag_monomial_product_wt_le
   (weights:Fin 3 → ℕ) (lam μ ν:K) (d:Fin 3 →₀ ℕ):
   wt weights (∏ i∈d.support,flagImage lam μ ν i^d i) ≤
     Finsupp.weight (flagPullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦flagImage lam μ ν i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (flagImage lam μ ν i^d i)) ≤
       ∑ i∈d.support,d i*flagPullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (flagImage lam μ ν i) (d i)).trans
       (Nat.mul_le_mul_left _ (flagImage_wt_le weights lam μ ν i))
   _=Finsupp.weight (flagPullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem flagAlgHom_wt_le_pulled
   (weights:Fin 3 → ℕ) (lam μ ν:K) (F:Poly3 K):
   wt weights (flagAlgHom lam μ ν F) ≤ wt (flagPullWeights weights) F:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C (flagImage lam μ ν) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=flag_monomial_product_wt_le weights lam μ ν d
 have hcoeff:wt weights (MvPolynomial.C (F.coeff d):Poly3 K)=0:=
   wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (F.coeff d):Poly3 K)
   (∏ i∈d.support,flagImage lam μ ν i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (flagPullWeights weights) hd))
def sWeight:Fin 3 → ℕ:=![0,1,0]
def ysWeight:Fin 3 → ℕ:=![1,1,0]
def totalWeight:Fin 3 → ℕ:=![1,1,1]
@[simp] theorem flagPullWeights_sWeight:flagPullWeights sWeight=sWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,sWeight]
@[simp] theorem flagPullWeights_ysWeight:flagPullWeights ysWeight=ysWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,ysWeight]
@[simp] theorem flagPullWeights_totalWeight:
   flagPullWeights totalWeight=totalWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,totalWeight]
def PolynomialInFlag (p:FlagDegree) (F:Poly3 K):Prop:=
 ∀ d∈F.support,InFlag p d
theorem wt_s_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):wt sWeight F ≤ p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).1
 simpa [sWeight,weight_fin3] using h
theorem wt_ys_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):wt ysWeight F ≤ p.yz+p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.1
 simpa [ysWeight,weight_fin3,Nat.add_comm] using h
theorem wt_total_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):
   wt totalWeight F ≤ p.zOnly+p.yz+p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.2
 simpa [totalWeight,weight_fin3,Nat.add_comm,Nat.add_left_comm,
   Nat.add_assoc] using h
theorem polynomialInFlag_flagAlgHom
   (p:FlagDegree) (F:Poly3 K) (lam μ ν:K)
   (hF:PolynomialInFlag p F):
   PolynomialInFlag p (flagAlgHom lam μ ν F):=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight hd
 have hys:=MvPolynomial.le_weightedTotalDegree ysWeight hd
 have htot:=MvPolynomial.le_weightedTotalDegree totalWeight hd
 have hsw:=(flagAlgHom_wt_le_pulled sWeight lam μ ν F).trans
   (by simpa using wt_s_le_of_inFlag hF)
 have hysw:=(flagAlgHom_wt_le_pulled ysWeight lam μ ν F).trans
   (by simpa using wt_ys_le_of_inFlag hF)
 have htotw:=(flagAlgHom_wt_le_pulled totalWeight lam μ ν F).trans
   (by simpa using wt_total_le_of_inFlag hF)
 refine ⟨?_,?_,?_⟩
 · have:=hs.trans hsw
   simpa [sWeight,weight_fin3] using this
 · have:=hys.trans hysw
   simpa [ysWeight,weight_fin3,Nat.add_comm] using this
 · have:=htot.trans htotw
   simpa [totalWeight,weight_fin3,Nat.add_comm,Nat.add_left_comm,
     Nat.add_assoc] using this
def uOrder:Fin 3 ≃ Fin 3:=Equiv.refl _
def vOrder:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
def zOrder:Fin 3 ≃ Fin 3:=Equiv.swap 0 2
end
end ProximityPrize.SubmissionLower.RCN125
end PackedLegacy_Z3

/-! Packed from ProximityPrize.SubmissionLower.B9. -/
section PackedLegacy_B9
namespace ProximityPrize.SubmissionLower.RCN094
open scoped Classical BigOperators
open RCN095 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN094.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def residualImage (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0+
     MvPolynomial.C bY*MvPolynomial.X 2,
   MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1+
     MvPolynomial.C bS*MvPolynomial.X 0+
     MvPolynomial.C cS*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def originalImage (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 let y:=MvPolynomial.C v⁻¹*
   (MvPolynomial.X 0-MvPolynomial.C aY-
     MvPolynomial.C bY*MvPolynomial.X 2)
 ![y,
   MvPolynomial.C v⁻¹*
     (MvPolynomial.X 1-MvPolynomial.C aS-
       MvPolynomial.C bS*y-MvPolynomial.C cS*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def residualAlgHom (aY v bY aS bS cS:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (residualImage aY v bY aS bS cS)
def originalAlgHom (aY v bY aS bS cS:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (originalImage aY v bY aS bS cS)
theorem original_comp_residual
   (aY v bY aS bS cS:K) (hv:v≠0):
   (originalAlgHom aY v bY aS bS cS).comp
       (residualAlgHom aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v:Poly3 K)*MvPolynomial.C v⁻¹=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 0-MvPolynomial.C bY*MvPolynomial.X 2-
       MvPolynomial.C aY)*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 1-MvPolynomial.C cS*MvPolynomial.X 2-
       (MvPolynomial.C aS+MvPolynomial.C v⁻¹*MvPolynomial.C bS*
         (MvPolynomial.X 0-MvPolynomial.C aY-
           MvPolynomial.C bY*MvPolynomial.X 2)))*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
theorem residual_comp_original
   (aY v bY aS bS cS:K) (hv:v≠0):
   (residualAlgHom aY v bY aS bS cS).comp
       (originalAlgHom aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v⁻¹:Poly3 K)*MvPolynomial.C v=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination MvPolynomial.X 0*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 1-
       MvPolynomial.C v⁻¹*MvPolynomial.C bS*MvPolynomial.X 0)*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
def residualEquiv (aY v bY aS bS cS:K) (hv:v≠0):
   Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom
   (residualAlgHom aY v bY aS bS cS)
   (originalAlgHom aY v bY aS bS cS)
   (residual_comp_original aY v bY aS bS cS hv)
   (original_comp_residual aY v bY aS bS cS hv)
@[simp] theorem residualEquiv_apply
   (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
   residualEquiv aY v bY aS bS cS hv F=
     residualAlgHom aY v bY aS bS cS F:=rfl
theorem eval₂Hom_residual
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (y s z:A) (aY v bY aS bS cS:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]
       (residualAlgHom aY v bY aS bS cS F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![algebraMap K A aY+algebraMap K A v*y+
           algebraMap K A bY*z,
         algebraMap K A aS+algebraMap K A v*s+
           algebraMap K A bS*y+algebraMap K A cS*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]).comp
         (residualAlgHom aY v bY aS bS cS).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![algebraMap K A aY+algebraMap K A v*y+
             algebraMap K A bY*z,
           algebraMap K A aS+algebraMap K A v*s+
             algebraMap K A bS*y+algebraMap K A cS*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,residualAlgHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,residualAlgHom,residualImage] <;> ring
 exact RingHom.congr_fun hhom F
end
end ProximityPrize.SubmissionLower.RCN094
end PackedLegacy_B9

/-! Packed from ProximityPrize.SubmissionLower.K4. -/
section PackedLegacy_K4
namespace ProximityPrize.SubmissionLower.RCN161
noncomputable section
open scoped Function
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
variable {K:Type*} [Field K]
variable {L:Type*} [Field L]
end
end ProximityPrize.SubmissionLower.RCN161
end PackedLegacy_K4

/-! Packed from ProximityPrize.SubmissionLower.EZ. -/
section PackedLegacy_EZ
namespace ProximityPrize.SubmissionLower.RCN160
open RCN238
noncomputable section
variable {K ι:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN160.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN160.instDecidableEq_proximityPrize_1 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN160
end PackedLegacy_EZ

/-! Packed from ProximityPrize.SubmissionLower.EX. -/
section PackedLegacy_EX
namespace ProximityPrize.SubmissionLower.RCN155
open RCN238 RCN161 RCN160
noncomputable section
variable {K ι:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN155.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN155.instDecidableEq_proximityPrize_1 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN155
end PackedLegacy_EX

/-! Packed from ProximityPrize.SubmissionLower.BQ. -/
section PackedLegacy_BQ
namespace ProximityPrize.SubmissionLower.RCN163
open scoped Classical
open RCN094 RCN157 RCN155 RCN160 RCN238 RCN125 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
local instance _root_.ProximityPrize.SubmissionLower.RCN163.instDecidableEq_proximityPrize :DecidableEq Omega:=Classical.decEq Omega
@[simp] theorem polynomial_eval₂_comp_C_X
   (phi:Polynomial K →+*Omega) (P:Polynomial K):
   P.eval₂ (phi.comp Polynomial.C) (phi Polynomial.X)=phi P:=by
 change (Polynomial.eval₂RingHom (phi.comp Polynomial.C)
   (phi Polynomial.X)) P=phi P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [RingHom.comp_apply]
 · simp
end
end ProximityPrize.SubmissionLower.RCN163
end PackedLegacy_BQ

/-! Packed from ProximityPrize.SubmissionLower.K5. -/
section PackedLegacy_K5
namespace ProximityPrize.SubmissionLower.RCN166
open RCN002 RCN136 RCN224 RCN139 RCN233 RCN231 RCN229 RCN313 RCN047 RCN147 RCN319 RCN065
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
 (phi:Polynomial K →+*Omega)
variable (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap phi F∈P)
 (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
end
end ProximityPrize.SubmissionLower.RCN166
end PackedLegacy_K5

/-! Packed from ProximityPrize.SubmissionLower.E8. -/
section PackedLegacy_E8
namespace ProximityPrize.SubmissionLower.RCN275
open RCN136 RCN313 RCN174 RCN081 RCN234 RCN157 RCN156 RCN095
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
structure ResidualSupportParameters where
 s:ℕ
 ys:ℕ
 total:ℕ
 one_le_s:1 ≤ s
 s_le_ys:s ≤ ys
 ys_le_total:ys ≤ total
 two_le_ys:2 ≤ ys
 deriving DecidableEq
namespace ResidualSupportParameters
def acceptedSupport:ResidualSupportParameters where
 s:=8
 ys:=43
 total:=503
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
end ResidualSupportParameters
variable {K Omega:Type} [Field K] [Field Omega]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure ResidualSupportData (P:ResidualSupportParameters) (F:Poly4 K):Prop where
 s_weight:wt residualSWeights F ≤ P.s
 ys_weight:wt residualYSWeights F ≤ P.ys
 total_weight:wt residualTotalWeights F ≤ P.total
namespace ResidualSupportData
theorem coordinate_bounds
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F):
   F.degreeOf (1:Fin 4) ≤ P.ys∧
     F.degreeOf (2:Fin 4) ≤ P.s∧
     F.degreeOf (3:Fin 4) ≤ P.total:=by
 have hR:F.degreeOf (2:Fin 4) ≤ P.s:=by
   have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
     funext i
     fin_cases i <;> rfl
   have hs:=H.s_weight
   rw [hw,wt,MvPolynomial.weightedTotalDegree_piSingle] at hs
   exact hs
 have hY:F.degreeOf (1:Fin 4) ≤ P.ys:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans
     H.ys_weight
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*0 ≤ P.ys at hw
   norm_num at hw
   omega
 have hZ:F.degreeOf (3:Fin 4) ≤ P.total:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans
     H.total_weight
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*1 ≤ P.total at hw
   norm_num at hw
   omega
 exact ⟨hY,hR,hZ⟩
end ResidualSupportData
end
end ProximityPrize.SubmissionLower.RCN275
end PackedLegacy_E8

/-! Packed from ProximityPrize.SubmissionLower.B. -/
section PackedLegacy_B
namespace ProximityPrize.SubmissionLower.RCN159
open scoped Classical
open RCN136 RCN231 RCN319 RCN313 RCN065 RCN238 RCN160 RCN157 RCN163 RCN166 RCN156 RCN275 RCN234 RCN094 RCN095 RCN125
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega]
local instance _root_.ProximityPrize.SubmissionLower.RCN159.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN159.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN159.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure ResidualStage
   (phi:Polynomial K →+*Omega) (Gamma:Finset K) (x:Iota → K)
   (p e:ℕ) [CharP Omega p] (flag:FlagDegree) (d:ℕ)
   (support:ResidualSupportParameters:=
     ResidualSupportParameters.acceptedSupport) where
 nodes:Finset Iota
 u0:Iota → K
 u1:Iota → K
 selected:K → Polynomial K
 F:Poly4 K
 G:Poly3 Omega
 irreducible_G:Irreducible G
 G_dvd_surface:G∣surfaceMap phi F
 y_dependent:0 < G.degreeOf 1
 regular_proper:¬ G∣surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)
 flag_support:RCN095.PolynomialInFlag flag G
 surface_s_weight:wt residualSWeights F ≤ support.s
 surface_ys_weight:wt residualYSWeights F ≤ support.ys
 surface_total_weight:wt residualTotalWeights F ≤ support.total
 x_injective:Set.InjOn x nodes
 degree_le:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d
 solution:∀ gamma∈Gamma,
   specialization K (selected gamma) gamma F=0
 regular:∀ gamma∈Gamma,
   MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
       (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0
 on_component:∀ gamma∈Gamma,
   MvPolynomial.eval (selectedPoint phi selected gamma) G=0
 no_large_pencil:NoLargeSelectedPencil selected Gamma d e
 characteristic_bound:d < p
namespace ResidualStage
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p] {flag:FlagDegree} {d:ℕ}
 {support:ResidualSupportParameters}
def componentIdeal (S:ResidualStage phi Gamma x p e flag d support):
   Ideal (Poly3 Omega):=Ideal.span {S.G}
def identities (S:ResidualStage phi Gamma x p e flag d support):Finset Iota:=
 identityNodes phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
def Agrees (S:ResidualStage phi Gamma x p e flag d support)
   (gamma:K) (i:Iota):Prop:=
 (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i
local instance  _root_.ProximityPrize.SubmissionLower.RCN159.ResidualStage.instDecidableAgrees (S:ResidualStage phi Gamma x p e flag d support):
   ∀ gamma i,Decidable (S.Agrees gamma i):=fun _ _↦Classical.propDecidable _
def agreementFiber (S:ResidualStage phi Gamma x p e flag d support)
   (gamma:K):Finset Iota:=
 S.nodes.filter (S.Agrees gamma)
theorem componentIdeal_isPrime
   (S:ResidualStage phi Gamma x p e flag d support):S.componentIdeal.IsPrime:=by
 exact Ideal.isPrime_span_singleton_of_prime S.irreducible_G.prime
theorem surface_mem_componentIdeal
   (S:ResidualStage phi Gamma x p e flag d support):
   surfaceMap phi S.F∈S.componentIdeal:=by
 exact Ideal.mem_span_singleton.mpr S.G_dvd_surface
theorem regularity_not_mem_componentIdeal
   (S:ResidualStage phi Gamma x p e flag d support):
   surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F)∉
     S.componentIdeal:=by
 intro h
 exact S.regular_proper (Ideal.mem_span_singleton.mp h)
theorem selected_point_ideal
   (S:ResidualStage phi Gamma x p e flag d support)
   {gamma:K} (hgamma:gamma∈Gamma):
   S.componentIdeal ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom:=by
 change Ideal.span {S.G} ≤
   RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom
 rw [Ideal.span_le]
 intro Q hQ
 simp only [Set.mem_singleton_iff] at hQ
 subst Q
 exact S.on_component gamma hgamma
end ResidualStage
end
end ProximityPrize.SubmissionLower.RCN159
end PackedLegacy_B

/-! Packed from ProximityPrize.SubmissionLower.D8. -/
section PackedLegacy_D8
namespace ProximityPrize.SubmissionLower.RCN221
open scoped Classical BigOperators
open RCN223 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN238 RCN231 RCN174 RCN319 RCN243 RCN222 RCN266 RCN159 RCN156 RCN275 RCN234 RCN095 RCN214
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable (K:Type) [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN221.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN221.instDecidableEqGenericField :DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def geometricFlag {F:MvPolynomial (Fin 4) K}
   (g:GeometricFactor K F):FlagDegree:=
 ⟨g.1.degreeOf (2:Fin 3),g.1.degreeOf (0:Fin 3),
   g.1.degreeOf (1:Fin 3)⟩
theorem polynomialIn_geometricFlag {F:MvPolynomial (Fin 4) K}
   (g:GeometricFactor K F):PolynomialInFlag (geometricFlag K g) g.1:=by
 intro d hd
 have h0:=MvPolynomial.monomial_le_degreeOf (0:Fin 3) hd
 have h1:=MvPolynomial.monomial_le_degreeOf (1:Fin 3) hd
 have h2:=MvPolynomial.monomial_le_degreeOf (2:Fin 3) hd
 change d 1 ≤ g.1.degreeOf 1∧
   d 0+d 1 ≤ g.1.degreeOf 0+g.1.degreeOf 1∧
   d 0+d 1+d 2 ≤
     g.1.degreeOf 2+g.1.degreeOf 0+g.1.degreeOf 1
 omega
variable {Iota:Type}
local instance _root_.ProximityPrize.SubmissionLower.RCN221.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
def geometricResidualStageOfSupport
   (support:ResidualSupportParameters)
   {pchar errorCap degree:ℕ} [CharP K pchar]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf (2:Fin 4))
   (hRsmall:F.degreeOf (2:Fin 4) < pchar)
   (hsupport:ResidualSupportData support F)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ degree)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma degree errorCap)
   (hdegreeChar:degree < pchar)
   (g:GeometricFactor K F):
   letI:CharP (GenericField K) pchar:=genericField_charP K pchar
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K F selected Gamma g) x pchar errorCap
     (geometricFlag K g) degree support:=by
 classical
 letI:CharP (GenericField K) pchar:=genericField_charP K pchar
 have hgspec:=surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
 have hgirred:=hgspec.1
 have hgdiv:=hgspec.2
 have hgate:=geometric_factor_regular_gate K (GenericField K) F hF pchar
   hRpos hRsmall g.1 hgirred
   (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
 have hsub:=geometricSeeds_subset K F selected Gamma g
 exact {
   nodes:=nodes
   u0:=u0
   u1:=u1
   selected:=selected
   F:=F
   G:=g.1
   irreducible_G:=hgirred
   G_dvd_surface:=hgdiv
   y_dependent:=hgate.1
   regular_proper:=by
     simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
   flag_support:=polynomialIn_geometricFlag K g
   surface_s_weight:=hsupport.s_weight
   surface_ys_weight:=hsupport.ys_weight
   surface_total_weight:=hsupport.total_weight
   x_injective:=hinj
   degree_le:=fun gamma hgamma↦hdegree gamma (hsub hgamma)
   solution:=fun gamma hgamma↦hsolutions gamma (hsub hgamma)
   regular:=fun gamma hgamma↦
     selectedPoint_regular_of_specialization K F selected gamma
       (hregular gamma (hsub hgamma))
   on_component:=fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2
   no_large_pencil:=noLargeSelectedPencil_mono selected Gamma _ degree errorCap
     hsub hnoPencil
   characteristic_bound:=hdegreeChar
 }
end
end ProximityPrize.SubmissionLower.RCN221
end PackedLegacy_D8

end Compact_PackedLegacyCore1

section Compact_AsymmetricHelper
/-!
The proper-cut argument uses agreement polynomials of the regular carrier F.
The auxiliary polynomial T supplies the intersection but does not supply an
agreement polynomial. Consequently, only the carrier's agreement degrees
enter the counting numerator; a maximum with the helper's degrees is unneeded.
The proof below specializes the inherited regular-pair proof at this sharper
agreement vector.
-/

namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174
  RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K] {ι : Type*}
local instance  _root_.ProximityPrize.SubmissionLower.AsymmetricHelper.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.AsymmetricHelper.instDecidableEq_proximityPrize_1 : DecidableEq ι := Classical.decEq ι

theorem regularPairSeeds_bound_left
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hrel:IsRelPrime Q T) (F:RegularIndex Q)
   (p:ℕ) [CharP K p]
   (hFY:F.1.degreeOf 1 ≤ P.leftY)
   (hFR:F.1.degreeOf 2 ≤ P.leftR)
   (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
     (P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 classical
 let phi:=polynomialEmbedding K
 let Delta:=regularPairSeeds Q T selected Gamma F
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFspec:=positiveRFactors_spec Q F.1 F.2
 have hFne:F.1≠0:=hFspec.1.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=regularPairSeeds_subset Q T selected Gamma F
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RegularSolution F.1 (selected gamma) gamma∧
       specialization K (selected gamma) gamma T=0:=
   regularPairSeeds_data Q T selected Gamma F gamma hgamma
 have hcover:=card_le_sum_geometricSeeds K F.1 hFne selected Delta
   (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=genericField_charP K p
 have hsingle (g:GeometricFactor K F.1):
     (geometricSeeds K F.1 selected Delta g).card*P.gap ≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=surfaceFactors_spec phi F.1 g.1 g.2
   have hsub:=geometricSeeds_subset K F.1 selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=geometricFactor_degree_le K F.1 hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (surfaceMap_degreeOf_le phi T 0).trans hTY
     · exact (surfaceMap_degreeOf_le phi T 1).trans hTR
     · exact (surfaceMap_degreeOf_le phi T 2).trans hTZ
   have hcarrierSmall:∀ i,capAt carrierCap i < p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=actual_characteristic_gates g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F.1)≠0:=by
     intro gamma hgamma
     exact selectedPoint_regular_of_specialization K F.1 selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [selectedPoint_surface_evaluation,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀ j,
       (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
         regularCapAt P.leftAgreement j:=by
     have h:=surface_agreement_caps phi F.1 P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j => (j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
           capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [agreementPolynomial] using h j
     fin_cases j <;> exact hj
   have hcount:=proper_cut_seed_bound phi F.1 g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (geometricFactor_not_dvd_second Q T hrel F g.1 g.2)
     selected (geometricSeeds K F.1 selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma => hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma => (hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma => (Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma => hagreement gamma (hDeltaSub (hsub hgamma)))
     (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
       (fun _ hgamma => hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.leftAgreement) (fun node _ => hcap node)
   simpa [hnodes,UnequalParameters.gap] using hcount
 have hbudget (i:Fin 3):=
   sum_coordinateMixedDegree_geometricFactors_le P F.1 T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:GeometricFactor K F.1,∑ i:Fin 3,
         regularCapAt P.leftAgreement i*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap ≤
       (∑ g:GeometricFactor K F.1,
         (geometricSeeds K F.1 selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:GeometricFactor K F.1,
       (geometricSeeds K F.1 selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F.1,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _ => hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.leftAgreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.leftAgreement i*regularCapAt (regularVector P F.1) i)+
       (P.errors+1)*P.gap*regularCapAt (regularVector P F.1) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]

end
end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricHelper


