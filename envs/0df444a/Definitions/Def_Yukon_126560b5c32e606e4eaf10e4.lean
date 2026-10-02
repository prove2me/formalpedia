-- Prove2me | Definitions.Def_Yukon_126560b5c32e606e4eaf10e4
-- name    : Yukon_126560b5c32e606e4eaf10e4
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T20:22:10.689739+00:00
-- url     : https://prove2.me/theorems/1167a06b-8291-4b94-8284-0f3e8f3da340
-- title:
--   LowerFoundation source part 1/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:bootstrap-v25-dc19057f45f4082498c0c69f7169fe824ef4e91f5fb4bde989cfd31f3351833a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYWE4NGRlNDViMzA0YjgyZDI0MTkyYzMwODk3NjgzM2FlNmM1N2IyMmIxZjAxMWJmMmM2NjkyNTM0OTRjNWEwZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmJvb3RzdHJhcC12MjUtZGMxOTA1N2Y0NWY0MDgyNDk4YzBjNjlmNzE2OWZlODI0ZWY0ZTkxZjVmYjRiZGU5ODljZmQzMWYzMzUxODMzYSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzEyNjU2MGI1YzMyZTYwNmU0ZWFmMTBlNCIsInYiOjJ9]

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
/-! Packed from ProximityPrize.SubmissionLower.BG. -/
section PackedLegacy_BG
namespace ProximityPrize.SubmissionLower.RCN130
open scoped Classical BigOperators
open RCN081 RCN136 RCN135 RCN137 RCN222 RCN266 RCN167 RCN156 RCN095
open RCN125 (sWeight ysWeight totalWeight)
open RCN071 RCN234 RCN275 RCN159
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K L:Type} [Field K] [Field L]
def flagFromCaps (total middle inner:ℕ):FlagDegree:=
 ⟨total-middle,middle-inner,inner⟩
theorem flagFromCaps_cumulative (total middle inner:ℕ)
   (hi:inner ≤ middle) (hm:middle ≤ total):
   (flagFromCaps total middle inner).all=inner∧
     (flagFromCaps total middle inner).yz+
       (flagFromCaps total middle inner).all=middle∧
     (flagFromCaps total middle inner).zOnly+
       (flagFromCaps total middle inner).yz+
       (flagFromCaps total middle inner).all=total:=by
 dsimp [flagFromCaps]
 omega
theorem residual_weight_nested (F:MvPolynomial (Fin 4) K):
   wt residualSWeights F ≤ wt residualYSWeights F∧
     wt residualYSWeights F ≤ wt residualTotalWeights F:=by
 constructor
 · apply (weightedTotalDegree_le_iff residualSWeights F _).mpr
   intro d hd
   have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
   rw [weight_fin4] at h ⊢
   simp [wt,residualSWeights,residualYSWeights] at h ⊢
   omega
 · apply (weightedTotalDegree_le_iff residualYSWeights F _).mpr
   intro d hd
   have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
   rw [weight_fin4] at h ⊢
   simp [wt,residualYSWeights,residualTotalWeights] at h ⊢
   omega
theorem surface_weight_nested (G:MvPolynomial (Fin 3) L):
   MvPolynomial.weightedTotalDegree sWeight G ≤
       MvPolynomial.weightedTotalDegree ysWeight G∧
     MvPolynomial.weightedTotalDegree ysWeight G ≤
       MvPolynomial.weightedTotalDegree totalWeight G:=by
 constructor
 · unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro d hd
   exact (show Finsupp.weight sWeight d ≤ Finsupp.weight ysWeight d by
     rw [RCN372.weight_fin3,RCN372.weight_fin3]
     simp [sWeight,ysWeight]).trans (Finset.le_sup hd)
 · unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro d hd
   exact (show Finsupp.weight ysWeight d ≤ Finsupp.weight totalWeight d by
     rw [RCN372.weight_fin3,RCN372.weight_fin3]
     simp [ysWeight,totalWeight]).trans (Finset.le_sup hd)
def originalCumulativeFlag (F:MvPolynomial (Fin 4) K):FlagDegree:=
 flagFromCaps (wt residualTotalWeights F) (wt residualYSWeights F)
   (wt residualSWeights F)
def surfaceCumulativeFlag (G:MvPolynomial (Fin 3) L):FlagDegree:=
 flagFromCaps (MvPolynomial.weightedTotalDegree totalWeight G)
   (MvPolynomial.weightedTotalDegree ysWeight G)
   (MvPolynomial.weightedTotalDegree sWeight G)
abbrev regularCumulativeFlag (Q:MvPolynomial (Fin 4) K) (R:RegularIndex Q):=
 originalCumulativeFlag R.1
abbrev geometricCumulativeFlag (K:Type) [Field K]
   {F:MvPolynomial (Fin 4) K} (g:GeometricFactor K F):=
 surfaceCumulativeFlag g.1
theorem originalCumulativeFlag_cumulative (F:MvPolynomial (Fin 4) K):
   (originalCumulativeFlag F).all=wt residualSWeights F∧
     (originalCumulativeFlag F).yz+(originalCumulativeFlag F).all=
       wt residualYSWeights F∧
     (originalCumulativeFlag F).zOnly+(originalCumulativeFlag F).yz+
       (originalCumulativeFlag F).all=wt residualTotalWeights F:=
 flagFromCaps_cumulative _ _ _ (residual_weight_nested F).1
   (residual_weight_nested F).2
theorem surfaceCumulativeFlag_cumulative (G:MvPolynomial (Fin 3) L):
   (surfaceCumulativeFlag G).all=MvPolynomial.weightedTotalDegree sWeight G∧
     (surfaceCumulativeFlag G).yz+(surfaceCumulativeFlag G).all=
       MvPolynomial.weightedTotalDegree ysWeight G∧
     (surfaceCumulativeFlag G).zOnly+(surfaceCumulativeFlag G).yz+
       (surfaceCumulativeFlag G).all=MvPolynomial.weightedTotalDegree totalWeight G:=
 flagFromCaps_cumulative _ _ _ (surface_weight_nested G).1
   (surface_weight_nested G).2
theorem polynomialIn_surfaceCumulativeFlag (G:MvPolynomial (Fin 3) L):
   PolynomialInFlag (surfaceCumulativeFlag G) G:=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight hd
 have hm:=MvPolynomial.le_weightedTotalDegree ysWeight hd
 have ht:=MvPolynomial.le_weightedTotalDegree totalWeight hd
 rw [RCN372.weight_fin3] at hs hm ht
 simp [sWeight,ysWeight,totalWeight] at hs hm ht
 have hc:=surfaceCumulativeFlag_cumulative G
 change d 1 ≤ (surfaceCumulativeFlag G).all∧
   d 0+d 1 ≤ (surfaceCumulativeFlag G).yz+(surfaceCumulativeFlag G).all∧
   d 0+d 1+d 2 ≤ (surfaceCumulativeFlag G).zOnly+
     (surfaceCumulativeFlag G).yz+(surfaceCumulativeFlag G).all
 rw [hc.2.2,hc.2.1,hc.1]
 exact ⟨hs,hm,ht⟩
theorem surfaceMap_nested_weights_le (phi:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree sWeight (surfaceMap phi F) ≤
       wt residualSWeights F∧
     MvPolynomial.weightedTotalDegree ysWeight (surfaceMap phi F) ≤
       wt residualYSWeights F∧
     MvPolynomial.weightedTotalDegree totalWeight (surfaceMap phi F) ≤
       wt residualTotalWeights F:=by
 refine ⟨?_,?_,?_⟩
 all_goals
   unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro e he
   obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset phi F he)
   rw [RCN372.weight_fin3]
 · have h:=MvPolynomial.le_weightedTotalDegree residualSWeights hd
   rw [weight_fin4] at h
   simpa [wt,sWeight,residualSWeights,Finsupp.tail_apply] using h
 · have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
   rw [weight_fin4] at h
   simpa [wt,ysWeight,residualYSWeights,Finsupp.tail_apply] using h
 · have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
   rw [weight_fin4] at h
   simpa [wt,totalWeight,residualTotalWeights,Finsupp.tail_apply] using h
theorem geometricCumulativeFlag_budgets (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∑ g:GeometricFactor K F,(geometricCumulativeFlag K g).all) ≤
       (originalCumulativeFlag F).all∧
     (∑ g:GeometricFactor K F,((geometricCumulativeFlag K g).yz+
       (geometricCumulativeFlag K g).all)) ≤
       (originalCumulativeFlag F).yz+(originalCumulativeFlag F).all∧
     (∑ g:GeometricFactor K F,((geometricCumulativeFlag K g).zOnly+
       (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all)) ≤
       (originalCumulativeFlag F).zOnly+(originalCumulativeFlag F).yz+
         (originalCumulativeFlag F).all:=by
 let phi:=polynomialEmbedding K
 have hSF:=surfaceMap_ne_zero phi (polynomialEmbedding_injective K) F hF
 have hp:=normalizedFactorSet_product_dvd (surfaceMap phi F) hSF
 have hs:=sum_weightedTotalDegree_le_of_prod_dvd_fin3 sWeight
   (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have hm:=sum_weightedTotalDegree_le_of_prod_dvd_fin3 ysWeight
   (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have ht:=sum_weightedTotalDegree_le_of_prod_dvd_fin3 totalWeight
   (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have hmap:=surfaceMap_nested_weights_le phi F
 have hc:=originalCumulativeFlag_cumulative F
 refine ⟨?_,?_,?_⟩
 · rw [Finset.sum_congr rfl (fun g _↦(surfaceCumulativeFlag_cumulative g.1).1),
     Finset.sum_coe_sort,hc.1]
   exact hs.trans hmap.1
 · rw [Finset.sum_congr rfl (fun g _↦(surfaceCumulativeFlag_cumulative g.1).2.1),
     Finset.sum_coe_sort,hc.2.1]
   exact hm.trans hmap.2.1
 · rw [Finset.sum_congr rfl (fun g _↦(surfaceCumulativeFlag_cumulative g.1).2.2),
     Finset.sum_coe_sort,hc.2.2]
   exact ht.trans hmap.2.2
theorem geometricCumulativeFlag_le_support
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   {P:ResidualSupportParameters} (H:ResidualSupportData P F)
   (g:GeometricFactor K F):
   (geometricCumulativeFlag K g).all ≤ P.s∧
     (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ P.ys∧
     (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
       (geometricCumulativeFlag K g).all ≤ P.total:=by
 have hb:=geometricCumulativeFlag_budgets F hF
 have hc:=originalCumulativeFlag_cumulative F
 rw [hc.2.2,hc.2.1,hc.1] at hb
 refine ⟨?_,?_,?_⟩
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.1.trans H.s_weight)
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.2.1.trans H.ys_weight)
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.2.2.trans H.total_weight)
theorem originalCumulativeFlag_all (F:MvPolynomial (Fin 4) K):
   (originalCumulativeFlag F).all=F.degreeOf 2:=by
 change MvPolynomial.weightedTotalDegree residualSWeights F=_
 have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
   funext i
   fin_cases i <;> simp [residualSWeights]
 rw [hw,MvPolynomial.weightedTotalDegree_piSingle]
theorem regularCumulativeFlag_positive
   (Q:MvPolynomial (Fin 4) K) (R:RegularIndex Q):
   0 < (regularCumulativeFlag Q R).all:=by
 rw [originalCumulativeFlag_all]
 exact (positiveRFactors_spec Q R.1 R.2).2.2
def reflagResidualStage {Iota:Type} {phi:Polynomial K →+*L}
   {Gamma:Finset K} {x:Iota → K} {p e d:ℕ} [CharP L p]
   {oldFlag newFlag:FlagDegree} {support:ResidualSupportParameters}
   (S:ResidualStage phi Gamma x p e oldFlag d support)
   (hflag:PolynomialInFlag newFlag S.G):
   ResidualStage phi Gamma x p e newFlag d support:=
 { S with flag_support:=hflag}
end
end ProximityPrize.SubmissionLower.RCN130
end PackedLegacy_BG

/-! Packed from ProximityPrize.SubmissionLower.AJ. -/
section PackedLegacy_AJ
namespace ProximityPrize.SubmissionLower.RCN302
open RCN100 RCN119
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
namespace Profile
end Profile
theorem coefficientCount_eq_sum_range_of_weighted_cutoff
   (D w L s t:ℕ) (ht:t ≤ L+1) (hD:D ≤ w*t):
   coefficientCount D w L s=
     ∑ i∈Finset.range t,
       ∑ j∈Finset.range (s+1),
         (L+1-i-j)*(D-w*i-(w-1)*j):=by
 have hsplit:L+1=t+(L+1-t):=by omega
 unfold coefficientCount
 rw [hsplit,Finset.sum_range_add]
 have htail:
     (∑ x∈Finset.range (L+1-t),
       ∑ j∈Finset.range (s+1),
         (t+(L+1-t)-(t+x)-j)*
           (D-w*(t+x)-(w-1)*j))=0:=by
   apply Finset.sum_eq_zero
   intro i hi
   apply Finset.sum_eq_zero
   intro j hj
   have hti:t ≤ t+i:=by omega
   have hzero:D-w*(t+i)=0:=
     Nat.sub_eq_zero_of_le (hD.trans (Nat.mul_le_mul_left w hti))
   simp [hzero]
 rw [htail,add_zero]
end ProximityPrize.SubmissionLower.RCN302
end PackedLegacy_AJ

/-! Packed from ProximityPrize.SubmissionLower.L1. -/
section PackedLegacy_L1
namespace ProximityPrize.SubmissionLower.RCN180
open scoped BigOperators
open RCN100 RCN081 RCN234 RCN156
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def reconstructLinear (D w L s:ℕ) :
   (CoefficientIndex D w L s → K) →ₗ[K] Poly4 K where
 toFun:=reconstruct K D w L s
 map_add' θ η:=by
   classical
   simp [reconstruct,Finset.sum_add_distrib]
 map_smul' a θ:=by
   classical
   rw [show reconstruct K D w L s (a • θ) =
       ∑ c:CoefficientIndex D w L s,
         MvPolynomial.monomial (columnExponent c) (a * θ c) by
     simp [reconstruct]]
   change (∑ c:CoefficientIndex D w L s,
     MvPolynomial.monomial (columnExponent c) (a * θ c)) =
     a • (∑ c:CoefficientIndex D w L s,
       MvPolynomial.monomial (columnExponent c) (θ c))
   rw [Finset.smul_sum]
   apply Finset.sum_congr rfl
   intro c hc
   rw [MvPolynomial.smul_monomial]
   simp [smul_eq_mul]
theorem reconstructLinear_injective (D w L s:ℕ) :
   Function.Injective (reconstructLinear (K:=K) D w L s) :=
 reconstruct_injective K D w L s
def reconstructIntoBox (D w L s:ℕ) :
   (CoefficientIndex D w L s → K) →ₗ[K]
     globalCoefficientBox K D w L s :=
 LinearMap.codRestrict (globalCoefficientBox K D w L s)
   (reconstructLinear (K:=K) D w L s)
   (reconstruct_mem_globalCoefficientBox K D w L s)
theorem reconstructIntoBox_injective (D w L s:ℕ) :
   Function.Injective (reconstructIntoBox (K:=K) D w L s):=by
 intro θ η h
 apply reconstructLinear_injective (K:=K) D w L s
 exact congrArg Subtype.val h
def columnIndexOfExponent {D w L s:ℕ} (d:Fin 4 →₀ ℕ)
   (hd:d ∈ globalExponents D w L s):CoefficientIndex D w L s:=by
 rcases hd with ⟨hL,hs,hD⟩
 have hi:d 1 < L + 1:=by omega
 have hj:d 2 < s + 1:=by omega
 have hz:d 3 < L + 1 - d 1 - d 2:=by omega
 have hx:d 0 < D - w * d 1 - (w - 1) * d 2:=by omega
 exact ⟨⟨d 1,hi⟩,⟨⟨d 2,hj⟩,⟨⟨d 3,hz⟩,⟨d 0,hx⟩⟩⟩⟩
theorem columnExponent_columnIndexOfExponent {D w L s:ℕ}
   (d:Fin 4 →₀ ℕ) (hd:d ∈ globalExponents D w L s) :
   columnExponent (columnIndexOfExponent d hd) = d:=by
 rcases hd with ⟨hL,hs,hD⟩
 ext i
 fin_cases i <;> simp [columnIndexOfExponent]
def encodeBox {D w L s:ℕ} (Q:globalCoefficientBox K D w L s) :
   CoefficientIndex D w L s → K :=
 fun c ↦ MvPolynomial.coeff (columnExponent c) Q.1
theorem reconstruct_encodeBox {D w L s:ℕ}
   (Q:globalCoefficientBox K D w L s) :
   reconstruct K D w L s (encodeBox Q) = Q.1:=by
 classical
 ext d
 by_cases hd:d ∈ globalExponents D w L s
 · let c:=columnIndexOfExponent d hd
   have hc:columnExponent c = d :=
     columnExponent_columnIndexOfExponent d hd
   rw [← hc,reconstruct_coeff]
   rfl
 · have hQ:MvPolynomial.coeff d Q.1 = 0:=by
     by_contra hn
     exact hd (Q.2 (MvPolynomial.mem_support_iff.mpr hn))
   have hRmem:=reconstruct_mem_globalCoefficientBox K D w L s (encodeBox Q)
   have hR:MvPolynomial.coeff d
       (reconstruct K D w L s (encodeBox Q)) = 0:=by
     by_contra hn
     exact hd (hRmem (MvPolynomial.mem_support_iff.mpr hn))
   rw [hQ,hR]
theorem reconstructIntoBox_surjective (D w L s:ℕ) :
   Function.Surjective (reconstructIntoBox (K:=K) D w L s):=by
 intro Q
 refine ⟨encodeBox Q,?_⟩
 apply Subtype.ext
 exact reconstruct_encodeBox Q
def reconstructBoxEquiv (D w L s:ℕ) :
   (CoefficientIndex D w L s → K) ≃ₗ[K]
     globalCoefficientBox K D w L s :=
 LinearEquiv.ofBijective (reconstructIntoBox (K:=K) D w L s)
   ⟨reconstructIntoBox_injective (K:=K) D w L s,
     reconstructIntoBox_surjective (K:=K) D w L s⟩
instance globalCoefficientBoxFinite (D w L s:ℕ) :
   Module.Finite K (globalCoefficientBox K D w L s) :=
 Module.Finite.of_surjective (reconstructIntoBox (K:=K) D w L s)
   (reconstructIntoBox_surjective (K:=K) D w L s)
theorem globalCoefficientBox_finrank (D w L s:ℕ) :
   Module.finrank K (globalCoefficientBox K D w L s) =
     coefficientCount D w L s:=by
 rw [← coefficient_index_card D w L s,
   ← Module.finrank_fintype_fun_eq_card K]
 exact LinearEquiv.finrank_eq (reconstructBoxEquiv (K:=K) D w L s).symm
theorem mem_flagGlobalCoefficientBox_iff (Q:Poly4 K)
   (D w L s:ℕ) (hD:0 < D) :
   Q ∈ globalCoefficientBox K D w L s ↔
     wt residualTotalWeights Q ≤ L ∧
     wt residualSWeights Q ≤ s ∧
     wt (contactWeights w) Q ≤ D - 1:=by
 constructor
 · intro h
   refine ⟨?_,?_,?_⟩
   · apply (weightedTotalDegree_le_iff residualTotalWeights Q L).mpr
     intro d hd
     have hq:=h hd
     rw [weight_fin4]
     simp [residualTotalWeights]
     exact hq.1
   · apply (weightedTotalDegree_le_iff residualSWeights Q s).mpr
     intro d hd
     have hq:=h hd
     rw [weight_fin4]
     simp [residualSWeights]
     exact hq.2.1
   · apply (weightedTotalDegree_le_iff (contactWeights w) Q (D - 1)).mpr
     intro d hd
     rw [contact_weight]
     have hq:=(h hd).2.2
     omega
 · rintro ⟨ht,hs,hc⟩ d hd
   have hdt:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
   have hds:=(MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
   have hdc:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hc
   rw [weight_fin4] at hdt hds
   rw [contact_weight] at hdc
   simp [residualTotalWeights] at hdt
   simp [residualSWeights] at hds
   exact ⟨hdt,hds,by omega⟩
theorem residualYS_mul_le_contact_add_slope (Q:Poly4 K)
   (w:ℕ) (hw:1 ≤ w) :
   w * wt residualYSWeights Q ≤
     wt (contactWeights w) Q + wt residualSWeights Q:=by
 by_cases hQ:Q = 0
 · subst Q
   simp [wt,MvPolynomial.weightedTotalDegree]
 obtain ⟨d,hd,heq⟩:=Finset.exists_mem_eq_sup Q.support
   (MvPolynomial.support_nonempty.mpr hQ)
   (Finsupp.weight residualYSWeights)
 have hc:=MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
 have hs:=MvPolynomial.le_weightedTotalDegree residualSWeights hd
 change wt residualYSWeights Q = Finsupp.weight residualYSWeights d at heq
 rw [weight_fin4] at heq hs
 rw [contact_weight] at hc
 simp [residualYSWeights] at heq
 simp [residualSWeights] at hs
 simp only [residualYSWeights,residualSWeights]
 rw [heq]
 have hwsub:w - 1 + 1 = w:=by omega
 have hwmul:w * d 2 = (w - 1) * d 2 + d 2:=by
   calc
     w * d 2 = ((w - 1) + 1) * d 2:=by rw [hwsub]
     _ = (w - 1) * d 2 + d 2:=by ring
 calc
   w * (d 1 + d 2) ≤
       (d 0 + w * d 1 + (w - 1) * d 2) + d 2:=by
     rw [Nat.mul_add,hwmul]
     omega
   _ ≤ wt (contactWeights w) Q + wt residualSWeights Q :=
     Nat.add_le_add hc hs
theorem quotient_mem_flagGlobalCoefficientBox_of_mul_eq
   (Q H R:Poly4 K) (D w L s contactLower totalLower slopeLower:ℕ)
   (hQ:Q ≠ 0) (hH:H ≠ 0) (hR:R ≠ 0)
   (hbox:Q ∈ globalCoefficientBox K D w L s)
   (heq:Q = H * R)
   (hcontact:contactLower ≤ wt (contactWeights w) H)
   (htotal:totalLower ≤ wt residualTotalWeights H)
   (hslope:slopeLower ≤ wt residualSWeights H) :
   R ∈ globalCoefficientBox K (D - contactLower) w
     (L - totalLower) (s - slopeLower):=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have:=(hbox hd).2.2
   omega
 have hc:=(mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hbox
 simp only [wt] at hc hcontact htotal hslope
 have hmulT:=weightedTotalDegree_mul residualTotalWeights H R hH hR
 have hmulS:=weightedTotalDegree_mul residualSWeights H R hH hR
 have hmulC:=weightedTotalDegree_mul (contactWeights w) H R hH hR
 rw [← heq] at hmulT hmulS hmulC
 have hDq:0 < D - contactLower:=by omega
 apply (mem_flagGlobalCoefficientBox_iff R (D - contactLower) w
   (L - totalLower) (s - slopeLower) hDq).mpr
 simp only [wt]
 omega
theorem mem_flagGlobalCoefficientBox_of_dvd
   (F Q:Poly4 K) (D w L s:ℕ)
   (hQ:Q ≠ 0) (hdiv:F ∣ Q)
   (hbox:Q ∈ globalCoefficientBox K D w L s) :
   F ∈ globalCoefficientBox K D w L s:=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have:=(hbox hd).2.2
   omega
 have hc:=(mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hbox
 apply (mem_flagGlobalCoefficientBox_iff F D w L s hD).mpr
 exact ⟨(weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans hc.1,
   (weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans hc.2.1,
   (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hc.2.2⟩
section CommonGCD
local instance _root_.ProximityPrize.SubmissionLower.RCN180.instStrongNormalizationMonoidPoly4 :StrongNormalizationMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance _root_.ProximityPrize.SubmissionLower.RCN180.instNormalizedGCDMonoidPoly4 :NormalizedGCDMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)
def commonGCD {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V):Poly4 K :=
 Finset.univ.gcd (fun i ↦ reconstruct K D w L s (b i).1)
theorem commonGCD_dvd_basis {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) (i:ι) :
   commonGCD V b ∣ reconstruct K D w L s (b i).1:=by
 exact Finset.gcd_dvd (Finset.mem_univ i)
theorem commonGCD_ne_zero {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] [Nonempty ι] (b:Module.Basis ι K V) :
   commonGCD V b ≠ 0:=by
 rw [commonGCD,Finset.gcd_ne_zero_iff]
 let i:ι:=Classical.choice inferInstance
 refine ⟨i,Finset.mem_univ i,?_⟩
 apply reconstruct_ne_zero K D w L s
 intro hi
 apply b.ne_zero i
 exact Subtype.ext hi
theorem commonGCD_dvd {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) (v:V) :
   commonGCD V b ∣ reconstruct K D w L s v.1:=by
 rw [← b.sum_repr v]
 simp only [Submodule.coe_sum,Submodule.coe_smul]
 change commonGCD V b ∣
   reconstructLinear (K:=K) D w L s
     (∑ i,(b.repr v) i • (b i).1)
 rw [map_sum]
 apply Finset.dvd_sum
 intro i hi
 rw [map_smul,MvPolynomial.smul_eq_C_mul]
 exact dvd_mul_of_dvd_right (commonGCD_dvd_basis V b i) _
theorem dvd_commonGCD_iff {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) (F:Poly4 K) :
   F ∣ commonGCD V b ↔
     ∀ v:V,F ∣ reconstruct K D w L s v.1:=by
 constructor
 · intro hF v
   exact hF.trans (commonGCD_dvd V b v)
 · intro hF
   apply Finset.dvd_gcd_iff.mpr
   intro i hi
   exact hF (b i)
end CommonGCD
section LinearQuotient
variable {V:Type*} [AddCommGroup V] [Module K V]
def quotientPolynomial (recon:V →ₗ[K] Poly4 K) (H:Poly4 K)
   (hdiv:∀ v,H ∣ recon v) (v:V):Poly4 K :=
 Classical.choose (hdiv v)
theorem recon_eq_mul_quotientPolynomial
   (recon:V →ₗ[K] Poly4 K) (H:Poly4 K)
   (hdiv:∀ v,H ∣ recon v) (v:V) :
   recon v = H * quotientPolynomial recon H hdiv v :=
 Classical.choose_spec (hdiv v)
def quotientLinear (recon:V →ₗ[K] Poly4 K) (H:Poly4 K)
   (hH:H ≠ 0) (hdiv:∀ v,H ∣ recon v):V →ₗ[K] Poly4 K where
 toFun:=quotientPolynomial recon H hdiv
 map_add' v z:=by
   apply mul_left_cancel₀ hH
   rw [← recon_eq_mul_quotientPolynomial recon H hdiv (v + z),map_add,
     recon_eq_mul_quotientPolynomial recon H hdiv v,
     recon_eq_mul_quotientPolynomial recon H hdiv z,mul_add]
 map_smul' a v:=by
   apply mul_left_cancel₀ hH
   rw [← recon_eq_mul_quotientPolynomial recon H hdiv (a • v),map_smul,
     recon_eq_mul_quotientPolynomial recon H hdiv v]
   simp only [MvPolynomial.smul_eq_C_mul]
   ac_rfl
theorem quotientLinear_injective
   (recon:V →ₗ[K] Poly4 K) (hrecon:Function.Injective recon)
   (H:Poly4 K) (hH:H ≠ 0) (hdiv:∀ v,H ∣ recon v) :
   Function.Injective (quotientLinear recon H hH hdiv):=by
 intro v z hvz
 apply hrecon
 rw [recon_eq_mul_quotientPolynomial recon H hdiv v,
   recon_eq_mul_quotientPolynomial recon H hdiv z]
 exact congrArg (fun Q:Poly4 K ↦ H * Q) hvz
theorem finrank_le_quotient_box
   (recon:V →ₗ[K] Poly4 K) (hrecon:Function.Injective recon)
   (H:Poly4 K) (hH:H ≠ 0) (hdiv:∀ v,H ∣ recon v)
   (W:Submodule K (Poly4 K)) [Module.Finite K W]
   (hmem:∀ v,quotientPolynomial recon H hdiv v ∈ W) :
   Module.finrank K V ≤ Module.finrank K W:=by
 let q:V →ₗ[K] W:=LinearMap.codRestrict W
   (quotientLinear recon H hH hdiv) hmem
 apply LinearMap.finrank_le_finrank_of_injective (f:=q)
 intro v z hvz
 apply quotientLinear_injective recon hrecon H hH hdiv
 exact congrArg Subtype.val hvz
end LinearQuotient
section ConstraintKernel
open RCN119
variable {I:Type*} [Fintype I]
abbrev ConstraintKernel (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :=
 LinearMap.ker (constraintMap K D w L s m nodes u₀ u₁)
def kernelReconstructLinear (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :
   ConstraintKernel (K:=K) D w L s m nodes u₀ u₁ →ₗ[K] Poly4 K :=
 (reconstructLinear (K:=K) D w L s).comp
   (ConstraintKernel (K:=K) D w L s m nodes u₀ u₁).subtype
@[simp] theorem kernelReconstructLinear_apply (D w L s m:ℕ)
   (nodes u₀ u₁:I → K)
   (v:ConstraintKernel (K:=K) D w L s m nodes u₀ u₁) :
   kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁ v =
     reconstruct K D w L s v.1:=rfl
theorem kernelReconstructLinear_injective (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :
   Function.Injective
     (kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁):=by
 intro v z hvz
 apply Subtype.ext
 apply reconstructLinear_injective (K:=K) D w L s
 exact hvz
public theorem nat_sub_le_of_add_eq_of_le {R K C B:ℕ}
   (hsum:R + K = C) (hr:R ≤ B):C - B ≤ K:=by
 apply Nat.sub_le_of_le_add
 rw [← hsum]
 simpa [Nat.add_comm] using Nat.add_le_add_right hr K
theorem constraintKernel_finrank_lower_bound (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :
   coefficientCount D w L s - Fintype.card I * localRankBound m L s ≤
     Module.finrank K
       (ConstraintKernel (K:=K) D w L s m nodes u₀ u₁):=by
 let f:=constraintMap K D w L s m nodes u₀ u₁
 have hsum:=f.finrank_range_add_finrank_ker
 have hrange:Module.finrank K f.range ≤
     Fintype.card I * localRankBound m L s :=
   f.range.finrank_le.trans (globalTarget_finrank_le K m L s)
 have hdom:Module.finrank K (CoefficientIndex D w L s → K) =
     coefficientCount D w L s:=by
   rw [Module.finrank_fintype_fun_eq_card K,coefficient_index_card]
 dsimp [f] at hsum hrange
 rw [hdom] at hsum
 dsimp [ConstraintKernel] at hsum ⊢
 exact nat_sub_le_of_add_eq_of_le hsum hrange
theorem common_divisor_dimension_obstruction
   (D w L s m Dq Lq sq:ℕ) (nodes u₀ u₁:I → K)
   (H:Poly4 K) (hH:H ≠ 0)
   (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u₀ u₁,
     H ∣ kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁ v)
   (hqbox:∀ v:ConstraintKernel (K:=K) D w L s m nodes u₀ u₁,
     quotientPolynomial
       (kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁)
       H hdiv v ∈ globalCoefficientBox K Dq w Lq sq) :
   coefficientCount D w L s - Fintype.card I * localRankBound m L s ≤
     coefficientCount Dq w Lq sq:=by
 have hlo:=constraintKernel_finrank_lower_bound
   (K:=K) D w L s m nodes u₀ u₁
 have hhi:=finrank_le_quotient_box
   (kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁)
   (kernelReconstructLinear_injective (K:=K) D w L s m nodes u₀ u₁)
   H hH hdiv (globalCoefficientBox K Dq w Lq sq) hqbox
 rw [globalCoefficientBox_finrank] at hhi
 exact hlo.trans hhi
end ConstraintKernel
namespace Numeric6733
open RCN119 RCN100 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
end Numeric6733
namespace Caps6733
open ProximityPrize.Benchmark RCN119 RCN100 RCN130 Numeric6733
local instance _root_.ProximityPrize.SubmissionLower.RCN180.Caps6733.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN180.Caps6733.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
end Caps6733
namespace Numeric6734
open RCN119 RCN100 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
end Numeric6734
namespace Caps6734
open ProximityPrize.Benchmark RCN119 RCN100 RCN130 Numeric6734
local instance _root_.ProximityPrize.SubmissionLower.RCN180.Caps6734.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.RCN180.Caps6734.instDecidableEqIndex :DecidableEq IRSProfile.Index:=Classical.decEq _
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
end Caps6734
end
end ProximityPrize.SubmissionLower.RCN180
end PackedLegacy_L1

/-! Packed from ProximityPrize.SubmissionLower.ContactOrderBridge. -/
section PackedLegacy_ContactOrderBridge
namespace ProximityPrize.SubmissionLower.ContactOrderBridge
open scoped BigOperators Pointwise
open RCN081 RCN119 RCN100 RCN122
noncomputable section
section MinimumWeight
variable {K σ:Type*} [Field K]
def AtLeast (w:σ → ℕ) (n:ℕ) (P:MvPolynomial σ K):Prop :=
  ∀ d ∈ P.support, n ≤ Finsupp.weight w d
theorem atLeast_mono (w:σ → ℕ) {m n:ℕ} {P:MvPolynomial σ K}
    (hmn:m ≤ n) (hP:AtLeast w n P):AtLeast w m P:=by
  intro d hd
  exact hmn.trans (hP d hd)
theorem atLeast_sub (w:σ → ℕ) {n:ℕ} {P Q:MvPolynomial σ K}
    (hP:AtLeast w n P) (hQ:AtLeast w n Q):AtLeast w n (P - Q):=by
  change P ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  exact (MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d}).sub_mem hP hQ
theorem atLeast_mul (w:σ → ℕ) {m n:ℕ} {P Q:MvPolynomial σ K}
    (hP:AtLeast w m P) (hQ:AtLeast w n Q):AtLeast w (m + n) (P * Q):=by
  have hset:{d:σ →₀ ℕ | m ≤ Finsupp.weight w d} +
      {d:σ →₀ ℕ | n ≤ Finsupp.weight w d} ⊆
      {d:σ →₀ ℕ | m + n ≤ Finsupp.weight w d}:=by
    rintro _ ⟨d, hd, e, he, rfl⟩
    simpa only [Set.mem_setOf_eq, map_add] using Nat.add_le_add hd he
  change P ∈ MvPolynomial.restrictSupport K {d | m ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  apply MvPolynomial.restrictSupport_mono (R:=K) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hP hQ
theorem atLeast_X (w:σ → ℕ) (i:σ) :
    AtLeast w (w i) (MvPolynomial.X i:MvPolynomial σ K):=by
  classical
  intro d hd
  have he:d = Finsupp.single i 1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp only [Finsupp.weight_single, one_nsmul, le_refl]
theorem atLeast_pderiv (w:σ → ℕ) (i:σ) {n:ℕ} {P:MvPolynomial σ K}
    (hP:AtLeast w n P):AtLeast w (n - w i) (MvPolynomial.pderiv i P):=by
  classical
  intro d hd
  have hbefore:d + Finsupp.single i 1 ∈ P.support:=by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hne:=MvPolynomial.mem_support_iff.mp hd
    apply hne
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have h:=hP _ hbefore
  simp only [map_add, Finsupp.weight_single, one_nsmul] at h
  omega
end MinimumWeight
section LocalCoordinates
variable (K:Type*) [Field K]
abbrev Poly4:=MvPolynomial (Fin 4) K
def localWeights:Fin 4 → ℕ:=![1, 2, 0, 0]
def localVariables (x u₀ u₁:K):Fin 4 → Poly4 K :=
  ![MvPolynomial.X 0 + MvPolynomial.C x,
    MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C u₁ +
      MvPolynomial.X 2 * MvPolynomial.X 0 + MvPolynomial.X 1,
    MvPolynomial.X 2, MvPolynomial.X 3]
def localize (x u₀ u₁:K):Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval (localVariables K x u₀ u₁)
def ContactAtLeast (x u₀ u₁:K) (m:ℕ) (P:Poly4 K):Prop :=
  AtLeast localWeights m (localize K x u₀ u₁ P)
theorem localize_pderiv_R (x u₀ u₁:K) (P:Poly4 K) :
    localize K x u₀ u₁ (MvPolynomial.pderiv (2:Fin 4) P) =
      MvPolynomial.pderiv (2:Fin 4) (localize K x u₀ u₁ P) -
        MvPolynomial.X 0 * MvPolynomial.pderiv (1:Fin 4) (localize K x u₀ u₁ P):=by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [localize]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      ring
  | mul_X P i hP =>
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hP]
      fin_cases i <;> simp [localize, localVariables, MvPolynomial.pderiv_mul] <;> ring
theorem contactAtLeast_pderiv_R (x u₀ u₁:K) (m:ℕ) (P:Poly4 K)
    (hP:ContactAtLeast K x u₀ u₁ m P) :
    ContactAtLeast K x u₀ u₁ (m - 1) (MvPolynomial.pderiv (2:Fin 4) P):=by
  change AtLeast localWeights (m - 1) (localize K x u₀ u₁ (MvPolynomial.pderiv 2 P))
  rw [localize_pderiv_R]
  have hR:=atLeast_pderiv localWeights (2:Fin 4) hP
  have hv:=atLeast_pderiv localWeights (1:Fin 4) hP
  have ht:=atLeast_X (K:=K) localWeights (0:Fin 4)
  have htv:=atLeast_mul localWeights ht hv
  apply atLeast_sub localWeights
  · apply atLeast_mono localWeights (show m - 1 ≤ m - localWeights 2 by
      change m - 1 ≤ m - 0
      omega) hR
  · apply atLeast_mono localWeights (show m - 1 ≤ localWeights 0 + (m - localWeights 1) by
      change m - 1 ≤ 1 + (m - 2)
      omega) htv
theorem specialized_R_derivative_degree (F:Poly4 K) (P:Polynomial K) (γ:K)
    (w d:ℕ) (hP:P.natDegree ≤ w)
    (hF:MvPolynomial.weightedTotalDegree (contactWeights w) F ≤ d)
    (hregular:specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0) :
    (specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)).natDegree + w ≤ d + 1:=by
  classical
  let H:Poly4 K:=MvPolynomial.pderiv (2:Fin 4) F
  have hsupport (e:Fin 4 →₀ ℕ) (he:e ∈ H.support) :
      Finsupp.weight (contactWeights w) e + (w - 1) ≤ d:=by
    have hbefore:e + Finsupp.single (2:Fin 4) 1 ∈ F.support:=by
      apply MvPolynomial.mem_support_iff.mpr
      intro hz
      have hne:=MvPolynomial.mem_support_iff.mp he
      apply hne
      change MvPolynomial.coeff e (MvPolynomial.pderiv (2:Fin 4) F) = 0
      rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
    have hh:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hbefore).trans hF
    simpa [map_add, Finsupp.weight_single, contactWeights] using hh
  have hH:H ≠ 0:=by
    intro hz
    apply hregular
    change specialization K P γ H = 0
    rw [hz, map_zero]
  obtain ⟨e, he⟩:=MvPolynomial.support_nonempty.mpr hH
  have hdrop:w - 1 ≤ d:=by
    have hh:=hsupport e he
    omega
  have hterms:∀ e ∈ H.support,
      (specialization K P γ (MvPolynomial.monomial e (MvPolynomial.coeff e H))).natDegree ≤
        d - (w - 1):=by
    intro e he
    have hw:=hsupport e he
    rw [contact_weight] at hw
    have ht:=specialization_monomial_natDegree_le K P γ w hP e (MvPolynomial.coeff e H)
    omega
  have hdegree:(specialization K P γ H).natDegree ≤ d - (w - 1):=by
    rw [MvPolynomial.as_sum H, map_sum]
    exact Polynomial.natDegree_sum_le_of_forall_le H.support
      (fun e => specialization K P γ (MvPolynomial.monomial e (MvPolynomial.coeff e H))) hterms
  change (specialization K P γ H).natDegree + w ≤ d + 1
  omega
end LocalCoordinates
section KernelBridge
variable (K:Type*) [Field K]
def diagonalWeights:Fin 4 → ℕ:=![1, 1, 0, 0]
def blowupExponent:(Fin 4 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun d:=Finsupp.single 0 (d 0 + d 1) + Finsupp.single 1 (d 1) +
    Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3)
  map_zero':=by simp
  map_add' d e:=by
    ext i
    fin_cases i <;> simp [Finsupp.add_apply] <;> omega
theorem blowupExponent_injective:Function.Injective blowupExponent:=by
  intro d e h
  have hsum:d 0 + d 1 = e 0 + e 1:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 0) h
  have h1:d 1 = e 1:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 1) h
  have h2:d 2 = e 2:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 2) h
  have h3:d 3 = e 3:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 3) h
  have h0:d 0 = e 0:=by omega
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
def contactBlowup:Poly4 K →+* Poly4 K :=
  AddMonoidAlgebra.mapDomainRingHom K blowupExponent
theorem contactBlowup_monomial (d:Fin 4 →₀ ℕ) (a:K) :
    contactBlowup K (MvPolynomial.monomial d a) = MvPolynomial.monomial (blowupExponent d) a:=by
  change AddMonoidAlgebra.mapDomain blowupExponent (AddMonoidAlgebra.single d a) =
    AddMonoidAlgebra.single (blowupExponent d) a
  exact AddMonoidAlgebra.mapDomain_single
@[simp] theorem contactBlowup_C (a:K) :
    contactBlowup K (MvPolynomial.C a) = MvPolynomial.C a:=by
  change contactBlowup K (MvPolynomial.monomial 0 a) = MvPolynomial.monomial 0 a
  rw [contactBlowup_monomial, map_zero]
@[simp] theorem contactBlowup_X (i:Fin 4) :
    contactBlowup K (MvPolynomial.X i) =
      ![MvPolynomial.X 0, MvPolynomial.X 0 * MvPolynomial.X 1,
        MvPolynomial.X 2, MvPolynomial.X 3] i:=by
  change contactBlowup K (MvPolynomial.monomial (Finsupp.single i 1) 1) = _
  rw [contactBlowup_monomial]
  fin_cases i <;> simp [blowupExponent, MvPolynomial.monomial_add_single,
    ← MvPolynomial.X_pow_eq_monomial]
theorem support_contactBlowup (P:Poly4 K) :
    (contactBlowup K P).support = P.support.image blowupExponent:=by
  change (Finsupp.mapDomain blowupExponent (AddMonoidAlgebra.coeff P)).support =
    Finset.image blowupExponent (AddMonoidAlgebra.coeff P).support
  exact Finsupp.mapDomain_support_of_injective blowupExponent_injective _
theorem weight_blowupExponent (d:Fin 4 →₀ ℕ) :
    Finsupp.weight diagonalWeights (blowupExponent d) = Finsupp.weight localWeights d:=by
  rw [weight_fin4, weight_fin4]
  simp [diagonalWeights, localWeights, blowupExponent] <;> omega
theorem atLeast_contactBlowup_iff (m:ℕ) (P:Poly4 K) :
    AtLeast diagonalWeights m (contactBlowup K P) ↔ AtLeast localWeights m P:=by
  classical
  constructor
  · intro h d hd
    have hmem:blowupExponent d ∈ (contactBlowup K P).support:=by
      rw [support_contactBlowup]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    simpa only [weight_blowupExponent] using h _ hmem
  · intro h d hd
    rw [support_contactBlowup] at hd
    obtain ⟨e, he, rfl⟩:=Finset.mem_image.mp hd
    simpa only [weight_blowupExponent] using h e he
@[simp] theorem shiftPlus_X_bridge (i:Fin 3) :
    shiftPlus K (MvPolynomial.X i) =
      ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 1, MvPolynomial.X 2] i:=by
  fin_cases i <;> simp [shiftPlus] <;> rfl
theorem collected_contactBlowup_localize (x u₀ u₁:K) (Q:Poly4 K) :
    MvPolynomial.finSuccEquiv K 3 (contactBlowup K (localize K x u₀ u₁ Q)) =
      Polynomial.map (shiftPlus K).toRingHom (homogenizedTranslation K x u₀ u₁ Q):=by
  classical
  have hC (a:K):MvPolynomial.finSuccEquiv K 3 (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a):=by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX0:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (0:Fin 4)) =
      Polynomial.X:=MvPolynomial.finSuccEquiv_X_zero
  have hX1:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (1:Fin 4)) =
      Polynomial.C (MvPolynomial.X (0:Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j:=(0:Fin 3))
  have hX2:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (2:Fin 4)) =
      Polynomial.C (MvPolynomial.X (1:Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j:=(1:Fin 3))
  have hX3:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (3:Fin 4)) =
      Polynomial.C (MvPolynomial.X (2:Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j:=(2:Fin 3))
  have hgen (i:Fin 4) :
      MvPolynomial.finSuccEquiv K 3
          (contactBlowup K (localize K x u₀ u₁ (MvPolynomial.X i))) =
        Polynomial.map (shiftPlus K).toRingHom
          (homogenizedTranslation K x u₀ u₁ (MvPolynomial.X i)):=by
    fin_cases i <;>
      simp [localize, localVariables, homogenizedTranslation, translationVariables,
        hC, hX0, hX1, hX2, hX3, seedAffine,
        ← MvPolynomial.C_mul_X_eq_monomial, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq] <;> ring
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp [localize, homogenizedTranslation, MvPolynomial.finSuccEquiv_apply,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.map_add, hP, hQ]
  | mul_X P i hP =>
      simpa only [map_mul, Polynomial.map_mul] using congrArg₂ (· * ·) hP (hgen i)
theorem diagonalAtLeast_iff_coeff (m:ℕ) (Q:Poly4 K) :
    AtLeast diagonalWeights m Q ↔
      ∀ (r:ℕ) (d:Fin 3 →₀ ℕ), r + d 0 < m →
        MvPolynomial.coeff d ((MvPolynomial.finSuccEquiv K 3 Q).coeff r) = 0:=by
  classical
  constructor
  · intro h r d hsmall
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_contra hc
    have hw:=h (Finsupp.cons r d) (MvPolynomial.mem_support_iff.mpr hc)
    have hcons:(Finsupp.cons r d) (1:Fin 4) = d 0:=rfl
    rw [weight_fin4] at hw
    simp [diagonalWeights, hcons] at hw
    omega
  · intro h d hd
    have hweight:Finsupp.weight diagonalWeights d = d 0 + d 1:=by
      rw [weight_fin4]
      simp [diagonalWeights]
    by_contra hsmall
    have hlt:d 0 + d.tail 0 < m:=by
      simp only [Finsupp.tail_apply]
      change d 0 + d 1 < m
      omega
    have hz:=h (d 0) d.tail hlt
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hz
    have he:Finsupp.cons (d 0) d.tail = d:=by
      ext i
      fin_cases i <;> simp [Finsupp.tail_apply]
    rw [he] at hz
    exact MvPolynomial.mem_support_iff.mp hd hz
theorem contactAtLeast_iff_block_divisibility (x u₀ u₁:K) (m:ℕ) (Q:Poly4 K) :
    ContactAtLeast K x u₀ u₁ m Q ↔
      ∀ r:ℕ, slopeDifference K ^ (m - r) ∣
        (homogenizedTranslation K x u₀ u₁ Q).coeff r:=by
  change AtLeast localWeights m (localize K x u₀ u₁ Q) ↔ _
  rw [← atLeast_contactBlowup_iff K m (localize K x u₀ u₁ Q), diagonalAtLeast_iff_coeff]
  simp only [collected_contactBlowup_localize, Polynomial.coeff_map]
  constructor
  · intro h r
    apply (contactJet_eq_zero_iff K (m - r) _).mp
    apply (contactJet_eq_zero_iff_coeff K (m - r) _).mpr
    intro d hd
    exact h r d (by omega)
  · intro h r d hd
    have hjet:=(contactJet_eq_zero_iff K (m - r) _).mpr (h r)
    exact (contactJet_eq_zero_iff_coeff K (m - r) _).mp hjet d (by omega)
theorem contactAtLeast_of_mem_kernel {I:Type*} [Fintype I]
    (D w L s m:ℕ) (nodes u₀ u₁:I → K)
    (a:CoefficientIndex D w L s → K)
    (ha:a ∈ LinearMap.ker (constraintMap K D w L s m nodes u₀ u₁)) (i:I) :
    ContactAtLeast K (nodes i) (u₀ i) (u₁ i) m (reconstruct K D w L s a):=by
  apply (contactAtLeast_iff_block_divisibility K (nodes i) (u₀ i) (u₁ i) m _).mpr
  exact RCN101.translated_contact_of_mem_ker
    K D w L s m nodes u₀ u₁ a ha i
end KernelBridge
end
end ProximityPrize.SubmissionLower.ContactOrderBridge
end PackedLegacy_ContactOrderBridge

/-! Packed from ProximityPrize.SubmissionLower.CH. -/
section PackedLegacy_CH
namespace ProximityPrize.SubmissionLower.RCN324
open IsLocalRing
variable {K R:Type*} [CommRing K] [CommRing R] [Algebra K R]
public theorem prime_dvd_factorial:∀ {n p:ℕ},p.Prime → (p∣n.factorial ↔ p ≤ n)
 | 0,_,hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
 | n+1,p,hp => by
     rw [Nat.factorial_succ,hp.dvd_mul,prime_dvd_factorial hp]
     exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
       fun h => (_root_.lt_or_eq_of_le h).elim
         (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
theorem derivation_pow_mul (D:Derivation K R R) (pi u:R) (mu:ℕ)
   (hmu:1 ≤ mu):
   D (pi^mu*u)=
     pi^(mu-1)*((mu:R)*u*D pi+pi*D u):=by
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_pow_mul (D:Derivation K R R) (pi u a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a):
   D (pi^mu*u)=pi^mu*((mu:R)*a*u+D u):=by
 rw [derivation_pow_mul D pi u mu hmu,htangent]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_preserves_divisibility (D:Derivation K R R) (pi a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a) (f:R) (hf:pi^mu∣f):
   pi^mu∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [tangent_pow_mul D pi u a mu hmu htangent]
 exact dvd_mul_right _ _
theorem iterate_pow_mul_expansion (D:Derivation K R R) (pi u:R)
   (mu r:ℕ) (hr:r ≤ mu):
   ∃ error:R,
     (D:R → R)^[r] (pi^mu*u)=
       (mu.descFactorial r:R)*pi^(mu-r)*u*(D pi)^r+
         pi^(mu-r+1)*error:=by
 induction r with
 | zero =>
     refine ⟨0,?_⟩
     simp
 | succ r ih =>
     have hr0:r ≤ mu:=le_trans (Nat.le_succ r) hr
     obtain ⟨error,herror⟩:=ih hr0
     obtain ⟨k,hk⟩:∃ k,mu-r=k+1:=by
       have hpos:0 < mu-r:=Nat.sub_pos_of_lt (Nat.lt_of_succ_le hr)
       exact Nat.exists_eq_succ_of_ne_zero hpos.ne'
     have hnext:mu-(r+1)=k:=by omega
     let q:=D pi
     let nextError:R:=
       (mu.descFactorial r:R)*D u*q^r+
       (mu.descFactorial r:R)*u*(r:R)*q^(r-1)*D q+
       (k+2:R)*q*error+pi*D error
     refine ⟨nextError,?_⟩
     rw [Function.iterate_succ_apply',herror,map_add]
     simp only [D.leibniz,Derivation.leibniz_pow,D.map_natCast,
       nsmul_eq_mul,smul_eq_mul]
     rw [hk,hnext,Nat.descFactorial_succ]
     have hmur:mu-r=k+1:=hk
     push_cast [hmur]
     dsimp only [q,nextError]
     ring
theorem isUnit_add_of_isUnit_of_not_isUnit [IsLocalRing R]
   {a b:R} (ha:IsUnit a) (hb:¬ IsUnit b):IsUnit (a+b):=by
 by_contra hab
 have hnb:¬ IsUnit (-b):=by simpa using hb
 have hs:=IsLocalRing.nonunits_add hab hnb
 apply hs
 simpa [add_assoc] using ha
section DVR
variable [IsDomain R] [IsDiscreteValuationRing R]
theorem addVal_iterate_eq_sub_of_transverse
   (D:Derivation K R R) (pi u:R) (mu r p:ℕ)
   [CharP R p] (hp:p.Prime) (hmu:mu < p) (hr:r ≤ mu)
   (hpi:Irreducible pi) (hu:IsUnit u) (htrans:IsUnit (D pi)):
   IsDiscreteValuationRing.addVal R ((D:R → R)^[r] (pi^mu*u))=mu-r:=by
 obtain ⟨error,herror⟩:=iterate_pow_mul_expansion D pi u mu r hr
 have hdescDvd:mu.descFactorial r∣mu.factorial:=by
   refine ⟨(mu-r).factorial,?_⟩
   rw [mul_comm,Nat.factorial_mul_descFactorial hr]
 have hnot:¬p∣mu.descFactorial r:=by
   intro hd
   have hpf:p∣mu.factorial:=hd.trans hdescDvd
   rw [prime_dvd_factorial hp] at hpf
   omega
 have hc:IsUnit (mu.descFactorial r:R):=
   (CharP.isUnit_natCast_iff hp).2 hnot
 have hlead:IsUnit ((mu.descFactorial r:R)*u*(D pi)^r):=
   (hc.mul hu).mul (htrans.pow r)
 let lead:R:=(mu.descFactorial r:R)*u*(D pi)^r
 have hpiError:¬IsUnit (pi*error):=
   not_isUnit_of_not_isUnit_dvd hpi.not_isUnit (dvd_mul_right pi error)
 have hbracket:IsUnit (lead+pi*error):=
   isUnit_add_of_isUnit_of_not_isUnit hlead hpiError
 have hfactor:
     (D:R → R)^[r] (pi^mu*u)=pi^(mu-r)*(lead+pi*error):=by
   rw [herror]
   simp only [lead]
   ring
 rw [hfactor,IsDiscreteValuationRing.addVal_mul,
   IsDiscreteValuationRing.addVal_pow,
   IsDiscreteValuationRing.addVal_uniformizer hpi,
   IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hbracket]
 simp
end DVR
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one
   [IsDomain R] [IsRegularLocalRing R] (hdim:ringKrullDim R=1):
   IsDiscreteValuationRing R:=by
 have hfin':=(IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
   (inferInstance:IsRegularLocalRing R)
 rw [hdim] at hfin'
 have hfin:Module.finrank (ResidueField R) (CotangentSpace R)=1:=by
   exact_mod_cast hfin'
 exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfin
end ProximityPrize.SubmissionLower.RCN324
end PackedLegacy_CH

/-! Packed from ProximityPrize.SubmissionLower.BI. -/
section PackedLegacy_BI
namespace ProximityPrize.SubmissionLower.RCN133
open Function Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {ι K M:Type*} [Field K] [AddCommGroup M] [Module K M]
theorem finite_iUnion_ssubset
   (s:Finset ι) (p:ι → Submodule K M)
   (h₁:∀ i,p i≠⊤) (h₂:s.card < ENat.card K):
   ⋃ i∈s,(p i:Set M) ⊂ univ:=by
 letI:DecidableEq ι:=Classical.decEq ι
 letI:DecidableEq K:=Classical.decEq K
 induction s using Finset.induction_on with
 | empty => simp
 | insert j s hj hj' =>
   simp only [ssubset_univ_iff] at hj' ⊢
   rcases s.eq_empty_or_nonempty with rfl | hs
   · simpa using! h₁ j
   replace h₂:s.card+1 < ENat.card K:=by simpa [Finset.card_insert_of_notMem hj] using! h₂
   specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
   contrapose hj'
   replace hj':(p j:Set M) ∪ (⋃ i∈s,p i)=univ:=by
     simpa [Finset.mem_insert] using! hj'
   suffices (p j:Set M) ⊆ ⋃ i∈s,p i by rwa [union_eq_right.mpr this] at hj'
   intro x (hx:x∈p j)
   rcases eq_or_ne x 0 with rfl | hx₀
   · simpa using! hs
   obtain ⟨y,hy⟩:∃ y,y∉p j:=by specialize h₁ j;contrapose! h₁;ext;simp [h₁]
   have hy₀:y≠0:=by aesop
   let sxy:={x+t • y | (t:K) (ht:t≠0)}
   have hsxy:sxy ⊆ ⋃ i∈s,p i:=by
     suffices Disjoint sxy (p j) from this.subset_right_of_subset_union <| hj' ▸ sxy.subset_univ
     rw [Set.disjoint_iff]
     rintro-⟨⟨t,ht₀,rfl⟩,ht:x+t • y∈p j⟩
     rw [(p j).add_mem_iff_right hx,(p j).smul_mem_iff ht₀] at ht
     contradiction
   obtain ⟨k,hk,t₁,t₂,ht,ht₁,ht₂⟩:∃ᵉ (k∈s) (t₁:K) (t₂:K),
       t₁≠t₂∧x+t₁ • y∈p k∧x+t₂ • y∈p k:=by
     suffices ∃ᵉ (k∈s) (z₁∈sxy) (z₂∈sxy),z₁≠z₂∧z₁∈p k∧z₂∈p k by
       obtain ⟨k,hk, -,⟨t₁, -,rfl⟩, -,⟨t₂, -,rfl⟩,htne,ht₁,ht₂⟩:=this
       exact ⟨k,hk,t₁,t₂,by aesop,ht₁,ht₂⟩
     choose f hf using fun z:sxy↦mem_iUnion.mp (hsxy z.property)
     have hf':MapsTo f univ s:=fun z _↦by specialize hf z;aesop
     suffices ∃ z₁ z₂,z₁≠z₂∧f z₁=f z₂ by
       obtain ⟨z₁,z₂,hne,heq⟩:=this
       exact ⟨f z₁,hf' (mem_univ _),z₁,z₁.property,z₂,z₂.property,
         Subtype.coe_ne_coe.mpr hne,by specialize hf z₁;simp_all,by specialize hf z₂;aesop⟩
     have key:s.card < sxy.encard:=by
       refine lt_of_add_lt_add_right <| lt_of_lt_of_le h₂ ?_
       have:Injective (fun t:K↦x+t • y):=
         fun t₁ t₂ ht↦smul_left_injective K hy₀ <| by simpa using! ht
       have aux:sxy=((fun t:K↦x+t • y) '' {t | t≠0}):=by ext;simp [sxy]
       rw [aux,this.encard_image,encard_ne_add_one]
     obtain ⟨z₁, -,z₂, -,h⟩:=exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
     exact ⟨z₁,z₂,h⟩
   replace ht:y∈p k:=by
     have:(t₁-t₂) • y∈p k:=by convert sub_mem ht₁ ht₂;module
     refine ((p k).smul_mem_iff ?_).mp this
     rwa [sub_ne_zero]
   replace ht:x∈p k:=by convert sub_mem ht₁ ((p k).smul_mem t₁ ht);simp
   simpa using! ⟨k,hk,ht⟩
theorem exists_avoiding_finite_proper_submodules
   [Finite ι] [Infinite K]
   (p:ι → Submodule K M) (hproper:∀ i,p i≠⊤):
   ∃ x,∀ i,x∉p i:=by
 let _i:Fintype ι:=Fintype.ofFinite ι
 suffices ⋃ i,(p i:Set M) ⊂ univ by
   simpa [ssubset_univ_iff,iUnion_eq_univ_iff] using this
 simpa using finite_iUnion_ssubset Finset.univ p hproper (by simp)
variable {N:Type*} [AddCommGroup N] [Module K N]
variable {σ:Type*} [DecidableEq σ]
def polynomialOfSupport (E:Finset (σ →₀ ℕ)) (c:E → K):
   MvPolynomial σ K:=
 ∑ d:E,MvPolynomial.monomial d.1 (c d)
@[simp] theorem coeff_polynomialOfSupport
   (E:Finset (σ →₀ ℕ)) (c:E → K) (d:σ →₀ ℕ):
   MvPolynomial.coeff d (polynomialOfSupport E c)=
     if hd:d∈E then c ⟨d,hd⟩ else 0:=by
 classical
 rw [show polynomialOfSupport E c=
     ∑ e∈(Finset.univ:Finset E),
       MvPolynomial.monomial e.1 (c e) by simp [polynomialOfSupport]]
 rw [MvPolynomial.coeff_sum]
 simp only [MvPolynomial.coeff_monomial]
 by_cases hd:d∈E
 · simp only [hd,dite_true]
   rw [Finset.sum_eq_single ⟨d,hd⟩]
   · simp
   · intro e _ hne
     have hval:e.1≠d:=by
       intro heq
       apply hne
       exact Subtype.ext heq
     rw [if_neg hval]
   · simp
 · simp only [hd,dite_false]
   apply Finset.sum_eq_zero
   intro e _
   have hval:e.1≠d:=by
     intro heq
     apply hd
     rw [←heq]
     exact e.2
   rw [if_neg hval]
theorem support_polynomialOfSupport_subset
   (E:Finset (σ →₀ ℕ)) (c:E → K):
   (polynomialOfSupport E c).support ⊆ E:=by
 intro d hd
 by_contra hnot
 have hcoeff:=MvPolynomial.mem_support_iff.mp hd
 rw [coeff_polynomialOfSupport,dif_neg hnot] at hcoeff
 exact hcoeff rfl
end
end ProximityPrize.SubmissionLower.RCN133
end PackedLegacy_BI

/-! Packed from ProximityPrize.SubmissionLower.AZ. -/
section PackedLegacy_AZ
namespace ProximityPrize.SubmissionLower
open scoped NNReal ProbabilityTheory
open CoreDefinitions ProximityGap
def AffineLineGivenSetsBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (a:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → F) (S:Finset F) (T:F → Finset ι),
   a < S.card →
   (∀ z∈S,(T z).card ≥ (Fintype.card ι:ℝ)*(1-δ)) →
   (∀ z∈S,
     LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (T z)∈
       LinearCode.projectedCodeSubmod C (T z)) →
   ∃ z∈S,∀ j:Fin 2,
     LinearCode.projectedWord (U j) (T z)∈LinearCode.projectedCodeSubmod C (T z)
theorem mcaError_affineLine_le_of_givenSetsBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (a:ℕ)
   (hgiven:AffineLineGivenSetsBound C δ a):
   mcaError (AffineLineGenerator F) C δ ≤
     ENNReal.ofReal ((a:ℝ)/Fintype.card F):=by
 classical
 unfold mcaError
 refine iSup_le fun U => ?_
 rw [Probability.prob_uniform_eq_ofReal]
 apply ENNReal.ofReal_le_ofReal
 apply div_le_div_of_nonneg_right
 · exact_mod_cast (show
     (Finset.univ.filter (fun z:F =>
       IsMCA (AffineLineGenerator F) C z U δ)).card ≤ a by
     by_contra hnot
     have hlarge:a < (Finset.univ.filter (fun z:F =>
         IsMCA (AffineLineGenerator F) C z U δ)).card:=by omega
     let S:Finset F:=Finset.univ.filter (fun z:F =>
       IsMCA (AffineLineGenerator F) C z U δ)
     have hmem (z:F) (hz:z∈S):
         IsMCA (AffineLineGenerator F) C z U δ:=by
       simpa [S] using hz
     let T:F → Finset ι:=fun z =>
       if hz:z∈S then Classical.choose (hmem z hz) else ∅
     have hTspec (z:F) (hz:z∈S):
         (T z).card ≥ (Fintype.card ι:ℝ)*(1-δ)∧
         LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (T z)∈
           LinearCode.projectedCodeSubmod C (T z)∧
         ∃ j:Fin 2,LinearCode.projectedWord (U j) (T z)∉
           LinearCode.projectedCodeSubmod C (T z):=by
       rcases Classical.choose_spec (hmem z hz) with ⟨hcard,hcomb,hbad⟩
       have hTz:T z=Classical.choose (hmem z hz):=by
         simp only [T,dif_pos hz]
       rw [hTz]
       refine ⟨hcard,?_,hbad⟩
       simpa [AffineLineGenerator,Fin.sum_univ_two] using hcomb
     obtain ⟨z,hzS,hall⟩:=hgiven U S T (by simpa [S] using hlarge)
       (fun z hz => (hTspec z hz).1) (fun z hz => (hTspec z hz).2.1)
     obtain ⟨j,hj⟩:=(hTspec z hzS).2.2
     exact hj (hall j))
 · positivity
open Finset
variable {ι F:Type} [Fintype ι] [DecidableEq ι]
 [Field F] [DecidableEq F]
theorem exists_common_affine_set
   (U p:Fin 2 → ι → F) (T:Finset F) (A:F → Finset ι) (e:ℕ)
   (hT:e+1 < T.card)
   (hAcard:∀ z∈T,Fintype.card ι-e ≤ (A z).card)
   (hEq:∀ z∈T,∀ x∈A z,
     U 0 x+z*U 1 x=p 0 x+z*p 1 x):
   ∃ z∈T,∀ x∈A z,U 0 x=p 0 x∧U 1 x=p 1 x:=by
 classical
 let B:Finset ι:=Finset.univ.filter fun x =>
   U 0 x≠p 0 x∨U 1 x≠p 1 x
 let R:F → Finset ι:=fun z => A z ∩ B
 have hRsub (z:F):R z ⊆ B:=by
   intro x hx
   exact (Finset.mem_inter.mp hx).2
 have hRpair:(↑T:Set F).PairwiseDisjoint R:=by
   rintro z hz w hw hzw
   change Disjoint (R z) (R w)
   rw [Finset.disjoint_left]
   intro x hxz hxw
   have hxAz:x∈A z:=(Finset.mem_inter.mp hxz).1
   have hxAw:x∈A w:=(Finset.mem_inter.mp hxw).1
   have hzEq:=hEq z hz x hxAz
   have hwEq:=hEq w hw x hxAw
   have hmul:(z-w)*(U 1 x-p 1 x)=0:=by
     linear_combination hzEq-hwEq
   have hzw0:z-w≠0:=sub_ne_zero.mpr hzw
   have hrow1:U 1 x=p 1 x:=by
     exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hzw0)
   have hrow0:U 0 x=p 0 x:=by
     rw [hrow1] at hzEq
     exact add_right_cancel hzEq
   have hxB:x∈B:=(Finset.mem_inter.mp hxz).2
   simp only [B,Finset.mem_filter,Finset.mem_univ,true_and] at hxB
   exact hxB.elim (fun h => h hrow0) (fun h => h hrow1)
 have hRlower (z:F) (hz:z∈T):B.card ≤ (R z).card+e:=by
   have hsplit:=Finset.card_inter_add_card_sdiff (A z) B
   have hsdiff:(A z \ B).card ≤ Bᶜ.card:=by
     apply Finset.card_le_card
     intro x hx
     rw [Finset.mem_compl]
     exact (Finset.mem_sdiff.mp hx).2
   rw [Finset.card_compl] at hsdiff
   have ha:=hAcard z hz
   have hbcard:B.card ≤ Fintype.card ι:=Finset.card_le_univ B
   dsimp only [R]
   omega
 have hB:B.card ≤ e:=by
   by_contra hnot
   have heB:e < B.card:=Nat.lt_of_not_ge hnot
   have hsumLower:T.card*(B.card-e) ≤ ∑ z∈T,(R z).card:=by
     calc
       T.card*(B.card-e)=∑ z∈T,(B.card-e):=by
         exact (Finset.sum_const_nat (fun _ _ => rfl)).symm
       _ ≤ ∑ z∈T,(R z).card:=by
         exact Finset.sum_le_sum fun z hz => by
           have:=hRlower z hz
           omega
   have hunionSub:(T.biUnion R).card ≤ B.card:=by
     apply Finset.card_le_card
     intro x hx
     obtain ⟨z,hzT,hxR⟩:=Finset.mem_biUnion.mp hx
     exact hRsub z hxR
   have hunionCard:(T.biUnion R).card=∑ z∈T,(R z).card:=
     Finset.card_biUnion hRpair
   rw [hunionCard] at hunionSub
   have hprod:T.card*(B.card-e) ≤ B.card:=hsumLower.trans hunionSub
   have hdpos:0 < B.card-e:=Nat.sub_pos_of_lt heB
   have htlo:e+2 ≤ T.card:=by omega
   have he_mul:e ≤ e*(B.card-e):=
     Nat.le_mul_of_pos_right e hdpos
   have hstrict:B.card < (e+2)*(B.card-e):=by
     calc
       B.card=e+(B.card-e):=(Nat.add_sub_of_le heB.le).symm
       _ ≤ e*(B.card-e)+(B.card-e):=Nat.add_le_add_right he_mul _
       _ < e*(B.card-e)+2*(B.card-e):=by omega
       _=(e+2)*(B.card-e):=by ring
   have hprodLower:(e+2)*(B.card-e) ≤
       T.card*(B.card-e):=Nat.mul_le_mul_right _ htlo
   omega
 by_contra hno
 push Not at hno
 have hRpos:∀ z∈T,1 ≤ (R z).card:=by
   intro z hz
   obtain ⟨x,hxA,hxnot⟩:=hno z hz
   apply Finset.card_pos.mpr
   refine ⟨x,Finset.mem_inter.mpr ⟨hxA,?_⟩⟩
   simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
   by_cases h0:U 0 x=p 0 x
   · exact Or.inr (hxnot h0)
   · exact Or.inl h0
 have hTsum:T.card ≤ ∑ z∈T,(R z).card:=by
   calc
     T.card=∑ z∈T,1:=by simp
     _ ≤ ∑ z∈T,(R z).card:=Finset.sum_le_sum hRpos
 have hunionSub:(T.biUnion R).card ≤ B.card:=by
   apply Finset.card_le_card
   intro x hx
   obtain ⟨z,hzT,hxR⟩:=Finset.mem_biUnion.mp hx
   exact hRsub z hxR
 rw [Finset.card_biUnion hRpair] at hunionSub
 have hTB:T.card ≤ B.card:=hTsum.trans hunionSub
 omega
def AffineLineAlignmentBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (e a:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → F) (S:Finset F) (A:F → Finset ι),
   a < S.card →
   (∀ z∈S,Fintype.card ι-e ≤ (A z).card) →
   (∀ z∈S,
     LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (A z)∈
       LinearCode.projectedCodeSubmod C (A z)) →
   ∃ p:Fin 2 → ι → F,
     (∀ j,p j∈C)∧
     ∃ T:Finset F,T ⊆ S∧e+1 < T.card∧
       ∀ z∈T,∀ x∈A z,
         U 0 x+z*U 1 x=p 0 x+z*p 1 x
theorem givenSetsBound_of_alignmentBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (e a:ℕ)
   (hsize:∀ A:Finset ι,
     (A.card:ℝ) ≥ (Fintype.card ι:ℝ)*(1-δ) →
     Fintype.card ι-e ≤ A.card)
   (halign:AffineLineAlignmentBound C e a):
   AffineLineGivenSetsBound C δ a:=by
 classical
 intro U S A hS hAcard hcomb
 obtain ⟨p,hpC,T,hTS,hTcard,hEq⟩:=
   halign U S A hS (fun z hz => hsize (A z) (hAcard z hz)) hcomb
 obtain ⟨z,hzT,hz⟩:=
   exists_common_affine_set U p T A e hTcard
     (fun z hz => hsize (A z) (hAcard z (hTS hz))) hEq
 refine ⟨z,hTS hzT,fun j => ?_⟩
 rw [LinearCode.mem_projectedCodeSubmod_iff]
 refine ⟨p j,hpC j,?_⟩
 funext x
 simp only [LinearCode.projectedWord]
 rcases hz x.1 x.2 with ⟨h0,h1⟩
 fin_cases j
 · exact h0
 · exact h1
end ProximityPrize.SubmissionLower
end PackedLegacy_AZ

/-! Packed from ProximityPrize.SubmissionLower.DV. -/
section PackedLegacy_DV
namespace ProximityPrize.SubmissionLower.RCN050
open ProximityPrize.Benchmark
noncomputable section
variable {ι K:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field K] [Fintype K] [DecidableEq K]
def pencilSeeds (seeds:Finset K) (selected:K → Polynomial K)
   (P₀ P₁:Polynomial K):Finset K:=by
 classical
 exact seeds.filter (fun γ => selected γ=P₀+Polynomial.C γ*P₁)
def SelectedNoLargePencilBound (domain:ι ↪ K) (w e B:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → K) (seeds:Finset K) (A:K → Finset ι)
   (selected:K → Polynomial K),
   (∀ γ∈seeds,(selected γ).natDegree ≤ w) →
   (∀ γ∈seeds,Fintype.card ι-e ≤ (A γ).card) →
   (∀ γ∈seeds,∀ i∈A γ,
     (selected γ).eval (domain i)=U 0 i+γ*U 1 i) →
   (∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
     (pencilSeeds seeds selected P₀ P₁).card ≤ e+1) →
   seeds.card ≤ B
theorem degree_lt_succ_of_natDegree_le (P:Polynomial K) (w:ℕ)
   (hdegree:P.natDegree ≤ w):P.degree < ((w+1:ℕ):WithBot ℕ):=by
 rcases eq_or_ne P 0 with hzero | hnonzero
 · simp [hzero]
 · rw [←Polynomial.natDegree_lt_iff_degree_lt hnonzero]
   omega
theorem exists_selected_polynomials
   (domain:ι ↪ K) (w:ℕ) (U:Fin 2 → ι → K)
   (seeds:Finset K) (A:K → Finset ι)
   (hprojected:∀ γ∈seeds,
     LinearCode.projectedWord (fun i => U 0 i+γ*U 1 i) (A γ)∈
       LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w+1)) (A γ)):
   ∃ selected:K → Polynomial K,
     (∀ γ∈seeds,(selected γ).natDegree ≤ w)∧
     (∀ γ∈seeds,∀ i∈A γ,
       (selected γ).eval (domain i)=U 0 i+γ*U 1 i):=by
 classical
 have hexists (γ:K) (hγ:γ∈seeds):∃ P:Polynomial K,
     P.natDegree ≤ w∧∀ i∈A γ,P.eval (domain i)=U 0 i+γ*U 1 i:=by
   have hc:=hprojected γ hγ
   rw [LinearCode.mem_projectedCodeSubmod_iff] at hc
   obtain ⟨c,hcode,hvalue⟩:=hc
   change c∈ReedSolomon.code domain (w+1) at hcode
   rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcode
   obtain ⟨P,hdegree,rfl⟩:=hcode
   refine ⟨P,?_,?_⟩
   · rcases eq_or_ne P 0 with hzero | hnonzero
     · simp [hzero]
     · have hd:P.natDegree < w+1:=
         (Polynomial.natDegree_lt_iff_degree_lt hnonzero).mpr hdegree
       omega
   · intro i hi
     have hh:=congrFun hvalue ⟨i,hi⟩
     simpa [LinearCode.projectedWord, Set.restrict, ReedSolomon.evalOnPoints] using hh.symm
 let selected:K → Polynomial K:=fun γ =>
   if hγ:γ∈seeds then Classical.choose (hexists γ hγ) else 0
 have hspec (γ:K) (hγ:γ∈seeds):
     (selected γ).natDegree ≤ w∧
       ∀ i∈A γ,(selected γ).eval (domain i)=U 0 i+γ*U 1 i:=by
   simpa only [selected,dif_pos hγ] using Classical.choose_spec (hexists γ hγ)
 exact ⟨selected,fun γ hγ => (hspec γ hγ).1,fun γ hγ => (hspec γ hγ).2⟩
theorem exists_large_pencil_of_selected_count
   (domain:ι ↪ K) (w e B:ℕ)
   (hcount:SelectedNoLargePencilBound domain w e B)
   (U:Fin 2 → ι → K) (seeds:Finset K) (A:K → Finset ι)
   (selected:K → Polynomial K) (hlarge:B < seeds.card)
   (hdegree:∀ γ∈seeds,(selected γ).natDegree ≤ w)
   (hcard:∀ γ∈seeds,Fintype.card ι-e ≤ (A γ).card)
   (hagreement:∀ γ∈seeds,∀ i∈A γ,
     (selected γ).eval (domain i)=U 0 i+γ*U 1 i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     e+1 < (pencilSeeds seeds selected P₀ P₁).card:=by
 by_contra hno
 have hsmall:∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
     (pencilSeeds seeds selected P₀ P₁).card ≤ e+1:=by
   intro P₀ P₁ h₀ h₁
   apply Nat.le_of_not_gt
   intro hh
   exact hno ⟨P₀,P₁,h₀,h₁,hh⟩
 have hh:=hcount U seeds A selected hdegree hcard hagreement hsmall
 omega
theorem alignmentBound_of_selected_count
   (domain:ι ↪ K) (w e B:ℕ)
   (hcount:SelectedNoLargePencilBound domain w e B):
   AffineLineAlignmentBound (ReedSolomon.code domain (w+1)) e B:=by
 classical
 intro U seeds A hlarge hcard hprojected
 obtain ⟨selected,hdegree,hagreement⟩:=exists_selected_polynomials domain w U seeds A hprojected
 obtain ⟨P₀,P₁,h₀,h₁,hTcard⟩:=exists_large_pencil_of_selected_count
   domain w e B hcount U seeds A selected hlarge hdegree hcard hagreement
 let T:=pencilSeeds seeds selected P₀ P₁
 have hTsub:T ⊆ seeds:=Finset.filter_subset _ _
 let rows:Fin 2 → ι → K:=
   ![ReedSolomon.evalOnPoints domain P₀,ReedSolomon.evalOnPoints domain P₁]
 refine ⟨rows,?_,T,hTsub,hTcard,?_⟩
 · intro j
   fin_cases j
   · change ReedSolomon.evalOnPoints domain P₀∈ReedSolomon.code domain (w+1)
     exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
       (degree_lt_succ_of_natDegree_le P₀ w h₀)
   · change ReedSolomon.evalOnPoints domain P₁∈ReedSolomon.code domain (w+1)
     exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
       (degree_lt_succ_of_natDegree_le P₁ w h₁)
 · intro γ hγ i hi
   have hpoly:selected γ=P₀+Polynomial.C γ*P₁:=(Finset.mem_filter.mp hγ).2
   have heval:=congrArg (Polynomial.eval (domain i)) hpoly
   have hword:=hagreement γ (hTsub hγ) i hi
   simpa [rows,ReedSolomon.evalOnPoints] using hword.symm.trans heval
end
end ProximityPrize.SubmissionLower.RCN050
end PackedLegacy_DV

/-! Packed from ProximityPrize.SubmissionLower.K7. -/
section PackedLegacy_K7
namespace ProximityPrize.SubmissionLower.RCN175
open RCN174 RCN256 RCN223 ProximityPrize.Benchmark
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
end
end ProximityPrize.SubmissionLower.RCN175
end PackedLegacy_K7

/-! Packed from ProximityPrize.SubmissionLower.GR. -/
section PackedLegacy_GR
namespace ProximityPrize.SubmissionLower.RCN320
open ProximityPrize.Benchmark RCN174 RCN175 RCN256 RCN223 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
end
end ProximityPrize.SubmissionLower.RCN320
end PackedLegacy_GR

/-! Packed from ProximityPrize.SubmissionLower.BF. -/
section PackedLegacy_BF
namespace ProximityPrize.SubmissionLower.RCN128
open ProximityPrize.Benchmark RCN050 RCN174 RCN319 RCN320 RCN238 RCN223
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
local instance _root_.ProximityPrize.SubmissionLower.RCN128.instDecidableEqField :DecidableEq IRSProfile.Field:=Classical.decEq _
theorem challenge_field_characteristic6600:
   CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
end
end ProximityPrize.SubmissionLower.RCN128
end PackedLegacy_BF

/-! Packed from ProximityPrize.SubmissionLower.BY. -/
section PackedLegacy_BY
namespace ProximityPrize.SubmissionLower.RCN179
open scoped BigOperators
open RCN081 RCN167 RCN313 RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem wt_polyG_le_of_R_le_Y
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hF:wt weights F ≤ C):
   wt weights (polyG K F) ≤ C:=by
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
theorem numeratorStep_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F M:Poly4 K) (b A C:ℕ)
   (hRY:weights 2 ≤ weights 1) (hYC:weights 1 ≤ C)
   (hRR:2*weights 2 ≤ C) (hA:weights 2 ≤ A)
   (hF:wt weights F ≤ C) (hM:wt weights M ≤ A):
   wt weights (numeratorStep K F b M) ≤
     A+2*(C-weights 2):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 let Hcap:=C-weights 2
 have hRC:weights 2 ≤ C:=by omega
 have hH:wt weights H ≤ Hcap:=wt_polyH_le weights F C hF
 have hG:wt weights G ≤ C:=
   wt_polyG_le_of_R_le_Y weights hX F C hRY hYC hF
 have hRwt:wt weights R=weights 2:=weighted_X weights 2
 have hRH:weights 2+Hcap=C:=by
   dsimp [Hcap]
   omega
 have hRH2:weights 2 ≤ Hcap:=by
   dsimp [Hcap]
   omega
 have hMX:wt weights (MvPolynomial.pderiv 0 M) ≤ A:=by
   have h:=wt_pderiv_le weights M 0 A hM
   rw [hX,Nat.sub_zero] at h
   exact h
 have hMY:wt weights (MvPolynomial.pderiv 1 M) ≤ A-weights 1:=
   wt_pderiv_le weights M 1 A hM
 have hMR:wt weights (MvPolynomial.pderiv 2 M) ≤ A-weights 2:=
   wt_pderiv_le weights M 2 A hM
 have hHX:wt weights (MvPolynomial.pderiv 0 H) ≤ Hcap:=by
   have h:=wt_pderiv_le weights H 0 Hcap hH
   rw [hX,Nat.sub_zero] at h
   exact h
 have hHY:wt weights (MvPolynomial.pderiv 1 H) ≤ Hcap-weights 1:=
   wt_pderiv_le weights H 1 Hcap hH
 have hHR:wt weights (MvPolynomial.pderiv 2 H) ≤ Hcap-weights 2:=
   wt_pderiv_le weights H 2 Hcap hH
 have hH2:wt weights (H^2) ≤ 2*Hcap:=
   (wt_pow_le weights H 2).trans (Nat.mul_le_mul_left 2 hH)
 have htermX:wt weights (H^2*MvPolynomial.pderiv 0 M) ≤
     A+2*Hcap:=by
   have h:=wt_mul_le weights (H^2) (MvPolynomial.pderiv 0 M)
   omega
 have htermY:wt weights (R*H^2*MvPolynomial.pderiv 1 M) ≤
     A+2*Hcap:=by
   have h1:=wt_mul_le weights R (H^2)
   have h2:=wt_mul_le weights (R*H^2) (MvPolynomial.pderiv 1 M)
   omega
 have htermR:wt weights (G*H*MvPolynomial.pderiv 2 M) ≤
     A+2*Hcap:=by
   have h1:=wt_mul_le weights G H
   have h2:=wt_mul_le weights (G*H) (MvPolynomial.pderiv 2 M)
   omega
 have hinnerX:wt weights (H*MvPolynomial.pderiv 0 H) ≤ 2*Hcap:=by
   have h:=wt_mul_le weights H (MvPolynomial.pderiv 0 H)
   omega
 have hinnerY:wt weights (R*H*MvPolynomial.pderiv 1 H) ≤
     2*Hcap:=by
   have h1:=wt_mul_le weights R H
   have h2:=wt_mul_le weights (R*H) (MvPolynomial.pderiv 1 H)
   omega
 have hinnerR:wt weights (G*MvPolynomial.pderiv 2 H) ≤ 2*Hcap:=by
   have h:=wt_mul_le weights G (MvPolynomial.pderiv 2 H)
   omega
 have hinner:wt weights
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H) ≤ 2*Hcap:=by
   exact (wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le hinnerX hinnerY)) hinnerR)
 have hn:wt weights (((2*b:ℕ):Poly4 K))=0:=wt_natCast weights (2*b)
 have hnM:wt weights (((2*b:ℕ):Poly4 K)*M) ≤ A:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)) M
   omega
 have hlast:wt weights (((2*b:ℕ):Poly4 K)*M*
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)) ≤ A+2*Hcap:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)*M)
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)
   omega
 change wt weights
     (H^2*MvPolynomial.pderiv 0 M+
       R*H^2*MvPolynomial.pderiv 1 M+
       G*H*MvPolynomial.pderiv 2 M-
       ((2*b:ℕ):Poly4 K)*M*
         (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
           G*MvPolynomial.pderiv 2 H)) ≤ A+2*Hcap
 exact (wt_sub_le weights _ _).trans
   (max_le ((wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le htermX htermY)) htermR)) hlast)
theorem numerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C) (b:ℕ):
   wt weights (numerator K F b) ≤
     weights 1+b*(2*(C-weights 2)):=by
 induction b with
 | zero =>
     rw [numerator_zero]
     unfold wt
     rw [weighted_X]
     simp
 | succ b ih =>
     rw [numerator_succ]
     have h:=numeratorStep_wt_le_equal_weight weights hX F
       (numerator K F b) b
       (weights 1+b*(2*(C-weights 2))) C hRY hYC hRR
       (hbase.trans (Nat.le_add_right _ _)) hF ih
     convert h using 1 <;> ring
theorem clearedTaylorNumerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C)
   (w:ℕ) (coeffs:ℕ → K) (x:K):
   wt weights (clearedTaylorNumerator F w coeffs x) ≤
     weights 1+w*(2*(C-weights 2)):=by
 unfold clearedTaylorNumerator
 apply wt_sum_le
 intro j hj
 have hjw:j ≤ w:=by
   have:=Finset.mem_range.mp hj
   omega
 have hM:=numerator_wt_le_equal_weight weights hX F C hRY hYC hRR
   hbase hF j
 have hCM:wt weights (MvPolynomial.C (coeffs j)*numerator K F j) ≤
     weights 1+j*(2*(C-weights 2)):=by
   have hm:=wt_mul_le weights (MvPolynomial.C (coeffs j)) (numerator K F j)
   rw [wt_C,Nat.zero_add] at hm
   exact hm.trans hM
 have hH:wt weights (polyH K F) ≤ C-weights 2:=
   wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*(w-j))) ≤
     2*(w-j)*(C-weights 2):=
   (wt_pow_le weights (polyH K F) (2*(w-j))).trans
     (Nat.mul_le_mul_left _ hH)
 have hSX:=shiftedX_wt_eq_zero weights hX x
 have hSXP:wt weights
     ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
   have hp:=wt_pow_le weights
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) j
   rw [hSX,Nat.mul_zero] at hp
   exact hp
 have h1:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j)
   (polyH K F^(2*(w-j)))
 have h2:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j*
     polyH K F^(2*(w-j)))
   ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j)
 simp only [commonNumeratorTerm]
 apply h2.trans
 calc
   wt weights (MvPolynomial.C (coeffs j)*numerator K F j*
       polyH K F^(2*(w-j)))+
       wt weights ((MvPolynomial.C x-MvPolynomial.X 0:Poly4 K)^j) ≤
       (weights 1+j*(2*(C-weights 2))+
         2*(w-j)*(C-weights 2))+0:=
     Nat.add_le_add (h1.trans (Nat.add_le_add hCM hHP)) hSXP
   _=weights 1+w*(2*(C-weights 2)):=by
     have hjw':j+(w-j)=w:=by omega
     calc
       (weights 1+j*(2*(C-weights 2))+
           2*(w-j)*(C-weights 2))+0=
           weights 1+(j+(w-j))*(2*(C-weights 2)):=by ring
       _=weights 1+w*(2*(C-weights 2)):=by rw [hjw']
theorem agreementNumerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C)
   (w:ℕ) (coeffs:ℕ → K) (x u₀ u₁:K):
   wt weights (agreementNumerator F w coeffs x u₀ u₁) ≤
     max (weights 1) (weights 3)+w*(2*(C-weights 2)):=by
 have hTaylor:=clearedTaylorNumerator_wt_le_equal_weight weights hX F C hRY
   hYC hRR hbase hF w coeffs x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ C-weights 2:=
   wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*w)) ≤
     2*w*(C-weights 2):=
   (wt_pow_le weights (polyH K F) (2*w)).trans
     (Nat.mul_le_mul_left _ hH)
 have hprod:=wt_mul_le weights (affineSeedPolynomial u₀ u₁)
   (polyH K F^(2*w))
 unfold agreementNumerator
 apply (wt_sub_le weights _ _).trans
 apply max_le
 · exact hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _)
 · apply hprod.trans
   calc
     wt weights (affineSeedPolynomial u₀ u₁)+
         wt weights (polyH K F^(2*w)) ≤
         weights 3+2*w*(C-weights 2):=Nat.add_le_add hA hHP
     _ ≤ max (weights 1) (weights 3)+w*(2*(C-weights 2)):=by
       have hz:=Nat.le_max_right (weights 1) (weights 3)
       calc
         weights 3+2*w*(C-weights 2)=
             weights 3+w*(2*(C-weights 2)):=by ring
         _ ≤ max (weights 1) (weights 3)+w*(2*(C-weights 2)):=
           Nat.add_le_add_right hz _
end
end ProximityPrize.SubmissionLower.RCN179
end PackedLegacy_BY

/-! Packed from ProximityPrize.SubmissionLower.Z6. -/
section PackedLegacy_Z6
namespace ProximityPrize.SubmissionLower.RCN164
open scoped Classical
open RCN159 RCN159.ResidualStage RCN213 RCN173 RCN238 RCN095 RCN275
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p] {flag:FlagDegree}
 {support:ResidualSupportParameters}
local instance _root_.ProximityPrize.SubmissionLower.RCN164.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN164.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN164.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN164
end PackedLegacy_Z6

/-! Packed from ProximityPrize.SubmissionLower.U. -/
section PackedLegacy_U
namespace ProximityPrize.SubmissionLower.RCN276
open scoped BigOperators
open RCN174 RCN286 RCN095 RCN266
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
namespace Profile
end Profile
noncomputable section
variable {K:Type} [Field K]
end
end ProximityPrize.SubmissionLower.RCN276
end PackedLegacy_U

/-! Packed from ProximityPrize.SubmissionLower.B8. -/
section PackedLegacy_B8
namespace ProximityPrize.SubmissionLower.RCN091
open scoped Classical
open RCN159 RCN164 RCN213 RCN275 RCN276 RCN238 RCN095
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance _root_.ProximityPrize.SubmissionLower.RCN091.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN091.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN091
end PackedLegacy_B8

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier13 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.EN. -/
section PackedLegacy_EN
namespace ProximityPrize.SubmissionLower.RCN141
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN167 RCN169 RCN290 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN141.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN141.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN141
end PackedLegacy_EN

/-! Packed from ProximityPrize.SubmissionLower.AG. -/
section PackedLegacy_AG
namespace ProximityPrize.SubmissionLower.RCN292
open scoped Classical BigOperators
open RCN286 RCN169 RCN167 RCN290 RCN293 RCN174 RCN319 RCN081 RCN238 RCN243 RCN291 RCN318 RCN172 RCN294
noncomputable section
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN292.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev TightParameters:=RCN318.TightParameters
namespace TightParameters
theorem implicitVector_budgets_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p) (hw:1 ≤ P.w):
   (∑ q:ImplicitIndex Q,(implicitVector Q q).y) ≤ P.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).r) ≤
       2*P.implicitYCap*P.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).z) ≤ P.implicitYCap:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 have hb:=implicitPair_input_budgets (singularAuxiliary Q) hJ
   (P.kappa*P.D) P.w P.algebraicCap (by omega) hJbox
 simpa only [implicitVector,Finset.sum_coe_sort,
   RCN318.TightParameters.implicitYCap] using hb
theorem exceptionalSeeds_bound_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hj:1 ≤ P.algebraicCap)
   (hjSmall:P.algebraicCap < p)
   (selected:K → Polynomial K) (Gamma:Finset K):
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
     2*P.algebraicCap^2:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=
   Nat.eq_zero_of_le_zero
     (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
 have hJY:(singularAuxiliary Q).degreeOf 1 ≤ P.algebraicCap:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hh:=(hJbox hd).1
   omega
 have hJZ:(singularAuxiliary Q).degreeOf 3 ≤ P.algebraicCap:=
   degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
 exact exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR
   P.algebraicCap p hj hjSmall hJY hJZ Gamma selected
variable {Iota:Type}
local instance _root_.ProximityPrize.SubmissionLower.RCN292.TightParameters.instDecidableEq :DecidableEq Iota:=Classical.decEq Iota
theorem implicitSeeds_pair_bound_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors)
   (q:ImplicitIndex Q):
   (implicitSeeds Q selected Gamma q).card*P.gap ≤
     (P.n-P.w)*dot P.agreement (implicitVector Q q)+
       (P.errors+1)*P.gap*(implicitVector Q q).z:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 obtain ⟨_hA,hG,hGR,hAbox,hGbox,hproper⟩:=
   implicitPair_data (singularAuxiliary Q) hJ
     (P.kappa*P.D) P.w P.algebraicCap hw hDw hJbox q.1 q.2
 have hsub:=implicitSeeds_subset Q selected Gamma q
 have hpair:=implicit_pair_seed_bound q.1.1 q.1.2 hG hGR hproper
   (P.kappa*P.D) P.w P.implicitYCap P.algebraicCap
   p P.n P.a P.errors hAbox hGbox rfl selected
   (implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
   hw hchar hwa han hjYSmall hjZSmall hmixedSmall
   (fun gamma hgamma => hdegree gamma (hsub hgamma))
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
   (fun gamma hgamma => hagreement gamma (hsub hgamma))
   (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors hsub hnoPencil)
 simpa [implicitVector,
   RCN318.TightParameters.agreement,
   RCN318.TightParameters.errors,
   RCN318.TightParameters.gap,dot] using hpair
theorem singularSeeds_tight_gap_bound
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hj:1 ≤ P.algebraicCap)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (singularSeeds Q selected Gamma).card*P.gap ≤ P.tightNumerator:=by
 have hcaps:=P.implicitVector_budgets_of_profile Q hQ hbox hs hsSmall hw
 have hexc:=P.exceptionalSeeds_bound_of_profile Q hQ hbox hs hsSmall
   hj hjZSmall selected Gamma
 have hsum:=P.with_exceptions_bound
   (fun q:ImplicitIndex Q => (implicitSeeds Q selected Gamma q).card)
   (implicitVector Q)
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
   hcaps.1 hcaps.2.1 hcaps.2.2
   (P.implicitSeeds_pair_bound_of_profile Q hQ hbox hs hsSmall hw hchar
     hDw hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
     hinj hnodes hdegree hagreement hnoPencil)
   hexc
 exact (Nat.mul_le_mul_right P.gap
   (singularSeeds_card_le_sum Q selected Gamma)).trans hsum
theorem singularSeeds_count_le_countCap
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hj:1 ≤ P.algebraicCap)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (singularSeeds Q selected Gamma).card ≤ P.countCap:=by
 apply P.count_le_countCap _ (by
   simpa [RCN318.TightParameters.gap] using
     Nat.sub_pos_of_lt hwa)
 exact P.singularSeeds_tight_gap_bound Q hQ hbox hs hsSmall hw hchar hDw
   hj hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
   hinj hnodes hdegree hagreement hnoPencil
end TightParameters
end
end ProximityPrize.SubmissionLower.RCN292
end PackedLegacy_AG

/-! Packed from ProximityPrize.SubmissionLower.J6. -/
section PackedLegacy_J6
namespace ProximityPrize.SubmissionLower.RCN092
open scoped Classical BigOperators
open RCN174 RCN319 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276 RCN141 RCN292
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN092.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN092.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN092
end PackedLegacy_J6

/-! Packed from ProximityPrize.SubmissionLower.GQ. -/
section PackedLegacy_GQ
namespace ProximityPrize.SubmissionLower.RCN317
open scoped Classical BigOperators
open RCN174 RCN319 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276 RCN141 RCN092
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN317.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN317.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN317
end PackedLegacy_GQ

/-! Packed from ProximityPrize.SubmissionLower.AF. -/
section PackedLegacy_AF
namespace ProximityPrize.SubmissionLower.RCN287
open scoped Classical BigOperators
open RCN081 RCN313 RCN136 RCN234 RCN179 RCN095 RCN275 RCN275.ResidualSupportParameters RCN156 RCN174 RCN238 RCN266 RCN159 RCN164 RCN091 RCN276 RCN318 RCN141 RCN317
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
def sharpAgreementDirection (P:ResidualSupportParameters):FlagDegree:=
 ⟨2*(P.total-P.ys),2*(P.ys-P.s)-1,2*P.s-1⟩
def sharpResidualAgreementFlag
   (P:ResidualSupportParameters) (d:ℕ):FlagDegree:=
 ⟨(sharpAgreementDirection P).zOnly*d,
   1+(sharpAgreementDirection P).yz*d,
   (sharpAgreementDirection P).all*d⟩
theorem sharpResidualAgreementFlag_ys
   (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
   (sharpResidualAgreementFlag P d).yz+
       (sharpResidualAgreementFlag P d).all=
     1+d*(2*P.ys-2):=by
 have hcoeff:
     (2*(P.ys-P.s)-1)+(2*P.s-1)=2*P.ys-2:=by
   have hleft:1 ≤ 2*(P.ys-P.s):=by
     have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
     omega
   have hright:1 ≤ 2*P.s:=by
     have:1 ≤ P.s:=P.one_le_s
     omega
   rw [tsub_add_tsub_comm hleft hright]
   have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
     calc
       2*(P.ys-P.s)+2*P.s=2*((P.ys-P.s)+P.s):=by ring
       _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
   rw [hsum]
 simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
 rw [←hcoeff]
 ring
theorem sharpResidualAgreementFlag_total
   (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
   (sharpResidualAgreementFlag P d).zOnly+
       (sharpResidualAgreementFlag P d).yz+
       (sharpResidualAgreementFlag P d).all=
     1+d*(2*P.total-2):=by
 have hcoeff:
     2*(P.total-P.ys)+(2*(P.ys-P.s)-1)+
         (2*P.s-1)=2*P.total-2:=by
   have hmiddle:
       (2*(P.ys-P.s)-1)+(2*P.s-1)=
         2*P.ys-2:=by
     have hleft:1 ≤ 2*(P.ys-P.s):=by
       have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
       omega
     have hright:1 ≤ 2*P.s:=by
       have:1 ≤ P.s:=P.one_le_s
       omega
     rw [tsub_add_tsub_comm hleft hright]
     have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
       calc
         2*(P.ys-P.s)+2*P.s=
             2*((P.ys-P.s)+P.s):=by ring
         _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
     rw [hsum]
   rw [Nat.add_assoc,hmiddle]
   have htwo:2 ≤ 2*P.ys:=by
     have:1 ≤ P.ys:=P.one_le_s.trans P.s_le_ys
     omega
   rw [←Nat.add_sub_assoc htwo]
   have hsum:2*(P.total-P.ys)+2*P.ys=2*P.total:=by
     calc
       2*(P.total-P.ys)+2*P.ys=
           2*((P.total-P.ys)+P.ys):=by ring
       _=2*P.total:=by rw [Nat.sub_add_cancel P.ys_le_total]
   rw [hsum]
 simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
 rw [←hcoeff]
 ring
variable {K Omega:Type} [Field K] [Field Omega]
theorem sharp_agreement_weight_bounds
   {P:ResidualSupportParameters} {F:MvPolynomial (Fin 4) K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   (agreementNumerator F d coeffs x u0 u1).degreeOf (2:Fin 4) ≤
       d*(2*P.s-1)∧
     wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.ys-2)∧
     wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.total-2):=by
 obtain ⟨hY,hR,hZ⟩:=H.coordinate_bounds
 refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
   P.one_le_s hY hR hZ d coeffs x u0 u1).2.1,?_,?_⟩
 · have h:=agreementNumerator_wt_le_equal_weight residualYSWeights rfl
     F P.ys (by change 1 ≤ 1;norm_num)
     (by change 1 ≤ P.ys;exact P.one_le_s.trans P.s_le_ys)
     (by change 2*1 ≤ P.ys;simpa using P.two_le_ys)
     (by change 1 ≤ 1;norm_num) H.ys_weight d coeffs x u0 u1
   have hcoeff:2*(P.ys-1)=2*P.ys-2:=by omega
   apply h.trans_eq
   change max 1 0+d*(2*(P.ys-1))=
     1+d*(2*P.ys-2)
   rw [hcoeff]
   norm_num
 · have htotalTwo:2 ≤ P.total:=P.two_le_ys.trans P.ys_le_total
   have honeTotal:1 ≤ P.total:=
     P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
   have h:=agreementNumerator_wt_le_equal_weight residualTotalWeights rfl
     F P.total (by change 1 ≤ 1;norm_num)
     (by change 1 ≤ P.total;exact honeTotal)
     (by change 2*1 ≤ P.total;simpa using htotalTwo)
     (by change 1 ≤ 1;norm_num) H.total_weight d coeffs x u0 u1
   have hcoeff:2*(P.total-1)=2*P.total-2:=by omega
   apply h.trans_eq
   change max 1 1+d*(2*(P.total-1))=
     1+d*(2*P.total-2)
   rw [hcoeff]
   norm_num
theorem surfaceMap_agreement_in_sharp_flag
   {P:ResidualSupportParameters} (hsy:P.s < P.ys)
   (phi:Polynomial K →+*Omega) {F:MvPolynomial (Fin 4) K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   PolynomialInFlag (sharpResidualAgreementFlag P d)
     (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
 obtain ⟨hR,hYS,hTotal⟩:=sharp_agreement_weight_bounds H
   d coeffs x u0 u1
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=
   (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal:=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0*0+q 1*1+q 2*1+q 3*0 ≤
   1+d*(2*P.ys-2) at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1 ≤
   1+d*(2*P.total-2) at hqTotal
 norm_num at hqYS hqTotal
 have hqR':q 2 ≤ (sharpResidualAgreementFlag P d).all:=by
   change q 2 ≤ (2*P.s-1)*d
   rw [Nat.mul_comm]
   exact hqR
 change q 2 ≤ (sharpResidualAgreementFlag P d).all∧
   q 1+q 2 ≤ (sharpResidualAgreementFlag P d).yz+
     (sharpResidualAgreementFlag P d).all∧
   q 1+q 2+q 3 ≤ (sharpResidualAgreementFlag P d).zOnly+
     (sharpResidualAgreementFlag P d).yz+
     (sharpResidualAgreementFlag P d).all
 refine ⟨hqR',?_,?_⟩
 · rw [sharpResidualAgreementFlag_ys P hsy]
   exact hqYS
 · rw [sharpResidualAgreementFlag_total P hsy]
   exact hqTotal
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance _root_.ProximityPrize.SubmissionLower.RCN287.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN287.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN287
end PackedLegacy_AF

/-! Packed from ProximityPrize.SubmissionLower.N7. -/
section PackedLegacy_N7
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN234 RCN179
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def vectorNumerator (F P:Poly K):Poly K :=
 polyH K F * MvPolynomial.pderiv (0:Fin 4) P +
   MvPolynomial.X (2:Fin 4) * polyH K F * MvPolynomial.pderiv (1:Fin 4) P +
   polyG K F * MvPolynomial.pderiv (2:Fin 4) P
theorem vectorNumerator_surface (F:Poly K):vectorNumerator F F = 0:=by
 unfold vectorNumerator polyG polyH
 ring
theorem vectorNumerator_mul (F P Q:Poly K) :
   vectorNumerator F (P * Q) = P * vectorNumerator F Q + Q * vectorNumerator F P:=by
 simp only [vectorNumerator,MvPolynomial.pderiv_mul]
 ring
theorem vectorNumerator_sub (F P Q:Poly K) :
   vectorNumerator F (P - Q) = vectorNumerator F P - vectorNumerator F Q:=by
 simp only [vectorNumerator,map_sub]
 ring
theorem numeratorStep_eq_vector (F P:Poly K) (b:ℕ) :
   numeratorStep K F b P =
     polyH K F * vectorNumerator F P -
       ((2 * b:ℕ):Poly K) * P * vectorNumerator F (polyH K F):=by
 unfold numeratorStep clearedStep vectorNumerator
 ring
theorem numeratorStep_sub (F P Q:Poly K) (b:ℕ) :
   numeratorStep K F b (P - Q) = numeratorStep K F b P - numeratorStep K F b Q:=by
 simp only [numeratorStep_eq_vector,vectorNumerator_sub]
 ring
theorem numeratorStep_mul_surface (F Q:Poly K) (b:ℕ) :
   numeratorStep K F b (F * Q) = F * numeratorStep K F b Q:=by
 simp only [numeratorStep_eq_vector,vectorNumerator_mul,vectorNumerator_surface,
   mul_zero,add_zero]
 ring
theorem numeratorStep_congr (F P Q:Poly K) (b:ℕ) (h:F ∣ P - Q) :
   F ∣ numeratorStep K F b P - numeratorStep K F b Q:=by
 obtain ⟨T,hT⟩:=h
 refine ⟨numeratorStep K F b T,?_⟩
 rw [← numeratorStep_sub,hT,numeratorStep_mul_surface]
theorem vectorNumerator_R_degree_bound (F P:Poly K) (a s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   (vectorNumerator F P).degreeOf (2:Fin 4) ≤ a + s:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s - 1 :=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s + 1 :=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) P a hP
 have hPY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) P a hP
 have hPR:=pderiv_same_degree_bound (2:Fin 4) P a hP
 have hx:(H * MvPolynomial.pderiv (0:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   have h:=degree_mul_bound (2:Fin 4) hH hPX
   omega
 have hy:(R * H * MvPolynomial.pderiv (1:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   have h:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH) hPY
   omega
 have hr:(G * MvPolynomial.pderiv (2:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   by_cases ha:a = 0
   · have hz:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) P (by simpa [ha] using hP)
     simp [hz]
   · have h:=degree_mul_bound (2:Fin 4) hG hPR
     omega
 exact degree_add_bound (2:Fin 4) (degree_add_bound (2:Fin 4) hx hy) hr
theorem pderiv_eq_zero_of_wt_lt (weights:Fin 4 → ℕ) (P:Poly K) (i:Fin 4)
   (hP:wt weights P < weights i):MvPolynomial.pderiv i P = 0:=by
 apply MvPolynomial.support_eq_empty.mp
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro d hd
 have hh:=MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 change Finsupp.weight weights d + weights i ≤ wt weights P at hh
 omega
def excessFactor (F P:Poly K) (s b:ℕ):Poly K :=
 (s:Poly K) *
   ((s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P (2 * b * (s - 1))) -
     ((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
         liftedCoefficient P (2 * b * (s - 1)))
def reductionMultiplier (F P:Poly K) (s b:ℕ):Poly K :=
 excessFactor F P s b * MvPolynomial.X (2:Fin 4) ^ ((2 * b + 1) * (s - 1))
def reducedStep (F P:Poly K) (s b:ℕ):Poly K :=
 numeratorStep K F b P - reductionMultiplier F P s b * F
def reducedNumerator (F:Poly K) (s:ℕ):ℕ → Poly K
 | 0 => MvPolynomial.X (1:Fin 4)
 | b + 1 => reducedStep F (reducedNumerator F s b) s b
@[simp] theorem reducedNumerator_zero (F:Poly K) (s:ℕ) :
   reducedNumerator F s 0 = MvPolynomial.X (1:Fin 4):=rfl
@[simp] theorem reducedNumerator_succ (F:Poly K) (s b:ℕ) :
   reducedNumerator F s (b + 1) = reducedStep F (reducedNumerator F s b) s b:=rfl
theorem numerator_sub_reduced_dvd (F:Poly K) (s b:ℕ) :
   F ∣ numerator K F b - reducedNumerator F s b:=by
 induction b with
 | zero => simp
 | succ b ih =>
     have hstep:=numeratorStep_congr F (numerator K F b) (reducedNumerator F s b) b ih
     obtain ⟨T,hT⟩:=hstep
     refine ⟨T + reductionMultiplier F (reducedNumerator F s b) s b,?_⟩
     rw [numerator_succ,reducedNumerator_succ,reducedStep]
     linear_combination hT
def reducedCommonNumeratorTerm (F:Poly K) (s w:ℕ) (c:ℕ → K) (x:K)
   (j:ℕ):Poly K :=
 MvPolynomial.C (c j) * reducedNumerator F s j *
   polyH K F ^ (2 * (w - j)) *
     (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j
def reducedClearedTaylorNumerator (F:Poly K) (s w:ℕ) (c:ℕ → K) (x:K) :
   Poly K :=
 ∑ j ∈ Finset.range (w + 1),reducedCommonNumeratorTerm F s w c x j
def reducedAgreementNumerator (F:Poly K) (s w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   Poly K :=
 reducedClearedTaylorNumerator F s w c x -
   affineSeedPolynomial u₀ u₁ * polyH K F ^ (2 * w)
theorem commonNumeratorTerm_sub_reduced_dvd (F:Poly K) (s w j:ℕ)
   (c:ℕ → K) (x:K) :
   F ∣ commonNumeratorTerm F w c x j - reducedCommonNumeratorTerm F s w c x j:=by
 obtain ⟨T,hT⟩:=numerator_sub_reduced_dvd F s j
 refine ⟨MvPolynomial.C (c j) * T * polyH K F ^ (2 * (w - j)) *
   (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j,?_⟩
 unfold commonNumeratorTerm reducedCommonNumeratorTerm
 linear_combination MvPolynomial.C (c j) * polyH K F ^ (2 * (w - j)) *
   (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j * hT
theorem clearedTaylorNumerator_sub_reduced_dvd (F:Poly K) (s w:ℕ)
   (c:ℕ → K) (x:K) :
   F ∣ clearedTaylorNumerator F w c x - reducedClearedTaylorNumerator F s w c x:=by
 unfold clearedTaylorNumerator reducedClearedTaylorNumerator
 rw [← Finset.sum_sub_distrib]
 exact Finset.dvd_sum fun j _ => commonNumeratorTerm_sub_reduced_dvd F s w j c x
theorem agreementNumerator_sub_reduced_dvd (F:Poly K) (s w:ℕ)
   (c:ℕ → K) (x u₀ u₁:K) :
   F ∣ agreementNumerator F w c x u₀ u₁ -
     reducedAgreementNumerator F s w c x u₀ u₁:=by
 unfold agreementNumerator reducedAgreementNumerator
 simpa only [sub_sub_sub_cancel_right] using
   clearedTaylorNumerator_sub_reduced_dvd F s w c x
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N7

/-! Packed from ProximityPrize.SubmissionLower.N6. -/
section PackedLegacy_N6
namespace ProximityPrize.SubmissionLower.RCN261
open RCN290 RCN293 RCN081
noncomputable section
variable {K:Type*} [Field K]
theorem embedCoefficients_injective:Function.Injective (embedCoefficients K):=by
 intro P Q h
 exact Polynomial.C_injective ((collectR K).symm.injective h)
@[simp] theorem liftedCoefficient_zero (n:ℕ) :
   liftedCoefficient (0:MvPolynomial (Fin 4) K) n = 0:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_add (P Q:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (P + Q) n = liftedCoefficient P n + liftedCoefficient Q n:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_sub (P Q:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (P - Q) n = liftedCoefficient P n - liftedCoefficient Q n:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_neg (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (-P) n = -liftedCoefficient P n:=by
 simp [liftedCoefficient]
theorem liftedCoefficient_eq_zero_iff (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient P n = 0 ↔ (collectR K P).coeff n = 0:=by
 change embedCoefficients K ((collectR K P).coeff n) = 0 ↔ _
 rw [← map_zero (embedCoefficients K),embedCoefficients_injective.eq_iff]
theorem liftedCoefficient_eq_zero_of_degree_lt (P:MvPolynomial (Fin 4) K)
   (n:ℕ) (hP:P.degreeOf 2 < n):liftedCoefficient P n = 0:=by
 apply (liftedCoefficient_eq_zero_iff P n).mpr
 exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [collectR_natDegree])
theorem collectR_X_R :
   collectR K (MvPolynomial.X (2:Fin 4)) = Polynomial.X:=by
 simp [collectR,MvPolynomial.renameEquiv_apply,
   Equiv.optionSubtypeNe_symm_apply]
theorem collectR_pderiv_R (P:MvPolynomial (Fin 4) K) :
   collectR K (MvPolynomial.pderiv (2:Fin 4) P) = (collectR K P).derivative:=by
 classical
 induction P using MvPolynomial.induction_on with
 | C c =>
     simp [collectR,MvPolynomial.renameEquiv_apply]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     by_cases hi:i = 2
     · subst i
       simp [map_mul,collectR_X_R,Polynomial.derivative_mul,hP]
       ring
     · have hX:=collectR_X_other (K:=K) (⟨i,hi⟩:RemainingCoordinates)
       simp only [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X_of_ne hi,
         mul_zero,add_zero,map_mul,hX,Polynomial.derivative_mul,
         Polynomial.derivative_C,mul_zero,add_zero,hP]
theorem liftedCoefficient_pderiv_R (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (MvPolynomial.pderiv (2:Fin 4) P) n =
     MvPolynomial.C ((n + 1:ℕ):K) * liftedCoefficient P (n + 1):=by
 unfold liftedCoefficient
 rw [collectR_pderiv_R,Polynomial.coeff_derivative,map_mul]
 simp only [map_add,map_natCast,map_one,Nat.cast_add,Nat.cast_one]
 ring
public theorem optionCoefficient_pderiv_some {σ:Type*}
   (P:MvPolynomial (Option σ) K) (i:σ) (n:ℕ) :
   (MvPolynomial.optionEquivLeft K σ (MvPolynomial.pderiv (some i) P)).coeff n =
     MvPolynomial.pderiv i ((MvPolynomial.optionEquivLeft K σ P).coeff n):=by
 classical
 ext e
 rw [MvPolynomial.optionEquivLeft_coeff_coeff,MvPolynomial.coeff_pderiv,
   MvPolynomial.coeff_pderiv,MvPolynomial.optionEquivLeft_coeff_coeff]
 have he:e.optionElim n + Finsupp.single (some i) 1 =
     (e + Finsupp.single i 1).optionElim n:=by
   ext j
   cases j with
   | none => simp
   | some j =>
       simp only [Finsupp.add_apply,Finsupp.optionElim_apply_some]
       rw [Finsupp.single_apply_left
         (show Function.Injective (some:σ → Option σ) from fun _ _ h => Option.some.inj h)]
 rw [he,Finsupp.optionElim_apply_some]
theorem liftedCoefficient_pderiv_other (P:MvPolynomial (Fin 4) K)
   (i:Fin 4) (hi:i ≠ 2) (n:ℕ) :
   liftedCoefficient (MvPolynomial.pderiv i P) n =
     MvPolynomial.pderiv i (liftedCoefficient P n):=by
 have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i = some ⟨i,hi⟩:=by
   simp [Equiv.optionSubtypeNe_symm_apply,hi]
 have hrename :
     MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P) =
     MvPolynomial.pderiv (some (⟨i,hi⟩:RemainingCoordinates))
       (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm P):=by
   rw [← MvPolynomial.pderiv_rename
     (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective i P,hindex]
 have hc:(collectR K (MvPolynomial.pderiv i P)).coeff n =
     MvPolynomial.pderiv (⟨i,hi⟩:RemainingCoordinates) ((collectR K P).coeff n):=by
   change (MvPolynomial.optionEquivLeft K RemainingCoordinates
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P))).coeff n = _
   rw [hrename,optionCoefficient_pderiv_some]
   rfl
 unfold liftedCoefficient
 rw [hc,embedCoefficients_eq_rename,embedCoefficients_eq_rename]
 exact (MvPolynomial.pderiv_rename Subtype.val_injective
   (⟨i,hi⟩:RemainingCoordinates) ((collectR K P).coeff n)).symm
theorem liftedCoefficient_pderiv_R_top (P:MvPolynomial (Fin 4) K) (a:ℕ)
   (ha:0 < a) :
   liftedCoefficient (MvPolynomial.pderiv (2:Fin 4) P) (a - 1) =
     MvPolynomial.C (a:K) * liftedCoefficient P a:=by
 simpa only [Nat.sub_add_cancel ha] using liftedCoefficient_pderiv_R P (a - 1)
theorem liftedCoefficient_mul_top (P Q:MvPolynomial (Fin 4) K) (a b:ℕ)
   (hP:P.degreeOf 2 ≤ a) (hQ:Q.degreeOf 2 ≤ b) :
   liftedCoefficient (P * Q) (a + b) =
     liftedCoefficient P a * liftedCoefficient Q b:=by
 unfold liftedCoefficient
 rw [map_mul,Polynomial.coeff_mul_add_eq_of_natDegree_le
   (by rwa [collectR_natDegree]) (by rwa [collectR_natDegree]),map_mul]
theorem liftedCoefficient_zero_degree (P:MvPolynomial (Fin 4) K)
   (hP:P.degreeOf 2 = 0):liftedCoefficient P 0 = P:=by
 have hC:collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
   Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
 change (collectR K).symm (Polynomial.C ((collectR K P).coeff 0)) = P
 rw [← hC,AlgEquiv.symm_apply_apply]
theorem liftedCoefficient_mul_degree_zero_left (P Q:MvPolynomial (Fin 4) K)
   (n:ℕ) (hP:P.degreeOf 2 = 0) :
   liftedCoefficient (P * Q) n = P * liftedCoefficient Q n:=by
 have hC:collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
   Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
 unfold liftedCoefficient
 rw [map_mul,hC,Polynomial.coeff_C_mul,map_mul]
 change liftedCoefficient P 0 * _ = _
 rw [liftedCoefficient_zero_degree P hP]
@[simp] theorem liftedCoefficient_C_mul (c:K) (P:MvPolynomial (Fin 4) K)
   (n:ℕ):liftedCoefficient (MvPolynomial.C c * P) n =
     MvPolynomial.C c * liftedCoefficient P n :=
 liftedCoefficient_mul_degree_zero_left _ P n (MvPolynomial.degreeOf_C c 2)
@[simp] theorem liftedCoefficient_natCast_mul (c:ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient ((c:MvPolynomial (Fin 4) K) * P) n =
     (c:MvPolynomial (Fin 4) K) * liftedCoefficient P n:=by
 simpa only [map_natCast] using liftedCoefficient_C_mul (c:K) P n
theorem liftedCoefficient_X_R_pow (n:ℕ) :
   liftedCoefficient ((MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) ^ n) n =
     1:=by
 simp [liftedCoefficient,map_pow,collectR_X_R]
theorem liftedCoefficient_X_R_mul (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (MvPolynomial.X (2:Fin 4) * P) (n + 1) =
     liftedCoefficient P n:=by
 unfold liftedCoefficient
 rw [map_mul,collectR_X_R,Polynomial.coeff_X_mul]
theorem liftedCoefficient_support_exact
   (P:MvPolynomial (Fin 4) K) (n:ℕ) (e:Fin 4 →₀ ℕ)
   (he:e ∈ (liftedCoefficient P n).support) :
   ∃ d ∈ P.support,d 2 = n ∧ e 2 = 0 ∧ ∀ i,i ≠ 2 → e i = d i:=by
 classical
 have heR:e 2 = 0:=by
   have hh:=MvPolynomial.monomial_le_degreeOf (2:Fin 4) he
   rw [liftedCoefficient_R_degree] at hh
   omega
 change e ∈ (embedCoefficients K ((collectR K P).coeff n)).support at he
 rw [embedCoefficients_eq_rename,
   MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
 obtain ⟨u,hu,heu⟩:=Finset.mem_image.mp he
 have hopt:u.optionElim n ∈
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm P).support :=
   (MvPolynomial.mem_support_coeff_optionEquivLeft (R:=K)).mp hu
 rw [MvPolynomial.support_rename_of_injective
   (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at hopt
 obtain ⟨d,hd,hdu⟩:=Finset.mem_image.mp hopt
 refine ⟨d,hd,?_,heR,?_⟩
 · have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm 2)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   simpa [Equiv.optionSubtypeNe_symm_apply] using huv
 · intro i hi
   have hev:e i = u ⟨i,hi⟩:=by
     rw [← heu]
     exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i,hi⟩
   have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm i)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i = some ⟨i,hi⟩:=by
     simp [Equiv.optionSubtypeNe_symm_apply,hi]
   rw [hindex,Finsupp.optionElim_apply_some] at huv
   exact hev.trans huv.symm
theorem liftedCoefficient_weight_add_le (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) (hn:liftedCoefficient P n ≠ 0) :
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) + n * weights 2 ≤
     MvPolynomial.weightedTotalDegree weights P:=by
 classical
 obtain ⟨e,he,hmax⟩:=Finset.exists_mem_eq_sup
   (liftedCoefficient P n).support (MvPolynomial.support_nonempty.mpr hn)
   (Finsupp.weight weights)
 obtain ⟨d,hd,hdR,heR,heq⟩:=liftedCoefficient_support_exact P n e he
 have hw:Finsupp.weight weights e + n * weights 2 = Finsupp.weight weights d:=by
   rw [weight_fin4,weight_fin4,hdR,heR,
     heq 0 (by decide),heq 1 (by decide),heq 3 (by decide)]
   omega
 change (liftedCoefficient P n).support.sup (Finsupp.weight weights) + _ ≤ _
 rw [hmax,hw]
 exact MvPolynomial.le_weightedTotalDegree weights hd
theorem liftedCoefficient_weight_le_sub (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) ≤
     MvPolynomial.weightedTotalDegree weights P - n * weights 2:=by
 by_cases hn:liftedCoefficient P n = 0
 · simp [hn,MvPolynomial.weightedTotalDegree]
 · have h:=liftedCoefficient_weight_add_le weights P n hn
   omega
theorem degreeR_le_sub_one_of_top_zero (P:MvPolynomial (Fin 4) K) (t:ℕ)
   (ht:0 < t) (hP:P.degreeOf 2 ≤ t) (hzero:liftedCoefficient P t = 0) :
   P.degreeOf 2 ≤ t - 1:=by
 rw [← collectR_natDegree]
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 by_cases heq:n = t
 · subst n
   exact (liftedCoefficient_eq_zero_iff P t).mp hzero
 · exact Polynomial.coeff_eq_zero_of_natDegree_lt
     (by rw [collectR_natDegree]; omega)
theorem degreeR_sub_cancel_top (W F q:MvPolynomial (Fin 4) K) (t s k:ℕ)
   (ht:0 < t) (hW:W.degreeOf 2 ≤ t) (hF:F.degreeOf 2 ≤ s)
   (hq:q.degreeOf 2 = 0) (hks:k + s = t)
   (hcoeff:liftedCoefficient W t = q * liftedCoefficient F s) :
   (W - q * MvPolynomial.X (2:Fin 4) ^ k * F).degreeOf 2 ≤ t - 1:=by
 have hR:((MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) ^ k).degreeOf 2 ≤ k:=by
   simpa using MvPolynomial.degreeOf_pow_le (2:Fin 4)
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) k
 have hqR:(q * MvPolynomial.X (2:Fin 4) ^ k).degreeOf 2 ≤ k:=by
   have h:=MvPolynomial.degreeOf_mul_le (2:Fin 4) q
     ((MvPolynomial.X (2:Fin 4)) ^ k)
   omega
 have hprod:(q * MvPolynomial.X (2:Fin 4) ^ k * F).degreeOf 2 ≤ t:=by
   have h:=RCN313.degree_mul_bound (2:Fin 4) hqR hF
   omega
 apply degreeR_le_sub_one_of_top_zero _ t ht
   (RCN313.degree_sub_bound (2:Fin 4) hW hprod)
 rw [liftedCoefficient_sub,← hks,
   liftedCoefficient_mul_top _ F k s hqR hF,
   liftedCoefficient_mul_degree_zero_left _ _ k hq,
   liftedCoefficient_X_R_pow,mul_one,hks,hcoeff,sub_self]
end
end ProximityPrize.SubmissionLower.RCN261
end PackedLegacy_N6

/-! Packed from ProximityPrize.SubmissionLower.N8. -/
section PackedLegacy_N8
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN261
noncomputable section
set_option maxHeartbeats 800000
variable {K:Type*} [Field K]
theorem liftedCoefficient_polyH_top (F:Poly K) (s:ℕ) (hs:1 ≤ s) :
   liftedCoefficient (polyH K F) (s - 1) = (s:Poly K) * liftedCoefficient F s:=by
 simpa only [polyH,map_natCast] using liftedCoefficient_pderiv_R_top F s hs
theorem liftedCoefficient_polyG_top (F:Poly K) (s:ℕ)
   (hF:F.degreeOf (2:Fin 4) ≤ s) :
   liftedCoefficient (polyG K F) (s + 1) =
     -MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s):=by
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) F s hF
 have hx:liftedCoefficient (MvPolynomial.pderiv (0:Fin 4) F) (s + 1) = 0 :=
   liftedCoefficient_eq_zero_of_degree_lt _ _ (by omega)
 simp only [polyG,liftedCoefficient_neg,liftedCoefficient_add,hx,zero_add,
   liftedCoefficient_X_R_mul,liftedCoefficient_pderiv_other F 1 (by decide) s]
theorem vectorNumerator_top_coefficient (F P:Poly K) (a s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   liftedCoefficient (vectorNumerator F P) (a + s) =
     (s:Poly K) * liftedCoefficient F s *
         MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a) -
       (a:Poly K) * MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
         liftedCoefficient P a:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s - 1 :=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s + 1 :=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) P a hP
 have hPY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) P a hP
 have hPR:=pderiv_same_degree_bound (2:Fin 4) P a hP
 have hcR:liftedCoefficient R 1 = 1:=by
   simpa only [R,pow_one] using liftedCoefficient_X_R_pow (K:=K) 1
 have hcH:liftedCoefficient H (s - 1) = (s:Poly K) * liftedCoefficient F s :=
   liftedCoefficient_polyH_top F s hs
 have hRH:(R * H).degreeOf (2:Fin 4) ≤ s:=by
   have h:=degree_mul_bound (2:Fin 4) hR hH
   omega
 have hcRH:liftedCoefficient (R * H) s = (s:Poly K) * liftedCoefficient F s:=by
   have h:=liftedCoefficient_mul_top R H 1 (s - 1) hR hH
   rw [show 1 + (s - 1) = s by omega,hcR,hcH,one_mul] at h
   exact h
 have hx:liftedCoefficient (H * MvPolynomial.pderiv (0:Fin 4) P) (a + s) = 0:=by
   apply liftedCoefficient_eq_zero_of_degree_lt
   have h:=degree_mul_bound (2:Fin 4) hH hPX
   omega
 have hy:liftedCoefficient (R * H * MvPolynomial.pderiv (1:Fin 4) P) (a + s) =
     (s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a):=by
   have h:=liftedCoefficient_mul_top (R * H) (MvPolynomial.pderiv (1:Fin 4) P)
     s a hRH hPY
   rw [hcRH,liftedCoefficient_pderiv_other P 1 (by decide) a] at h
   simpa only [Nat.add_comm] using h
 have hr:liftedCoefficient (G * MvPolynomial.pderiv (2:Fin 4) P) (a + s) =
     -(a:Poly K) * MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
       liftedCoefficient P a:=by
   by_cases ha:a = 0
   · have hz:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) P (by simpa [ha] using hP)
     simp [ha,hz]
   · have hapos:0 < a:=Nat.pos_of_ne_zero ha
     have h:=liftedCoefficient_mul_top G (MvPolynomial.pderiv (2:Fin 4) P)
       (s + 1) (a - 1) hG hPR
     rw [show s + 1 + (a - 1) = a + s by omega,
       liftedCoefficient_polyG_top F s hF,
       liftedCoefficient_pderiv_R_top P a hapos,map_natCast] at h
     rw [h]
     ring
 change liftedCoefficient (H * MvPolynomial.pderiv (0:Fin 4) P +
   R * H * MvPolynomial.pderiv (1:Fin 4) P +
     G * MvPolynomial.pderiv (2:Fin 4) P) (a + s) = _
 rw [liftedCoefficient_add,liftedCoefficient_add,hx,hy,hr]
 ring
theorem vectorNumerator_H_top_coefficient (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) :
   liftedCoefficient (vectorNumerator F (polyH K F)) (2 * s - 1) =
     (s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s):=by
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have h:=vectorNumerator_top_coefficient F (polyH K F) (s - 1) s hs hF hH
 rw [show s - 1 + s = 2 * s - 1 by omega,
   liftedCoefficient_polyH_top F s hs] at h
 rw [h,MvPolynomial.pderiv_mul]
 simp only [Derivation.map_natCast,zero_mul,mul_zero,add_zero,zero_add]
 rw [Nat.cast_sub hs]
 simp only [Nat.cast_one]
 ring
theorem numeratorStep_top_coefficient (F P:Poly K) (a s b:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   liftedCoefficient (numeratorStep K F b P) (a + (2 * s - 1)) =
     liftedCoefficient F s * ((s:Poly K) *
       ((s:Poly K) * liftedCoefficient F s *
           MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a) -
         ((a + 2 * b:ℕ):Poly K) *
           MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
             liftedCoefficient P a)):=by
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have hV:=vectorNumerator_R_degree_bound F P a s hs hF hP
 have hVH:(vectorNumerator F (polyH K F)).degreeOf (2:Fin 4) ≤ 2 * s - 1:=by
   have h:=vectorNumerator_R_degree_bound F (polyH K F) (s - 1) s hs hF hH
   omega
 have hfirst:=liftedCoefficient_mul_top (polyH K F) (vectorNumerator F P)
   (s - 1) (a + s) hH hV
 rw [show s - 1 + (a + s) = a + (2 * s - 1) by omega,
   liftedCoefficient_polyH_top F s hs,
   vectorNumerator_top_coefficient F P a s hs hF hP] at hfirst
 have hlast:=liftedCoefficient_mul_top P (vectorNumerator F (polyH K F))
   a (2 * s - 1) hP hVH
 rw [vectorNumerator_H_top_coefficient F s hs hF] at hlast
 rw [numeratorStep_eq_vector,liftedCoefficient_sub,hfirst]
 rw [show ((2 * b:ℕ):Poly K) * P * vectorNumerator F (polyH K F) =
   ((2 * b:ℕ):Poly K) * (P * vectorNumerator F (polyH K F)) by ring,
   liftedCoefficient_natCast_mul,hlast]
 push_cast
 ring
theorem excessFactor_R_degree (F P:Poly K) (s b:ℕ) :
   (excessFactor F P s b).degreeOf (2:Fin 4) = 0:=by
 have hf:(liftedCoefficient F s).degreeOf (2:Fin 4) ≤ 0 :=
   (liftedCoefficient_R_degree F s).le
 have hc:(liftedCoefficient P (2 * b * (s - 1))).degreeOf (2:Fin 4) ≤ 0 :=
   (liftedCoefficient_R_degree P _).le
 have hdf:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) _ 0 hf
 have hdc:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) _ 0 hc
 have hs:(s:Poly K).degreeOf (2:Fin 4) ≤ 0:=(degree_natCast_eq_zero 2 s).le
 have hn:((2 * b * (s - 1) + 2 * b:ℕ):Poly K).degreeOf (2:Fin 4) ≤ 0 :=
   (degree_natCast_eq_zero 2 _).le
 have hleft:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hs hf) hdc
 have hright:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hn hdf) hc
 have hinner:=degree_sub_bound (2:Fin 4) hleft hright
 have h:=degree_mul_bound (2:Fin 4) hs hinner
 exact Nat.eq_zero_of_le_zero (by simpa only [excessFactor,Nat.zero_add] using h)
theorem reducedStep_R_degree_bound (F P:Poly K) (s b:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ 2 * b * (s - 1)) :
   (reducedStep F P s b).degreeOf (2:Fin 4) ≤ 2 * (b + 1) * (s - 1):=by
 let a:=2 * b * (s - 1)
 let t:=a + (2 * s - 1)
 have ht:0 < t:=by dsimp [t]; omega
 have hW:=numeratorStep_R_degree_bound F P b a s hs hF hP
 have hcoeff:liftedCoefficient (numeratorStep K F b P) t =
     excessFactor F P s b * liftedCoefficient F s:=by
   rw [numeratorStep_top_coefficient F P a s b hs hF hP]
   dsimp [excessFactor,a]
   ring
 have hks:(2 * b + 1) * (s - 1) + s = t:=by
   dsimp [t,a]
   have hsi:s = (s - 1) + 1:=by omega
   conv_lhs => rhs; rw [hsi]
   have ht':2 * s - 1 = 2 * (s - 1) + 1:=by omega
   rw [ht']
   ring
 have h:=degreeR_sub_cancel_top (numeratorStep K F b P) F (excessFactor F P s b)
   t s ((2 * b + 1) * (s - 1)) ht hW hF (excessFactor_R_degree F P s b) hks hcoeff
 have heq:t - 1 = 2 * (b + 1) * (s - 1):=by
   dsimp [t,a]
   have ht':2 * s - 1 = 2 * (s - 1) + 1:=by omega
   rw [ht',← Nat.add_assoc,Nat.add_sub_cancel]
   ring
 simpa only [reducedStep,reductionMultiplier,heq] using h
theorem reducedNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) (b:ℕ) :
   (reducedNumerator F s b).degreeOf (2:Fin 4) ≤ 2 * b * (s - 1):=by
 induction b with
 | zero => simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 1)]
 | succ b ih => exact reducedStep_R_degree_bound F (reducedNumerator F s b) s b hs hF ih
theorem reducedCommonNumeratorTerm_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K) :
   (reducedCommonNumeratorTerm F s w c x j).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 have hN:=reducedNumerator_R_degree_bound F s hs hF j
 have hCN:(MvPolynomial.C (c j) * reducedNumerator F s j).degreeOf (2:Fin 4) ≤
     2 * j * (s - 1) :=
   (MvPolynomial.degreeOf_C_mul_le (reducedNumerator F s j) (2:Fin 4) (c j)).trans hN
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have hHP:=degree_pow_bound (2:Fin 4) (2 * (w - j)) hH
 have hXP:((MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) ^ j).degreeOf
     (2:Fin 4) ≤ 0:=by
   simpa only [Nat.mul_zero] using
     degree_pow_bound (2:Fin 4) j (shiftedX_degree_bound (2:Fin 4) (by decide) x)
 have h:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hCN hHP) hXP
 apply h.trans
 have hw:j + (w - j) = w:=by omega
 calc
   2 * j * (s - 1) + 2 * (w - j) * (s - 1) + 0 =
       2 * (j + (w - j)) * (s - 1):=by ring
   _ ≤ 2 * w * (s - 1):=by simp only [hw,le_refl]
theorem reducedClearedTaylorNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x:K) :
   (reducedClearedTaylorNumerator F s w c x).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 apply degree_sum_bound (2:Fin 4)
 intro j hj
 exact reducedCommonNumeratorTerm_R_degree_bound F s hs hF w j
   (by have h:=Finset.mem_range.mp hj; omega) c x
theorem reducedAgreementNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   (reducedAgreementNumerator F s w c x u₀ u₁).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 apply degree_sub_bound (2:Fin 4)
 · exact reducedClearedTaylorNumerator_R_degree_bound F s hs hF w c x
 · have hA:=affineSeedPolynomial_degree_bound (2:Fin 4) 0
     (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 3)]) u₀ u₁
   have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
   simpa only [polyH,Nat.zero_add] using
     degree_mul_bound (2:Fin 4) hA (degree_pow_bound (2:Fin 4) (2 * w) hH)
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N8

/-! Packed from ProximityPrize.SubmissionLower.N9. -/
section PackedLegacy_N9
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN261 RCN234 RCN179
noncomputable section
variable {K:Type*} [Field K]
theorem excessFactor_wt_le (weights:Fin 4 → ℕ)
   (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (excessFactor F P s b) ≤ (2 * b + 1) * (C - s):=by
 by_cases hfzero:liftedCoefficient F s = 0
 · simp [excessFactor,hfzero,wt,MvPolynomial.weightedTotalDegree]
 let f:=liftedCoefficient F s
 let c:=liftedCoefficient P (2 * b * (s - 1))
 let D:=C - s
 have hfadd:=liftedCoefficient_weight_add_le weights F s hfzero
 change wt weights f + s * weights 2 ≤ wt weights F at hfadd
 rw [hR,Nat.mul_one] at hfadd
 have hsC:s ≤ C:=by omega
 have hf:wt weights f ≤ D:=by dsimp [D]; omega
 have hc:wt weights c ≤ 1 + 2 * b * D:=by
   have h:=liftedCoefficient_weight_le_sub weights P (2 * b * (s - 1))
   change wt weights c ≤ wt weights P - 2 * b * (s - 1) * weights 2 at h
   rw [hR,Nat.mul_one] at h
   have h':=h.trans (Nat.sub_le_sub_right hP (2 * b * (s - 1)))
   have hdecomp:C - 1 = D + (s - 1):=by dsimp [D]; omega
   have heq:1 + 2 * b * (C - 1) = (1 + 2 * b * D) + 2 * b * (s - 1):=by
     rw [hdecomp]
     ring
   rwa [heq,Nat.add_sub_cancel] at h'
 have hdc:wt weights (MvPolynomial.pderiv (1:Fin 4) c) ≤ 2 * b * D:=by
   have h:=wt_pderiv_le weights c 1 (1 + 2 * b * D) hc
   rw [hY] at h
   omega
 have hdf:wt weights (MvPolynomial.pderiv (1:Fin 4) f) ≤ D - 1:=by
   simpa only [hY] using wt_pderiv_le weights f 1 D hf
 have hsf:wt weights ((s:Poly K) * f) ≤ D:=by
   have h:=wt_mul_le weights (s:Poly K) f
   rw [wt_natCast,Nat.zero_add] at h
   exact h.trans hf
 have hleft:wt weights ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c) ≤
     (2 * b + 1) * D:=by
   have h:=(wt_mul_le weights ((s:Poly K) * f) (MvPolynomial.pderiv (1:Fin 4) c)).trans
     (Nat.add_le_add hsf hdc)
   apply h.trans
   apply le_of_eq
   ring
 have hright:wt weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
     MvPolynomial.pderiv (1:Fin 4) f * c) ≤ (2 * b + 1) * D:=by
   by_cases hD:D = 0
   · have hz:MvPolynomial.pderiv (1:Fin 4) f = 0 :=
       pderiv_eq_zero_of_wt_lt weights f 1 (by rw [hY]; omega)
     simp [hz,wt,MvPolynomial.weightedTotalDegree]
   · have hn:wt weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
         MvPolynomial.pderiv (1:Fin 4) f) ≤ D - 1:=by
       have h:=wt_mul_le weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K))
         (MvPolynomial.pderiv (1:Fin 4) f)
       rw [wt_natCast,Nat.zero_add] at h
       exact h.trans hdf
     have h:=(wt_mul_le weights
       (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f)
       c).trans (Nat.add_le_add hn hc)
     apply h.trans
     rw [Nat.add_mul,Nat.one_mul]
     omega
 have hinner:=(wt_sub_le weights
   ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c)
   (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f * c)).trans
   (max_le hleft hright)
 have h:=wt_mul_le weights (s:Poly K)
   ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c -
     ((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f * c)
 rw [wt_natCast,Nat.zero_add] at h
 exact h.trans hinner
theorem reductionCorrection_wt_le (weights:Fin 4 → ℕ)
   (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (reductionMultiplier F P s b * F) ≤ 1 + 2 * (b + 1) * (C - 1):=by
 by_cases hfzero:liftedCoefficient F s = 0
 · simp [reductionMultiplier,excessFactor,hfzero,wt,MvPolynomial.weightedTotalDegree]
 have hfadd:=liftedCoefficient_weight_add_le weights F s hfzero
 change wt weights (liftedCoefficient F s) + s * weights 2 ≤ wt weights F at hfadd
 rw [hR,Nat.mul_one] at hfadd
 have hsC:s ≤ C:=by omega
 have hCpos:1 ≤ C:=hs.trans hsC
 have hq:=excessFactor_wt_le weights hY hR F P s b C hs hF hP
 have hpow:wt weights ((MvPolynomial.X (2:Fin 4):Poly K) ^ ((2 * b + 1) * (s - 1))) ≤
     (2 * b + 1) * (s - 1):=by
   have h:=wt_pow_le weights (MvPolynomial.X (2:Fin 4):Poly K) ((2 * b + 1) * (s - 1))
   simpa only [wt_X,hR,Nat.mul_one] using h
 have hqR:=(wt_mul_le weights (excessFactor F P s b)
   ((MvPolynomial.X (2:Fin 4)) ^ ((2 * b + 1) * (s - 1)))).trans
   (Nat.add_le_add hq hpow)
 have h:=(wt_mul_le weights (reductionMultiplier F P s b) F).trans
   (Nat.add_le_add hqR hF)
 apply h.trans
 have hdecomp:(C - s) + (s - 1) = C - 1:=by omega
 apply le_of_eq
 calc
   (2 * b + 1) * (C - s) + (2 * b + 1) * (s - 1) + C =
       (2 * b + 1) * ((C - s) + (s - 1)) + C:=by ring
   _ = (2 * b + 1) * (C - 1) + C:=by rw [hdecomp]
   _ = (2 * b + 1) * (C - 1) + ((C - 1) + 1) :=
     congrArg (fun n => (2 * b + 1) * (C - 1) + n) (Nat.sub_add_cancel hCpos).symm
   _ = 1 + 2 * (b + 1) * (C - 1):=by ring
theorem reducedStep_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (reducedStep F P s b) ≤ 1 + 2 * (b + 1) * (C - 1):=by
 have hstep:=numeratorStep_wt_le_equal_weight weights hX F P b
   (1 + 2 * b * (C - 1)) C (by omega) (by omega) (by omega) (by omega) hF hP
 rw [hR] at hstep
 have hstep':wt weights (numeratorStep K F b P) ≤ 1 + 2 * (b + 1) * (C - 1):=by
   convert hstep using 1 <;> ring
 exact (wt_sub_le weights _ _).trans
   (max_le hstep' (reductionCorrection_wt_le weights hY hR F P s b C hs hF hP))
theorem reducedNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (b:ℕ) :
   wt weights (reducedNumerator F s b) ≤ 1 + 2 * b * (C - 1):=by
 induction b with
 | zero => simp only [reducedNumerator_zero,wt_X,hY,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,le_refl]
 | succ b ih => exact reducedStep_wt_le weights hX hY hR F (reducedNumerator F s b) s b C hs hC hF ih
theorem reducedCommonNumeratorTerm_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w j:ℕ) (hj:j ≤ w)
   (c:ℕ → K) (x:K) :
   wt weights (reducedCommonNumeratorTerm F s w c x j) ≤ 1 + 2 * w * (C - 1):=by
 have hN:=reducedNumerator_wt_le weights hX hY hR F s C hs hC hF j
 have hCN:wt weights (MvPolynomial.C (c j) * reducedNumerator F s j) ≤
     1 + 2 * j * (C - 1):=by
   have h:=wt_mul_le weights (MvPolynomial.C (c j)) (reducedNumerator F s j)
   rw [wt_C,Nat.zero_add] at h
   exact h.trans hN
 have hH:wt weights (polyH K F) ≤ C - 1:=by
   simpa only [hR] using wt_polyH_le weights F C hF
 have hHP:=(wt_pow_le weights (polyH K F) (2 * (w - j))).trans
   (Nat.mul_le_mul_left _ hH)
 have hXP:wt weights ((MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) ^ j) ≤ 0:=by
   have h:=wt_pow_le weights
     (MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) j
   simpa only [shiftedX_wt_eq_zero weights hX x,Nat.mul_zero] using h
 have h1:=(wt_mul_le weights (MvPolynomial.C (c j) * reducedNumerator F s j)
   (polyH K F ^ (2 * (w - j)))).trans (Nat.add_le_add hCN hHP)
 have h2:=(wt_mul_le weights
   (MvPolynomial.C (c j) * reducedNumerator F s j * polyH K F ^ (2 * (w - j)))
   ((MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j)).trans (Nat.add_le_add h1 hXP)
 apply h2.trans
 have hw:j + (w - j) = w:=by omega
 apply le_of_eq
 calc
   (1 + 2 * j * (C - 1) + 2 * (w - j) * (C - 1)) + 0 =
       1 + 2 * (j + (w - j)) * (C - 1):=by ring
   _ = 1 + 2 * w * (C - 1):=by rw [hw]
theorem reducedClearedTaylorNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w:ℕ) (c:ℕ → K) (x:K) :
   wt weights (reducedClearedTaylorNumerator F s w c x) ≤ 1 + 2 * w * (C - 1):=by
 apply wt_sum_le
 intro j hj
 exact reducedCommonNumeratorTerm_wt_le weights hX hY hR F s C hs hC hF w j
   (by have h:=Finset.mem_range.mp hj; omega) c x
theorem reducedAgreementNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   wt weights (reducedAgreementNumerator F s w c x u₀ u₁) ≤
     max 1 (weights 3) + 2 * w * (C - 1):=by
 have hTaylor:=reducedClearedTaylorNumerator_wt_le weights hX hY hR F s C hs hC hF w c x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ C - 1:=by
   simpa only [hR] using wt_polyH_le weights F C hF
 have hHP:=(wt_pow_le weights (polyH K F) (2 * w)).trans
   (Nat.mul_le_mul_left _ hH)
 have hprod:=(wt_mul_le weights (affineSeedPolynomial u₀ u₁) (polyH K F ^ (2 * w))).trans
   (Nat.add_le_add hA hHP)
 exact (wt_sub_le weights _ _).trans (max_le
   (hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _))
   (hprod.trans (Nat.add_le_add_right (Nat.le_max_right _ _) _)))
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N9
end Compact_PackedLegacyCore2


