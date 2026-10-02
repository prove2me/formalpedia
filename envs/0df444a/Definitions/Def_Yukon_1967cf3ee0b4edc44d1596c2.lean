-- Prove2me | Definitions.Def_Yukon_1967cf3ee0b4edc44d1596c2
-- name    : Yukon_1967cf3ee0b4edc44d1596c2
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T20:36:33.419982+00:00
-- url     : https://prove2.me/theorems/4e1b60e2-309b-49e1-afb0-bbe6f72ac38f
-- title:
--   LowerFoundation source part 2/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:bootstrap-v25-34ade0ee60f550846d286032a91dc340bb46df7cfc34cf1d529ef27a77fb1507
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjJmYWU5YTlmNjJhZDBjOThhOGIwNGFhNjk1YzY3NmQ3ZTI5MDAwZjNmM2FmMDk2ZWZjZWEyNWVjMTQ1NTQxNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmJvb3RzdHJhcC12MjUtMzRhZGUwZWU2MGY1NTA4NDZkMjg2MDMyYTkxZGMzNDBiYjQ2ZGY3Y2ZjMzRjZjFkNTI5ZWYyN2E3N2ZiMTUwNyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzE5NjdjZjNlZTBiNGVkYzQ0ZDE1OTZjMiIsInYiOjJ9]

import Definitions.Def_Yukon_126560b5c32e606e4eaf10e4
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


/-! Packed from ProximityPrize.SubmissionLower.Z5. -/
section PackedLegacy_Z5
namespace ProximityPrize.SubmissionLower.RCN162
open scoped Classical
open RCN094
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN162.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def forwardResidualPoint
   (aY v bY aS bS cS:K) (q:Fin 3 → K):Fin 3 → K:=
 ![aY+v*q 0+bY*q 2,
   aS+v*q 1+bS*q 0+cS*q 2,
   q 2]
theorem eval_residualEquiv
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3 → K) (F:Poly3 K):
   MvPolynomial.eval q
       (residualEquiv aY v bY aS bS cS hv F)=
     MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F:=by
 change MvPolynomial.eval₂Hom (RingHom.id K) q
     (residualAlgHom aY v bY aS bS cS F)=
   MvPolynomial.eval₂Hom (RingHom.id K)
     (forwardResidualPoint aY v bY aS bS cS q) F
 have hq:q=![q 0,q 1,q 2]:=by
   funext i
   fin_cases i <;> rfl
 have hforward:
     forwardResidualPoint aY v bY aS bS cS q=
       ![aY+v*q 0+bY*q 2,
         aS+v*q 1+bS*q 0+cS*q 2,
         q 2]:=by
   funext i
   fin_cases i <;> simp [forwardResidualPoint]
 calc
   _=MvPolynomial.eval₂Hom (RingHom.id K) ![q 0,q 1,q 2]
         (residualAlgHom aY v bY aS bS cS F):=by rw [←hq]
   _=MvPolynomial.eval₂Hom (RingHom.id K)
         ![aY+v*q 0+bY*q 2,
           aS+v*q 1+bS*q 0+cS*q 2,
           q 2] F:=by
     simpa only [Algebra.algebraMap_self,RingHom.id_apply] using
       (eval₂Hom_residual F (q 0) (q 1) (q 2) aY v bY aS bS cS)
   _=_:=by rw [hforward]
theorem comap_pointKernel_residualEquiv
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3 → K):
   (RingHom.ker (MvPolynomial.aeval q).toRingHom).comap
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom=
     RingHom.ker
       (MvPolynomial.aeval
         (forwardResidualPoint aY v bY aS bS cS q)).toRingHom:=by
 ext F
 simp only [Ideal.mem_comap,RingHom.mem_ker]
 change MvPolynomial.eval q
     (residualEquiv aY v bY aS bS cS hv F)=0 ↔
   MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F=0
 rw [eval_residualEquiv]
structure RegularPrimeData (G T H:Poly3 K) where
 ideal:Ideal (Poly3 K)
 isPrime:ideal.IsPrime
 G_mem:G∈ideal
 T_mem:T∈ideal
 H_not_mem:H∉ideal
 ne_point:∀ q:Fin 3 → K,
   ideal≠RingHom.ker (MvPolynomial.aeval q).toRingHom
def RegularPrimeData.mulRegularityUnit
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (c:K) (hc:c≠0):
   RegularPrimeData G T (MvPolynomial.C c*H):=by
 have hu:IsUnit (MvPolynomial.C c:Poly3 K):=
   (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
 refine {
   ideal:=D.ideal
   isPrime:=D.isPrime
   G_mem:=D.G_mem
   T_mem:=D.T_mem
   H_not_mem:=?_
   ne_point:=D.ne_point
 }
 intro hmem
 exact D.H_not_mem ((D.ideal.unit_mul_mem_iff_mem hu).mp hmem)
@[simp] theorem RegularPrimeData.mulRegularityUnit_ideal
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (c:K) (hc:c≠0):
   (D.mulRegularityUnit c hc).ideal=D.ideal:=rfl
def RegularPrimeData.mapResidual
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   RegularPrimeData
     (residualAlgHom aY v bY aS bS cS G)
     (residualAlgHom aY v bY aS bS cS T)
     (residualAlgHom aY v bY aS bS cS H):=by
 let E:=residualEquiv aY v bY aS bS cS hv
 let Pnext:Ideal (Poly3 K):=D.ideal.map E.toRingEquiv.toRingHom
 letI:D.ideal.IsPrime:=D.isPrime
 haveI:Pnext.IsPrime:=Ideal.map_isPrime_of_equiv E.toRingEquiv
 refine {
   ideal:=Pnext
   isPrime:=inferInstance
   G_mem:=?_
   T_mem:=?_
   H_not_mem:=?_
   ne_point:=?_
 }
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.G_mem
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.T_mem
 · intro hmem
   exact D.H_not_mem
     ((Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=H)).mp hmem)
 · intro q heq
   apply D.ne_point (forwardResidualPoint aY v bY aS bS cS q)
   have hback:Pnext.comap E.toRingEquiv.toRingHom=D.ideal:=by
     ext F
     exact Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=F)
   rw [←hback,heq,
     comap_pointKernel_residualEquiv aY v bY aS bS cS hv q]
@[simp] theorem RegularPrimeData.mapResidual_ideal
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   (D.mapResidual aY v bY aS bS cS hv).ideal=
     D.ideal.map
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom:=rfl
end
end ProximityPrize.SubmissionLower.RCN162
end PackedLegacy_Z5

/-! Packed from ProximityPrize.SubmissionLower.AE. -/
section PackedLegacy_AE
namespace ProximityPrize.SubmissionLower.RCN272
open scoped Classical BigOperators
open RCN002 RCN007 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance _root_.ProximityPrize.SubmissionLower.RCN272.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN272.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
def FiniteZeroSetBound
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (A:MvPolynomial (Fin 3) Ω) (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → Ω),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v A=0) →
   points.card ≤ cost
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN272.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN272
end PackedLegacy_AE

/-! Packed from ProximityPrize.SubmissionLower.BR. -/
section PackedLegacy_BR
namespace ProximityPrize.SubmissionLower.RCN165
open scoped Classical
open RCN095 RCN094 RCN162 RCN272
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN165.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
structure PrimeFlagZeroBudget
   (P:Ideal (Poly3 K)) (cost:FlagDegree → ℕ) where
 zero_le:∀ (r:FlagDegree) (A:Poly3 K),
   PolynomialInFlag r A → A∉P → FiniteZeroSetBound P A (cost r)
end
end ProximityPrize.SubmissionLower.RCN165
end PackedLegacy_BR

/-! Packed from ProximityPrize.SubmissionLower.BE. -/
section PackedLegacy_BE
namespace ProximityPrize.SubmissionLower.RCN123
open scoped Classical
open RCN095 RCN125 RCN371 RCN011
 RCN009 RCN012
noncomputable section
variable {K:Type} [Field K]
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
structure FlagTrapezoidCaps (p:FlagDegree) (F:Poly3 K):Prop where
 uOuter:(planeMap K uOrder F).natDegree ≤ p.all
 uTotal:∀ d∈(rationalMap K uOrder F).support,
   d 0+d 1 ≤ p.zOnly+p.yz+p.all
 vOuter:(planeMap K vOrder F).natDegree ≤ p.yz+p.all
 vTotal:∀ d∈(rationalMap K vOrder F).support,
   d 0+d 1 ≤ p.zOnly+p.yz+p.all
 zOuter:(planeMap K zOrder F).natDegree ≤ p.all
 zTotal:∀ d∈(rationalMap K zOrder F).support,
   d 0+d 1 ≤ p.yz+p.all
public theorem degreeOf_s_le
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.PolynomialInFlag p F):
   F.degreeOf 1 ≤ p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hF d hd).1
public theorem degreeOf_y_le
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.PolynomialInFlag p F):
   F.degreeOf 0 ≤ p.yz+p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (Nat.le_add_right (d 0) (d 1)).trans (hF d hd).2.1
theorem flagTrapezoidCaps_of_inFlag
   (p:FlagDegree) (F:Poly3 K)
   (hF:RCN125.PolynomialInFlag p F):
   FlagTrapezoidCaps p F:=by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · exact (planeMap_natDegree_le K uOrder F).trans
     (by simpa [uOrder] using degreeOf_s_le hF)
 · apply rationalMap_joint_support_of_original K uOrder F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 1+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
   simpa [uOrder] using h'
 · exact (planeMap_natDegree_le K vOrder F).trans
     (by simpa [vOrder,Equiv.swap_apply_def] using degreeOf_y_le hF)
 · apply rationalMap_joint_support_of_original K vOrder F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 0+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
   simpa [vOrder,Equiv.swap_apply_def] using h'
 · exact (planeMap_natDegree_le K zOrder F).trans
     (by simpa [zOrder,Equiv.swap_apply_def] using degreeOf_s_le hF)
 · apply rationalMap_joint_support_of_original K zOrder F _
   intro d hd
   have h:=(hF d hd).2.1
   simpa [zOrder,Equiv.swap_apply_def,Nat.add_comm] using h
theorem flagTrapezoidCaps_flagAlgHom
   (p:FlagDegree) (F:Poly3 K) (lam mu nu:K)
   (hF:F.support ⊆ flagSupport p):
   FlagTrapezoidCaps p (flagAlgHom lam mu nu F):=by
 apply flagTrapezoidCaps_of_inFlag
 apply polynomialInFlag_flagAlgHom p F lam mu nu
 intro d hd
 exact (mem_flagSupport_iff p d).mp (hF hd)
theorem u_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
   m*376+5*98434322-m*5 ≤ flagYZMixedCap:=by
 rw [flag_mixed_values.2.2.1]
 omega
theorem v_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 6684622):
   m*376+26*98434322-m*26 ≤ flagAllMixedCap:=by
 rw [flag_mixed_values.2.2.2]
 omega
theorem z_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
   m*26+5*6684622-m*5 ≤ flagZMixedCap:=by
 rw [flag_mixed_values.2.1]
 omega
end
end ProximityPrize.SubmissionLower.RCN123
end PackedLegacy_BE

/-! Packed from ProximityPrize.SubmissionLower.Z2. -/
section PackedLegacy_Z2
namespace ProximityPrize.SubmissionLower.RCN121
open RCN095
theorem flagMixed_projection_decomposition
   (p q r:FlagDegree):
   flagMixed p q r=
     r.zOnly*flagMixed p q unitZFlag+
     r.yz*flagMixed p q unitYZFlag+
     r.all*flagMixed p q unitAllFlag:=by
 cases p
 cases q
 cases r
 simp [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem trapezoid_budget_mono
   (n mCap totalG totalT m:ℕ)
   (hn:n ≤ totalG) (hm:m ≤ mCap):
   m*totalG+n*totalT-m*n ≤
     mCap*totalG+n*totalT-mCap*n:=by
 let delta:=totalG-n
 have hsplit:totalG=n+delta:=by
   dsimp only [delta]
   omega
 have hdecomp (a:ℕ):
     a*totalG=a*n+a*delta:=by
   rw [hsplit,Nat.mul_add]
 have hdelta:m*delta ≤ mCap*delta:=
   Nat.mul_le_mul_right delta hm
 rw [hdecomp m,hdecomp mCap]
 omega
theorem u_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.all):
   m*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-m*p.all ≤
     flagMixed p q unitYZFlag:=by
 calc
   m*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-m*p.all ≤
       q.all*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-q.all*p.all:=
     trapezoid_budget_mono p.all q.all
       (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all) m
       (by omega) hm
   _=flagMixed p q unitYZFlag:=by
     have hsum:
         q.all*(p.zOnly+p.yz+p.all)+
             p.all*(q.zOnly+q.yz+q.all)=
           q.all*p.all+flagMixed p q unitYZFlag:=by
       simp [flagMixed,unitYZFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
theorem v_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.yz+q.all):
   m*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           m*(p.yz+p.all) ≤
     flagMixed p q unitAllFlag:=by
 calc
   m*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           m*(p.yz+p.all) ≤
       (q.yz+q.all)*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           (q.yz+q.all)*(p.yz+p.all):=
     trapezoid_budget_mono (p.yz+p.all) (q.yz+q.all)
       (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all) m
       (by omega) hm
   _=flagMixed p q unitAllFlag:=by
     have hsum:
         (q.yz+q.all)*(p.zOnly+p.yz+p.all)+
             (p.yz+p.all)*(q.zOnly+q.yz+q.all)=
           (q.yz+q.all)*(p.yz+p.all)+
             flagMixed p q unitAllFlag:=by
       simp [flagMixed,unitAllFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
theorem z_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.all):
   m*(p.yz+p.all)+p.all*(q.yz+q.all)-m*p.all ≤
     flagMixed p q unitZFlag:=by
 calc
   m*(p.yz+p.all)+p.all*(q.yz+q.all)-m*p.all ≤
       q.all*(p.yz+p.all)+p.all*(q.yz+q.all)-
         q.all*p.all:=
     trapezoid_budget_mono p.all q.all (p.yz+p.all)
       (q.yz+q.all) m (by omega) hm
   _=flagMixed p q unitZFlag:=by
     have hsum:
         q.all*(p.yz+p.all)+p.all*(q.yz+q.all)=
           q.all*p.all+flagMixed p q unitZFlag:=by
       simp [flagMixed,unitZFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
end ProximityPrize.SubmissionLower.RCN121
end PackedLegacy_Z2

/-! Packed from ProximityPrize.SubmissionLower.I. -/
section PackedLegacy_I
namespace ProximityPrize.SubmissionLower.RCN237
open scoped Classical BigOperators
open RCN264 RCN095 RCN121 RCN165 RCN156 RCN213 RCN215 RCN275
noncomputable section
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure PrimeFlagBudgetFamily (p q:FlagDegree) where
 zCost:RegularComponent Omega G T H → ℕ
 yzCost:RegularComponent Omega G T H → ℕ
 allCost:RegularComponent Omega G T H → ℕ
 primeBudget:∀ C:RegularComponent Omega G T H,
   PrimeFlagZeroBudget C.1 (fun r↦
     r.zOnly*zCost C+r.yz*yzCost C+r.all*allCost C)
 sum_zCost_le:(∑ C:RegularComponent Omega G T H,zCost C) ≤
   flagMixed p q unitZFlag
 sum_yzCost_le:(∑ C:RegularComponent Omega G T H,yzCost C) ≤
   flagMixed p q unitYZFlag
 sum_allCost_le:(∑ C:RegularComponent Omega G T H,allCost C) ≤
   flagMixed p q unitAllFlag
def PrimeFlagBudgetFamily.weightedCost
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree) (C:RegularComponent Omega G T H):ℕ:=
 r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C
theorem PrimeFlagBudgetFamily.sum_weightedCost_le
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree):
   (∑ C:RegularComponent Omega G T H,B.weightedCost r C) ≤
     flagMixed p q r:=by
 calc
   (∑ C:RegularComponent Omega G T H,B.weightedCost r C)=
       r.zOnly*(∑ C:RegularComponent Omega G T H,B.zCost C)+
       r.yz*(∑ C:RegularComponent Omega G T H,B.yzCost C)+
       r.all*(∑ C:RegularComponent Omega G T H,B.allCost C):=by
     simp only [PrimeFlagBudgetFamily.weightedCost,
       Finset.sum_add_distrib,Finset.mul_sum]
   _ ≤ r.zOnly*flagMixed p q unitZFlag+
       r.yz*flagMixed p q unitYZFlag+
       r.all*flagMixed p q unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_left r.zOnly B.sum_zCost_le)
         (Nat.mul_le_mul_left r.yz B.sum_yzCost_le))
       (Nat.mul_le_mul_left r.all B.sum_allCost_le)
   _=flagMixed p q r:=(flagMixed_projection_decomposition p q r).symm
end
end ProximityPrize.SubmissionLower.RCN237
end PackedLegacy_I

/-! Packed from ProximityPrize.SubmissionLower.B1. -/
section PackedLegacy_B1
namespace ProximityPrize.SubmissionLower.RCN066
open scoped Classical BigOperators
open RCN072 RCN264 RCN095 RCN272 RCN165 RCN237
noncomputable section
variable {K:Type} [Field K]
abbrev Poly3:=MvPolynomial (Fin 3) K
theorem mem_iff_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} (h:A - B ∈ P):A ∈ P ↔ B ∈ P:=by
 constructor
 · intro hA
   simpa only [sub_sub_cancel] using P.sub_mem hA h
 · intro hB
   simpa only [sub_add_cancel] using P.add_mem h hB
theorem sub_mem_of_dvd (P:Ideal (Poly3 (K:=K)))
   {G A B:Poly3 (K:=K)} (hG:G ∈ P) (h:G ∣ A - B) :
   A - B ∈ P:=by
 obtain ⟨Q,hQ⟩:=h
 rw [hQ]
 exact P.mul_mem_right Q hG
theorem cutIdeal_eq_of_dvd_sub {G T T':Poly3 (K:=K)}
   (h:G ∣ T - T'):cutIdeal K G T = cutIdeal K G T':=by
 have hG:G ∈ cutIdeal K G T:=Ideal.subset_span (by simp)
 have hG':G ∈ cutIdeal K G T':=Ideal.subset_span (by simp)
 have hT:T ∈ cutIdeal K G T:=Ideal.subset_span (by simp)
 have hT':T' ∈ cutIdeal K G T':=Ideal.subset_span (by simp)
 have hd:=sub_mem_of_dvd (cutIdeal K G T) hG h
 have hd':=sub_mem_of_dvd (cutIdeal K G T') hG' h
 apply le_antisymm
 · apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hG'
   · exact (mem_iff_of_sub_mem _ hd').mpr hT'
 · apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hG
   · exact (mem_iff_of_sub_mem _ hd).mp hT
theorem regularComponents_eq_of_dvd_sub {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') :
   regularComponents K G T H = regularComponents K G T' H:=by
 classical
 ext P
 simp only [regularComponents_def,Finset.mem_filter,mem_componentFamily,
   cutIdeal_eq_of_dvd_sub h]
def regularComponentEquiv {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') :
   RegularComponent K G T H ≃ RegularComponent K G T' H :=
 Equiv.subtypeEquivRight (fun P => by rw [regularComponents_eq_of_dvd_sub h])
@[simp] theorem regularComponentEquiv_val {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') (C:RegularComponent K G T H) :
   (regularComponentEquiv h C).1 = C.1:=Equiv.subtypeEquivRight_apply_coe _ _
@[simp] theorem regularComponentEquiv_symm_val {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') (C:RegularComponent K G T' H) :
   ((regularComponentEquiv h).symm C).1 = C.1:=Equiv.subtypeEquivRight_symm_apply_coe _ _
theorem eval_eq_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} (h:A - B ∈ P) (v:Fin 3 → K)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
   MvPolynomial.aeval v A = MvPolynomial.aeval v B:=by
 have hz:=hv h
 change MvPolynomial.aeval v (A - B) = 0 at hz
 rw [map_sub] at hz
 exact sub_eq_zero.mp hz
theorem finiteZeroSetBound_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} {cost:ℕ}
   (h:A - B ∈ P) (hB:FiniteZeroSetBound P B cost) :
   FiniteZeroSetBound P A cost:=by
 intro points hpointsP hpointsA
 apply hB points hpointsP
 intro v hv
 rw [← eval_eq_of_sub_mem P h v (hpointsP v hv)]
 exact hpointsA v hv
def PolynomialInFlagMod (P:Ideal (Poly3 (K:=K)))
   (r:FlagDegree) (A:Poly3 (K:=K)):Prop :=
 ∃ B,PolynomialInFlag r B ∧ A - B ∈ P
theorem PrimeFlagZeroBudget.zero_le_congr
   {P:Ideal (Poly3 (K:=K))} {cost:FlagDegree → ℕ}
   (B:PrimeFlagZeroBudget P cost) (r:FlagDegree)
   (A:Poly3 (K:=K)) (hA:PolynomialInFlagMod P r A)
   (hproper:A ∉ P):FiniteZeroSetBound P A (cost r):=by
 obtain ⟨A',hflag,hcongr⟩:=hA
 have hproper':A' ∉ P:=by
   intro hmem
   exact hproper ((mem_iff_of_sub_mem P hcongr).mpr hmem)
 exact finiteZeroSetBound_of_sub_mem P hcongr (B.zero_le r A' hflag hproper')
def PrimeFlagBudgetFamily.ofCongruentCut
   {G T T' H:Poly3 (K:=K)} {p q:FlagDegree}
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H) p q) :
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q where
 zCost C:=B.zCost (regularComponentEquiv h C)
 yzCost C:=B.yzCost (regularComponentEquiv h C)
 allCost C:=B.allCost (regularComponentEquiv h C)
 primeBudget C:=B.primeBudget (regularComponentEquiv h C)
 sum_zCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.zCost] using B.sum_zCost_le
 sum_yzCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.yzCost] using B.sum_yzCost_le
 sum_allCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.allCost] using B.sum_allCost_le
end
end ProximityPrize.SubmissionLower.RCN066
end PackedLegacy_B1

/-! Packed from ProximityPrize.SubmissionLower.E5. -/
section PackedLegacy_E5
namespace ProximityPrize.SubmissionLower.RCN263
open RCN136 RCN231 RCN313 RCN238 RCN156 RCN234 RCN095 RCN275 RCN262 RCN066
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
def reducedAgreementDirection (P:ResidualSupportParameters):FlagDegree :=
 ⟨2 * (P.total - P.ys),2 * (P.ys - P.s),2 * P.s - 2⟩
def reducedResidualAgreementFlag
   (P:ResidualSupportParameters) (d:ℕ):FlagDegree :=
 ⟨(reducedAgreementDirection P).zOnly * d,
   1 + (reducedAgreementDirection P).yz * d,
   (reducedAgreementDirection P).all * d⟩
theorem reducedResidualAgreementFlag_ys
   (P:ResidualSupportParameters) (d:ℕ) :
   (reducedResidualAgreementFlag P d).yz +
       (reducedResidualAgreementFlag P d).all =
     1 + d * (2 * P.ys - 2):=by
 have hs:=P.s_le_ys
 have h1:=P.one_le_s
 have hcoeff :
     2 * (P.ys - P.s) + (2 * P.s - 2) = 2 * P.ys - 2:=by
   rw [Nat.mul_sub_left_distrib]
   omega
 simp only [reducedResidualAgreementFlag,reducedAgreementDirection]
 rw [← hcoeff]
 ring
theorem reducedResidualAgreementFlag_total
   (P:ResidualSupportParameters) (d:ℕ) :
   (reducedResidualAgreementFlag P d).zOnly +
       (reducedResidualAgreementFlag P d).yz +
       (reducedResidualAgreementFlag P d).all =
     1 + d * (2 * P.total - 2):=by
 have hs:=P.s_le_ys
 have ht:=P.ys_le_total
 have h1:=P.one_le_s
 have hcoeff:2 * (P.total - P.ys) + 2 * (P.ys - P.s) +
     (2 * P.s - 2) = 2 * P.total - 2:=by
   rw [Nat.mul_sub_left_distrib,Nat.mul_sub_left_distrib]
   omega
 simp only [reducedResidualAgreementFlag,reducedAgreementDirection]
 rw [← hcoeff]
 ring
theorem surfaceMap_reducedAgreement_in_flag
   (phi:Polynomial K →+* Omega) (P:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K) :
   PolynomialInFlag (reducedResidualAgreementFlag P d)
     (surfaceMap phi
       (reducedAgreementNumerator F P.s d coeffs x u0 u1)):=by
 have hR:=reducedAgreementNumerator_R_degree_bound F P.s P.one_le_s
   H.coordinate_bounds.2.1 d coeffs x u0 u1
 have hYS:=reducedAgreementNumerator_wt_le residualYSWeights rfl rfl rfl
   F P.s P.ys P.one_le_s P.two_le_ys H.ys_weight d coeffs x u0 u1
 have hTotal:=reducedAgreementNumerator_wt_le residualTotalWeights rfl rfl rfl
   F P.s P.total P.one_le_s (P.two_le_ys.trans P.ys_le_total)
   H.total_weight d coeffs x u0 u1
 rw [show residualYSWeights 3 = 0 from rfl] at hYS
 rw [show residualTotalWeights 3 = 1 from rfl] at hTotal
 norm_num at hYS hTotal
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi
     (reducedAgreementNumerator F P.s d coeffs x u0 u1) he)
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS :=
   (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal :=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ _ at hqYS
 change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ _ at hqTotal
 norm_num at hqYS hqTotal
 change q 2 ≤ (reducedResidualAgreementFlag P d).all ∧
   q 1 + q 2 ≤ (reducedResidualAgreementFlag P d).yz +
     (reducedResidualAgreementFlag P d).all ∧
   q 1 + q 2 + q 3 ≤ (reducedResidualAgreementFlag P d).zOnly +
     (reducedResidualAgreementFlag P d).yz +
     (reducedResidualAgreementFlag P d).all
 refine ⟨?_,?_,?_⟩
 · change q 2 ≤ (2 * P.s - 2) * d
   have hs:2 * (P.s - 1) = 2 * P.s - 2:=by omega
   have heq:2 * d * (P.s - 1) = (2 * P.s - 2) * d:=by
     rw [← hs]
     ring
   rw [heq] at hqR
   exact hqR
 · rw [reducedResidualAgreementFlag_ys]
   have hs:2 * (P.ys - 1) = 2 * P.ys - 2:=by omega
   have heq:2 * d * (P.ys - 1) = d * (2 * P.ys - 2):=by
     rw [← hs]
     ring
   rw [heq] at hqYS
   exact hqYS
 · rw [reducedResidualAgreementFlag_total]
   have hs:2 * (P.total - 1) = 2 * P.total - 2:=by
     have:=P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
     omega
   have heq:2 * d * (P.total - 1) = d * (2 * P.total - 2):=by
     rw [← hs]
     ring
   rw [heq] at hqTotal
   exact hqTotal
end
end ProximityPrize.SubmissionLower.RCN263
end PackedLegacy_E5

/-! Packed from ProximityPrize.SubmissionLower.Y3. -/
section PackedLegacy_Y3
namespace ProximityPrize.SubmissionLower.RCN055
open RCN077 RCN313 RCN347
noncomputable section
section Algebra
variable {K:Type*} [CommRing K]
def horizontalDerivation:Derivation K (Poly4 K) (Poly4 K):=
 MvPolynomial.pderiv (0:Fin 4)+
   (MvPolynomial.X (2:Fin 4):Poly4 K) • MvPolynomial.pderiv (1:Fin 4)
def baseDerivation (F:Poly4 K):Derivation K (Poly4 K) (Poly4 K):=
 polyH K F • horizontalDerivation+polyG K F • MvPolynomial.pderiv (2:Fin 4)
theorem baseDerivation_apply (F P:Poly4 K):
   baseDerivation F P=polyH K F*
     (MvPolynomial.pderiv (0:Fin 4) P+
       MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)+
     polyG K F*MvPolynomial.pderiv (2:Fin 4) P:=by
 simp only [baseDerivation,horizontalDerivation,Derivation.add_apply,
   Derivation.smul_apply,smul_eq_mul]
theorem numeratorStep_eq (F P:Poly4 K) (b:ℕ):
   numeratorStep K F b P=polyH K F*baseDerivation F P-
     (2*b:ℕ)*P*baseDerivation F (polyH K F):=by
 simp only [numeratorStep,clearedStep,baseDerivation_apply]
 ring
theorem numerator_one (F:Poly4 K):
   numerator K F 1=MvPolynomial.X (2:Fin 4)*polyH K F^2:=by
 simp [numerator,numeratorStep,clearedStep,MvPolynomial.pderiv_X]
theorem baseDerivation_R (F:Poly4 K):
   baseDerivation F (MvPolynomial.X (2:Fin 4))=polyG K F:=by
 simp [baseDerivation_apply,MvPolynomial.pderiv_X]
theorem numerator_two (F:Poly4 K):
   numerator K F 2=polyH K F^3*polyG K F:=by
 rw [numerator_succ,numerator_one,numeratorStep_eq,leibniz_product,
   baseDerivation_R,Derivation.leibniz_pow]
 simp only [smul_eq_mul,nsmul_eq_mul,Nat.reduceSub,Nat.cast_ofNat]
 ring
def baseNumerator (F:Poly4 K):ℕ → Poly4 K
 | 0 => polyG K F
 | n+1 => polyH K F*baseDerivation F (baseNumerator F n)-
     (2*n+1:ℕ)*baseNumerator F n*baseDerivation F (polyH K F)
theorem numeratorStep_H_cube (F P:Poly4 K) (n:ℕ):
   numeratorStep K F (n+2) (polyH K F^3*P)=
     polyH K F^3*(polyH K F*baseDerivation F P-
       (2*n+1:ℕ)*P*baseDerivation F (polyH K F)):=by
 rw [numeratorStep_eq,leibniz_product,Derivation.leibniz_pow]
 simp only [smul_eq_mul,nsmul_eq_mul,Nat.reduceSub,Nat.cast_add,
   Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
 ring
theorem numerator_eq_H_cube (F:Poly4 K) (n:ℕ):
   numerator K F (n+2)=polyH K F^3*baseNumerator F n:=by
 induction n with
 | zero => exact numerator_two F
 | succ n ih =>
   rw [show n+1+2=(n+2)+1 by omega,numerator_succ,ih,
     numeratorStep_H_cube]
   rfl
end Algebra
section Agreement
variable {K:Type*} [Field K]
end Agreement
end
end ProximityPrize.SubmissionLower.RCN055
end PackedLegacy_Y3

/-! Packed from ProximityPrize.SubmissionLower.A6. -/
section PackedLegacy_A6
namespace ProximityPrize.SubmissionLower.RCN056
open RCN077 RCN313 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
def sameContribution (F:Poly4 K) (n j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*horizontalDerivation P-
   (n+j:ℕ)*P*horizontalDerivation (polyH K F)+
     (j:ℕ)*P*MvPolynomial.pderiv (2:Fin 4) (polyG K F)
def downContribution (F:Poly4 K) (j:ℕ) (P:Poly4 K):Poly4 K:=
 (j:ℕ)*P*horizontalDerivation (polyG K F)
def upContribution (F:Poly4 K) (n j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*MvPolynomial.pderiv (2:Fin 4) P-
   (n+j:ℕ)*P*MvPolynomial.pderiv (2:Fin 4) (polyH K F)
def baseMonomial (F:Poly4 K) (k j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F^(k-j)*polyG K F^j*P
def baseStep (F:Poly4 K) (n:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*baseDerivation F P-
   (2*n+1:ℕ)*P*baseDerivation F (polyH K F)
theorem baseStep_monomial (F P:Poly4 K) (n j:ℕ) (hj:j ≤ n+1):
   baseStep F n (baseMonomial F (n+1) j P)=
     baseMonomial F (n+2) j (sameContribution F n j P)+
     baseMonomial F (n+2) (j-1) (downContribution F j P)+
     baseMonomial F (n+2) (j+1) (upContribution F n j P):=by
 cases j with
 | zero =>
   have he:n+2-1=n+1:=by omega
   simp only [baseStep,baseMonomial,sameContribution,downContribution,
     upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
     smul_eq_mul,Nat.sub_zero,Nat.zero_sub,Nat.cast_zero,zero_mul,mul_zero,
     pow_zero,mul_one,Nat.zero_add,he,add_zero,leibniz_product,
     Derivation.leibniz_pow,nsmul_eq_mul,Nat.add_sub_cancel]
   simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
   ring
 | succ j =>
   by_cases ht:j=n
   · subst j
     simp only [baseStep,baseMonomial,sameContribution,downContribution,
       upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
       smul_eq_mul,Nat.add_sub_add_left,Nat.add_sub_cancel,Nat.sub_self,
       Nat.reduceSub,Nat.add_sub_cancel_left,pow_zero,one_mul,
       leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul]
     simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
     ring
   · have hjn:j+1 ≤ n:=by omega
     obtain ⟨u,hu⟩:=Nat.exists_eq_add_of_le hjn
     subst n
     have e₁:j+1+u+1-(j+1)=u+1:=by omega
     have e₂:j+1+u+2-(j+1)=u+2:=by omega
     have e₃:j+1+u+2-j=u+3:=by omega
     have e₄:j+1+u+2-(j+1+1)=u+1:=by omega
     simp only [baseStep,baseMonomial,sameContribution,downContribution,
       upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
       smul_eq_mul,Nat.add_sub_cancel,e₁,e₂,e₃,e₄,
       leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul]
     simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
     ring
def coefficientStep (F:Poly4 K) (n:ℕ) (C:ℕ → Poly4 K) (j:ℕ):Poly4 K:=
 sameContribution F n j (C j)+downContribution F (j+1) (C (j+1))+
   if j=0 then 0 else upContribution F n (j-1) (C (j-1))
def baseCoefficients (F:Poly4 K):ℕ → ℕ → Poly4 K
 | 0,j => if j=1 then 1 else 0
 | n+1,j => coefficientStep F n (baseCoefficients F n) j
theorem baseCoefficients_zero (F:Poly4 K) (n j:ℕ) (hj:n+1 < j):
   baseCoefficients F n j=0:=by
 induction n generalizing j with
 | zero => simp [baseCoefficients,show j≠1 by omega]
 | succ n ih =>
   simp [baseCoefficients,coefficientStep,ih j (by omega),
     ih (j+1) (by omega),ih (j-1) (by omega),
     sameContribution,downContribution,upContribution]
theorem baseStep_sum (F:Poly4 K) (n:ℕ) (s:Finset ℕ) (P:ℕ → Poly4 K):
   baseStep F n (∑ j∈s,P j)=∑ j∈s,baseStep F n (P j):=by
 simp only [baseStep,map_sum,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]
theorem coefficientStep_represents (F:Poly4 K) (n:ℕ) (C:ℕ → Poly4 K)
   (hC:∀ j,n+1 < j → C j=0):
   baseStep F n (∑ j∈Finset.range (n+2),baseMonomial F (n+1) j (C j))=
     ∑ j∈Finset.range (n+3),baseMonomial F (n+2) j (coefficientStep F n C j):=by
 let a j:=baseMonomial F (n+2) j (sameContribution F n j (C j))
 let b j:=baseMonomial F (n+2) (j-1) (downContribution F j (C j))
 let c j:=baseMonomial F (n+2) (j+1) (upContribution F n j (C j))
 have ha:(∑ j∈Finset.range (n+2),a j)=∑ j∈Finset.range (n+3),a j:=by
   conv_rhs => rw [Finset.sum_range_succ]
   simp [a,hC (n+2) (by omega),sameContribution,baseMonomial]
 have hb0:b 0=0:=by simp [b,downContribution,baseMonomial]
 have hb2:b (n+2)=0:=by
   simp [b,hC (n+2) (by omega),downContribution,baseMonomial]
 have hb3:b (n+3)=0:=by
   simp [b,hC (n+3) (by omega),downContribution,baseMonomial]
 have hb:(∑ j∈Finset.range (n+2),b j)=
     ∑ j∈Finset.range (n+3),b (j+1):=by
   calc
     _=∑ j∈Finset.range (n+1),b (j+1):=by
       rw [Finset.sum_range_succ']
       simp only [hb0,add_zero]
     _=_:=by
       symm
       rw [Finset.sum_range_succ,Finset.sum_range_succ]
       simp only [show n+1+1=n+2 by omega,show n+2+1=n+3 by omega,
         hb2,hb3,add_zero]
 have hc:(∑ j∈Finset.range (n+2),c j)=
     ∑ j∈Finset.range (n+3),baseMonomial F (n+2) j
       (if j=0 then 0 else upContribution F n (j-1) (C (j-1))):=by
   conv_rhs => rw [Finset.sum_range_succ']
   simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,
     Nat.add_sub_cancel,baseMonomial,mul_zero,add_zero]
   rfl
 rw [baseStep_sum]
 calc
   _=∑ j∈Finset.range (n+2),(a j+b j+c j):=by
     apply Finset.sum_congr rfl
     intro j hj
     exact baseStep_monomial F (C j) n j (by have:=Finset.mem_range.mp hj;omega)
   _=(∑ j∈Finset.range (n+2),a j)+
       (∑ j∈Finset.range (n+2),b j)+(∑ j∈Finset.range (n+2),c j):=by
     simp only [Finset.sum_add_distrib]
   _=_:=by
     rw [ha,hb,hc]
     simp only [a,b,coefficientStep,baseMonomial,mul_add,
       Finset.sum_add_distrib,Nat.add_sub_cancel]
theorem baseNumerator_eq_sum (F:Poly4 K) (n:ℕ):
   baseNumerator F n=
     ∑ j∈Finset.range (n+2),baseMonomial F (n+1) j (baseCoefficients F n j):=by
 induction n with
 | zero => simp [baseNumerator,baseCoefficients,baseMonomial]
 | succ n ih =>
   change baseStep F n (baseNumerator F n)=_
   rw [ih,coefficientStep_represents F n _ (baseCoefficients_zero F n)]
   rfl
theorem numerator_eq_coefficient_sum (F:Poly4 K) (n:ℕ):
   numerator K F (n+2)=polyH K F^3*
     ∑ j∈Finset.range (n+2),
       polyH K F^(n+1-j)*polyG K F^j*baseCoefficients F n j:=by
 rw [numerator_eq_H_cube,baseNumerator_eq_sum]
 rfl
end
end ProximityPrize.SubmissionLower.RCN056
end PackedLegacy_A6

/-! Packed from ProximityPrize.SubmissionLower.DX. -/
section PackedLegacy_DX
namespace ProximityPrize.SubmissionLower.RCN053
open RCN077 RCN313 RCN055 RCN056
noncomputable section
variable {K:Type*} [Field K]
def agreementLow (c:ℕ → K) (x u₀ u₁:K):Poly4 K:=
 MvPolynomial.C (c 0)*MvPolynomial.X (1:Fin 4)+
   MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))-affineSeedPolynomial u₀ u₁
def agreementHighCoefficient (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x:K)
   (n j:ℕ):Poly4 K:=
 MvPolynomial.C (c (n+2))*polyH K F^(d-(n+2)+3)*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2)
def agreementCoefficients (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x u₀ u₁:K)
   (j:ℕ):Poly4 K:=
 (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0)+
   ∑ n∈Finset.range (d-1),agreementHighCoefficient F d c x n j
theorem agreementNumerator_eq_low_add_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=polyH K F^(2*d)*agreementLow c x u₀ u₁+
     ∑ n∈Finset.range (d-1),commonNumeratorTerm F d c x (n+2):=by
 have hpow:polyH K F^2*polyH K F^(2*(d-1))=polyH K F^(2*d):=by
   rw [←pow_add,show 2+2*(d-1)=2*d by omega]
 unfold agreementNumerator clearedTaylorNumerator
 rw [show d+1=2+(d-1) by omega,Finset.sum_range_add]
 simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,
   show ∀ n:ℕ,2+n=n+2 from fun n => Nat.add_comm 2 n]
 simp only [commonNumeratorTerm,numerator_one,numerator_zero,Nat.sub_zero,
   pow_zero,mul_one,pow_one]
 unfold agreementLow
 linear_combination (MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4)))*hpow
theorem highCoefficient_monomial (F:Poly4 K) (d n j:ℕ)
   (hn:n+2 ≤ d) (hj:j ≤ n+1) (c:ℕ → K) (x:K):
   baseMonomial F (d-1) j (agreementHighCoefficient F d c x n j)=
     MvPolynomial.C (c (n+2))*polyH K F^3*
       (polyH K F^(n+1-j)*polyG K F^j*baseCoefficients F n j)*
         polyH K F^(2*(d-(n+2)))*
           (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2):=by
 have hp:polyH K F^(d-1-j)*polyH K F^(d-(n+2)+3)=
     polyH K F^3*polyH K F^(n+1-j)*polyH K F^(2*(d-(n+2))):=by
   simp only [←pow_add]
   congr 1
   omega
 unfold baseMonomial agreementHighCoefficient
 linear_combination (MvPolynomial.C (c (n+2))*polyG K F^j*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2))*hp
theorem commonNumeratorTerm_eq_coefficient_sum (F:Poly4 K) (d n:ℕ)
   (hn:n+2 ≤ d) (c:ℕ → K) (x:K):
   commonNumeratorTerm F d c x (n+2)=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
 have hs:(∑ j∈Finset.range (n+2),baseMonomial F (d-1) j
     (agreementHighCoefficient F d c x n j))=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
   apply Finset.sum_subset (Finset.range_mono hn)
   intro j _ hj
   have hz:=baseCoefficients_zero F n j (by simp only [Finset.mem_range] at hj;omega)
   simp only [baseMonomial,agreementHighCoefficient,hz,mul_zero,zero_mul]
 rw [←hs]
 unfold commonNumeratorTerm
 rw [numerator_eq_coefficient_sum]
 simp only [Finset.mul_sum,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro j hj
 simpa only [mul_assoc] using (highCoefficient_monomial F d n j hn
   (by have:=Finset.mem_range.mp hj;omega) c x).symm
theorem agreementNumerator_eq_coefficient_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=
     ∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
       agreementCoefficients F d c x u₀ u₁ j:=by
 rw [agreementNumerator_eq_low_add_sum F d hd c x u₀ u₁]
 have hlo:(∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
     (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0))=
     polyH K F^(2*d)*agreementLow c x u₀ u₁:=by
   rw [Finset.sum_eq_single 0]
   · simp only [Nat.sub_zero,pow_zero,mul_one,if_true]
     rw [←mul_assoc, ←pow_add,show d-1+(d+1)=2*d by omega]
   · intro j _ hj
     simp only [if_neg hj,mul_zero]
   · intro hj
     exact (hj (Finset.mem_range.mpr (by omega))).elim
 simp only [agreementCoefficients,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
 rw [hlo,Finset.sum_comm]
 apply congrArg (fun P:Poly4 K => polyH K F^(2*d)*agreementLow c x u₀ u₁+P)
 apply Finset.sum_congr rfl
 intro n hn
 exact commonNumeratorTerm_eq_coefficient_sum F d n
   (by have:=Finset.mem_range.mp hn;omega) c x
end
end ProximityPrize.SubmissionLower.RCN053
end PackedLegacy_DX

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier14 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DZ. -/
section PackedLegacy_DZ
namespace ProximityPrize.SubmissionLower.RCN057
open RCN313 RCN055 RCN056 RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
public theorem pderiv_eq_zero_of_wt_lt (weights:Fin 4 → ℕ) (P:Poly K) (i:Fin 4)
   (hP:wt weights P < weights i):MvPolynomial.pderiv i P=0:=by
 apply MvPolynomial.support_eq_empty.mp
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro d hd
 have hh:=MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 change Finsupp.weight weights d+weights i ≤ wt weights P at hh
 omega
def WeightBound (w:Fin 4 → ℕ) (P:Poly K) (c:ℤ):Prop:=
 P=0∨(wt w P:ℤ) ≤ c
namespace WeightBound
variable {w:Fin 4 → ℕ} {P Q:Poly K} {a b:ℤ}
theorem mono (h:WeightBound w P a) (hab:a ≤ b):WeightBound w P b:=
 h.imp_right (fun hp => hp.trans hab)
theorem add (hP:WeightBound w P a) (hQ:WeightBound w Q a):
   WeightBound w (P+Q) a:=by
 rcases hP with rfl | hp
 · simpa only [zero_add] using hQ
 rcases hQ with rfl | hq
 · rw [add_zero]
   exact Or.inr hp
 right
 have h:(wt w (P+Q):ℤ) ≤ max (wt w P:ℤ) (wt w Q:ℤ):=by
   exact_mod_cast wt_add_le w P Q
 exact h.trans (max_le hp hq)
theorem neg (hP:WeightBound w P a):WeightBound w (-P) a:=by
 rcases hP with rfl | hp
 · exact Or.inl neg_zero
 exact Or.inr (by simpa only [wt_neg] using hp)
theorem sub (hP:WeightBound w P a) (hQ:WeightBound w Q a):
   WeightBound w (P-Q) a:=by
 simpa only [sub_eq_add_neg] using hP.add hQ.neg
theorem mul (hP:WeightBound w P a) (hQ:WeightBound w Q b):
   WeightBound w (P*Q) (a+b):=by
 rcases hP with rfl | hp
 · exact Or.inl (zero_mul _)
 rcases hQ with rfl | hq
 · exact Or.inl (mul_zero _)
 right
 have h:(wt w (P*Q):ℤ) ≤ (wt w P:ℤ)+(wt w Q:ℤ):=by
   exact_mod_cast wt_mul_le w P Q
 linarith
theorem natCast (n:ℕ):WeightBound w (n:Poly K) 0:=
 Or.inr (by simp only [wt_natCast,Nat.cast_zero,le_refl])
theorem scale (n:ℕ) (hP:WeightBound w P a):WeightBound w ((n:Poly K)*P) a:=by
 simpa only [zero_add] using (natCast n).mul hP
theorem pderiv (hP:WeightBound w P a) (i:Fin 4):
   WeightBound w (MvPolynomial.pderiv i P) (a-w i):=by
 by_cases hz:MvPolynomial.pderiv i P=0
 · exact Or.inl hz
 rcases hP with rfl | hp
 · exact (hz (map_zero _)).elim
 right
 have hi:w i ≤ wt w P:=by
   by_contra hh
   exact hz (pderiv_eq_zero_of_wt_lt w P i (by omega))
 have hd:=wt_pderiv_le w P i (wt w P) le_rfl
 have hsum:wt w (MvPolynomial.pderiv i P)+w i ≤ wt w P:=by omega
 have hsum':(wt w (MvPolynomial.pderiv i P):ℤ)+w i ≤ wt w P:=by
   exact_mod_cast hsum
 linarith
theorem horizontal (hP:WeightBound w P a) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1):
   WeightBound w (horizontalDerivation P) (a+1-t):=by
 have hx:=hP.pderiv (0:Fin 4)
 have hy:=hP.pderiv (1:Fin 4)
 have hr:WeightBound w (MvPolynomial.X (2:Fin 4):Poly K) 1:=
   Or.inr (by simp only [wt_X,hR,Nat.cast_one,le_refl])
 simp only [hX,Nat.cast_zero,sub_zero] at hx
 rw [hY] at hy
 have hxy:WeightBound w (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)
     (a+1-t):=by convert hr.mul hy using 1;ring
 have ht':(t:ℤ) ≤ 1:=by exact_mod_cast ht
 simpa only [horizontalDerivation,Derivation.add_apply,Derivation.smul_apply,
   smul_eq_mul] using (hx.mono (by linarith)).add hxy
end WeightBound
theorem contribution_bounds (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
   (F P:Poly K) (C a:ℤ) (hF:WeightBound w F C) (hP:WeightBound w P a)
   (n j:ℕ):
   WeightBound w (sameContribution F n j P) (a+C-t)∧
   WeightBound w (downContribution F j P) (a+C+2-2*t)∧
   WeightBound w (upContribution F n j P) (a+C-2):=by
 have hH:WeightBound w (polyH K F) (C-1):=by
   simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
 have hG:WeightBound w (polyG K F) (C+1-t):=by
   simpa only [polyG,horizontalDerivation,Derivation.add_apply,
     Derivation.smul_apply,smul_eq_mul] using (hF.horizontal t hX hY hR ht).neg
 have hDH:=hH.horizontal t hX hY hR ht
 have hDG:=hG.horizontal t hX hY hR ht
 have hDP:=hP.horizontal t hX hY hR ht
 have hGR:=hG.pderiv (2:Fin 4)
 have hHR:=hH.pderiv (2:Fin 4)
 have hPR:=hP.pderiv (2:Fin 4)
 simp only [hR,Nat.cast_one] at hGR hHR hPR
 refine ⟨?_,?_,?_⟩
 · unfold sameContribution
   apply WeightBound.add
   · apply WeightBound.sub
     · convert hH.mul hDP using 1;ring
     · convert (hP.scale (n+j)).mul hDH using 1;ring
   · convert (hP.scale j).mul hGR using 1;ring
 · unfold downContribution
   convert (hP.scale j).mul hDG using 1;ring
 · unfold upContribution
   apply WeightBound.sub
   · convert hH.mul hPR using 1;ring
   · convert (hP.scale (n+j)).mul hHR using 1;ring
theorem baseCoefficients_weightBound (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
   (F:Poly K) (C:ℤ) (hF:WeightBound w F C) (n j:ℕ):
   WeightBound w (baseCoefficients F n j)
     (2-t+n*(C-t)-j*(2-t)):=by
 induction n generalizing j with
 | zero =>
   by_cases hj:j=1
   · subst j
     simp only [baseCoefficients,↓reduceIte]
     convert WeightBound.natCast (w:=w) (K:=K) 1 using 1 <;> push_cast <;> ring
   · exact Or.inl (by simp [baseCoefficients,hj])
 | succ n ih =>
   rw [baseCoefficients,coefficientStep]
   apply WeightBound.add
   · apply WeightBound.add
     · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih j) n j).1 using 1
       push_cast
       ring
     · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j+1)) n (j+1)).2.1
         using 1
       push_cast
       ring
   · by_cases hj:j=0
     · rw [if_pos hj]
       exact Or.inl rfl
     · rw [if_neg hj]
       have hj1:1 ≤ j:=by omega
       convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j-1)) n (j-1)).2.2
         using 1
       simp only [Nat.cast_sub hj1,Nat.cast_one,Nat.cast_add]
       ring
end
end ProximityPrize.SubmissionLower.RCN057
end PackedLegacy_DZ

/-! Packed from ProximityPrize.SubmissionLower.DY. -/
section PackedLegacy_DY
namespace ProximityPrize.SubmissionLower.RCN054
open RCN313 RCN055 RCN056 RCN057 RCN053 RCN234 RCN095
noncomputable section
variable {K:Type*} [Field K]
theorem weightBound_C (w:Fin 4 → ℕ) (c:K):
   WeightBound w (MvPolynomial.C c:Poly K) 0:=
 Or.inr (by simp only [wt_C,Nat.cast_zero,le_refl])
theorem weightBound_pow {w:Fin 4 → ℕ} {P:Poly K} {a:ℤ}
   (hP:WeightBound w P a) (n:ℕ):WeightBound w (P^n) (n*a):=by
 induction n with
 | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul,Nat.cast_one] using
     (WeightBound.natCast (w:=w) (K:=K) 1)
 | succ n ih =>
   rw [pow_succ]
   convert ih.mul hP using 1
   push_cast
   ring
theorem weightBound_sum {w:Fin 4 → ℕ} {a:ℤ} (I:Finset ℕ) (P:ℕ → Poly K)
   (hP:∀ i∈I,WeightBound w (P i) a):WeightBound w (∑ i∈I,P i) a:=by
 classical
 induction I using Finset.induction_on with
 | empty => exact Or.inl (by simp)
 | @insert i I hi ih =>
   rw [Finset.sum_insert hi]
   exact (hP i (Finset.mem_insert_self _ _)).add
     (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))
theorem weightBound_shift (w:Fin 4 → ℕ) (hX:w 0=0) (x:K):
   WeightBound w (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly K) 0:=
 (weightBound_C w x).sub (Or.inr (by simp only [wt_X,hX,Nat.cast_zero,le_refl]))
theorem agreementLow_weightBound (w:Fin 4 → ℕ) (hX:w 0=0)
   (hY:w 1 ≤ 1) (hR:w 2=1) (hZ:w 3 ≤ 1)
   (c:ℕ → K) (x u₀ u₁:K):WeightBound w (agreementLow c x u₀ u₁) 1:=by
 have hvar (i:Fin 4) (hi:w i ≤ 1):
     WeightBound w (MvPolynomial.X i:Poly K) 1:=by
   right
   rw [wt_X]
   exact_mod_cast hi
 have h₀:=(weightBound_C w (c 0)).mul (hvar 1 hY)
 have h₁:=((weightBound_C w (c 1)).mul (hvar 2 (by omega))).mul (weightBound_shift w hX x)
 have hseed:=((weightBound_C w u₀).mono (by norm_num:(0:ℤ) ≤ 1)).add
   (by simpa only [add_zero] using (hvar 3 hZ).mul (weightBound_C w u₁))
 simpa only [agreementLow,affineSeedPolynomial,zero_add,add_zero] using (h₀.add h₁).sub hseed
theorem agreementCoefficients_weightBound (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (hZ:w 3 ≤ 1) (ht:t ≤ 1)
   (F:Poly K) (C:ℤ) (hF:WeightBound w F C) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ):
   WeightBound w (agreementCoefficients F d c x u₀ u₁ j)
     ((d+1:ℕ)*(C-1)+1+(d-1:ℕ)*(1-(t:ℤ))-j*(2-(t:ℤ))):=by
 have ht':(t:ℤ) ≤ 1:=by exact_mod_cast ht
 have hH:WeightBound w (polyH K F) (C-1):=by
   simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
 unfold agreementCoefficients
 apply WeightBound.add
 · by_cases hj:j=0
   · subst j
     rw [if_pos rfl]
     apply ((weightBound_pow hH (d+1)).mul
       (agreementLow_weightBound w hX (by omega) hR hZ c x u₀ u₁)).mono
     simp only [Nat.cast_zero,zero_mul,sub_zero]
     have hn:(0:ℤ) ≤ (d-1:ℕ):=Nat.cast_nonneg _
     nlinarith
   · rw [if_neg hj]
     exact Or.inl rfl
 · apply weightBound_sum
   intro n hn
   have hn':n+2 ≤ d:=by have:=Finset.mem_range.mp hn;omega
   have he:((d-(n+2)+3:ℕ):ℤ)=(d:ℤ)-n+1:=by
     push_cast [Nat.cast_sub hn']
     ring
   have hn'':(n:ℤ)+2 ≤ d:=by exact_mod_cast hn'
   have hd':((d-1:ℕ):ℤ)=(d:ℤ)-1:=by omega
   have hterm:=(((weightBound_C w (c (n+2))).mul
     (weightBound_pow hH (d-(n+2)+3))).mul
       (baseCoefficients_weightBound w t hX hY hR ht F C hF n j)).mul
         (weightBound_pow (weightBound_shift w hX x) (n+2))
   apply hterm.mono
   rw [he,hd']
   push_cast
   nlinarith
theorem agreementCoefficients_support_bounds (F:Poly K) (s M L:ℕ)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ M)
   (hAll:wt ![0,1,1,1] F ≤ L) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ):
   (agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4) ≤ (d+1)*s-1-2*j∧
   wt ![0,1,1,0] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*M-d-j∧
   wt ![0,1,1,1] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*L-d-j:=by
 have hcoord (P:Poly K):wt (Pi.single (2:Fin 4) 1) P=P.degreeOf (2:Fin 4):=by
   rw [wt,MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
   apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
   funext e
   exact Finsupp.weight_single_one_apply _ e
 have hbound (w:Fin 4 → ℕ) (t:ℕ) (hX:w 0=0) (hY:w 1=t)
     (hR':w 2=1) (hZ:w 3 ≤ 1) (ht:t ≤ 1) (N:ℕ) (hF:wt w F ≤ N):=
   agreementCoefficients_weightBound w t hX hY hR' hZ ht F N
     (Or.inr (by exact_mod_cast hF)) d hd c x u₀ u₁ j
 constructor
 · have h:=hbound (Pi.single (2:Fin 4) 1) 0 (by simp) (by simp) (by simp)
     (by simp) (by omega) s (by simpa only [hcoord] using hR)
   rcases h with hz | hb
   · simp [hz]
   · rw [hcoord] at hb
     have he:((d-1:ℕ):ℤ)=(d:ℤ)-1:=by omega
     rw [he] at hb
     push_cast at hb
     have hh:((agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4):ℤ)+1+
         2*j ≤ (d+1:ℕ)*s:=by push_cast;nlinarith
     have hn:(agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4)+1+
         2*j ≤ (d+1)*s:=by exact_mod_cast hh
     omega
 · have cumulative (w:Fin 4 → ℕ) (hX:w 0=0) (hY:w 1=1)
       (hR':w 2=1) (hZ:w 3 ≤ 1) (N:ℕ) (hF:wt w F ≤ N):
       wt w (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*N-d-j:=by
     rcases hbound w 1 hX hY hR' hZ le_rfl N hF with hz | hb
     · simp [hz,wt,MvPolynomial.weightedTotalDegree]
     · have hh:(wt w (agreementCoefficients F d c x u₀ u₁ j):ℤ)+d+j ≤
           (d+1:ℕ)*N:=by push_cast at hb ⊢;nlinarith
       have hn:wt w (agreementCoefficients F d c x u₀ u₁ j)+d+j ≤
           (d+1)*N:=by exact_mod_cast hh
       omega
   exact ⟨cumulative _ rfl rfl rfl (by decide) M hYR,
     cumulative _ rfl rfl rfl (by decide) L hAll⟩
def coefficientFlag (a b s d j:ℕ):FlagDegree:=
 ⟨(d+1)*a,1+(d+1)*b-d+j,(d+1)*s-1-2*j⟩
def hFlag (a b s:ℕ):FlagDegree:=⟨a,b,s-1⟩
def gFlag (a b s:ℕ):FlagDegree:=⟨a,b-1,s+1⟩
def directionFlag (a b s:ℕ):FlagDegree:=⟨2*a,2*b-1,2*s-1⟩
theorem coefficientFlag_cumulative (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):
   (coefficientFlag a b s d j).all=(d+1)*s-1-2*j∧
   (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all=
     (d+1)*(b+s)-d-j∧
   (coefficientFlag a b s d j).zOnly+(coefficientFlag a b s d j).yz+
     (coefficientFlag a b s d j).all=(d+1)*(a+b+s)-d-j:=by
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 simp only [coefficientFlag,Nat.succ_eq_add_one,Nat.mul_add,Nat.add_mul,
   Nat.mul_one,Nat.one_mul]
 exact ⟨trivial,by omega,by omega⟩
theorem coefficientFlag_nonnegative_form (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):coefficientFlag a b s d j=
     ⟨(d+1)*a,(d+1)*(b-1)+2+j,
       (d+1)*(s-2)+3+2*(d-1-j)⟩:=by
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 dsimp only [coefficientFlag]
 congr 1 <;> simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.add_mul,Nat.mul_one,
   Nat.one_mul,Nat.add_sub_cancel_left] <;> omega
theorem coefficientFlag_add_baseMonomial (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):
   coefficientFlag a b s d j+(d-1-j) • hFlag a b s+j • gFlag a b s=
     unitYZFlag+d • directionFlag a b s:=by
 rw [coefficientFlag_nonnegative_form a b s d j hb hs hj]
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 have hk:j+1+k-1-j=k:=by omega
 have hs':2+s-1=1+s:=by omega
 have hb':2*(1+b)-1=1+2*b:=by omega
 have hs'':2*(2+s)-1=3+2*s:=by omega
 simp only [hk,hFlag,gFlag,directionFlag,unitYZFlag,Nat.add_sub_cancel_left,
   hs',hb',hs'']
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
   <;> dsimp <;> ring
theorem agreementCoefficients_in_flag (F:Poly K) (a b s:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ b+s)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ) (hj:j < d):
   ∀ e∈(agreementCoefficients F d c x u₀ u₁ j).support,
     e 2 ≤ (coefficientFlag a b s d j).all∧
     e 1+e 2 ≤ (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all∧
     e 1+e 2+e 3 ≤ (coefficientFlag a b s d j).zOnly+
       (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all:=by
 intro e he
 obtain ⟨hr,hyr,ht⟩:=agreementCoefficients_support_bounds F s (b+s) (a+b+s)
   hR hYR hAll d hd c x u₀ u₁ j
 obtain ⟨fr,fyr,ft⟩:=coefficientFlag_cumulative a b s d j hb hs hj
 rw [ft,fyr,fr]
 have heR:=(MvPolynomial.le_degreeOf_of_mem_support (2:Fin 4) he).trans hr
 have heYR:=(MvPolynomial.le_weightedTotalDegree ![0,1,1,0] he).trans hyr
 have heT:=(MvPolynomial.le_weightedTotalDegree ![0,1,1,1] he).trans ht
 rw [RCN081.weight_fin4] at heYR heT
 change e 0*0+e 1*1+e 2*1+e 3*0 ≤ _ at heYR
 change e 0*0+e 1*1+e 2*1+e 3*1 ≤ _ at heT
 simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.zero_add] at heYR heT
 exact ⟨heR,heYR,heT⟩
theorem surfaceMap_agreementCoefficients_in_flag {Ω:Type*} [Field Ω]
   (φ:Polynomial K →+*Ω) (F:Poly K) (a b s:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ b+s)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ) (hj:j < d):
   PolynomialInFlag (coefficientFlag a b s d j)
     (RCN136.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (RCN136.support_surfaceMap_subset φ _ he)
 exact agreementCoefficients_in_flag F a b s hb hs hR hYR hAll d hd c x u₀ u₁ j hj q hq
theorem surfaceMap_agreementNumerator_eq_coefficient_sum {Ω:Type*} [Field Ω]
   (φ:Polynomial K →+*Ω) (F:Poly K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   RCN136.surfaceMap φ (agreementNumerator F d c x u₀ u₁)=
     ∑ j∈Finset.range d,RCN136.surfaceMap φ (polyH K F)^(d-1-j)*
       RCN136.surfaceMap φ (polyG K F)^j*
         RCN136.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j):=by
 rw [agreementNumerator_eq_coefficient_sum F d hd c x u₀ u₁]
 simp only [map_sum,map_mul,map_pow]
end
end ProximityPrize.SubmissionLower.RCN054
end PackedLegacy_DY

/-! Packed from ProximityPrize.SubmissionLower.D2. -/
section PackedLegacy_D2
namespace ProximityPrize.SubmissionLower.RCN207
open scoped Classical BigOperators Pointwise
open RCN095
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
variable {K:Type*} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K
def filteredCut {R:Type*} [CommRing R] (k:ℕ) (B:Fin (k+1) → R)
   (H G:R):R:=∑ j,B j*H^(k-j.val)*G^j.val
def movingEquation (H G Q U:Poly) (t:K):Poly:=
 H*(MvPolynomial.C t-Q)-U*G
def eliminatedCut (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly) (t:K):Poly:=
 filteredCut k B U (MvPolynomial.C t-Q)
theorem map_filteredCut {R S:Type*} [CommRing R] [CommRing S]
   (ev:R →+*S) (k:ℕ) (B:Fin (k+1) → R) (H G:R):
   ev (filteredCut k B H G)=filteredCut k (fun j↦ev (B j)) (ev H) (ev G):=by
 simp [filteredCut]
theorem binary_clearing {R:Type*} [CommRing R] (k:ℕ) (B:Fin (k+1) → R)
   (H G U V:R) (hrel:H*V=U*G):
   H^k*filteredCut k B U V=U^k*filteredCut k B H G:=by
 unfold filteredCut
 rw [Finset.mul_sum,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro j _
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 have hh:H^k=H^(k-j.val)*H^j.val:=by rw [←pow_add,hj]
 have hu:U^k=U^(k-j.val)*U^j.val:=by rw [←pow_add,hj]
 calc
   _=B j*H^(k-j.val)*U^(k-j.val)*(H*V)^j.val:=by
     rw [hh,mul_pow];ring
   _=B j*H^(k-j.val)*U^(k-j.val)*(U*G)^j.val:=by rw [hrel]
   _=_:=by rw [hu,mul_pow];ring
theorem clearing_at_equation {R:Type*} [CommRing R] (ev:Poly →+*R)
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:ev (movingEquation H G Q U t)=0):
   ev H^k*ev (eliminatedCut k B Q U t)=
     ev U^k*ev (filteredCut k B H G):=by
 have hrel:ev H*ev (MvPolynomial.C t-Q)=ev U*ev G:=by
   simpa [movingEquation,sub_eq_zero] using hN
 simp only [eliminatedCut,map_filteredCut]
 exact binary_clearing k _ _ _ _ _ hrel
theorem eliminatedCut_zero_iff {L:Type*} [Field L] (ev:Poly →+*L)
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:ev (movingEquation H G Q U t)=0) (hH:ev H≠0) (hU:ev U≠0):
   ev (eliminatedCut k B Q U t)=0 ↔ ev (filteredCut k B H G)=0:=by
 have heq:=clearing_at_equation ev k B H G Q U t hN
 constructor
 · intro hz
   rw [hz,mul_zero] at heq
   exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hU)
 · intro hz
   rw [hz,mul_zero] at heq
   exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hH)
theorem original_mem_of_eliminated_mem (P:Ideal Poly) [P.IsPrime]
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:movingEquation H G Q U t∈P)
   (hT:eliminatedCut k B Q U t∈P) (hU:U∉P):
   filteredCut k B H G∈P:=by
 let ev:=Ideal.Quotient.mk P
 have heq:=clearing_at_equation ev k B H G Q U t
   (Ideal.Quotient.eq_zero_iff_mem.mpr hN)
 have hzero:ev (eliminatedCut k B Q U t)=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr hT
 have hUne:ev U≠0:=fun h↦hU (Ideal.Quotient.eq_zero_iff_mem.mp h)
 rw [hzero,mul_zero] at heq
 exact Ideal.Quotient.eq_zero_iff_mem.mp
   ((mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hUne))
theorem inFlag_const (p:FlagDegree) (c:K):PolynomialInFlag p (MvPolynomial.C c):=by
 intro d hd
 have hd0:d=0:=by
   by_contra h
   exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.coeff_C_of_ne_zero h _)
 subst d
 exact inFlag_zero p
public theorem flag_eq {p q:FlagDegree} (hx:p.zOnly=q.zOnly)
   (hy:p.yz=q.yz) (hz:p.all=q.all):p=q:=by
 cases p;cases q;simp_all
theorem inFlag_map {E:Type*} [Field E] (f:K →+*E)
   {p:FlagDegree} {A:Poly} (hA:PolynomialInFlag p A):
   PolynomialInFlag p (MvPolynomial.map f A):=by
 intro d hd
 exact hA d (MvPolynomial.support_map_subset f A hd)
theorem inFlag_sub_poly {p:FlagDegree} {A B:Poly}
   (hA:PolynomialInFlag p A) (hB:PolynomialInFlag p B):
   PolynomialInFlag p (A-B):=by
 intro d hd
 rcases Finset.mem_union.mp (MvPolynomial.support_sub (Fin 3) A B hd) with h | h
 · exact hA d h
 · exact hB d h
theorem inFlag_mul_poly {p q:FlagDegree} {A B:Poly}
   (hA:PolynomialInFlag p A) (hB:PolynomialInFlag q B):
   PolynomialInFlag (p+q) (A*B):=by
 intro d hd
 obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul A B hd)
 exact inFlag_add (hA a ha) (hB b hb)
theorem inFlag_pow_poly {p:FlagDegree} {A:Poly} (hA:PolynomialInFlag p A) (k:ℕ):
   PolynomialInFlag (k • p) (A^k):=by
 induction k with
 | zero => simpa using inFlag_const (0 • p) (1:K)
 | succ k ih =>
   have heq:(k+1) • p=k • p+p:=by
     apply flag_eq <;> simp only [nsmul_zOnly,nsmul_yz,nsmul_all,
       add_zOnly,add_yz,add_all] <;> ring
   rw [pow_succ,heq]
   exact inFlag_mul_poly ih hA
theorem inFlag_sum_poly {ι:Type*} (s:Finset ι) (p:FlagDegree) (A:ι → Poly)
   (hA:∀ i∈s,PolynomialInFlag p (A i)):PolynomialInFlag p (∑ i∈s,A i):=by
 intro d hd
 obtain ⟨i,hi,hdi⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
 exact hA i hi d hdi
theorem eliminatedCut_inFlag (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1) → FlagDegree) (P:FlagDegree)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U)
   (hc:∀ j,c j+(k-j.val) • unitYZFlag+j.val • (2 • unitAllFlag)=P):
   PolynomialInFlag P (eliminatedCut k B Q U t):=by
 unfold eliminatedCut filteredCut
 apply inFlag_sum_poly
 intro j _
 rw [←hc j]
 exact inFlag_mul_poly (inFlag_mul_poly (hB j) (inFlag_pow_poly hU _))
   (inFlag_pow_poly (inFlag_sub_poly (inFlag_const _ _) hQ) _)
theorem eliminatedCut_small_flag (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1) → Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1) → FlagDegree)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U)
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (eliminatedCut k B Q U t):=by
 apply eliminatedCut_inFlag k B Q U t c _ hB hQ hU
 intro j
 have hx:=congrArg FlagDegree.zOnly (hc j)
 have hy:=congrArg FlagDegree.yz (hc j)
 have hz:=congrArg FlagDegree.all (hc j)
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 apply flag_eq
 all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,
   nsmul_all,unitYZFlag,unitAllFlag] at*
 all_goals nlinarith
theorem movingEquation_inFlag (a b s:ℕ) (H G Q U:Poly) (t:K)
   (hH:PolynomialInFlag ⟨a,b+1,s+1⟩ H)
   (hG:PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U):
   PolynomialInFlag ⟨a,b+1,s+3⟩ (movingEquation H G Q U t):=by
 apply inFlag_sub_poly
 · have hc:(⟨a,b+1,s+1⟩:FlagDegree)+2 • unitAllFlag=⟨a,b+1,s+3⟩:=by
     apply flag_eq
     all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,
       nsmul_yz,nsmul_all,unitAllFlag]
     omega
   rw [←hc]
   exact inFlag_mul_poly hH (inFlag_sub_poly (inFlag_const _ _) hQ)
 · have hc:unitYZFlag+(⟨a,b,s+3⟩:FlagDegree)=⟨a,b+1,s+3⟩:=by
     apply flag_eq <;> simp only [add_zOnly,add_yz,add_all,unitYZFlag] <;> omega
   rw [←hc]
   exact inFlag_mul_poly hU hG
end
end ProximityPrize.SubmissionLower.RCN207
end PackedLegacy_D2

/-! Packed from ProximityPrize.SubmissionLower.Z8. -/
section PackedLegacy_Z8
namespace ProximityPrize.SubmissionLower.RCN198
open scoped Classical BigOperators
open RCN313 RCN136 RCN238 RCN053 RCN054 RCN095 RCN207 RCN234 RCN156 RCN275 RCN287
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Ω:Type} [Field K] [Field Ω]
def direction (a b s:ℕ):FlagDegree:=⟨2*a,2*b+1,2*s+3⟩
def center (a b s:ℕ):FlagDegree:=unitYZFlag+direction a b s
def support (a b s:ℕ):ResidualSupportParameters:=
 ⟨s+2,b+s+3,a+b+s+3,by omega,by omega,by omega,by omega⟩
theorem shifted_flags (a b s:ℕ):
   hFlag a (b+1) (s+2)=⟨a,b+1,s+1⟩∧
   gFlag a (b+1) (s+2)=⟨a,b,s+3⟩∧
   directionFlag a (b+1) (s+2)=direction a b s:=by
 refine ⟨?_,?_,?_⟩ <;>
   simp only [hFlag,gFlag,directionFlag,direction] <;> congr 1 <;> omega
theorem class_total (a b s k:ℕ):
   unitYZFlag+(k+1) • direction a b s=
     center a b s+k • direction a b s:=by
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [center,direction,unitYZFlag,
   add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
theorem support_data (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3):
   ResidualSupportData (support a b s) F:=by
 refine ⟨?_,hYR,hAll⟩
 have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
   funext i;fin_cases i <;> rfl
 simpa only [hw,wt,support,MvPolynomial.weightedTotalDegree_piSingle] using hR
theorem sharp_flag_eq (a b s d:ℕ):
   sharpResidualAgreementFlag (support a b s) d=
     unitYZFlag+d • direction a b s:=by
 have hdir:sharpAgreementDirection (support a b s)=direction a b s:=by
   simp only [sharpAgreementDirection,support,direction]
   congr 1 <;> omega
 simp only [sharpResidualAgreementFlag,hdir,direction,unitYZFlag]
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [add_zOnly,add_yz,add_all,
   nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
end
end ProximityPrize.SubmissionLower.RCN198
end PackedLegacy_Z8

/-! Packed from ProximityPrize.SubmissionLower.BZ. -/
section PackedLegacy_BZ
namespace ProximityPrize.SubmissionLower.RCN184
open scoped Classical BigOperators WithZero
open RCN187 RCN133 RCN295
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
 [DecidableEq σ] [Algebra K L]
def coefficientEvaluation (x:σ → L) (E:Finset (σ →₀ ℕ)):
   (E → K) →ₗ[K] L where
 toFun c:=MvPolynomial.eval₂Hom (algebraMap K L) x
   (polynomialOfSupport E c)
 map_add' c d:=by
   rw [show polynomialOfSupport E (c+d)=
       polynomialOfSupport E c+polynomialOfSupport E d by
     ext m
     by_cases hm:m∈E <;>
       simp [coeff_polynomialOfSupport,hm]]
   exact map_add (MvPolynomial.eval₂Hom (algebraMap K L) x)
     (polynomialOfSupport E c) (polynomialOfSupport E d)
 map_smul' a c:=by
   rw [show polynomialOfSupport E (a • c)=
       a • polynomialOfSupport E c by
     ext m
     by_cases hm:m∈E <;>
       simp [coeff_polynomialOfSupport,hm]]
   simpa [Algebra.smul_def] using
     MvPolynomial.eval₂Hom_smul (algebraMap K L) x a
       (polynomialOfSupport E c)
def livePoleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):σ →₀ ℕ:=
 d.filter (fun i↦x i≠0∧0 ≤ (v (x i)).log)
theorem livePoleTruncation_le
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   livePoleTruncation v x d ≤ d:=by
 intro i
 simp only [livePoleTruncation,Finsupp.filter_apply]
 split_ifs
 · exact le_rfl
 · exact Nat.zero_le _
theorem exponentValuationWeight_livePoleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   exponentValuationWeight v x (livePoleTruncation v x d)=
     exponentPoleWeight v x d:=by
 classical
 unfold exponentValuationWeight exponentPoleWeight poleOrder
 apply Finset.sum_congr rfl
 intro i _
 simp only [livePoleTruncation,Finsupp.filter_apply]
 by_cases hx:x i=0
 · simp [hx]
 · by_cases hlog:0 ≤ (v (x i)).log
   · rw [if_pos ⟨hx,hlog⟩,max_eq_right hlog]
   · have hle:(v (x i)).log ≤ 0:=le_of_not_ge hlog
     rw [if_neg (fun h↦hlog h.2),max_eq_left hle]
     simp
theorem livePoleTruncation_coordinate_ne_zero
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ) (i:σ)
   (hi:livePoleTruncation v x d i≠0):x i≠0:=by
 classical
 simp only [livePoleTruncation,Finsupp.filter_apply] at hi
 split at hi
 · exact ‹x i≠0∧0 ≤ (v (x i)).log›.1
 · exact (hi rfl).elim
public theorem exp_sum (s:Finset σ) (z:σ → ℤ):
   WithZero.exp (∑ i∈s,z i)=∏ i∈s,WithZero.exp (z i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp
 | @insert i s hi ih => simp [hi,ih,WithZero.exp_add]
theorem valuation_eval_monomial_one_eq_exp
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ)
   (hlive:∀ i,d i≠0 → x i≠0):
   v (MvPolynomial.eval₂Hom (algebraMap K L) x
       (MvPolynomial.monomial d (1:K)))=
     WithZero.exp (exponentValuationWeight v x d):=by
 classical
 rw [MvPolynomial.eval₂Hom_monomial,
   Finsupp.prod_fintype _ _ (fun _↦pow_zero _),map_mul,map_prod]
 simp only [map_one,one_mul,map_pow]
 rw [show WithZero.exp (exponentValuationWeight v x d)=
     ∏ i,WithZero.exp ((d i:ℤ)*(v (x i)).log) by
   unfold exponentValuationWeight
   simpa only using exp_sum (Finset.univ:Finset σ)
     (fun i↦(d i:ℤ)*(v (x i)).log)]
 apply Finset.prod_congr rfl
 intro i _
 by_cases hd:d i=0
 · simp [hd]
 · have hvx:v (x i)≠0:=
     (Valuation.ne_zero_iff v).mpr (hlive i hd)
   rw [show ((d i:ℤ)*(v (x i)).log)=
       d i • (v (x i)).log by simp,
     WithZero.exp_nsmul,WithZero.exp_log hvx]
theorem exists_mem_exponentPoleWeight_eq
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (hzero:0∈E):
   ∃ d∈E,exponentPoleWeight v x d=exponentSetPoleWeight v x E:=by
 classical
 let S:=insert (0:ℤ) (E.image (exponentPoleWeight v x))
 have hS:S.Nonempty:=⟨0,Finset.mem_insert_self 0 _⟩
 have hmem:S.max' hS∈S:=Finset.max'_mem S hS
 change S.max' hS∈insert (0:ℤ) (E.image (exponentPoleWeight v x)) at hmem
 rcases Finset.mem_insert.mp hmem with hmax | hmax
 · refine ⟨0,hzero,?_⟩
   unfold exponentSetPoleWeight
   change exponentPoleWeight v x 0=S.max' hS
   simp only [exponentPoleWeight,Finsupp.zero_apply,Nat.cast_zero,
     zero_mul,Finset.sum_const_zero]
   exact hmax.symm
 · obtain ⟨d,hd,heq⟩:=Finset.mem_image.mp hmax
   refine ⟨d,hd,?_⟩
   unfold exponentSetPoleWeight
   change exponentPoleWeight v x d=S.max' hS
   exact heq
def deltaCoefficient (E:Finset (σ →₀ ℕ)) (e:E):E → K:=
 fun d↦if d=e then 1 else 0
theorem polynomialOfSupport_deltaCoefficient
   (E:Finset (σ →₀ ℕ)) (e:E):
   polynomialOfSupport E (deltaCoefficient E e:E → K)=
     MvPolynomial.monomial e.1 1:=by
 classical
 unfold polynomialOfSupport deltaCoefficient
 rw [Finset.sum_eq_single e]
 · simp
 · intro d _ hd
   simp [hd]
 · simp
theorem exists_exact_support_evaluation_of_downwardClosed
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   ∃ c:E → K,
     v (coefficientEvaluation x E c)=
       WithZero.exp (exponentSetPoleWeight v x E):=by
 obtain ⟨d,hd,hmax⟩:=exists_mem_exponentPoleWeight_eq v x E hzero
 let e:σ →₀ ℕ:=livePoleTruncation v x d
 have he:e∈E:=hdown d hd e (livePoleTruncation_le v x d)
 let esub:E:=⟨e,he⟩
 refine ⟨deltaCoefficient E esub,?_⟩
 rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
   polynomialOfSupport_deltaCoefficient]
 rw [valuation_eval_monomial_one_eq_exp v x e
   (livePoleTruncation_coordinate_ne_zero v x d)]
 rw [exponentValuationWeight_livePoleTruncation,hmax]
theorem poleOrder_eq_of_valuation_eq_exp
   (v:Valuation L (WithZero (Multiplicative ℤ))) (b:L) (q:ℤ)
   (hq:0 ≤ q) (hexact:v b=WithZero.exp q):
   poleOrder v b=q:=by
 unfold poleOrder
 rw [hexact,WithZero.log_exp,max_eq_right hq]
def cancellationSubmodule
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   Submodule K (E → K) where
 carrier:={c | v (coefficientEvaluation x E c) <
   WithZero.exp (exponentSetPoleWeight v x E)}
 zero_mem':=by
   change v (coefficientEvaluation x E 0) <
     WithZero.exp (exponentSetPoleWeight v x E)
   rw [map_zero,map_zero]
   exact WithZero.exp_pos
 add_mem':=by
   intro c d hc hd
   change v (coefficientEvaluation x E (c+d)) <
     WithZero.exp (exponentSetPoleWeight v x E)
   change v (coefficientEvaluation x E c) <
     WithZero.exp (exponentSetPoleWeight v x E) at hc
   change v (coefficientEvaluation x E d) <
     WithZero.exp (exponentSetPoleWeight v x E) at hd
   rw [map_add]
   exact (v.map_add _ _).trans_lt (max_lt hc hd)
 smul_mem':=by
   intro a c hc
   change v (coefficientEvaluation x E (a • c)) <
     WithZero.exp (exponentSetPoleWeight v x E)
   change v (coefficientEvaluation x E c) <
     WithZero.exp (exponentSetPoleWeight v x E) at hc
   rw [map_smul,Algebra.smul_def,map_mul]
   calc
     v (algebraMap K L a)*v (coefficientEvaluation x E c) ≤
         1*v (coefficientEvaluation x E c):=
       mul_le_mul' (hcoeff a) le_rfl
     _ < WithZero.exp (exponentSetPoleWeight v x E):=by
       simpa using hc
theorem cancellationSubmodule_ne_top_of_exact
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (c:E → K)
   (hc:v (coefficientEvaluation x E c)=
     WithZero.exp (exponentSetPoleWeight v x E)):
   cancellationSubmodule v hcoeff x E≠⊤:=by
 intro htop
 have hmem:c∈cancellationSubmodule v hcoeff x E:=by
   rw [htop]
   trivial
 change v (coefficientEvaluation x E c) <
   WithZero.exp (exponentSetPoleWeight v x E) at hmem
 rw [hc] at hmem
 exact (lt_irrefl _ hmem)
end
end ProximityPrize.SubmissionLower.RCN184
end PackedLegacy_BZ

/-! Packed from ProximityPrize.SubmissionLower.GA. -/
section PackedLegacy_GA
namespace ProximityPrize.SubmissionLower.RCN296
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN344 RCN002 RCN005 RCN006 RCN007
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance _root_.ProximityPrize.SubmissionLower.RCN296.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN296.instDecidableEqPlace :DecidableEq (Place K L):=Classical.decEq _
variable (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
theorem finite_model_zero_points_le_exponentSet
   (x:σ → A) (E:Finset (σ →₀ ℕ))
   (F:MvPolynomial σ K) (hFE:F.support ⊆ E)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (q:ℕ)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap A L (x i)) E) ≤ (q:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hS:∀ ψ∈S,ψ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   S.card ≤ q:=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=
   (map_model_eval K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L)
       (fun i↦algebraMap A L (x i)) F):=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one
     K A L ψ _ hF (hS ψ hψ)
 let W:=RCN026.placesFor K L _ hnonzero
 have hcount:=RCN026.finite_zero_places_le_poleMass
   K L _ hnonzero U hU
 have hsupport:=weighted_poleOrder_eval_le_exponentSet W
   (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ c↦constant_value_le_one K L v c)
   (fun i↦algebraMap A L (x i)) E F hFE
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hq:(S.card:ℤ) ≤ q:=by
   calc
     (S.card:ℤ)=(U.card:ℤ):=by rw [hcard]
     _ ≤ ∑ v∈W,RCN346.poleOrder K L v
         (MvPolynomial.eval₂Hom (algebraMap K L)
           (fun i↦algebraMap A L (x i)) F):=hcount
     _ ≤ ∑ v∈W,exponentSetPoleWeight v.val
         (fun i↦algebraMap A L (x i)) E:=by
       simpa only [RCN346.poleOrder,Nat.cast_one,one_mul] using hsupport
     _ ≤ (q:ℤ):=hpole W
 exact_mod_cast hq
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
end ActualCurve
end
end ProximityPrize.SubmissionLower.RCN296
end PackedLegacy_GA

/-! Packed from ProximityPrize.SubmissionLower.O4. -/
section PackedLegacy_O4
namespace ProximityPrize.SubmissionLower.RCN273
open scoped Classical BigOperators WithZero
open RCN002 RCN007 RCN264 RCN243 RCN295 RCN296 RCN272 RCN344
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
structure ResidualPoleComponentBudget
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 separator_transcendental:∀ C:RegularComponent Ω G T H,
   Transcendental Ω (coordinate Ω C.1 separator)
 pole_le:∀ C:RegularComponent Ω G T H,
   let htr:=separator_transcendental C
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   ∀ W:Finset (Place Ω (CoordinateField Ω C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1) E) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
end
end ProximityPrize.SubmissionLower.RCN273
end PackedLegacy_O4

/-! Packed from ProximityPrize.SubmissionLower.GU. -/
section PackedLegacy_GU
namespace ProximityPrize.SubmissionLower.RCN323
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN273
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance _root_.ProximityPrize.SubmissionLower.RCN323.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN323.instDecidableEqPlace :DecidableEq (Place K L):=Classical.decEq _
theorem exponentSetPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   0 ≤ exponentSetPoleWeight v x E:=by
 unfold exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem support_sum_le_principal_poleMass_of_exact
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (b:L) (hb:b≠0)
   (hexact:∀ v:Place K L,
     RCN187.poleOrder v.val b=
       exponentSetPoleWeight v.val x E)
   (W:Finset (Place K L)):
   (∑ v∈W,exponentSetPoleWeight v.val x E) ≤
     ∑ v∈RCN026.placesFor K L b hb,
       RCN346.poleOrder K L v b:=by
 classical
 let P:=RCN026.placesFor K L b hb
 have hout:∀ v∈W,v∉P →
     exponentSetPoleWeight v.val x E=0:=by
   intro v hvW hvP
   have hpole:RCN187.poleOrder v.val b=0:=by
     by_contra hpole
     apply hvP
     apply RCN026.placesFor_covers K L b hb v
     unfold RCN026.order RCN187.poleOrder at*
     omega
   rw [←hexact v,hpole]
 calc
   (∑ v∈W,exponentSetPoleWeight v.val x E)=
       ∑ v∈W ∩ P,exponentSetPoleWeight v.val x E:=by
     symm
     apply Finset.sum_subset Finset.inter_subset_left
     intro v hvW hvnot
     apply hout v hvW
     intro hvP
     exact hvnot (Finset.mem_inter.mpr ⟨hvW,hvP⟩)
   _ ≤ ∑ v∈P,exponentSetPoleWeight v.val x E:=by
     apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
     intro v _ _
     exact exponentSetPoleWeight_nonneg v.val x E
   _=∑ v∈P,RCN346.poleOrder K L v b:=by
     apply Finset.sum_congr rfl
     intro v _
     exact (hexact v).symm
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
theorem coordinate_eval_ne_zero_of_not_mem
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Ω) (hF:F∉P):
   MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω P))
     (coordinate Ω P) F≠0:=by
 intro hz
 apply hF
 rw [←aeval_coordinate_ker Ω P]
 exact hz
structure GenericSparseBKKWitness
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀ C:RegularComponent Ω G T H,polynomial∉C.1
 cost:RegularComponent Ω G T H → ℕ
 exact_pole:∀ C:RegularComponent Ω G T H,
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
   ∀ v:Place Ω (CoordinateField Ω C.1),
     RCN187.poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Ω C.1) E
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
     (coordinate Ω C.1) polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem C.1 polynomial (proper C)
   (∑ v∈RCN026.placesFor Ω (CoordinateField Ω C.1) b hb,
     RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
def GenericSparseBKKWitness.toResidualPoleComponentBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericSparseBKKWitness G T H E separator wholeCost
     hseparator hproj):
   ResidualPoleComponentBudget G T H E separator wholeCost where
 cost:=B.cost
 separator_transcendental:=hseparator
 pole_le:=by
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
   intro W
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   have hb:b≠0:=
     coordinate_eval_ne_zero_of_not_mem C.1 B.polynomial (B.proper C)
   exact (support_sum_le_principal_poleMass_of_exact
     (K:=Ω) (L:=CoordinateField Ω C.1)
     (coordinate Ω C.1) E b hb (B.exact_pole C) W).trans
       (B.cycle_le C)
 sum_cost_le:=B.sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN323
end PackedLegacy_GU

/-! Packed from ProximityPrize.SubmissionLower.B4. -/
section PackedLegacy_B4
namespace ProximityPrize.SubmissionLower.RCN075
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN187 RCN133 RCN184 RCN295 RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN273 RCN323
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
def componentRelevantPlaces
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (C:RegularComponent Ω G T H):
   Finset (Place Ω (CoordinateField Ω C.1)):=by
 classical
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
 exact Finset.univ.biUnion (fun i:Fin 3↦
   if hi:coordinate Ω C.1 i≠0 then
     RCN026.placesFor Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 i) hi
   else ∅)
theorem coordinate_poleOrder_eq_zero_of_not_mem_relevant
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (C:RegularComponent Ω G T H)
   (v:Place Ω (CoordinateField Ω C.1))
   (hv:v∉componentRelevantPlaces hseparator hproj C) (i:Fin 3):
   poleOrder v.val (coordinate Ω C.1 i)=0:=by
 classical
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
 by_cases hi:coordinate Ω C.1 i=0
 · simp [hi,poleOrder]
 · have hnot:v∉RCN026.placesFor Ω
       (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi:=by
     intro hmem
     apply hv
     unfold componentRelevantPlaces
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:RCN026.order Ω (CoordinateField Ω C.1) v
       (coordinate Ω C.1 i)=0:=by
     by_contra hne
     exact hnot (RCN026.placesFor_covers Ω
       (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi v hne)
   unfold RCN026.order at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Ω C.1 i)).log=0:=by omega
   rw [hlog]
   simp
structure GenericExactPolePolynomial
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀ C:RegularComponent Ω G T H,polynomial∉C.1
 exact_pole:∀ C:RegularComponent Ω G T H,
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
   ∀ v:Place Ω (CoordinateField Ω C.1),
     poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Ω C.1) E
def GenericExactPolePolynomial.toGenericSparseBKKWitness
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj)
   (cost:RegularComponent Ω G T H → ℕ)
   (cycle_le:∀ C:RegularComponent Ω G T H,
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
         (cost C:ℤ))
   (sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost):
   GenericSparseBKKWitness G T H E separator wholeCost hseparator hproj where
 polynomial:=B.polynomial
 support_subset:=B.support_subset
 proper:=B.proper
 cost:=cost
 exact_pole:=B.exact_pole
 cycle_le:=cycle_le
 sum_cost_le:=sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN075
end PackedLegacy_B4

/-! Packed from ProximityPrize.SubmissionLower.DO. -/

/-! Packed from ProximityPrize.SubmissionLower.X. -/
section PackedLegacy_X
namespace ProximityPrize.SubmissionLower.RCN341
open scoped Classical
open RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN295 RCN296
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
structure SeparableLiteralCoordinate
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] where
 index:Fin 3
 transcendental:Transcendental Omega (coordinate Omega P index)
 finite:
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P index transcendental
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)
 separable:
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P index transcendental
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)
theorem rationalBaseEmbedding_surjective_of_other_coordinates_algebraic
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hS:Transcendental Omega (coordinate Omega P 1))
   (hY:IsAlgebraic Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   Function.Surjective (rationalBaseEmbedding Omega P 1 hS):=by
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P 1 hS
 letI:IsScalarTower Omega (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseScalarTower Omega P 1 hS
 obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hY
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZ
 have hYbot:coordinate Omega P 0∈
     (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
   rw [IntermediateField.mem_bot]
   refine ⟨algebraMap Omega (RatFunc Omega) y,?_⟩
   rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
     (CoordinateField Omega P)]
   exact hy
 have hZbot:coordinate Omega P 2∈
     (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
   rw [IntermediateField.mem_bot]
   refine ⟨algebraMap Omega (RatFunc Omega) z,?_⟩
   rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
     (CoordinateField Omega P)]
   exact hz
 have hadjoinBot:IntermediateField.adjoin (RatFunc Omega)
     ({coordinate Omega P 2,coordinate Omega P 0}:
       Set (CoordinateField Omega P))=⊥:=by
   rw [IntermediateField.adjoin_eq_bot_iff]
   intro x hx
   rcases hx with (rfl | hx)
   · exact hZbot
   · simpa using hx ▸ hYbot
 have hadjoinTop:IntermediateField.adjoin (RatFunc Omega)
     ({coordinate Omega P 2,coordinate Omega P 0}:
       Set (CoordinateField Omega P))=⊤:=
   adjoin_two_coordinates_over_ratFunc_eq_top Omega P 1 2 0 hS
     (by intro i;fin_cases i <;> simp)
 have htopbot:
     (⊤:IntermediateField (RatFunc Omega) (CoordinateField Omega P))=⊥:=
   hadjoinTop.symm.trans hadjoinBot
 intro x
 obtain ⟨a,ha⟩:=
   IntermediateField.mem_bot.mp (by rw [←htopbot];trivial:
     x∈(⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)))
 refine ⟨a,?_⟩
 exact ha
theorem finite_separable_at_S_of_other_coordinates_algebraic
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hS:Transcendental Omega (coordinate Omega P 1))
   (hY:IsAlgebraic Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P 1 hS
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=by
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P 1 hS
 have hsurj:Function.Surjective
     (algebraMap (RatFunc Omega) (CoordinateField Omega P)):=by
   have hs:=
     rationalBaseEmbedding_surjective_of_other_coordinates_algebraic P hS hY hZ
   exact hs
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   FiniteDimensional.of_surjective
     (Algebra.linearMap (RatFunc Omega) (CoordinateField Omega P)) hsurj
 have hsep:Algebra.IsSeparable
     (RatFunc Omega) (CoordinateField Omega P):=by
   constructor
   intro x
   obtain ⟨a,rfl⟩:=hsurj x
   exact isSeparable_algebraMap a
 exact ⟨inferInstance,hsep⟩
theorem finite_zero_points_le_exponentSet_of_literalCoordinate
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (E:Finset (Fin 3 →₀ ℕ)) (q:ℕ)
   (hpole:
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P D.index D.transcendental
     ∀ W:Finset (Place Omega (CoordinateField Omega P)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
         (q:ℤ))
   (F:MvPolynomial (Fin 3) Omega) (hFE:F.support ⊆ E) (hF:F∉P)
   (S:Finset (Fin 3 → Omega))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   S.card ≤ q:=by
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
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=
   D.separable
 let liftPoint:{v:Fin 3 → Omega//v∈S} →
     (CoordinateRing Omega P →ₐ[Omega] Omega):=
   fun v↦pointHom Omega P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   have h:=pointHom_injective Omega P hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn Omega P↦z.val) h
 let points:=S.attach.image liftPoint
 have hpoints:∀ psi∈points,psi (MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateRing Omega P))
     (quotientCoordinate Omega P) F)=0:=by
   intro psi hpsi
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hpsi
   rw [quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hpole':∀ W:Finset (Place Omega (CoordinateField Omega P)),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap (CoordinateRing Omega P) (CoordinateField Omega P)
         (quotientCoordinate Omega P i)) E) ≤ (q:ℤ):=by
   intro W
   simpa only [quotientCoordinate_fraction] using hpole W
 have hcount:=finite_model_zero_points_le_exponentSet
   (K:=Omega) (L:=CoordinateField Omega P) (σ:=Fin 3)
   (CoordinateRing Omega P) (quotientCoordinate Omega P) E F hFE
   (quotient_eval_ne_zero_of_not_mem Omega P F hF) q hpole' points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
theorem exists_separableLiteralCoordinate_of_YZ_gates
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hY:∀ h:Transcendental Omega (coordinate Omega P 0),
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P 0 h
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P))
   (hZ:∀ h:Transcendental Omega (coordinate Omega P 2),
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P 2 h
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)):
   Nonempty (SeparableLiteralCoordinate P):=by
 by_cases hy:Transcendental Omega (coordinate Omega P 0)
 · exact ⟨⟨0,hy,(hY hy).1,(hY hy).2⟩⟩
 by_cases hz:Transcendental Omega (coordinate Omega P 2)
 · exact ⟨⟨2,hz,(hZ hz).1,(hZ hz).2⟩⟩
 have hyalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hy
 have hzalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hz
 obtain ⟨i,hi⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
 have hi1:i=(1:Fin 3):=by
   fin_cases i <;> simp_all
 subst i
 have hs:=finite_separable_at_S_of_other_coordinates_algebraic
   P hi hyalg hzalg
 exact ⟨⟨1,hi,hs.1,hs.2⟩⟩
end
end ProximityPrize.SubmissionLower.RCN341
end PackedLegacy_X

/-! Packed from ProximityPrize.SubmissionLower.P. -/
section PackedLegacy_P
namespace ProximityPrize.SubmissionLower.RCN114
open scoped Classical BigOperators WithZero
open RCN187 RCN295 RCN095
noncomputable section
theorem exponent_weight_le_flag_bound
   (p:FlagDegree) (d:Fin 3 →₀ ℕ) (q:Fin 3 → ℤ)
   (hd:InFlag p d) (hq:∀ i,0 ≤ q i):
   (∑ i,(d i:ℤ)*q i) ≤
     (p.zOnly:ℤ)*q 2+
       (p.yz:ℤ)*max (q 0) (q 2)+
       (p.all:ℤ)*max (q 1) (max (q 0) (q 2)):=by
 let m₁:ℤ:=max (q 0) (q 2)
 let m₂:ℤ:=max (q 1) m₁
 have hq0m₁:q 0 ≤ m₁:=le_max_left _ _
 have hq2m₁:q 2 ≤ m₁:=le_max_right _ _
 have hq1m₂:q 1 ≤ m₂:=le_max_left _ _
 have hm₁m₂:m₁ ≤ m₂:=le_max_right _ _
 have hreplace0:(d 0:ℤ)*q 0 ≤ (d 0:ℤ)*m₁:=
   mul_le_mul_of_nonneg_left hq0m₁ (by positivity)
 have hreplace1:(d 1:ℤ)*q 1 ≤ (d 1:ℤ)*m₂:=
   mul_le_mul_of_nonneg_left hq1m₂ (by positivity)
 have htotal:((d 0+d 1+d 2:ℕ):ℤ) ≤
     ((p.zOnly+p.yz+p.all:ℕ):ℤ):=by
   exact_mod_cast hd.2.2
 have hys:((d 0+d 1:ℕ):ℤ) ≤
     ((p.yz+p.all:ℕ):ℤ):=by
   exact_mod_cast hd.2.1
 have hs:(d 1:ℤ) ≤ (p.all:ℤ):=by
   exact_mod_cast hd.1
 have hdiff₁:0 ≤ m₁-q 2:=sub_nonneg.mpr hq2m₁
 have hdiff₂:0 ≤ m₂-m₁:=sub_nonneg.mpr hm₁m₂
 have hcap:
     ((d 0+d 1+d 2:ℕ):ℤ)*q 2+
         ((d 0+d 1:ℕ):ℤ)*(m₁-q 2)+
         (d 1:ℤ)*(m₂-m₁) ≤
       ((p.zOnly+p.yz+p.all:ℕ):ℤ)*q 2+
         ((p.yz+p.all:ℕ):ℤ)*(m₁-q 2)+
         (p.all:ℤ)*(m₂-m₁):=by
   exact add_le_add
     (add_le_add (mul_le_mul_of_nonneg_right htotal (hq 2))
       (mul_le_mul_of_nonneg_right hys hdiff₁))
     (mul_le_mul_of_nonneg_right hs hdiff₂)
 calc
   (∑ i,(d i:ℤ)*q i)=
       (d 0:ℤ)*q 0+(d 1:ℤ)*q 1+(d 2:ℤ)*q 2:=by
     simp [Fin.sum_univ_three]
   _ ≤ (d 0:ℤ)*m₁+(d 1:ℤ)*m₂+(d 2:ℤ)*q 2:=
     add_le_add (add_le_add hreplace0 hreplace1) le_rfl
   _=((d 0+d 1+d 2:ℕ):ℤ)*q 2+
         ((d 0+d 1:ℕ):ℤ)*(m₁-q 2)+
         (d 1:ℤ)*(m₂-m₁):=by
     push_cast
     ring
   _ ≤ ((p.zOnly+p.yz+p.all:ℕ):ℤ)*q 2+
         ((p.yz+p.all:ℕ):ℤ)*(m₁-q 2)+
         (p.all:ℤ)*(m₂-m₁):=hcap
   _=(p.zOnly:ℤ)*q 2+(p.yz:ℤ)*m₁+
         (p.all:ℤ)*m₂:=by
     push_cast
     ring
   _=_:=rfl
variable {L:Type*} [Field L]
theorem exponentSetPoleWeight_flagSupport_le
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree):
   exponentSetPoleWeight v x (flagSupport p) ≤
     (p.zOnly:ℤ)*poleOrder v (x 2)+
       (p.yz:ℤ)*max (poleOrder v (x 0)) (poleOrder v (x 2))+
       (p.all:ℤ)*max (poleOrder v (x 1))
         (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 classical
 unfold exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · have h0:∀ i:Fin 3,0 ≤ poleOrder v (x i):=fun i↦by
     unfold poleOrder
     exact le_max_left _ _
   exact add_nonneg
     (add_nonneg (mul_nonneg (by positivity) (h0 2))
       (mul_nonneg (by positivity)
         ((h0 0).trans (le_max_left _ _))))
     (mul_nonneg (by positivity)
       ((h0 1).trans (le_max_left _ _)))
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   exact exponent_weight_le_flag_bound p d (fun i↦poleOrder v (x i))
     ((mem_flagSupport_iff p d).mp hd)
     (fun i↦by unfold poleOrder;exact le_max_left _ _)
theorem exponentPoleWeight_single
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (i:Fin 3):
   exponentPoleWeight v x (Finsupp.single i 1)=poleOrder v (x i):=by
 classical
 fin_cases i <;> simp [exponentPoleWeight,Fin.sum_univ_three]
public theorem poleOrder_le_support_of_mem
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree) (i:Fin 3)
   (hi:Finsupp.single i 1∈flagSupport p):
   poleOrder v (x i) ≤ exponentSetPoleWeight v x (flagSupport p):=by
 rw [←exponentPoleWeight_single v x i]
 unfold exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
   ⟨Finsupp.single i 1,hi,rfl⟩)
theorem exponentSetPoleWeight_unitZ
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitZFlag)=poleOrder v (x 2):=by
 apply le_antisymm
 · simpa [unitZFlag] using exponentSetPoleWeight_flagSupport_le v x unitZFlag
 · apply poleOrder_le_support_of_mem v x unitZFlag 2
   rw [mem_flagSupport_iff]
   simp [InFlag,unitZFlag]
theorem exponentSetPoleWeight_unitYZ
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitYZFlag)=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 apply le_antisymm
 · simpa [unitYZFlag] using exponentSetPoleWeight_flagSupport_le v x unitYZFlag
 · apply max_le
   · apply poleOrder_le_support_of_mem v x unitYZFlag 0
     rw [mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
   · apply poleOrder_le_support_of_mem v x unitYZFlag 2
     rw [mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
theorem exponentSetPoleWeight_unitAll
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitAllFlag)=
     max (poleOrder v (x 1))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 apply le_antisymm
 · simpa [unitAllFlag] using exponentSetPoleWeight_flagSupport_le v x unitAllFlag
 · apply max_le
   · apply poleOrder_le_support_of_mem v x unitAllFlag 1
     rw [mem_flagSupport_iff]
     simp [InFlag,unitAllFlag]
   · apply max_le
     · apply poleOrder_le_support_of_mem v x unitAllFlag 0
       rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
     · apply poleOrder_le_support_of_mem v x unitAllFlag 2
       rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
theorem exponentSetPoleWeight_flagSupport_le_three
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree):
   exponentSetPoleWeight v x (flagSupport p) ≤
     (p.zOnly:ℤ)*exponentSetPoleWeight v x (flagSupport unitZFlag)+
     (p.yz:ℤ)*exponentSetPoleWeight v x (flagSupport unitYZFlag)+
     (p.all:ℤ)*exponentSetPoleWeight v x (flagSupport unitAllFlag):=by
 rw [exponentSetPoleWeight_unitZ,exponentSetPoleWeight_unitYZ,
   exponentSetPoleWeight_unitAll]
 exact exponentSetPoleWeight_flagSupport_le v x p
end
end ProximityPrize.SubmissionLower.RCN114
end PackedLegacy_P

/-! Packed from ProximityPrize.SubmissionLower.Q8. -/
section PackedLegacy_Q8
namespace ProximityPrize.SubmissionLower.RCN340
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006
open RCN344 RCN264 RCN095 RCN114 RCN295 RCN341 RCN237 RCN165
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def LiteralSupportPoleBound
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (E:Finset (Fin 3 →₀ ℕ)) (cost:ℕ):Prop:=
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
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=
   D.separable
 ∀ W:Finset (Place Omega (CoordinateField Omega P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
     (cost:ℤ)
structure AdaptiveUnitPoleBudget
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 zCost:RegularComponent Omega G T H → ℕ
 yzCost:RegularComponent Omega G T H → ℕ
 allCost:RegularComponent Omega G T H → ℕ
 zPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitZFlag) (zCost C)
 yzPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitYZFlag) (yzCost C)
 allPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitAllFlag) (allCost C)
 sum_zCost_le:(∑ C:RegularComponent Omega G T H,zCost C) ≤
   flagMixed p q unitZFlag
 sum_yzCost_le:(∑ C:RegularComponent Omega G T H,yzCost C) ≤
   flagMixed p q unitYZFlag
 sum_allCost_le:(∑ C:RegularComponent Omega G T H,allCost C) ≤
   flagMixed p q unitAllFlag
def AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (U:AdaptiveUnitPoleBudget base p q):
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q where
 zCost:=U.zCost
 yzCost:=U.yzCost
 allCost:=U.allCost
 sum_zCost_le:=U.sum_zCost_le
 sum_yzCost_le:=U.sum_yzCost_le
 sum_allCost_le:=U.sum_allCost_le
 primeBudget:=by
   intro C
   refine ⟨?_⟩
   intro r A hA hproper points hpointsP hpointsA
   let D:=base C
   let i0:=D.index
   let htr:=D.transcendental
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 i0 htr
   letI:=quotientBaseScalarTower Omega C.1 i0
   letI:=polynomialBaseScalarTower Omega C.1 i0
   letI:=quotientFractionScalarTower Omega C.1 i0
   letI:=polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     D.finite
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     D.separable
   have hz:=U.zPole C
   have hyz:=U.yzPole C
   have hall:=U.allPole C
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitZFlag)) ≤ (U.zCost C:ℤ) at hz
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitYZFlag)) ≤ (U.yzCost C:ℤ) at hyz
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitAllFlag)) ≤ (U.allCost C:ℤ) at hall
   have hpole:∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport r)) ≤
       ((r.zOnly*U.zCost C+r.yz*U.yzCost C+
         r.all*U.allCost C:ℕ):ℤ):=by
     intro W
     calc
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
           (flagSupport r)) ≤
           ∑ v∈W,
             ((r.zOnly:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitZFlag)+
              (r.yz:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitYZFlag)+
              (r.all:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitAllFlag)):=by
         apply Finset.sum_le_sum
         intro v _
         exact exponentSetPoleWeight_flagSupport_le_three v.val
           (coordinate Omega C.1) r
       _=(r.zOnly:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitZFlag))+
           (r.yz:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitYZFlag))+
           (r.all:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitAllFlag)):=by
         simp only [Finset.sum_add_distrib,Finset.mul_sum]
       _ ≤ (r.zOnly:ℤ)*(U.zCost C:ℤ)+
           (r.yz:ℤ)*(U.yzCost C:ℤ)+
           (r.all:ℤ)*(U.allCost C:ℤ):=by
         exact add_le_add
           (add_le_add
             (mul_le_mul_of_nonneg_left (hz W) (by positivity))
             (mul_le_mul_of_nonneg_left (hyz W) (by positivity)))
           (mul_le_mul_of_nonneg_left (hall W) (by positivity))
       _=((r.zOnly*U.zCost C+r.yz*U.yzCost C+
           r.all*U.allCost C:ℕ):ℤ):=by
         push_cast
         ring
   exact finite_zero_points_le_exponentSet_of_literalCoordinate C.1 D
     (flagSupport r)
     (r.zOnly*U.zCost C+r.yz*U.yzCost C+r.all*U.allCost C)
     hpole A ((support_subset_flagSupport_iff r A).2 hA) hproper
     points hpointsP hpointsA
end
end ProximityPrize.SubmissionLower.RCN340
end PackedLegacy_Q8

/-! Packed from ProximityPrize.SubmissionLower.G. -/
section PackedLegacy_G
namespace ProximityPrize.SubmissionLower.RCN022
open scoped Classical
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
def elementEmbedding (s:L) (hs:Transcendental K s):RatFunc K →ₐ[K] L:=
 RatFunc.liftAlgHom (Polynomial.aeval s)
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
     (Polynomial.aeval s).toRingHom (transcendental_iff_injective.mp hs))
theorem elementEmbedding_variable (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s:=by
 change RatFunc.liftAlgHom (Polynomial.aeval s) _
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s
 calc
   _=Polynomial.aeval s Polynomial.X:=
     RatFunc.liftRingHom_algebraMap _ _ Polynomial.X
   _=s:=Polynomial.aeval_X s
theorem elementEmbedding_eq_adjoin_comp (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs=
     (IntermediateField.adjoin K ({s}:Set L)).val.comp
       (RatFunc.algEquivOfTranscendental s hs).toAlgHom:=by
 apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
 ext
 change elementEmbedding K L s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=
   ((RatFunc.algEquivOfTranscendental s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X):
       IntermediateField.adjoin K ({s}:Set L)):L)
 rw [elementEmbedding_variable]
 simp
theorem finiteDimensional_elementEmbedding
   (base:RatFunc K →ₐ[K] L)
   (hfinite:
     letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (s:L) (hs:Transcendental K s):
   letI:Algebra (RatFunc K) L:=
     (elementEmbedding K L s hs).toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L:=by
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 have hadjoin:FiniteDimensional (IntermediateField.adjoin K ({s}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental hs
 let e:RatFunc K ≃ₐ[K] (IntermediateField.adjoin K ({s}:Set L)):=
   RatFunc.algEquivOfTranscendental s hs
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L s hs).toRingHom.toAlgebra
 have hsmul:∀ (c:IntermediateField.adjoin K ({s}:Set L)) (x:L),
     e.symm c • x=c • x:=by
   intro c x
   rw [Algebra.smul_def,Algebra.smul_def]
   change elementEmbedding K L s hs (e.symm c)*x=(c:L)*x
   rw [elementEmbedding_eq_adjoin_comp]
   simp [e]
 let b:=Module.finBasis (IntermediateField.adjoin K ({s}:Set L)) L
 exact (b.mapCoeffs e.symm hsmul).finiteDimensional_of_finite
end
end ProximityPrize.SubmissionLower.RCN022
end PackedLegacy_G

/-! Packed from ProximityPrize.SubmissionLower.G7. -/
section PackedLegacy_G7
namespace ProximityPrize.SubmissionLower.RCN369
open scoped Classical
open KaehlerDifferential
noncomputable section
set_option maxHeartbeats 2000000
section RatFuncDifferential
variable (K:Type*) [Field K]
theorem span_singleton_D_ratFunc_X:
   Submodule.span (RatFunc K)
       ({D K (RatFunc K)
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)}:
         Set Ω[RatFunc K⁄K])=⊤:=by
 have hall:=span_range_map_derivation_of_isLocalization
   K (Polynomial K) (RatFunc K) (nonZeroDivisors (Polynomial K))
 apply top_unique
 rw [←hall]
 apply Submodule.span_le.mpr
 rintro x ⟨P,rfl⟩
 change map K K (Polynomial K) (RatFunc K) (D K (Polynomial K) P)∈_
 rw [polynomial_D_apply,LinearMap.map_smul_of_tower,map_D]
 exact Submodule.smul_of_tower_mem _ _
   (Submodule.subset_span (Set.mem_singleton _))
end RatFuncDifferential
section ProjectionCriterion
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
def parameterDifferential (embedding:RatFunc K →ₐ[K] L):Ω[L⁄K]:=
 D K L (embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
theorem isSeparable_iff_span_parameterDifferential
   (embedding:RatFunc K →ₐ[K] L):
   letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L →
     (Algebra.IsSeparable (RatFunc K) L ↔
       Submodule.span L ({parameterDifferential K L embedding}:Set Ω[L⁄K])=⊤):=by
 letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(embedding.commutes c).symm
 intro hfinite
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 constructor
 · intro hsep
   letI:Algebra.IsSeparable (RatFunc K) L:=hsep
   letI:Algebra.FormallyUnramified (RatFunc K) L:=
     Algebra.FormallyUnramified.of_isSeparable (RatFunc K) L
   have htarget:Subsingleton Ω[L⁄RatFunc K]:=inferInstance
   have hsurj:Function.Surjective (mapBaseChange K (RatFunc K) L):=by
     rw [←LinearMap.range_eq_top,range_mapBaseChange]
     apply top_unique
     intro x _
     change map K (RatFunc K) L L x=0
     exact Subsingleton.elim _ _
   have hsource:=span_singleton_D_ratFunc_X K
   rw [←LinearMap.range_eq_top] at hsurj
   apply top_unique
   rw [←hsurj]
   rintro x ⟨x,rfl⟩
   induction x with
   | zero => simp
   | add x y hx hy =>
       rw [map_add]
       exact Submodule.add_mem _ hx hy
   | tmul l ω =>
       have hω:ω∈Submodule.span (RatFunc K)
           ({D K (RatFunc K)
             (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)}:
             Set Ω[RatFunc K⁄K]):=by
         rw [hsource]
         trivial
       obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hω
       rw [TensorProduct.tmul_smul]
       change mapBaseChange K (RatFunc K) L
         ((algebraMap (RatFunc K) L a*l) ⊗ₜ
           D K (RatFunc K)
             (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))∈_
       rw [mapBaseChange_tmul,map_D]
       change (algebraMap (RatFunc K) L a*l) •
         parameterDifferential K L embedding∈
           Submodule.span L
             ({parameterDifferential K L embedding}:Set Ω[L⁄K])
       exact Submodule.smul_mem _ _
         (Submodule.subset_span (Set.mem_singleton _))
 · intro hspan
   have hrange:LinearMap.range (mapBaseChange K (RatFunc K) L)=⊤:=by
     apply top_unique
     rw [←hspan]
     apply Submodule.span_le.mpr
     intro η hη
     rw [Set.mem_singleton_iff.mp hη]
     refine ⟨1 ⊗ₜ D K (RatFunc K)
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X),?_⟩
     rw [mapBaseChange_tmul,one_smul,map_D]
     rfl
   have hker:LinearMap.ker (map K (RatFunc K) L L)=⊤:=by
     rw [←range_mapBaseChange]
     exact hrange
   have hzero:map K (RatFunc K) L L=0:=by
     apply LinearMap.ker_eq_top.mp hker
   have hsub:Subsingleton Ω[L⁄RatFunc K]:=by
     constructor
     intro x y
     obtain ⟨x,rfl⟩:=map_surjective K (RatFunc K) L x
     obtain ⟨y,rfl⟩:=map_surjective K (RatFunc K) L y
     rw [hzero,LinearMap.zero_apply,LinearMap.zero_apply]
   letI:Subsingleton Ω[L⁄RatFunc K]:=hsub
   letI:Algebra.FormallyUnramified (RatFunc K) L:=⟨inferInstance⟩
   exact Algebra.FormallyUnramified.isSeparable (RatFunc K) L
end ProjectionCriterion
end
end ProximityPrize.SubmissionLower.RCN369
end PackedLegacy_G7

/-! Packed from ProximityPrize.SubmissionLower.X1. -/
section PackedLegacy_X1
namespace ProximityPrize.SubmissionLower.RCN370
open scoped Classical
open KaehlerDifferential RCN369
noncomputable section
set_option maxHeartbeats 2000000
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
theorem eq_algebraMap_of_isAlgebraic [IsAlgClosed K]
   (s:L) (hs:IsAlgebraic K s):
   ∃ c:K,algebraMap K L c=s:=by
 let S:IntermediateField K L:=IntermediateField.adjoin K {s}
 letI:Algebra.IsAlgebraic K S:=
   IntermediateField.isAlgebraic_adjoin_simple hs.isIntegral
 obtain ⟨c,hc⟩:=
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S)).2
     (⟨s,IntermediateField.mem_adjoin_simple_self K s⟩:S)
 refine ⟨c,?_⟩
 have hcast:=congrArg (algebraMap S L) hc
 simpa only [IntermediateField.algebraMap_apply,
   IntermediateField.coe_algebraMap_apply] using hcast
end
end ProximityPrize.SubmissionLower.RCN370
end PackedLegacy_X1

/-! Packed from ProximityPrize.SubmissionLower.R7. -/
section PackedLegacy_R7
namespace ProximityPrize.SubmissionLower.RCN351
open scoped Classical TensorProduct
open Polynomial KaehlerDifferential RCN369 RCN370 RCN022
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
theorem formallyEtale_of_finite_isSeparable
   (F E:Type*) [Field F] [Field E] [Algebra F E]
   [FiniteDimensional F E] [Algebra.IsSeparable F E]:
   Algebra.FormallyEtale F E:=by
 have:=Algebra.FormallyUnramified.of_isSeparable F E
 have:=Algebra.FormallyUnramified.finite_of_free (R:=F) (S:=E)
 refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h↦?_
 refine ⟨Algebra.FormallyUnramified.iff_comp_injective_of_small.mp
   (Algebra.FormallyUnramified.of_isSeparable F E) I h,?_⟩
 intro f
 let pb:=Field.powerBasisOfFiniteOfSeparable F E
 obtain ⟨x,hx⟩:=Ideal.Quotient.mk_surjective (f pb.gen)
 have helper:∀ x,IsScalarTower.toAlgHom F B
     (HasQuotient.Quotient B I) x=
     Ideal.Quotient.mk I x:=fun _↦rfl
 have hx':Ideal.Quotient.mk I (aeval x (minpoly F pb.gen))=0:=by
   rw [←helper, ←aeval_algHom_apply,helper,hx,aeval_algHom_apply,
     minpoly.aeval,map_zero]
 obtain ⟨u,hu⟩:∃ u,
     (aeval x) (derivative (minpoly F pb.gen))*u+1∈I:=by
   have hunit:=(isUnit_iff_ne_zero.mpr
     ((Algebra.IsSeparable.isSeparable F pb.gen).aeval_derivative_ne_zero
       (minpoly.aeval F _))).map f
   rw [←aeval_algHom_apply, ←hx, ←helper,aeval_algHom_apply,
     helper] at hunit
   obtain ⟨u,hu⟩:=Ideal.Quotient.mk_surjective
     (-hunit.unit⁻¹:HasQuotient.Quotient B I)
   use u
   rw [←Ideal.Quotient.eq_zero_iff_mem,map_add,map_mul,map_one,hu,
     mul_neg,IsUnit.mul_val_inv,neg_add_cancel]
 use pb.liftEquiv.symm ⟨x+u*aeval x (minpoly F pb.gen),?_⟩
 · apply pb.algHom_ext
   simp [hx,hx']
 · rw [←eval_map_algebraMap,Polynomial.eval_add_of_sq_eq_zero,
     derivative_map, ←one_mul (eval x _),eval_map_algebraMap,
     eval_map_algebraMap, ←mul_assoc, ←add_mul, ←Ideal.mem_bot,
     ←h,pow_two,add_comm]
   · exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
   rw [←Ideal.mem_bot, ←h]
   apply Ideal.pow_mem_pow
   rw [←Ideal.Quotient.eq_zero_iff_mem,map_mul,hx',mul_zero]
theorem ratFunc_variableDifferential_ne_zero (K:Type*) [Field K]:
   D K (RatFunc K)
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)≠0:=by
 letI:Algebra.FormallyEtale (Polynomial K) (RatFunc K):=
   Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Polynomial K))
 intro hzero
 have htensor:=congrArg
   (tensorKaehlerEquivOfFormallyEtale
     K (Polynomial K) (RatFunc K)).symm hzero
 have htensor':(1:RatFunc K) ⊗ₜ[Polynomial K]
     D K (Polynomial K) Polynomial.X=0:=by
   simpa only [map_zero,
     tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
 let l:Ω[Polynomial K⁄K] →ₗ[Polynomial K] RatFunc K:=
   (Algebra.linearMap (Polynomial K) (RatFunc K)).comp
     (polynomialEquiv K).toLinearMap
 have himage:=congrArg (l.liftBaseChange (RatFunc K)) htensor'
 have hone:(1:RatFunc K)=0:=by
   rw [LinearMap.liftBaseChange_tmul,one_smul,map_zero] at himage
   change algebraMap (Polynomial K) (RatFunc K)
     (polynomialEquiv K (D K (Polynomial K) Polynomial.X))=0 at himage
   simpa only [polynomialEquiv_D,derivative_X,map_one] using himage
 exact one_ne_zero hone
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
theorem parameterDifferential_ne_zero_of_isSeparable
   (embedding:RatFunc K →ₐ[K] L)
   (hfinite:
     letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hsep:
     letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) L):
   parameterDifferential K L embedding≠0:=by
 letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(embedding.commutes c).symm
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 letI:Algebra.IsSeparable (RatFunc K) L:=hsep
 letI:Algebra.FormallyEtale (RatFunc K) L:=
   formallyEtale_of_finite_isSeparable (RatFunc K) L
 intro hzero
 change D K L
   (algebraMap (RatFunc K) L
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))=0 at hzero
 have htensor:=congrArg
   (tensorKaehlerEquivOfFormallyEtale K (RatFunc K) L).symm hzero
 have htensor':(1:L) ⊗ₜ[RatFunc K]
     D K (RatFunc K)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=0:=by
   simpa only [map_zero,
     tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
 have hsource:D K (RatFunc K)
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=0:=by
   rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at htensor'
   exact htensor'
 exact ratFunc_variableDifferential_ne_zero K hsource
theorem shear_bad_coefficient_subsingleton
   (r z:L) (hdz:D K L z≠0):
   ∀ {a b:K},
     D K L r+a • D K L z=0 →
     D K L r+b • D K L z=0 → a=b:=by
 intro a b ha hb
 apply smul_left_injective K hdz
 exact (eq_neg_of_add_eq_zero_right ha).trans
   (eq_neg_of_add_eq_zero_right hb).symm
section FiniteFamily
variable {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN351
end PackedLegacy_R7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier15 : True := by trivial
end ProximityPrize.SubmissionLower
end Compact_PackedLegacyCore2


