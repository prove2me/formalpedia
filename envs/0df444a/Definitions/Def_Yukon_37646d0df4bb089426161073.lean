-- Prove2me | Definitions.Def_Yukon_37646d0df4bb089426161073
-- name    : Yukon_37646d0df4bb089426161073
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T22:16:48.618393+00:00
-- url     : https://prove2.me/theorems/41f2e0a1-be47-4b13-922d-59ce43fb3978
-- title:
--   LowerFoundation source part 4/5
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-compact-module-Yukon_37646d0df4bb089426161073
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZDMwMTM4NmFlZjhjNDFkMGQ4NWQwMDAyMmFhYjc4OTc5ZDU0YzFhYTg1MWQxYmJiMjdlNzJmOGNjYjVhY2EwOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tY29tcGFjdC1tb2R1bGUtWXVrb25fMzc2NDZkMGRmNGJiMDg5NDI2MTYxMDczIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMzc2NDZkMGRmNGJiMDg5NDI2MTYxMDczIiwidiI6Mn0]

import Definitions.Def_Yukon_baa5877344aa01c8873b10a8
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


/-! Packed from ProximityPrize.SubmissionLower.J3. -/
section PackedLegacy_J3
namespace ProximityPrize.SubmissionLower.RCN085
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
 [IsScalarTower Ω (RatFunc Ω) E]
end
end ProximityPrize.SubmissionLower.RCN085
end PackedLegacy_J3

/-! Packed from ProximityPrize.SubmissionLower.ET. -/
section PackedLegacy_ET
namespace ProximityPrize.SubmissionLower.RCN151
open scoped Classical
open RCN136 RCN231 RCN319 RCN313 RCN065 RCN238 RCN160 RCN157 RCN163 RCN156 RCN275 RCN234 RCN094 RCN095 RCN125 RCN162
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega]
local instance _root_.ProximityPrize.SubmissionLower.RCN151.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN151.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN151.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure CurveResidualStage
   (phi:Polynomial K →+*Omega) (Gamma:Finset K) (x:Iota → K)
   (p e:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree) (d:ℕ)
   (support:ResidualSupportParameters:=
     ResidualSupportParameters.acceptedSupport) where
 nodes:Finset Iota
 u0:Iota → K
 u1:Iota → K
 selected:K → Polynomial K
 F:Poly4 K
 G:Poly3 Omega
 T:Poly3 Omega
 primeData:RegularPrimeData G T
   (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))
 G_dvd_surface:G∣surfaceMap phi F
 G_flag_support:RCN095.PolynomialInFlag surfaceFlag G
 T_flag_support:RCN095.PolynomialInFlag cutFlag T
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
 on_prime:∀ gamma∈Gamma,primeData.ideal ≤ RingHom.ker
   (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom
 no_large_pencil:NoLargeSelectedPencil selected Gamma d e
 characteristic_bound:d < p
namespace CurveResidualStage
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K}
 {x:Iota → K} {p e:ℕ} [CharP Omega p]
 {surfaceFlag cutFlag:FlagDegree} {d:ℕ}
 {support:ResidualSupportParameters}
def Agrees
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (gamma:K) (i:Iota):Prop:=
 (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i
local instance
    _root_.ProximityPrize.SubmissionLower.RCN151.CurveResidualStage.instDecidableAgrees (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   ∀ gamma i,Decidable (S.Agrees gamma i):=
 fun _ _↦Classical.propDecidable _
end CurveResidualStage
end
end ProximityPrize.SubmissionLower.RCN151
end PackedLegacy_ET

/-! Packed from ProximityPrize.SubmissionLower.EY. -/
section PackedLegacy_EY
namespace ProximityPrize.SubmissionLower.RCN158
open RCN213
section FiniteAgreement
variable {Node:Type*} [DecidableEq Node]
end FiniteAgreement
section IteratedSets
variable {Node:Type*} [DecidableEq Node]
end IteratedSets
section Arithmetic
end Arithmetic
section Terminalization
open scoped Classical
open RCN159 RCN157 RCN156 RCN275
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p]
 {flag:RCN095.FlagDegree}
 {support:ResidualSupportParameters}
end
end Terminalization
end ProximityPrize.SubmissionLower.RCN158
end PackedLegacy_EY

/-! Packed from ProximityPrize.SubmissionLower.D6. -/
section PackedLegacy_D6
namespace ProximityPrize.SubmissionLower.RCN216
open RCN173 RCN213
end ProximityPrize.SubmissionLower.RCN216
end PackedLegacy_D6

/-! Packed from ProximityPrize.SubmissionLower.EU. -/
section PackedLegacy_EU
namespace ProximityPrize.SubmissionLower.RCN152
open scoped Classical
open RCN136 RCN231 RCN319 RCN238 RCN173 RCN151 RCN151.CurveResidualStage RCN216 RCN213 RCN272 RCN095 RCN156 RCN158 RCN165 RCN275
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p]
 {surfaceFlag cutFlag:FlagDegree}
 {support:ResidualSupportParameters}
local instance _root_.ProximityPrize.SubmissionLower.RCN152.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN152.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN152.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN152
end PackedLegacy_EU

/-! Packed from ProximityPrize.SubmissionLower.GJ. -/
section PackedLegacy_GJ
namespace ProximityPrize.SubmissionLower.RCN305
open scoped Classical BigOperators
open RCN002 RCN007 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN272 RCN216
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
 {Iota:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN305.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN305.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN305.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN305
end PackedLegacy_GJ

/-! Packed from ProximityPrize.SubmissionLower.ER. -/
section PackedLegacy_ER
namespace ProximityPrize.SubmissionLower.RCN148
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN151 RCN152 RCN156 RCN165 RCN237 RCN305 RCN234 RCN215 RCN275
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega}
local instance _root_.ProximityPrize.SubmissionLower.RCN148.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN148.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN148.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN148
end PackedLegacy_ER

/-! Packed from ProximityPrize.SubmissionLower.BN. -/
section PackedLegacy_BN
namespace ProximityPrize.SubmissionLower.RCN149
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN151 RCN152 RCN156 RCN165 RCN237 RCN305 RCN234 RCN215 RCN148 RCN275
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega}
local instance _root_.ProximityPrize.SubmissionLower.RCN149.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN149.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN149.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN149
end PackedLegacy_BN
end Compact_PackedLegacy


