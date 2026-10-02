-- Prove2me | Definitions.Def_Yukon_cc09659938447005331d9581
-- name    : Yukon_cc09659938447005331d9581
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T19:11:04.878908+00:00
-- url     : https://prove2.me/theorems/9d01bb3a-77bb-4963-a381-c0a22bfbcbb8
-- title:
--   LowerFoundation source part 3/4
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-small-split-Yukon_cc09659938447005331d9581
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTQzZWM5OTdmNTU1YzIyZjgwYzUxNzMzN2ZlMWQ1NTBiMTE2MmVmMzE0ZDMzZDViODU1NjIzYjg3MDcwMzY0ZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tc21hbGwtc3BsaXQtWXVrb25fY2MwOTY1OTkzODQ0NzAwNTMzMWQ5NTgxIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fY2MwOTY1OTkzODQ0NzAwNTMzMWQ5NTgxIiwidiI6Mn0]

import Definitions.Def_Yukon_4328c3a3fc53bf96b4a2a518
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


/-! Packed from ProximityPrize.SubmissionLower.AD. -/
section PackedLegacy_AD
namespace ProximityPrize.SubmissionLower.RCN267
open RCN136 RCN313 RCN138 RCN132 RCN137
noncomputable section
section PartialDerivatives
variable {σ K:Type*} [Field K]
theorem pderiv_zero_of_degree_zero (i:σ) (F:MvPolynomial σ K)
   (hdegree:F.degreeOf i=0):MvPolynomial.pderiv i F=0:=by
 apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
 intro hmem
 exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hmem) hdegree
theorem pderiv_zero_iff_degree_zero_below_char
   (i:σ) (F:MvPolynomial σ K) (p:ℕ) [CharP K p]
   (hdegree:F.degreeOf i < p):
   MvPolynomial.pderiv i F=0 ↔ F.degreeOf i=0:=by
 classical
 constructor
 · intro hzero
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   by_contra hn
   have hpos:0 < d i:=by omega
   have hsmall:d i < p:=(MvPolynomial.monomial_le_degreeOf i hd).trans_lt hdegree
   let e:σ →₀ ℕ:=d-Finsupp.single i 1
   have he:e+Finsupp.single i 1=d:=
     Finsupp.sub_add_single_one_cancel (by omega:d i≠0)
   have hnat:e i+1=d i:=by
     have hh:=congrArg (fun f:σ →₀ ℕ => f i) he
     simpa only [Finsupp.add_apply,Finsupp.single_eq_same] using hh
   have hcast:(d i:K)≠0:=
     (CharP.cast_eq_zero_iff K p (d i)).not.mpr (Nat.not_dvd_of_pos_of_lt hpos hsmall)
   have hcoef:(e i:K)+1≠0:=by
     simpa only [←hnat,Nat.cast_add,Nat.cast_one] using hcast
   have hz:MvPolynomial.coeff e (MvPolynomial.pderiv i F)=0:=by
     rw [hzero,MvPolynomial.coeff_zero]
   rw [MvPolynomial.coeff_pderiv,he] at hz
   exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcoef hz
 · exact pderiv_zero_of_degree_zero i F
end PartialDerivatives
section SurfaceCommutation
variable {K L:Type*} [Field K] [Field L]
theorem surfaceMap_pderiv_X (φ:Polynomial K →+*L) (i:Fin 4) (j:Fin 3):
   MvPolynomial.pderiv j (surfaceMap φ (MvPolynomial.X i))=
     surfaceMap φ (MvPolynomial.pderiv j.succ (MvPolynomial.X i)):=by
 classical
 refine Fin.cases ?_ (fun k => ?_) i
 · simp [MvPolynomial.pderiv_X,Pi.single_apply,Fin.succ_ne_zero]
 · by_cases h:k=j
   · subst k
     simp
   · simp [MvPolynomial.pderiv_X,Pi.single_apply,h,Fin.succ_inj,apply_ite]
theorem surfaceMap_pderiv (φ:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K) (j:Fin 3):
   MvPolynomial.pderiv j (surfaceMap φ F)=
     surfaceMap φ (MvPolynomial.pderiv j.succ F):=by
 classical
 induction F using MvPolynomial.induction_on with
 | C a => simp [MvPolynomial.pderiv_C]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     simp only [map_mul,map_add,MvPolynomial.pderiv_mul,hP,surfaceMap_pderiv_X]
theorem surfaceMap_pderiv_R (φ:Polynomial K →+*L) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 3) (surfaceMap φ F)=
     surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F):=
 surfaceMap_pderiv φ F 1
end SurfaceCommutation
section BaseRegularity
variable {K:Type*} [Field K]
theorem R_derivative_nonzero (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p):
   MvPolynomial.pderiv (2:Fin 4) F≠0:=by
 intro hzero
 have hd:=(pderiv_zero_iff_degree_zero_below_char (2:Fin 4) F p hsmall).mp hzero
 omega
theorem R_derivative_degree_lt (F:MvPolynomial (Fin 4) K) (hpos:0 < F.degreeOf 2):
   (MvPolynomial.pderiv (2:Fin 4) F).degreeOf 2 < F.degreeOf 2:=by
 have hb:=pderiv_same_degree_bound (2:Fin 4) F (F.degreeOf 2) le_rfl
 omega
theorem equation_not_dvd_R_derivative
   (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p):
   ¬ F∣MvPolynomial.pderiv (2:Fin 4) F:=by
 intro hdiv
 have hle:=RCN081.degreeOf_le_of_dvd (2:Fin 4) F _ hdiv
   (R_derivative_nonzero F p hpos hsmall)
 have hlt:=R_derivative_degree_lt F hpos
 omega
end BaseRegularity
section GeometricRegularity
variable (K L:Type*) [Field K] [Field L] [Algebra (RationalCoefficients K) L]
theorem geometricSurfaceMap_pderiv_R (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 3) (geometricSurfaceMap K L F)=
     geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 rw [geometricSurfaceMap_eq_surfaceMap]
 exact surfaceMap_pderiv_R _ F
theorem H_proper_on_every_geometric_factor
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   ¬ g∣geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 intro hdivH
 apply equation_not_dvd_R_derivative F p hpos hsmall
 exact (geometric_factor_dvd_iff K L F (MvPolynomial.pderiv (2:Fin 4) F)
   hF (by omega) g hg hdivF).mp hdivH
theorem geometric_factor_R_derivative_nonzero
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   MvPolynomial.pderiv (1:Fin 3) g≠0:=by
 intro hgzero
 have hdivH:g∣MvPolynomial.pderiv (1:Fin 3) (geometricSurfaceMap K L F):=by
   obtain ⟨G,hG⟩:=hdivF
   refine ⟨MvPolynomial.pderiv (1:Fin 3) G,?_⟩
   rw [hG,MvPolynomial.pderiv_mul,hgzero,zero_mul,zero_add]
 rw [geometricSurfaceMap_pderiv_R] at hdivH
 exact H_proper_on_every_geometric_factor K L F hF p hpos hsmall g hg hdivF hdivH
theorem geometric_factor_R_degree_positive
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   0 < g.degreeOf (1:Fin 3):=by
 apply Nat.pos_of_ne_zero
 intro hzero
 exact geometric_factor_R_derivative_nonzero K L F hF p hpos hsmall g hg hdivF
   (pderiv_zero_of_degree_zero (1:Fin 3) g hzero)
theorem geometric_factor_R_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (g:MvPolynomial (Fin 3) L) (hdivF:g∣geometricSurfaceMap K L F):
   g.degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4):=by
 have hφ:Function.Injective (geometricPolynomialEmbedding K L):=
   (algebraMap (RationalCoefficients K) L).injective.comp
     (IsFractionRing.injective (Polynomial K) (RationalCoefficients K))
 have hne:geometricSurfaceMap K L F≠0:=by
   rw [geometricSurfaceMap_eq_surfaceMap]
   exact surfaceMap_ne_zero _ hφ F hF
 have hc:(geometricSurfaceMap K L F).degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4):=by
   rw [geometricSurfaceMap_eq_surfaceMap]
   exact surfaceMap_degreeOf_le _ F 1
 exact (coordinate_degree_le_of_dvd (1:Fin 3) g _ hdivF hne).trans hc
theorem geometric_factor_regular_gate
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   0 < g.degreeOf (1:Fin 3)∧g.degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4)∧
     g.degreeOf (1:Fin 3) < p∧MvPolynomial.pderiv (1:Fin 3) g≠0∧
     ¬ g∣geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 have hle:=geometric_factor_R_degree_le K L F hF.ne_zero g hdivF
 exact ⟨geometric_factor_R_degree_positive K L F hF p hpos hsmall g hg hdivF,
   hle,hle.trans_lt hsmall,
   geometric_factor_R_derivative_nonzero K L F hF p hpos hsmall g hg hdivF,
   H_proper_on_every_geometric_factor K L F hF p hpos hsmall g hg hdivF⟩
end GeometricRegularity
end
end ProximityPrize.SubmissionLower.RCN267
end PackedLegacy_AD

/-! Packed from ProximityPrize.SubmissionLower.P5. -/
section PackedLegacy_P5
namespace ProximityPrize.SubmissionLower.RCN290
open RCN082 RCN136 RCN267
noncomputable section
section GenericResultant
variable {A:Type*} [CommRing A] [IsDomain A] [IsGCDMonoid A]
theorem primitive_irreducible_dvd_of_resultant_zero
   (P Q:Polynomial A) (hprimitive:P.IsPrimitive) (hP:Irreducible P)
   (hzero:Polynomial.resultant P Q P.natDegree Q.natDegree=0):P∣Q:=by
 classical
 let T:=FractionRing A
 let f:A →+*T:=algebraMap A T
 have hf:Function.Injective f:=IsFractionRing.injective A T
 have hPd:(P.map f).natDegree=P.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf P
 have hQd:(Q.map f).natDegree=Q.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf Q
 have hfixed:Polynomial.resultant (P.map f) (Q.map f)
     P.natDegree Q.natDegree=0:=by
   rw [Polynomial.resultant_map_map,hzero,map_zero]
 have hres:Polynomial.resultant (P.map f) (Q.map f)=0:=by
   simpa only [hPd,hQd] using hfixed
 have hnot:¬ IsCoprime (P.map f) (Q.map f):=
   (Polynomial.resultant_eq_zero_iff.mp hres).2
 have hi:Irreducible (P.map f):=
   hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hP
 exact hprimitive.dvd_of_fraction_map_dvd_fraction_map
   ((Irreducible.dvd_iff_not_isCoprime hi).mpr hnot)
theorem irreducible_resultant_nonzero
   (P Q:Polynomial A) (hP:Irreducible P) (hpos:0 < P.natDegree)
   (hproper:¬ P∣Q):
   Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=by
 intro hz
 exact hproper (primitive_irreducible_dvd_of_resultant_zero P Q
   (hP.isPrimitive (Nat.ne_of_gt hpos)) hP hz)
end GenericResultant
section Construction
variable {K:Type*} [Field K]
abbrev RemainingCoordinates:={i:Fin 4//i≠2}
abbrev CoefficientRing (K:Type*) [Field K]:=
 MvPolynomial RemainingCoordinates K
def collectR (K:Type*) [Field K]:
   MvPolynomial (Fin 4) K ≃ₐ[K] Polynomial (CoefficientRing K):=
 (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe (2:Fin 4)).symm).trans
   (MvPolynomial.optionEquivLeft K RemainingCoordinates)
theorem collectR_natDegree (F:MvPolynomial (Fin 4) K):
   (collectR K F).natDegree=F.degreeOf 2:=by
 exact (MvPolynomial.degreeOf_eq_natDegree (2:Fin 4) F).symm
def eliminateR (F G:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 (collectR K).symm (Polynomial.C
   (Polynomial.resultant (collectR K F) (collectR K G)))
theorem eliminateR_R_degree (F G:MvPolynomial (Fin 4) K):
   (eliminateR F G).degreeOf 2=0:=by
 rw [←collectR_natDegree,eliminateR,AlgEquiv.apply_symm_apply,
   Polynomial.natDegree_C]
theorem eliminateR_nonzero
   (F G:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 2) (hproper:¬ F∣G):eliminateR F G≠0:=by
 have hi:Irreducible (collectR K F):=(MulEquiv.irreducible_iff (collectR K)).mpr hF
 have hdegree:0 < (collectR K F).natDegree:=by
   rw [collectR_natDegree]
   exact hpos
 have hnot:¬ collectR K F∣collectR K G:=by
   intro hd
   apply hproper
   obtain ⟨T,hT⟩:=hd
   refine ⟨(collectR K).symm T,?_⟩
   apply (collectR K).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hT
 have hres:=irreducible_resultant_nonzero (collectR K F) (collectR K G)
   hi hdegree hnot
 intro hz
 have hh:=congrArg (collectR K) hz
 have hc:Polynomial.C (Polynomial.resultant (collectR K F) (collectR K G))=0:=by
   simpa only [eliminateR,AlgEquiv.apply_symm_apply,map_zero] using hh
 exact hres (Polynomial.C_eq_zero.mp hc)
theorem eliminateR_bezout (F G:MvPolynomial (Fin 4) K)
   (hpos:0 < F.degreeOf 2):
   ∃ A B:MvPolynomial (Fin 4) K,F*A+G*B=eliminateR F G:=by
 obtain ⟨A,B,_,_,hab⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
   (collectR K F) (collectR K G) le_rfl le_rfl
     (Or.inl (by rw [collectR_natDegree];omega))
 refine ⟨(collectR K).symm A,(collectR K).symm B,?_⟩
 apply (collectR K).injective
 simpa only [map_add,map_mul,AlgEquiv.apply_symm_apply,eliminateR] using hab
theorem eliminateR_map_zero {A:Type*} [CommRing A]
   (ψ:MvPolynomial (Fin 4) K →+*A)
   (F G:MvPolynomial (Fin 4) K) (hpos:0 < F.degreeOf 2)
   (hF:ψ F=0) (hG:ψ G=0):ψ (eliminateR F G)=0:=by
 obtain ⟨U,V,huv⟩:=eliminateR_bezout F G hpos
 rw [←huv,map_add,map_mul,map_mul,hF,hG,zero_mul,zero_mul,zero_add]
def singularContribution (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 if F.degreeOf 2=0 then F else eliminateR F (MvPolynomial.pderiv (2:Fin 4) F)
def singularAuxiliary (Q:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 ∏ F∈activeFactors Q,singularContribution F
theorem singularContribution_nonzero
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hsmall:F.degreeOf 2 < p):singularContribution F≠0:=by
 unfold singularContribution
 split_ifs with h
 · exact hF.ne_zero
 · have hp:0 < F.degreeOf 2:=Nat.pos_of_ne_zero h
   exact eliminateR_nonzero F _ hF hp (equation_not_dvd_R_derivative F p hp hsmall)
theorem singularContribution_R_degree (F:MvPolynomial (Fin 4) K):
   (singularContribution F).degreeOf 2=0:=by
 unfold singularContribution
 split_ifs with h
 · exact h
 · exact eliminateR_R_degree F _
theorem singularAuxiliary_nonzero
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (p:ℕ) [CharP K p]
   (hsmall:Q.degreeOf 2 < p):singularAuxiliary Q≠0:=by
 classical
 apply Finset.prod_ne_zero_iff.mpr
 intro F hF
 have hs:=activeFactors_spec Q F hF
 apply singularContribution_nonzero F hs.1 p
 exact (RCN081.degreeOf_le_of_dvd (2:Fin 4) F Q hs.2.1 hQ).trans_lt hsmall
theorem singularAuxiliary_R_degree
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (p:ℕ) [CharP K p]
   (hsmall:Q.degreeOf 2 < p):(singularAuxiliary Q).degreeOf 2=0:=by
 classical
 have hne:∀ F∈activeFactors Q,singularContribution F≠0:=by
   intro F hF
   have hs:=activeFactors_spec Q F hF
   exact singularContribution_nonzero F hs.1 p
     ((RCN081.degreeOf_le_of_dvd (2:Fin 4) F Q hs.2.1 hQ).trans_lt hsmall)
 change (∏ F∈activeFactors Q,singularContribution F).degreeOf 2=0
 rw [MvPolynomial.degreeOf_prod_eq (n:=(2:Fin 4)) _ _ hne]
 simp only [singularContribution_R_degree,Finset.sum_const_zero]
theorem singularContribution_map_zero {A:Type*} [CommRing A]
   (ψ:MvPolynomial (Fin 4) K →+*A) (F:MvPolynomial (Fin 4) K)
   (hF:ψ F=0) (hsingular:F.degreeOf 2=0∨ψ (MvPolynomial.pderiv 2 F)=0):
   ψ (singularContribution F)=0:=by
 unfold singularContribution
 split_ifs with h
 · exact hF
 · exact eliminateR_map_zero ψ F _ (Nat.pos_of_ne_zero h) hF
     (hsingular.resolve_left h)
theorem singularAuxiliary_map_zero {A:Type*} [CommRing A]
   (ψ:MvPolynomial (Fin 4) K →+*A) (Q F:MvPolynomial (Fin 4) K)
   (hmem:F∈activeFactors Q) (hF:ψ F=0)
   (hsingular:F.degreeOf 2=0∨ψ (MvPolynomial.pderiv 2 F)=0):
   ψ (singularAuxiliary Q)=0:=by
 classical
 change ψ (∏ G∈activeFactors Q,singularContribution G)=0
 rw [map_prod]
 apply Finset.prod_eq_zero hmem
 exact singularContribution_map_zero ψ F hF hsingular
end Construction
section ActualCoverage
variable {K L:Type*} [Field K] [Field L]
theorem surface_zero_singular_or_regular
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (v:Fin 3 → L) (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
   MvPolynomial.eval v (surfaceMap φ (singularAuxiliary Q))=0∨
     ∃ F∈activeFactors Q,Irreducible F∧0 < F.degreeOf 2∧
       MvPolynomial.eval v (surfaceMap φ F)=0∧
       MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv 2 F))≠0:=by
 classical
 obtain ⟨F,hF,hz⟩:=exists_active_factor_of_surface_zero φ hφ Q hQ v hzero
 by_cases hr:F.degreeOf 2=0
 · exact Or.inl (singularAuxiliary_map_zero
     ((MvPolynomial.eval v).comp (surfaceMap φ)) Q F hF hz (Or.inl hr))
 · rcases eq_or_ne (MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv 2 F))) 0 with hh | hh
   · exact Or.inl (singularAuxiliary_map_zero
       ((MvPolynomial.eval v).comp (surfaceMap φ)) Q F hF hz (Or.inr hh))
   · exact Or.inr ⟨F,hF,(activeFactors_spec Q F hF).1,Nat.pos_of_ne_zero hr,hz,hh⟩
end ActualCoverage
end
end ProximityPrize.SubmissionLower.RCN290
end PackedLegacy_P5

/-! Packed from ProximityPrize.SubmissionLower.CA. -/
section PackedLegacy_CA
namespace ProximityPrize.SubmissionLower.RCN293
open RCN290 RCN081 RCN082
noncomputable section
variable {K:Type*} [Field K]
def embedCoefficients (K:Type*) [Field K]:
   CoefficientRing K →+*MvPolynomial (Fin 4) K:=
 (collectR K).symm.toRingHom.comp Polynomial.C
theorem collectR_X_other (i:RemainingCoordinates):
   collectR K (MvPolynomial.X (i:Fin 4))=Polynomial.C (MvPolynomial.X i):=by
 simp [collectR,MvPolynomial.renameEquiv_apply,
   Equiv.optionSubtypeNe_symm_apply,i.property]
theorem collectR_rename_remaining (P:CoefficientRing K):
   collectR K (MvPolynomial.rename Subtype.val P)=Polynomial.C P:=by
 induction P using MvPolynomial.induction_on with
 | C a => simp [collectR,MvPolynomial.renameEquiv_apply]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     simp only [map_mul,MvPolynomial.rename_X,hP,collectR_X_other]
theorem embedCoefficients_eq_rename (P:CoefficientRing K):
   embedCoefficients K P=MvPolynomial.rename Subtype.val P:=by
 apply (collectR K).injective
 rw [collectR_rename_remaining]
 exact (collectR K).apply_symm_apply (Polynomial.C P)
def liftedCoefficient (F:MvPolynomial (Fin 4) K) (n:ℕ):
   MvPolynomial (Fin 4) K:=embedCoefficients K ((collectR K F).coeff n)
theorem liftedCoefficient_R_degree (F:MvPolynomial (Fin 4) K) (n:ℕ):
   (liftedCoefficient F n).degreeOf 2=0:=by
 rw [←collectR_natDegree]
 change ((collectR K) ((collectR K).symm (Polynomial.C ((collectR K F).coeff n)))).natDegree=0
 rw [AlgEquiv.apply_symm_apply,Polynomial.natDegree_C]
theorem liftedCoefficient_support
   (F:MvPolynomial (Fin 4) K) (n:ℕ) (e:Fin 4 →₀ ℕ)
   (he:e∈(liftedCoefficient F n).support):
   ∃ d∈F.support,∀ i,e i ≤ d i:=by
 classical
 have heR:e 2=0:=by
   have hh:=MvPolynomial.monomial_le_degreeOf (2:Fin 4) he
   rw [liftedCoefficient_R_degree] at hh
   omega
 change e∈(embedCoefficients K ((collectR K F).coeff n)).support at he
 rw [embedCoefficients_eq_rename,
   MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
 obtain ⟨u,hu,heu⟩:=Finset.mem_image.mp he
 have hopt:u.optionElim n∈
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm F).support:=
   (MvPolynomial.mem_support_coeff_optionEquivLeft (R:=K)).mp hu
 rw [MvPolynomial.support_rename_of_injective
   (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at hopt
 obtain ⟨d,hd,hdu⟩:=Finset.mem_image.mp hopt
 refine ⟨d,hd,?_⟩
 intro i
 by_cases hi:i=2
 · subst i
   rw [heR]
   exact Nat.zero_le _
 · have hev:e i=u ⟨i,hi⟩:=by
     rw [←heu]
     exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i,hi⟩
   have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm i)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i=some ⟨i,hi⟩:=by
     simp [Equiv.optionSubtypeNe_symm_apply,hi]
   rw [hindex,Finsupp.optionElim_apply_some] at huv
   exact le_of_eq (hev.trans huv.symm)
theorem weight_mono_fin4 (weights:Fin 4 → ℕ) (e d:Fin 4 →₀ ℕ)
   (h:∀ i,e i ≤ d i):Finsupp.weight weights e ≤ Finsupp.weight weights d:=by
 rw [weight_fin4,weight_fin4]
 gcongr <;> exact h _
theorem liftedCoefficient_weight_le (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (n:ℕ):
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient F n) ≤
     MvPolynomial.weightedTotalDegree weights F:=by
 apply (weightedTotalDegree_le_iff weights _ _).mpr
 intro e he
 obtain ⟨d,hd,hed⟩:=liftedCoefficient_support F n e he
 exact (weight_mono_fin4 weights e d hed).trans (MvPolynomial.le_weightedTotalDegree weights hd)
theorem pderiv_weight_le (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (i:Fin 4):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.pderiv i F) ≤
     MvPolynomial.weightedTotalDegree weights F:=by
 apply (weightedTotalDegree_le_iff weights _ _).mpr
 intro e he
 have hd:=RCN313.support_before_pderiv i F e he
 have hle:Finsupp.weight weights e ≤
     Finsupp.weight weights (e+Finsupp.single i 1):=by
   rw [map_add]
   exact Nat.le_add_right _ _
 exact hle.trans (MvPolynomial.le_weightedTotalDegree weights hd)
theorem degreeOf_det_le_uniform (N a:ℕ)
   (M:Matrix (Fin N) (Fin N) (MvPolynomial (Fin 5) K))
   (hM:∀ i j,(M i j).degreeOf 4 ≤ a):M.det.degreeOf 4 ≤ N*a:=by
 classical
 rw [Matrix.det_apply']
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) Finset.univ _).trans
 apply Finset.sup_le_iff.mpr
 intro σ _
 have hprod:(∏ i,M (σ i) i).degreeOf (4:Fin 5) ≤ N*a:=by
   calc
     _ ≤ ∑ i:Fin N,(M (σ i) i).degreeOf (4:Fin 5):=
       MvPolynomial.degreeOf_prod_le (4:Fin 5) Finset.univ _
     _ ≤ ∑ _i:Fin N,a:=Finset.sum_le_sum fun i _ => hM (σ i) i
     _=N*a:=by simp
 have hsign:(((Equiv.Perm.sign σ:ℤ):MvPolynomial (Fin 5) K)).degreeOf 4 ≤ 0:=by
   simpa only [map_intCast] using
     (MvPolynomial.degreeOf_C (((Equiv.Perm.sign σ:ℤ):K)) (4:Fin 5)).le
 exact (MvPolynomial.degreeOf_mul_le (4:Fin 5) _ _).trans
   ((Nat.add_le_add hsign hprod).trans_eq (zero_add _))
def weightedCoefficientEmbedding (K:Type*) [Field K] (weights:Fin 4 → ℕ):
   CoefficientRing K →+*MvPolynomial (Fin 5) K:=
 (weightedLift K weights).comp (embedCoefficients K)
theorem degree_weightedCoefficient (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (n:ℕ):
   (weightedCoefficientEmbedding K weights ((collectR K F).coeff n)).degreeOf 4 ≤
     MvPolynomial.weightedTotalDegree weights F:=by
 change (weightedLift K weights (liftedCoefficient F n)).degreeOf 4 ≤ _
 rw [degree_weightedLift]
 exact liftedCoefficient_weight_le weights F n
theorem eliminateR_weight_le (weights:Fin 4 → ℕ)
   (F G:MvPolynomial (Fin 4) K) (a:ℕ)
   (hF:MvPolynomial.weightedTotalDegree weights F ≤ a)
   (hG:MvPolynomial.weightedTotalDegree weights G ≤ a):
   MvPolynomial.weightedTotalDegree weights (eliminateR F G) ≤
     (F.degreeOf 2+G.degreeOf 2)*a:=by
 let ψ:=weightedCoefficientEmbedding K weights
 let M:=Polynomial.sylvester (collectR K F) (collectR K G)
   (collectR K F).natDegree (collectR K G).natDegree
 have hentry:∀ i j,((ψ.mapMatrix M) i j).degreeOf (4:Fin 5) ≤ a:=by
   intro i j
   induction j using Fin.addCases with
   | «left» j =>
       simp only [RingHom.mapMatrix_apply,Matrix.map_apply,M,Polynomial.sylvester,
         Matrix.of_apply,Fin.addCases_left]
       split_ifs
       · exact (degree_weightedCoefficient weights G _).trans hG
       · simp
   | «right» j =>
       simp only [RingHom.mapMatrix_apply,Matrix.map_apply,M,Polynomial.sylvester,
         Matrix.of_apply,Fin.addCases_right]
       split_ifs
       · exact (degree_weightedCoefficient weights F _).trans hF
       · simp
 have hdet:=degreeOf_det_le_uniform
   ((collectR K F).natDegree+(collectR K G).natDegree) a (ψ.mapMatrix M) hentry
 rw [←ψ.map_det] at hdet
 change (weightedLift K weights (eliminateR F G)).degreeOf 4 ≤ _ at hdet
 rw [degree_weightedLift,collectR_natDegree,collectR_natDegree] at hdet
 exact hdet
theorem weightedTotalDegree_prod_le {ι:Type*} (weights:Fin 4 → ℕ)
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (∏ i∈I,f i) ≤
     ∑ i∈I,MvPolynomial.weightedTotalDegree weights (f i):=by
 rw [←degree_weightedLift,map_prod]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_prod_le (4:Fin 5) I (fun i => weightedLift K weights (f i)))
theorem sum_weighted_degrees_le_of_prod_dvd {ι:Type*} (weights:Fin 4 → ℕ)
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ i∈I,f i)∣Q):
   (∑ i∈I,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈I,f i)≠0:=by
   intro hz
   obtain ⟨T,hT⟩:=hdiv
   exact hQ (by rw [hT,hz,zero_mul])
 have hf:∀ i∈I,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 have hmap:(∏ i∈I,weightedLift K weights (f i))∣weightedLift K weights Q:=by
   obtain ⟨T,hT⟩:=hdiv
   refine ⟨weightedLift K weights T,?_⟩
   rw [hT,map_mul,map_prod]
 calc
   (∑ i∈I,MvPolynomial.weightedTotalDegree weights (f i))=
       ∑ i∈I,(weightedLift K weights (f i)).degreeOf (4:Fin 5):=by
     simp only [degree_weightedLift]
   _=(∏ i∈I,weightedLift K weights (f i)).degreeOf (4:Fin 5):=
     (MvPolynomial.degreeOf_prod_eq I _
       (fun i hi => weightedLift_ne_zero weights (f i) (hf i hi))).symm
   _ ≤ (weightedLift K weights Q).degreeOf (4:Fin 5):=
     RCN137.coordinate_degree_le_of_dvd (4:Fin 5) _ _ hmap
       (weightedLift_ne_zero weights Q hQ)
   _=MvPolynomial.weightedTotalDegree weights Q:=degree_weightedLift weights Q
theorem singularContribution_weight_le (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (s:ℕ) (hs:1 ≤ s) (hR:F.degreeOf 2 ≤ s):
   MvPolynomial.weightedTotalDegree weights (singularContribution F) ≤
     (2*s-1)*MvPolynomial.weightedTotalDegree weights F:=by
 unfold singularContribution
 split_ifs with h
 · have hfactor:1 ≤ 2*s-1:=by omega
   simpa only [one_mul] using
     (Nat.mul_le_mul_right (MvPolynomial.weightedTotalDegree weights F) hfactor)
 · have hpos:0 < F.degreeOf 2:=Nat.pos_of_ne_zero h
   have hder:=RCN267.R_derivative_degree_lt F hpos
   have hfactor:F.degreeOf 2+(MvPolynomial.pderiv (2:Fin 4) F).degreeOf 2 ≤
       2*s-1:=by omega
   exact (eliminateR_weight_le weights F (MvPolynomial.pderiv (2:Fin 4) F)
     (MvPolynomial.weightedTotalDegree weights F) le_rfl (pderiv_weight_le weights F 2)).trans
     (Nat.mul_le_mul_right _ hfactor)
theorem singularAuxiliary_weight_le (weights:Fin 4 → ℕ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (s:ℕ) (hs:1 ≤ s) (hR:Q.degreeOf 2 ≤ s):
   MvPolynomial.weightedTotalDegree weights (singularAuxiliary Q) ≤
     (2*s-1)*MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 calc
   _ ≤ ∑ F∈activeFactors Q,
       MvPolynomial.weightedTotalDegree weights (singularContribution F):=
     weightedTotalDegree_prod_le weights (activeFactors Q) singularContribution
   _ ≤ ∑ F∈activeFactors Q,
       (2*s-1)*MvPolynomial.weightedTotalDegree weights F:=by
     apply Finset.sum_le_sum
     intro F hF
     exact singularContribution_weight_le weights F s hs
       ((RCN081.degreeOf_le_of_dvd (2:Fin 4) F Q
         (activeFactors_spec Q F hF).2.1 hQ).trans hR)
   _=(2*s-1)*∑ F∈activeFactors Q,MvPolynomial.weightedTotalDegree weights F:=by
     rw [Finset.mul_sum]
   _ ≤ (2*s-1)*MvPolynomial.weightedTotalDegree weights Q:=
     Nat.mul_le_mul_left _ (sum_weighted_degrees_le_of_prod_dvd weights
       (activeFactors Q) id Q hQ (activeFactors_product_dvd Q hQ))
theorem singularAuxiliary_input_caps
   (Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
   (hQ:Q≠0) (hs:1 ≤ s)
   (hbox:Q∈RCN174.globalCoefficientBox K D w L s):
   MvPolynomial.weightedTotalDegree seedWeights (singularAuxiliary Q) ≤ (2*s-1)*L∧
     MvPolynomial.weightedTotalDegree (contactWeights w) (singularAuxiliary Q) <
       (2*s-1)*D:=by
 have hD:0 < D:=by
   obtain ⟨d,hd⟩:=MvPolynomial.support_nonempty.mpr hQ
   have hh:=(hbox hd).2.2
   omega
 have hcaps:=(mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
 have hR:Q.degreeOf 2 ≤ s:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hpositive:0 < 2*s-1:=by omega
 refine ⟨(singularAuxiliary_weight_le seedWeights Q hQ s hs hR).trans
   (Nat.mul_le_mul_left _ hcaps.1),?_⟩
 have hle:=(singularAuxiliary_weight_le (contactWeights w) Q hQ s hs hR).trans
   (Nat.mul_le_mul_left _ hcaps.2.2)
 exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left (by omega:D-1 < D) hpositive)
theorem singularAuxiliary_nonzero_mem_box
   (Q:MvPolynomial (Fin 4) K) (D w L s p:ℕ) [CharP K p]
   (hQ:Q≠0) (hs:1 ≤ s) (hsmall:s < p)
   (hbox:Q∈RCN174.globalCoefficientBox K D w L s):
   singularAuxiliary Q≠0∧
     singularAuxiliary Q∈RCN174.globalCoefficientBox K
       ((2*s-1)*D) w ((2*s-1)*L) 0:=by
 have hR:Q.degreeOf 2 ≤ s:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hjR:=singularAuxiliary_R_degree Q hQ p (hR.trans_lt hsmall)
 have hc:=singularAuxiliary_input_caps Q D w L s hQ hs hbox
 refine ⟨singularAuxiliary_nonzero Q hQ p (hR.trans_lt hsmall),?_⟩
 intro d hd
 have hseed:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hc.1
 have hcontact:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans_lt hc.2
 have hslope:=MvPolynomial.monomial_le_degreeOf (f:=singularAuxiliary Q) (2:Fin 4) hd
 rw [hjR] at hslope
 rw [seed_weight] at hseed
 rw [contact_weight] at hcontact
 exact ⟨hseed,hslope,hcontact⟩
end
end ProximityPrize.SubmissionLower.RCN293
end PackedLegacy_CA

/-! Packed from ProximityPrize.SubmissionLower.BS. -/
section PackedLegacy_BS
namespace ProximityPrize.SubmissionLower.RCN167
open RCN081 RCN082 RCN293 RCN267 RCN313 RCN136 RCN319 RCN231
noncomputable section
variable {K:Type*} [Field K]
def implicitLift (A:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 MvPolynomial.pderiv (0:Fin 4) A+
   MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) A
theorem implicitLift_R_derivative (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0):
   MvPolynomial.pderiv (2:Fin 4) (implicitLift A)=MvPolynomial.pderiv (1:Fin 4) A:=by
 have hX:(MvPolynomial.pderiv (0:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 0 2 A 0 (by omega)
 have hY:(MvPolynomial.pderiv (1:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 1 2 A 0 (by omega)
 have hx0:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) _ hX
 have hy0:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) _ hY
 simp only [implicitLift,map_add,MvPolynomial.pderiv_mul,hx0,hy0,
   MvPolynomial.pderiv_X_self,one_mul,mul_zero,add_zero,zero_add]
theorem implicitLift_nonzero (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
   implicitLift A≠0:=by
 intro h
 apply hY
 rw [←implicitLift_R_derivative A hR,h,map_zero]
theorem implicitLift_R_degree_le (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0):(implicitLift A).degreeOf 2 ≤ 1:=by
 have hX:(MvPolynomial.pderiv (0:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 0 2 A 0 (by omega)
 have hY:(MvPolynomial.pderiv (1:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 1 2 A 0 (by omega)
 have hvar:(MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K).degreeOf 2 ≤ 1:=by simp
 have hm:=degree_mul_bound (2:Fin 4) hvar hY
 exact degree_add_bound (2:Fin 4) (hX.trans (by omega)) (by simpa using hm)
theorem implicitLift_other_degree_le (A:MvPolynomial (Fin 4) K)
   (i:Fin 4) (hi:i≠2):(implicitLift A).degreeOf i ≤ A.degreeOf i:=by
 have hX:=pderiv_degree_bound 0 i A (A.degreeOf i) le_rfl
 have hY:=pderiv_degree_bound 1 i A (A.degreeOf i) le_rfl
 have hvar:(MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K).degreeOf i ≤ 0:=by
   simp [MvPolynomial.degreeOf_X,hi]
 have hm:=degree_mul_bound i hvar hY
 exact degree_add_bound i hX (by simpa using hm)
theorem implicitLift_solution (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0) (P:Polynomial K) (γ:K)
   (hA:specialization K P γ A=0):specialization K P γ (implicitLift A)=0:=by
 have hchain:=derivative_specialization K P γ A
 rw [hA,Polynomial.derivative_zero,pderiv_zero_of_degree_zero (2:Fin 4) A hR,
   map_zero,mul_zero,add_zero] at hchain
 have hspec:specialization K P γ (implicitLift A)=
     specialization K P γ (MvPolynomial.pderiv (0:Fin 4) A)+
       P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A):=by
   simp [implicitLift,specialization]
 exact hspec.trans hchain.symm
theorem weighted_mul_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (P*Q) ≤
     MvPolynomial.weightedTotalDegree weights P+MvPolynomial.weightedTotalDegree weights Q:=by
 rw [←degree_weightedLift,map_mul]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_mul_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_add_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (P+Q) ≤
     max (MvPolynomial.weightedTotalDegree weights P) (MvPolynomial.weightedTotalDegree weights Q):=by
 rw [←degree_weightedLift,map_add]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_add_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_X (weights:Fin 4 → ℕ) (i:Fin 4):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.X i:MvPolynomial (Fin 4) K)=weights i:=by
 simp [MvPolynomial.weightedTotalDegree,MvPolynomial.support_X,Finsupp.weight_single]
theorem pderiv_weight_sub_bound (weights:Fin 4 → ℕ)
   (A:MvPolynomial (Fin 4) K) (i:Fin 4) (B:ℕ)
   (hA:MvPolynomial.weightedTotalDegree weights A ≤ B):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.pderiv i A) ≤ B-weights i:=by
 apply (weightedTotalDegree_le_iff weights _ _).mpr
 intro d hd
 have hh:=(MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i A d hd)).trans hA
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 omega
theorem implicitLift_seed_weight_le (A:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree seedWeights (implicitLift A) ≤
     MvPolynomial.weightedTotalDegree seedWeights A:=by
 have hX:=pderiv_weight_le seedWeights A 0
 have hY:=pderiv_weight_le seedWeights A 1
 have hvar:MvPolynomial.weightedTotalDegree seedWeights
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K)=0:=by
   rw [weighted_X]
   simp [seedWeights]
 have hm:=weighted_mul_le seedWeights (MvPolynomial.X (2:Fin 4))
   (MvPolynomial.pderiv (1:Fin 4) A)
 rw [hvar,zero_add] at hm
 exact (weighted_add_le seedWeights _ _).trans (max_le hX (hm.trans hY))
theorem implicitLift_contact_weight_le
   (A:MvPolynomial (Fin 4) K) (D w:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hA:MvPolynomial.weightedTotalDegree (contactWeights w) A ≤ D-1):
   MvPolynomial.weightedTotalDegree (contactWeights w) (implicitLift A) ≤ D-2:=by
 have hX:=pderiv_weight_sub_bound (contactWeights w) A 0 (D-1) hA
 have hY:=pderiv_weight_sub_bound (contactWeights w) A 1 (D-1) hA
 change MvPolynomial.weightedTotalDegree (contactWeights w)
   (MvPolynomial.pderiv (0:Fin 4) A) ≤ D-1-1 at hX
 change MvPolynomial.weightedTotalDegree (contactWeights w)
   (MvPolynomial.pderiv (1:Fin 4) A) ≤ D-1-w at hY
 have hx:MvPolynomial.weightedTotalDegree (contactWeights w)
     (MvPolynomial.pderiv (0:Fin 4) A) ≤ D-2:=by omega
 have hvar:MvPolynomial.weightedTotalDegree (contactWeights w)
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K)=w-1:=by
   rw [weighted_X]
   simp [contactWeights]
 have hm:=weighted_mul_le (contactWeights w) (MvPolynomial.X (2:Fin 4))
   (MvPolynomial.pderiv (1:Fin 4) A)
 rw [hvar] at hm
 have hm':MvPolynomial.weightedTotalDegree (contactWeights w)
     (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) A) ≤ D-2:=by omega
 exact (weighted_add_le (contactWeights w) _ _).trans (max_le hx hm')
theorem implicitLift_mem_box
   (A:MvPolynomial (Fin 4) K) (D w L:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:A∈RCN174.globalCoefficientBox K D w L 0):
   implicitLift A∈RCN174.globalCoefficientBox K D w L 1:=by
 have hD:0 < D:=by omega
 have hcaps:=(mem_globalCoefficientBox_iff A D w L 0 hD).mp hbox
 have hR:A.degreeOf 2=0:=by
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hs:=(implicitLift_seed_weight_le A).trans hcaps.1
 have hc:=implicitLift_contact_weight_le A D w hw hDw hcaps.2.2
 have hr:=implicitLift_R_degree_le A hR
 intro d hd
 have hseed:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hs
 have hcontact:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hc
 have hslope:=(MvPolynomial.monomial_le_degreeOf (f:=implicitLift A) (2:Fin 4) hd).trans hr
 rw [seed_weight] at hseed
 rw [contact_weight] at hcontact
 exact ⟨hseed,hslope,by omega⟩
def positiveRFactors (F:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (activeFactors F).filter (fun G => 0 < G.degreeOf 2)
theorem positiveRFactors_spec (F G:MvPolynomial (Fin 4) K)
   (hG:G∈positiveRFactors F):Irreducible G∧G∣F∧0 < G.degreeOf 2:=by
 classical
 obtain ⟨hmem,hpos⟩:=Finset.mem_filter.mp hG
 have hh:=activeFactors_spec F G hmem
 exact ⟨hh.1,hh.2.1,hpos⟩
theorem positiveRFactors_product_dvd (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∏ G∈positiveRFactors F,G)∣F:=by
 classical
 exact (Finset.prod_dvd_prod_of_subset (positiveRFactors F) (activeFactors F) id
   (Finset.filter_subset _ _)).trans (activeFactors_product_dvd F hF)
theorem factor_derivative_regular_at_zero {B:Type*} [CommRing B]
   (ψ:MvPolynomial (Fin 4) K →+*B) (F G:MvPolynomial (Fin 4) K)
   (hdiv:G∣F) (hG:ψ G=0)
   (hregular:ψ (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   ψ (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
 intro hz
 obtain ⟨T,hT⟩:=hdiv
 apply hregular
 rw [hT,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hz,hG,
   zero_mul,zero_mul,zero_add]
theorem lift_positive_factor_budgets (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
   (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4)) ≤ 1∧
     (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (1:Fin 4)) ≤ A.degreeOf 1∧
     (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (3:Fin 4)) ≤ A.degreeOf 3:=by
 have hF:=implicitLift_nonzero A hR hY
 have hprod:=positiveRFactors_product_dvd (implicitLift A) hF
 have hb:=RCN081.sum_degreeOf_le_of_prod_dvd
   (positiveRFactors (implicitLift A)) id (implicitLift A) hF hprod
 exact ⟨(hb 2).trans (implicitLift_R_degree_le A hR),
   (hb 1).trans (implicitLift_other_degree_le A 1 (by decide)),
   (hb 3).trans (implicitLift_other_degree_le A 3 (by decide))⟩
section SurfacePoints
variable {T:Type*} [Field T]
theorem exists_regular_lift_factor_at_surface
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (A:MvPolynomial (Fin 4) K) (hA:A≠0) (hR:A.degreeOf 2=0)
   (v:Fin 3 → T) (hzero:MvPolynomial.eval v (surfaceMap φ (implicitLift A))=0)
   (hregular:MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0):
   ∃ G∈positiveRFactors (implicitLift A),Irreducible G∧G∣implicitLift A∧
     G.degreeOf 2=1∧MvPolynomial.eval v (surfaceMap φ G)=0∧
     MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) G))≠0∧¬ G∣A:=by
 classical
 let ψ:MvPolynomial (Fin 4) K →+*T:=(MvPolynomial.eval v).comp (surfaceMap φ)
 have hY:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
   intro hz
   apply hregular
   rw [hz,map_zero,map_zero]
 have hF:=implicitLift_nonzero A hR hY
 obtain ⟨G,hG,hz⟩:=exists_active_factor_of_surface_zero φ hφ (implicitLift A) hF v hzero
 have hspec:=activeFactors_spec (implicitLift A) G hG
 have hFregular:ψ (MvPolynomial.pderiv (2:Fin 4) (implicitLift A))≠0:=by
   rw [implicitLift_R_derivative A hR]
   exact hregular
 have hGreg:=factor_derivative_regular_at_zero ψ (implicitLift A) G hspec.2.1 hz hFregular
 have hpos:0 < G.degreeOf 2:=by
   apply Nat.pos_of_ne_zero
   intro hn
   apply hGreg
   rw [pderiv_zero_of_degree_zero (2:Fin 4) G hn,map_zero]
 have hdeg:G.degreeOf 2=1:=by
   have hh:=(RCN081.degreeOf_le_of_dvd (2:Fin 4) G (implicitLift A)
     hspec.2.1 hF).trans (implicitLift_R_degree_le A hR)
   omega
 have hproper:¬ G∣A:=by
   intro hd
   have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) G A hd hA
   omega
 exact ⟨G,Finset.mem_filter.mpr ⟨hG,hpos⟩,hspec.1,hspec.2.1,hdeg,hz,hGreg,hproper⟩
end SurfacePoints
theorem exists_regular_lift_factor_of_solution
   (A:MvPolynomial (Fin 4) K) (hA:A≠0) (P:Polynomial K) (γ:K)
   (D w L:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:A∈RCN174.globalCoefficientBox K D w L 0)
   (hsolution:specialization K P γ A=0)
   (hregular:specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A)≠0):
   ∃ G∈positiveRFactors (implicitLift A),Irreducible G∧G.degreeOf 2=1∧
     G∈RCN174.globalCoefficientBox K D w L 1∧
     specialization K P γ G=0∧
     specialization K P γ (MvPolynomial.pderiv (2:Fin 4) G)≠0∧¬ G∣A:=by
 have hR:A.degreeOf 2=0:=by
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hFsolution:=implicitLift_solution A hR P γ hsolution
 let φ:=RCN135.polynomialEmbedding K
 let v:Fin 3 → RCN135.GenericField K:=
   fun i => RCN135.initialPoint K P γ i.succ
 have hzero:MvPolynomial.eval v (surfaceMap φ (implicitLift A))=0:=by
   have hh:=(RCN138.actual_generic_initial_zero_iff K P γ (implicitLift A)).mpr hFsolution
   simpa only [RCN138.canonical_geometricSurfaceMap] using hh
 have hreg:MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0:=by
   intro hz
   apply hregular
   apply (RCN138.actual_generic_initial_zero_iff K P γ _).mp
   simpa only [RCN138.canonical_geometricSurfaceMap] using hz
 obtain ⟨G,hG,hi,hd,hdeg,hpoint,hGreg,hproper⟩:=
   exists_regular_lift_factor_at_surface φ (RCN135.polynomialEmbedding_injective K)
     A hA hR v hzero hreg
 have hY:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
   intro hz
   exact hregular (by rw [hz,map_zero])
 have hGbox:=RCN081.mem_globalCoefficientBox_of_dvd G (implicitLift A)
   D w L 1 (implicitLift_nonzero A hR hY) hd (implicitLift_mem_box A D w L hw hDw hbox)
 have hGsol:specialization K P γ G=0:=by
   apply (RCN138.actual_generic_initial_zero_iff K P γ G).mp
   simpa only [RCN138.canonical_geometricSurfaceMap] using hpoint
 have hGregular:specialization K P γ (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
   intro hz
   apply hGreg
   have hh:=(RCN138.actual_generic_initial_zero_iff K P γ _).mpr hz
   simpa only [RCN138.canonical_geometricSurfaceMap] using hh
 exact ⟨G,hG,hi,hdeg,hGbox,hGsol,hGregular,hproper⟩
end
end ProximityPrize.SubmissionLower.RCN167
end PackedLegacy_BS

/-! Packed from ProximityPrize.SubmissionLower.I9. -/
section PackedLegacy_I9
namespace ProximityPrize.SubmissionLower.RCN079
open RCN136 RCN082 RCN290 RCN293 RCN081 RCN319
noncomputable section
variable {K:Type*} [Field K]
def swapYR (K:Type*) [Field K]:MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K:=
 MvPolynomial.renameEquiv K (Equiv.swap (1:Fin 4) 2)
@[simp] theorem swapYR_twice (F:MvPolynomial (Fin 4) K):swapYR K (swapYR K F)=F:=by
 simp [swapYR,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_rename,Function.comp_def]
 exact MvPolynomial.rename_id_apply F
theorem swapYR_ne_zero (F:MvPolynomial (Fin 4) K) (hF:F≠0):swapYR K F≠0:=by
 intro h
 apply hF
 apply (swapYR K).injective
 simpa only [map_zero] using h
theorem swapYR_degree_Y (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 1=F.degreeOf 2:=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (2:Fin 4))
theorem swapYR_degree_R (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 2=F.degreeOf 1:=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (1:Fin 4))
theorem swapYR_degree_Z (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 3=F.degreeOf 3:=by
 have hfix:Equiv.swap (1:Fin 4) 2 (3:Fin 4)=3:=by decide
 simpa only [swapYR,MvPolynomial.renameEquiv_apply,hfix] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (3:Fin 4))
theorem swapYR_pderiv_Y (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 4) (swapYR K F)=
     swapYR K (MvPolynomial.pderiv (2:Fin 4) F):=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.pderiv_rename (Equiv.swap (1:Fin 4) 2).injective (2:Fin 4) F)
theorem coordinate_weight_degree (F:MvPolynomial (Fin 4) K) (i:Fin 4):
   MvPolynomial.weightedTotalDegree (Pi.single i 1) F=F.degreeOf i:=by
 rw [MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => F.support.sup f)
 funext d
 exact Finsupp.weight_single_one_apply i d
def exceptionalAuxiliary (J:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 swapYR K (singularAuxiliary (swapYR K J))
theorem exceptionalAuxiliary_nonzero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (j p:ℕ) [CharP K p]
   (hY:J.degreeOf 1 ≤ j) (hsmall:j < p):exceptionalAuxiliary J≠0:=by
 apply swapYR_ne_zero
 apply singularAuxiliary_nonzero (swapYR K J) (swapYR_ne_zero J hJ) p
 rw [swapYR_degree_R]
 exact hY.trans_lt hsmall
theorem exceptionalAuxiliary_Y_degree_zero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (j p:ℕ) [CharP K p]
   (hY:J.degreeOf 1 ≤ j) (hsmall:j < p):(exceptionalAuxiliary J).degreeOf 1=0:=by
 rw [exceptionalAuxiliary,swapYR_degree_Y]
 apply singularAuxiliary_R_degree (swapYR K J) (swapYR_ne_zero J hJ) p
 rw [swapYR_degree_R]
 exact hY.trans_lt hsmall
theorem exceptionalAuxiliary_R_degree_zero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j:ℕ) (hj:1 ≤ j) (hY:J.degreeOf 1 ≤ j):(exceptionalAuxiliary J).degreeOf 2=0:=by
 have hRswap:(swapYR K J).degreeOf 2 ≤ j:=by rw [swapYR_degree_R];exact hY
 have hb:=singularAuxiliary_weight_le (Pi.single (1:Fin 4) 1)
   (swapYR K J) (swapYR_ne_zero J hJ) j hj hRswap
 rw [coordinate_weight_degree,coordinate_weight_degree,swapYR_degree_Y,hR,mul_zero] at hb
 rw [exceptionalAuxiliary,swapYR_degree_R]
 exact Nat.eq_zero_of_le_zero hb
theorem exceptionalAuxiliary_Z_degree_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (j:ℕ) (hj:1 ≤ j) (hY:J.degreeOf 1 ≤ j):
   (exceptionalAuxiliary J).degreeOf 3 ≤ (2*j-1)*J.degreeOf 3:=by
 have hRswap:(swapYR K J).degreeOf 2 ≤ j:=by rw [swapYR_degree_R];exact hY
 have hb:=singularAuxiliary_weight_le (Pi.single (3:Fin 4) 1)
   (swapYR K J) (swapYR_ne_zero J hJ) j hj hRswap
 rw [coordinate_weight_degree,coordinate_weight_degree,swapYR_degree_Z] at hb
 rw [exceptionalAuxiliary,swapYR_degree_Z]
 exact hb
theorem exceptionalAuxiliary_data
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j):
   exceptionalAuxiliary J≠0∧(exceptionalAuxiliary J).degreeOf 1=0∧
     (exceptionalAuxiliary J).degreeOf 2=0∧
     (exceptionalAuxiliary J).degreeOf 3 ≤ (2*j-1)*j∧
     (exceptionalAuxiliary J).degreeOf 3 ≤ 2*j^2:=by
 have hz:=(exceptionalAuxiliary_Z_degree_le J hJ j hj hY).trans (Nat.mul_le_mul_left _ hZ)
 refine ⟨exceptionalAuxiliary_nonzero J hJ j p hY hsmall,
   exceptionalAuxiliary_Y_degree_zero J hJ j p hY hsmall,
   exceptionalAuxiliary_R_degree_zero J hJ hR j hj hY,hz,?_⟩
 calc
   _ ≤ (2*j-1)*j:=hz
   _ ≤ (2*j)*j:=Nat.mul_le_mul_right j (Nat.sub_le _ _)
   _=2*j^2:=by ring
def originalImplicitFactors (J:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (activeFactors (swapYR K J)).image (swapYR K)
theorem swapYR_dvd_swapYR_iff (F J:MvPolynomial (Fin 4) K):
   swapYR K F∣swapYR K J ↔ F∣J:=by
 constructor
 · rintro ⟨T,hT⟩
   refine ⟨swapYR K T,?_⟩
   have hh:=congrArg (swapYR K) hT
   simpa only [map_mul,swapYR_twice] using hh
 · rintro ⟨T,hT⟩
   exact ⟨swapYR K T,by rw [hT,map_mul]⟩
theorem originalImplicitFactors_spec (J A:MvPolynomial (Fin 4) K)
   (hA:A∈originalImplicitFactors J):Irreducible A∧A∣J:=by
 classical
 obtain ⟨F,hF,rfl⟩:=Finset.mem_image.mp hA
 have hf:=activeFactors_spec (swapYR K J) F hF
 refine ⟨(MulEquiv.irreducible_iff (swapYR K)).mpr hf.1,?_⟩
 have hh:=(swapYR_dvd_swapYR_iff F (swapYR K J)).mpr hf.2.1
 simpa only [swapYR_twice] using hh
theorem originalImplicitFactors_product_dvd (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∏ A∈originalImplicitFactors J,A)∣J:=by
 classical
 have hi:Set.InjOn (swapYR K) (activeFactors (swapYR K J)):=(swapYR K).injective.injOn
 have heq:(∏ A∈originalImplicitFactors J,A)=
     swapYR K (∏ F∈activeFactors (swapYR K J),F):=by
   rw [originalImplicitFactors,Finset.prod_image hi,map_prod]
 rw [heq]
 have hh:=(swapYR_dvd_swapYR_iff (∏ F∈activeFactors (swapYR K J),F) (swapYR K J)).mpr
   (activeFactors_product_dvd (swapYR K J) (swapYR_ne_zero J hJ))
 simpa only [swapYR_twice] using hh
theorem originalImplicitFactors_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈originalImplicitFactors J,A.degreeOf (1:Fin 4)) ≤ J.degreeOf 1∧
     (∑ A∈originalImplicitFactors J,A.degreeOf (3:Fin 4)) ≤ J.degreeOf 3:=by
 have hh:=RCN081.sum_degreeOf_le_of_prod_dvd
   (originalImplicitFactors J) id J hJ (originalImplicitFactors_product_dvd J hJ)
 exact ⟨hh 1,hh 3⟩
section SurfaceCoverage
variable {T:Type*} [Field T]
def swapSurfacePoint (v:Fin 3 → T):Fin 3 → T:=![v 1,v 0,v 2]
@[simp] theorem swapSurfacePoint_twice (v:Fin 3 → T):
   swapSurfacePoint (swapSurfacePoint v)=v:=by
 funext i
 fin_cases i <;> simp [swapSurfacePoint]
theorem eval_surface_swap (φ:Polynomial K →+*T) (v:Fin 3 → T)
   (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval v (surfaceMap φ (swapYR K F))=
     MvPolynomial.eval (swapSurfacePoint v) (surfaceMap φ F):=by
 have hfix0:Equiv.swap (1:Fin 4) 2 (0:Fin 4)=0:=by decide
 have hfix3:Equiv.swap (1:Fin 4) 2 (3:Fin 4)=3:=by decide
 have hs1:surfaceMap φ (MvPolynomial.X (1:Fin 4))=MvPolynomial.X (0:Fin 3):=
   surfaceMap_X_succ φ 0
 have hs2:surfaceMap φ (MvPolynomial.X (2:Fin 4))=MvPolynomial.X (1:Fin 3):=
   surfaceMap_X_succ φ 1
 have hs3:surfaceMap φ (MvPolynomial.X (3:Fin 4))=MvPolynomial.X (2:Fin 3):=
   surfaceMap_X_succ φ 2
 have hh:((MvPolynomial.eval v).comp (surfaceMap φ)).comp (swapYR K).toRingHom=
     (MvPolynomial.eval (swapSurfacePoint v)).comp (surfaceMap φ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,swapYR,MvPolynomial.renameEquiv_apply]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,swapYR,MvPolynomial.renameEquiv_apply,
         hfix0,hfix3,hs1,hs2,hs3,swapSurfacePoint]
 exact RingHom.congr_fun hh F
theorem surface_zero_exceptional_or_implicit_regular
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (v:Fin 3 → T) (hzero:MvPolynomial.eval v (surfaceMap φ J)=0):
   MvPolynomial.eval v (surfaceMap φ (exceptionalAuxiliary J))=0∨
     ∃ A∈originalImplicitFactors J,Irreducible A∧A∣J∧
       A.degreeOf 2=0∧0 < A.degreeOf 1∧
       MvPolynomial.eval v (surfaceMap φ A)=0∧
       MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0:=by
 classical
 have hswap:MvPolynomial.eval (swapSurfacePoint v) (surfaceMap φ (swapYR K J))=0:=by
   rw [eval_surface_swap,swapSurfacePoint_twice]
   exact hzero
 obtain haux | ⟨F,hF,hi,hpos,hz,hreg⟩:=surface_zero_singular_or_regular
   φ hφ (swapYR K J) (swapYR_ne_zero J hJ) (swapSurfacePoint v) hswap
 · left
   rw [exceptionalAuxiliary,eval_surface_swap]
   exact haux
 · right
   have hmem:swapYR K F∈originalImplicitFactors J:=Finset.mem_image.mpr ⟨F,hF,rfl⟩
   have hs:=originalImplicitFactors_spec J (swapYR K F) hmem
   have hAR:(swapYR K F).degreeOf 2=0:=by
     have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) (swapYR K F) J hs.2 hJ
     omega
   refine ⟨swapYR K F,hmem,hs.1,hs.2,hAR,?_,?_,?_⟩
   · rw [swapYR_degree_Y]
     exact hpos
   · rw [eval_surface_swap]
     exact hz
   · rw [swapYR_pderiv_Y,eval_surface_swap]
     exact hreg
end SurfaceCoverage
theorem solution_exceptional_or_implicit_regular
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ J=0):
   specialization K P γ (exceptionalAuxiliary J)=0∨
     ∃ A∈originalImplicitFactors J,Irreducible A∧A∣J∧
       A.degreeOf 2=0∧0 < A.degreeOf 1∧specialization K P γ A=0∧
       specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A)≠0:=by
 let φ:=RCN135.polynomialEmbedding K
 let v:Fin 3 → RCN135.GenericField K:=
   fun i => RCN135.initialPoint K P γ i.succ
 have heval (F:MvPolynomial (Fin 4) K):
     MvPolynomial.eval v (surfaceMap φ F)=0 ↔ specialization K P γ F=0:=by
   simpa only [RCN138.canonical_geometricSurfaceMap] using
     (RCN138.actual_generic_initial_zero_iff K P γ F)
 obtain haux | ⟨A,hA,hi,hd,hAR,hAY,hz,hreg⟩:=
   surface_zero_exceptional_or_implicit_regular φ
     (RCN135.polynomialEmbedding_injective K) J hJ hR v ((heval J).mpr hsolution)
 · exact Or.inl ((heval _).mp haux)
 · exact Or.inr ⟨A,hA,hi,hd,hAR,hAY,(heval _).mp hz,(heval _).not.mp hreg⟩
end
end ProximityPrize.SubmissionLower.RCN079
end PackedLegacy_I9

/-! Packed from ProximityPrize.SubmissionLower.J0. -/
section PackedLegacy_J0
namespace ProximityPrize.SubmissionLower.RCN080
open RCN136 RCN079 RCN319
noncomputable section
section SeedProjection
variable {T:Type*} [Field T]
def seedProjection (T:Type*) [Field T]:MvPolynomial (Fin 3) T →+*Polynomial T:=
 MvPolynomial.eval₂Hom Polynomial.C ![0,0,Polynomial.X]
def seedEmbedding (T:Type*) [Field T]:Polynomial T →+*MvPolynomial (Fin 3) T:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2:Fin 3))
theorem seed_only_vars (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0)
   (i:Fin 3) (hi:i∈S.vars):i=2:=by
 fin_cases i
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hY)
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
 · rfl
theorem seedProjection_reconstruct (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0):
   seedEmbedding T (seedProjection T S)=S:=by
 change ((seedEmbedding T).comp (seedProjection T)) S=(RingHom.id _) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [seedEmbedding,seedProjection]
 · intro i hi _
   rw [seed_only_vars S hY hR i hi]
   simp [seedEmbedding,seedProjection]
 · rfl
theorem seedProjection_nonzero (S:MvPolynomial (Fin 3) T) (hS:S≠0)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0):seedProjection T S≠0:=by
 intro hz
 apply hS
 rw [←seedProjection_reconstruct S hY hR,hz,map_zero]
theorem monomial_fin3 (d:Fin 3 →₀ ℕ) (a:T):
   MvPolynomial.monomial d a=MvPolynomial.C a*MvPolynomial.X 0^d 0*
     MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem seedProjection_monomial (d:Fin 3 →₀ ℕ) (a:T):
   seedProjection T (MvPolynomial.monomial d a)=
     Polynomial.C a*0^d 0*0^d 1*Polynomial.X^d 2:=by
 rw [monomial_fin3]
 simp [seedProjection]
theorem seedProjection_monomial_natDegree_le (d:Fin 3 →₀ ℕ) (a:T):
   (seedProjection T (MvPolynomial.monomial d a)).natDegree ≤ d 2:=by
 rw [seedProjection_monomial]
 have hc:(Polynomial.C a).natDegree ≤ 0:=by simp
 have h0:((0:Polynomial T)^d 0).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 0)
     (show (0:Polynomial T).natDegree ≤ 0 by simp)
 have h1:((0:Polynomial T)^d 1).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 1)
     (show (0:Polynomial T).natDegree ≤ 0 by simp)
 have hx:((Polynomial.X:Polynomial T)^d 2).natDegree ≤ d 2:=by simp
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hc h0) h1) hx
 simpa using hh
theorem seedProjection_natDegree_le (S:MvPolynomial (Fin 3) T):
   (seedProjection T S).natDegree ≤ S.degreeOf 2:=by
 classical
 have hsum:seedProjection T S=
     ∑ d∈S.support,seedProjection T (MvPolynomial.monomial d (S.coeff d)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 rw [hsum]
 exact Polynomial.natDegree_sum_le_of_forall_le S.support _ (fun d hd =>
   (seedProjection_monomial_natDegree_le d (S.coeff d)).trans (MvPolynomial.monomial_le_degreeOf 2 hd))
theorem seedProjection_eval (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0) (v:Fin 3 → T):
   (seedProjection T S).eval (v 2)=MvPolynomial.eval v S:=by
 change ((Polynomial.evalRingHom (v 2)).comp (seedProjection T)) S=(MvPolynomial.eval v) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [seedProjection]
 · intro i hi _
   rw [seed_only_vars S hY hR i hi]
   simp [seedProjection]
 · rfl
end SeedProjection
section GenericSurface
variable {K T:Type*} [Field K] [Field T]
def auxiliarySeedPolynomial (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K):Polynomial T:=
 seedProjection T (surfaceMap φ H)
theorem surface_seed_only (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0):
   (surfaceMap φ H).degreeOf 0=0∧(surfaceMap φ H).degreeOf 1=0:=
 ⟨Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 0).trans_eq hY),
   Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 1).trans_eq hR)⟩
theorem auxiliarySeedPolynomial_nonzero
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0):auxiliarySeedPolynomial φ H≠0:=by
 have hs:=surface_seed_only φ H hY hR
 exact seedProjection_nonzero (surfaceMap φ H) (surfaceMap_ne_zero φ hφ H hH) hs.1 hs.2
theorem auxiliarySeedPolynomial_natDegree_le
   (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K):
   (auxiliarySeedPolynomial φ H).natDegree ≤ H.degreeOf 3:=
 (seedProjection_natDegree_le (surfaceMap φ H)).trans (surfaceMap_degreeOf_le φ H 2)
theorem auxiliarySeedPolynomial_eval
   (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (v:Fin 3 → T):
   (auxiliarySeedPolynomial φ H).eval (v 2)=MvPolynomial.eval v (surfaceMap φ H):=by
 have hs:=surface_seed_only φ H hY hR
 exact seedProjection_eval (surfaceMap φ H) hs.1 hs.2 v
theorem card_surface_seeds_le
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ v:Fin 3 → T,
     v 2=φ (Polynomial.C γ)∧MvPolynomial.eval v (surfaceMap φ H)=0):
   seeds.card ≤ H.degreeOf 3:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq T:=Classical.decEq T
 let q:Polynomial T:=auxiliarySeedPolynomial φ H
 let c:K →+*T:=φ.comp Polynomial.C
 have hq:q≠0:=auxiliarySeedPolynomial_nonzero φ hφ H hH hY hR
 have hroots:∀ z∈seeds.image c,z∈q.roots:=by
   intro z hz
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
   obtain ⟨v,hv,hzero⟩:=hsolutions γ hγ
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (φ (Polynomial.C γ))=0
   rw [←hv]
   exact (auxiliarySeedPolynomial_eval φ H hY hR v).trans hzero
 calc
   seeds.card=(seeds.image c).card:=(Finset.card_image_of_injOn c.injective.injOn).symm
   _ ≤ q.natDegree:=Polynomial.card_le_degree_of_subset_roots hroots
   _ ≤ H.degreeOf 3:=auxiliarySeedPolynomial_natDegree_le φ H
end GenericSurface
section ActualSolutions
variable {K:Type*} [Field K]
theorem card_actual_solution_seeds_le
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ P:Polynomial K,specialization K P γ H=0):
   seeds.card ≤ H.degreeOf 3:=by
 apply card_surface_seeds_le (RCN135.polynomialEmbedding K)
   (RCN135.polynomialEmbedding_injective K) H hH hY hR seeds
 intro γ hγ
 obtain ⟨P,hP⟩:=hsolutions γ hγ
 refine ⟨fun i => RCN135.initialPoint K P γ i.succ,?_,?_⟩
 · rfl
 · have hh:=(RCN138.actual_generic_initial_zero_iff K P γ H).mpr hP
   simpa only [RCN138.canonical_geometricSurfaceMap] using hh
theorem exceptional_solution_seed_card_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ P:Polynomial K,
     specialization K P γ (exceptionalAuxiliary J)=0):seeds.card ≤ 2*j^2:=by
 have hd:=exceptionalAuxiliary_data J hJ hR j p hj hsmall hY hZ
 exact (card_actual_solution_seeds_le (exceptionalAuxiliary J) hd.1 hd.2.1 hd.2.2.1
   seeds hsolutions).trans hd.2.2.2.2
end ActualSolutions
end
end ProximityPrize.SubmissionLower.RCN080
end PackedLegacy_J0

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier09 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.BU. -/
section PackedLegacy_BU
namespace ProximityPrize.SubmissionLower.RCN169
open RCN079 RCN167 RCN081 RCN267 RCN174
noncomputable section
variable {K:Type*} [Field K]
def implicitBaseFactors (J:MvPolynomial (Fin 4) K):
   Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (originalImplicitFactors J).filter
   (fun A => MvPolynomial.pderiv (1:Fin 4) A≠0)
theorem implicitBaseFactors_subset (J:MvPolynomial (Fin 4) K):
   implicitBaseFactors J ⊆ originalImplicitFactors J:=by
 classical
 exact Finset.filter_subset _ _
theorem implicitBaseFactors_spec (J A:MvPolynomial (Fin 4) K)
   (hJ:J≠0) (hR:J.degreeOf 2=0) (hA:A∈implicitBaseFactors J):
   Irreducible A∧A∣J∧A.degreeOf 2=0∧
     MvPolynomial.pderiv (1:Fin 4) A≠0:=by
 classical
 obtain ⟨hm,hy⟩:=Finset.mem_filter.mp hA
 have hs:=originalImplicitFactors_spec J A hm
 have hr:=RCN081.degreeOf_le_of_dvd (2:Fin 4) A J hs.2 hJ
 exact ⟨hs.1,hs.2,by omega,hy⟩
theorem implicitBaseFactors_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)) ≤ J.degreeOf 1∧
     (∑ A∈implicitBaseFactors J,A.degreeOf (3:Fin 4)) ≤ J.degreeOf 3:=by
 classical
 have hb:=originalImplicitFactors_degree_budgets J hJ
 exact ⟨(Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.1,
   (Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.2⟩
def implicitPairSet (J:MvPolynomial (Fin 4) K):
   Finset ((A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):=
 (implicitBaseFactors J).sigma (fun A => positiveRFactors (implicitLift A))
theorem mem_implicitPairSet (J A G:MvPolynomial (Fin 4) K):
   (⟨A,G⟩:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)∈
       implicitPairSet J ↔
     A∈implicitBaseFactors J∧G∈positiveRFactors (implicitLift A):=by
 classical
 exact Finset.mem_sigma
theorem implicitPair_spec (J A G:MvPolynomial (Fin 4) K)
   (hJ:J≠0) (hR:J.degreeOf 2=0)
   (hpair:(⟨A,G⟩:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)∈
     implicitPairSet J):
   Irreducible A∧A∣J∧A.degreeOf 2=0∧
     MvPolynomial.pderiv (1:Fin 4) A≠0∧
     Irreducible G∧G∣implicitLift A∧G.degreeOf 2=1∧¬ G∣A:=by
 obtain ⟨hA,hG⟩:=(mem_implicitPairSet J A G).mp hpair
 obtain ⟨hiA,hdA,hrA,hyA⟩:=implicitBaseFactors_spec J A hJ hR hA
 obtain ⟨hiG,hdG,hrG⟩:=positiveRFactors_spec (implicitLift A) G hG
 have hF:=implicitLift_nonzero A hrA hyA
 have hgcap:=(RCN081.degreeOf_le_of_dvd (2:Fin 4)
   G (implicitLift A) hdG hF).trans (implicitLift_R_degree_le A hrA)
 refine ⟨hiA,hdA,hrA,hyA,hiG,hdG,by omega,?_⟩
 intro hd
 have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) G A hd hiA.ne_zero
 omega
theorem sum_products_le_product_sums {ι:Type*} (I:Finset ι) (f g:ι → ℕ):
   (∑ i∈I,f i*g i) ≤ (∑ i∈I,f i)*(∑ i∈I,g i):=by
 calc
   _ ≤ ∑ i∈I,f i*(∑ j∈I,g j):=by
     apply Finset.sum_le_sum
     intro i hi
     exact Nat.mul_le_mul_left (f i) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
   _=_:=(Finset.sum_mul I f (∑ j∈I,g j)).symm
theorem implicitBaseFactors_product_degree_budget
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)) ≤
     J.degreeOf 1*J.degreeOf 3:=by
 have hb:=implicitBaseFactors_degree_budgets J hJ
 exact (sum_products_le_product_sums (implicitBaseFactors J)
   (fun A => A.degreeOf 1) (fun A => A.degreeOf 3)).trans (Nat.mul_le_mul hb.1 hb.2)
def pairYCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 2*q.1.degreeOf 3
def pairRCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 1*q.1.degreeOf 3+q.2.degreeOf 3*q.1.degreeOf 1
def pairZCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 2*q.1.degreeOf 1
theorem implicitPair_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0):
   (∑ q∈implicitPairSet J,pairYCost q) ≤ J.degreeOf 3∧
     (∑ q∈implicitPairSet J,pairRCost q) ≤ 2*J.degreeOf 1*J.degreeOf 3∧
     (∑ q∈implicitPairSet J,pairZCost q) ≤ J.degreeOf 1:=by
 classical
 have hlocal (A:MvPolynomial (Fin 4) K) (hA:A∈implicitBaseFactors J):
     (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4)) ≤ 1∧
       (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (1:Fin 4)) ≤ A.degreeOf 1∧
       (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (3:Fin 4)) ≤ A.degreeOf 3:=by
   obtain ⟨_,_,hr,hy⟩:=implicitBaseFactors_spec J A hJ hR hA
   exact lift_positive_factor_budgets A hr hy
 have hb:=implicitBaseFactors_degree_budgets J hJ
 have hy:(∑ q∈implicitPairSet J,pairYCost q) ≤
     ∑ A∈implicitBaseFactors J,A.degreeOf (3:Fin 4):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),G.degreeOf 2*A.degreeOf 3) ≤ _
   rw [←Finset.sum_mul]
   simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 3) (hlocal A hA).1
 have hz:(∑ q∈implicitPairSet J,pairZCost q) ≤
     ∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),G.degreeOf 2*A.degreeOf 1) ≤ _
   rw [←Finset.sum_mul]
   simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 1) (hlocal A hA).1
 have hr:(∑ q∈implicitPairSet J,pairRCost q) ≤
     ∑ A∈implicitBaseFactors J,2*(A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),
     (G.degreeOf 1*A.degreeOf 3+G.degreeOf 3*A.degreeOf 1)) ≤ _
   rw [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.sum_mul]
   calc
     _ ≤ A.degreeOf 1*A.degreeOf 3+A.degreeOf 3*A.degreeOf 1:=
       Nat.add_le_add (Nat.mul_le_mul_right _ (hlocal A hA).2.1)
         (Nat.mul_le_mul_right _ (hlocal A hA).2.2)
     _=_:=by ring
 refine ⟨hy.trans hb.2,?_,hz.trans hb.1⟩
 calc
   _ ≤ ∑ A∈implicitBaseFactors J,2*(A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=hr
   _=2*(∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=
     (Finset.mul_sum _ _ _).symm
   _ ≤ 2*(J.degreeOf 1*J.degreeOf 3):=
     Nat.mul_le_mul_left 2 (implicitBaseFactors_product_degree_budget J hJ)
   _=_:=by ring
theorem implicitPair_input_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (D w j:ℕ) (hw:0 < w) (hbox:J∈globalCoefficientBox K D w j 0):
   (∑ q∈implicitPairSet J,pairYCost q) ≤ j∧
     (∑ q∈implicitPairSet J,pairRCost q) ≤ 2*((D-1)/w)*j∧
     (∑ q∈implicitPairSet J,pairZCost q) ≤ (D-1)/w:=by
 have hR:J.degreeOf 2=0:=by
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hcaps:=degree_bounds_of_mem_box J D w j 0 hw hbox
 have hy:J.degreeOf 1 ≤ (D-1)/w:=hcaps.1
 have hz:J.degreeOf 3 ≤ j:=hcaps.2.2
 have hb:=implicitPair_degree_budgets J hJ hR
 exact ⟨hb.1.trans hz,
   hb.2.1.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hy) hz),hb.2.2.trans hy⟩
end
end ProximityPrize.SubmissionLower.RCN169
end PackedLegacy_BU

/-! Packed from ProximityPrize.SubmissionLower.V. -/
section PackedLegacy_V
namespace ProximityPrize.SubmissionLower.RCN286
open RCN169 RCN167 RCN079 RCN080 RCN290 RCN293 RCN135 RCN136 RCN138 RCN082 RCN081 RCN174 RCN319
noncomputable section
variable {K:Type*} [Field K]
def RegularSolution (F:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ F=0∧
   specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0
def LiftedSolutionPair
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ q.1=0∧
   specialization K P γ (MvPolynomial.pderiv (1:Fin 4) q.1)≠0∧
   RegularSolution q.2 P γ
theorem solution_regular_or_auxiliary
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ Q=0):
   specialization K P γ (singularAuxiliary Q)=0∨
     ∃ F∈positiveRFactors Q,RegularSolution F P γ:=by
 classical
 let φ:=polynomialEmbedding K
 let v:Fin 3 → GenericField K:=fun i => initialPoint K P γ i.succ
 have heval (F:MvPolynomial (Fin 4) K):
     MvPolynomial.eval v (surfaceMap φ F)=0 ↔ specialization K P γ F=0:=by
   simpa only [canonical_geometricSurfaceMap] using (actual_generic_initial_zero_iff K P γ F)
 obtain haux | ⟨F,hF,_hi,hpos,hz,hregular⟩:=
   surface_zero_singular_or_regular φ (polynomialEmbedding_injective K)
     Q hQ v ((heval Q).mpr hsolution)
 · exact Or.inl ((heval _).mp haux)
 · exact Or.inr ⟨F,Finset.mem_filter.mpr ⟨hF,hpos⟩,
     (heval F).mp hz,(heval _).not.mp hregular⟩
theorem directFactor_data
   (Q F:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s)
   (hF:F∈positiveRFactors Q):
   Irreducible F∧0 < F.degreeOf 2∧F∈globalCoefficientBox K D w L s:=by
 obtain ⟨hi,hd,hr⟩:=positiveRFactors_spec Q F hF
 exact ⟨hi,hr,mem_globalCoefficientBox_of_dvd F Q D w L s hQ hd hbox⟩
theorem directFactor_input_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hw:0 < w) (hbox:Q∈globalCoefficientBox K D w L s):
   (∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
     (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
     (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L:=
 separated_factor_caps_of_prod_dvd (positiveRFactors Q) id Q D w L s hw hQ hbox
   (positiveRFactors_product_dvd Q hQ)
theorem implicitPair_data
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (D w j:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:J∈globalCoefficientBox K D w j 0)
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (hq:q∈implicitPairSet J):
   Irreducible q.1∧Irreducible q.2∧q.2.degreeOf 2=1∧
     q.1∈globalCoefficientBox K D w j 0∧
     q.2∈globalCoefficientBox K D w j 1∧¬ q.2∣q.1:=by
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain ⟨hiA,hdA,hrA,hyA,hiG,hdG,hrG,hproper⟩:=
   implicitPair_spec J q.1 q.2 hJ hR hq
 have hAbox:=mem_globalCoefficientBox_of_dvd q.1 J D w j 0 hJ hdA hbox
 have hGbox:=mem_globalCoefficientBox_of_dvd q.2 (implicitLift q.1) D w j 1
   (implicitLift_nonzero q.1 hrA hyA) hdG
   (implicitLift_mem_box q.1 D w j hw hDw hAbox)
 exact ⟨hiA,hiG,hrG,hAbox,hGbox,hproper⟩
theorem solution_implicit_pair_or_exceptional
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (P:Polynomial K) (γ:K) (D w j:ℕ)
   (hw:1 ≤ w) (hDw:w < D) (hbox:J∈globalCoefficientBox K D w j 0)
   (hsolution:specialization K P γ J=0):
   specialization K P γ (exceptionalAuxiliary J)=0∨
     ∃ q∈implicitPairSet J,LiftedSolutionPair q P γ:=by
 classical
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain haux | ⟨A,hA,hi,hd,_hAR,_hAY,hsolA,hregA⟩:=
   solution_exceptional_or_implicit_regular J hJ hR P γ hsolution
 · exact Or.inl haux
 · have hy:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
     intro hz
     exact hregA (by rw [hz,map_zero])
   have hAmem:A∈implicitBaseFactors J:=Finset.mem_filter.mpr ⟨hA,hy⟩
   have hAbox:=mem_globalCoefficientBox_of_dvd A J D w j 0 hJ hd hbox
   obtain ⟨G,hG,_hiG,_hrG,_hGbox,hsolG,hregG,_hproper⟩:=
     exists_regular_lift_factor_of_solution A hi.ne_zero P γ D w j hw hDw hAbox hsolA hregA
   exact Or.inr ⟨⟨A,G⟩,(mem_implicitPairSet J A G).mpr ⟨hAmem,hG⟩,
     hsolA,hregA,hsolG,hregG⟩
def exceptionalSeeds (J:MvPolynomial (Fin 4) K) (seeds:Finset K)
   (selected:K → Polynomial K):Finset K:=by
 classical
 exact seeds.filter (fun γ => specialization K (selected γ) γ (exceptionalAuxiliary J)=0)
theorem exceptionalSeeds_card_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j)
   (seeds:Finset K) (selected:K → Polynomial K):
   (exceptionalSeeds J seeds selected).card ≤ 2*j^2:=by
 classical
 apply exceptional_solution_seed_card_le J hJ hR j p hj hsmall hY hZ
 intro γ hγ
 exact ⟨selected γ,(Finset.mem_filter.mp hγ).2⟩
theorem solution_three_way
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ Q=0):
   (∃ F∈positiveRFactors Q,RegularSolution F P γ)∨
     (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q P γ)∨
     specialization K P γ (exceptionalAuxiliary (singularAuxiliary Q))=0:=by
 obtain haux | hregular:=solution_regular_or_auxiliary Q hQ P γ hsolution
 · have hJ:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
   obtain hexceptional | himplicit:=solution_implicit_pair_or_exceptional
     (singularAuxiliary Q) hJ.1 P γ ((2*s-1)*D) w ((2*s-1)*L)
     hw hDw hJ.2 haux
   · exact Or.inr (Or.inr hexceptional)
   · exact Or.inr (Or.inl himplicit)
 · exact Or.inl hregular
theorem selected_seed_decomposition
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hj:1 ≤ (2*s-1)*L) (hjSmall:(2*s-1)*L < p)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (seeds:Finset K) (selected:K → Polynomial K)
   (hsolutions:∀ γ∈seeds,specialization K (selected γ) γ Q=0):
   (exceptionalSeeds (singularAuxiliary Q) seeds selected).card ≤
       2*((2*s-1)*L)^2∧
     (∀ γ∈seeds,γ∉exceptionalSeeds (singularAuxiliary Q) seeds selected →
       (∃ F∈positiveRFactors Q,RegularSolution F (selected γ) γ)∨
         (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q (selected γ) γ))∧
     ((∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
       (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
       (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L)∧
     ((∑ q∈implicitPairSet (singularAuxiliary Q),pairYCost q) ≤ (2*s-1)*L∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairRCost q) ≤
         2*(((2*s-1)*D-1)/w)*((2*s-1)*L)∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairZCost q) ≤
         ((2*s-1)*D-1)/w):=by
 classical
 have hwpos:0 < w:=by omega
 obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=Nat.eq_zero_of_le_zero
   (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
 have hJY:(singularAuxiliary Q).degreeOf 1 ≤ (2*s-1)*L:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hh:=(hJbox hd).1
   omega
 have hJZ:=degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
 refine ⟨exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR ((2*s-1)*L)
     p hj hjSmall hJY hJZ seeds selected,?_,
   directFactor_input_budgets Q hQ D w L s hwpos hbox,
   implicitPair_input_budgets (singularAuxiliary Q) hJ ((2*s-1)*D) w
     ((2*s-1)*L) hwpos hJbox⟩
 intro γ hγ hnot
 obtain hregular | himplicit | hexceptional:=solution_three_way
   Q hQ D w L s p hs hsmall hw hDw hbox (selected γ) γ (hsolutions γ hγ)
 · exact Or.inl hregular
 · exact Or.inr himplicit
 · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hγ,hexceptional⟩))
end
end ProximityPrize.SubmissionLower.RCN286
end PackedLegacy_V

/-! Packed from ProximityPrize.SubmissionLower.FS. -/
section PackedLegacy_FS
namespace ProximityPrize.SubmissionLower.RCN242
open RCN051
end ProximityPrize.SubmissionLower.RCN242
end PackedLegacy_FS

/-! Packed from ProximityPrize.SubmissionLower.BT. -/
section PackedLegacy_BT
namespace ProximityPrize.SubmissionLower.RCN168
open RCN051
end ProximityPrize.SubmissionLower.RCN168
end PackedLegacy_BT

/-! Packed from ProximityPrize.SubmissionLower.P4. -/
section PackedLegacy_P4
namespace ProximityPrize.SubmissionLower.RCN289
open RCN174 RCN081 RCN313
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K]
end
end ProximityPrize.SubmissionLower.RCN289
end PackedLegacy_P4

/-! Packed from ProximityPrize.SubmissionLower.Y4. -/
section PackedLegacy_Y4
namespace ProximityPrize.SubmissionLower.RCN068
open scoped Classical
open RCN051 RCN313 RCN136 RCN174 RCN231 RCN238 RCN289
noncomputable section
def capAt (v:DegreeVector):Fin 3 → ℕ:=![v.y,v.r,v.z]
def agreementCaps (ell s L w:ℕ):DegreeVector:=
 ⟨1+2*w*ell,w*(2*s-1),2*w*L+1⟩
variable {K Ω:Type} [Field K] [Field Ω]
local instance _root_.ProximityPrize.SubmissionLower.RCN068.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN068.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
def HasCaps (Q:MvPolynomial (Fin 3) Ω) (v:DegreeVector):Prop:=
 ∀ i,Q.degreeOf i ≤ capAt v i
variable (φ:Polynomial K →+*Ω)
def firstTailSurface (F:MvPolynomial (Fin 4) K) (w:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (numerator K F (w+1))
theorem surface_agreement_caps
   (F:MvPolynomial (Fin 4) K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf 1 ≤ ell) (hR:F.degreeOf 2 ≤ s) (hZ:F.degreeOf 3 ≤ L)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   HasCaps (surfaceMap φ (agreementNumerator F w c x u₀ u₁))
     (agreementCaps ell s L w):=by
 obtain ⟨hy,hr,hz⟩:=agreementNumerator_degree_bounds F ell s L hs hY hR hZ w c x u₀ u₁
 intro i
 fin_cases i
 · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
 · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
 · exact (surfaceMap_degreeOf_le φ _ 2).trans hz
theorem selected_firstTail_zero
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ) (firstTailSurface φ F w)=0:=by
 change MvPolynomial.eval (selectedPoint φ selected γ)
   (surfaceMap φ (numerator K F (w+1)))=0
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
 exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F (selected γ) γ
   (φ Polynomial.X) hsolution (w+1) (Nat.lt_succ_of_le hdegree)
section MixedGates
variable (G T:MvPolynomial (Fin 3) Ω) (g t:DegreeVector)
theorem actual_pair_degree_le (hG:HasCaps G g) (hT:HasCaps T t) (j k:Fin 3):
   T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k ≤
     capAt t j*capAt g k+capAt g j*capAt t k:=
 Nat.add_le_add (Nat.mul_le_mul (hT j) (hG k)) (Nat.mul_le_mul (hG j) (hT k))
theorem pair_caps_below_of_mixed (p:ℕ)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   ∀ j k:Fin 3,j≠k →
     capAt t j*capAt g k+capAt g j*capAt t k < p:=by
 intro j k hne
 fin_cases j <;> fin_cases k
 all_goals try exact (hne rfl).elim
 all_goals first
   | simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
   | simpa [capAt,mixed,unitR,Nat.mul_comm,Nat.add_comm] using hR
   | simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem actual_characteristic_gates (p:ℕ)
   (hG:HasCaps G g) (hT:HasCaps T t)
   (hg:∀ j,capAt g j < p)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   (∀ j,G.degreeOf j < p)∧
     ∀ j k:Fin 3,j≠k →
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p:=by
 refine ⟨fun j↦(hG j).trans_lt (hg j),?_⟩
 intro j k hjk
 exact (actual_pair_degree_le G T g t hG hT j k).trans_lt
   (pair_caps_below_of_mixed g t p hY hR hZ j k hjk)
end MixedGates
end
end ProximityPrize.SubmissionLower.RCN068
end PackedLegacy_Y4

/-! Packed from ProximityPrize.SubmissionLower.B2. -/
section PackedLegacy_B2
namespace ProximityPrize.SubmissionLower.RCN070
open RCN051 RCN168
open scoped BigOperators
end ProximityPrize.SubmissionLower.RCN070
end PackedLegacy_B2

/-! Packed from ProximityPrize.SubmissionLower.BV. -/
section PackedLegacy_BV
namespace ProximityPrize.SubmissionLower.RCN170
open scoped Classical BigOperators
open RCN051 RCN168 RCN068 RCN070 RCN169 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance _root_.ProximityPrize.SubmissionLower.RCN170.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN170.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
def pairCost (A G:MvPolynomial (Fin 4) K):DegreeVector:=
 ⟨pairYCost ⟨A,G⟩,pairRCost ⟨A,G⟩,pairZCost ⟨A,G⟩⟩
def geometricPairCost (A:MvPolynomial (Fin 4) K)
   (g:MvPolynomial (Fin 3) Ω):DegreeVector:=
 ⟨g.degreeOf 1*A.degreeOf 3,
   g.degreeOf 0*A.degreeOf 3+g.degreeOf 2*A.degreeOf 1,
   g.degreeOf 1*A.degreeOf 1⟩
theorem coordinateMixedDegree_le_geometricPairCost
   (φ:Polynomial K →+*Ω) (A:MvPolynomial (Fin 4) K)
   (hAR:A.degreeOf 2=0) (g:MvPolynomial (Fin 3) Ω) (i:Fin 3):
   coordinateMixedDegree Ω g (surfaceMap φ A) i ≤ capAt (geometricPairCost A g) i:=by
 have hTY:(surfaceMap φ A).degreeOf (0:Fin 3) ≤ A.degreeOf (1:Fin 4):=
   surfaceMap_degreeOf_le φ A (0:Fin 3)
 have hTRle:(surfaceMap φ A).degreeOf (1:Fin 3) ≤ A.degreeOf (2:Fin 4):=
   surfaceMap_degreeOf_le φ A (1:Fin 3)
 rw [hAR] at hTRle
 have hTR:(surfaceMap φ A).degreeOf (1:Fin 3)=0:=
   Nat.eq_zero_of_le_zero hTRle
 have hTZ:(surfaceMap φ A).degreeOf (2:Fin 3) ≤ A.degreeOf (3:Fin 4):=
   surfaceMap_degreeOf_le φ A (2:Fin 3)
 fin_cases i
 · simpa [coordinateMixedDegree_zero,hTR,capAt,geometricPairCost] using
     Nat.mul_le_mul_left (g.degreeOf 1) hTZ
 · have h:=Nat.add_le_add
     (Nat.mul_le_mul_right (g.degreeOf 2) hTY)
     (Nat.mul_le_mul_left (g.degreeOf 0) hTZ)
   simpa [coordinateMixedDegree_one,capAt,geometricPairCost,
     Nat.mul_comm,Nat.add_comm] using h
 · simpa [coordinateMixedDegree_two,hTR,capAt,geometricPairCost,Nat.mul_comm] using
     Nat.mul_le_mul_right (g.degreeOf 1) hTY
theorem sum_geometricPairCost_le
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (A G:MvPolynomial (Fin 4) K) (hG:G≠0) (i:Fin 3):
   (∑ g∈surfaceFactors φ G,capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i:=by
 have hY:=surfaceFactors_degree_budget φ hφ G hG (0:Fin 3)
 have hR:=surfaceFactors_degree_budget φ hφ G hG (1:Fin 3)
 have hZ:=surfaceFactors_degree_budget φ hφ G hG (2:Fin 3)
 fin_cases i
 · simpa [capAt,geometricPairCost,pairCost,pairYCost, ←Finset.sum_mul] using
     Nat.mul_le_mul_right (A.degreeOf 3) hR
 · simpa [capAt,geometricPairCost,pairCost,pairRCost,
     Finset.sum_add_distrib, ←Finset.sum_mul] using
     Nat.add_le_add (Nat.mul_le_mul_right (A.degreeOf 3) hY)
       (Nat.mul_le_mul_right (A.degreeOf 1) hZ)
 · simpa [capAt,geometricPairCost,pairCost,pairZCost, ←Finset.sum_mul] using
     Nat.mul_le_mul_right (A.degreeOf 1) hR
theorem canonical_selectedPoint_surface_evaluation
   (selected:K → Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
     (surfaceMap (polynomialEmbedding K) F)=
       polynomialEmbedding K (specialization K (selected γ) γ F):=by
 rw [selectedPoint_evaluation]
 exact evaluation_at_initialPoint K (selected γ) γ F
theorem geometric_factor_proper_cut
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hg:g∈surfaceFactors (polynomialEmbedding K) G):
   ¬ g∣surfaceMap (polynomialEmbedding K) A:=by
 obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec (polynomialEmbedding K) G g hg
 have hpos:0 < G.degreeOf 1+G.degreeOf 2+G.degreeOf 3:=by omega
 have hgeo:g∣geometricSurfaceMap K (GenericField K) G:=by
   simpa only [canonical_geometricSurfaceMap] using hdiv
 intro h
 apply hproper
 apply (geometric_factor_dvd_iff K (GenericField K) G A hG hpos g hgi hgeo).mp
 simpa only [canonical_geometricSurfaceMap] using h
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN170.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN170
end PackedLegacy_BV

/-! Packed from ProximityPrize.SubmissionLower.BW. -/
section PackedLegacy_BW
namespace ProximityPrize.SubmissionLower.RCN172
open scoped Classical BigOperators
open RCN169 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001 RCN068
noncomputable section
variable {K:Type} [Field K]
 {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN172.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN172.instDecidableEq_proximityPrize_1 :DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (implicitD w jY jZ p n a e:ℕ)
   (hAbox:A∈globalCoefficientBox K implicitD w jZ 0)
   (hGbox:G∈globalCoefficientBox K implicitD w jZ 1)
   (hjY:(implicitD-1)/w=jY)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K p]
   (hw:1 ≤ w) (hchar:w < p) (hwa:w < a) (han:a ≤ n)
   (hjYsmall:jY < p) (hjZsmall:jZ < p)
   (hmixedSmall:2*jY*jZ < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i =>
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e):
   Γ.card*(a-w) ≤
     (n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 let surfaceCap:RCN051.DegreeVector:=⟨jY,1,jZ⟩
 let cutCap:RCN051.DegreeVector:=⟨jY,0,jZ⟩
 let agreementCap:RCN051.DegreeVector:=
   ⟨1+2*w*jY,w,2*w*jZ+1⟩
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitD w jZ 0 hw hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitD w jZ 1 hw hGbox
 have hAY:A.degreeOf 1 ≤ jY:=hAGcaps.1.trans_eq hjY
 have hGY:G.degreeOf 1 ≤ jY:=hGGcaps.1.trans_eq hjY
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) cutCap:=by
   intro i
   fin_cases i
   · exact (surfaceMap_degreeOf_le φ A 0).trans hAY
   · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ
     (polynomialEmbedding_injective K) G hG.ne_zero
     (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*(a-w) ≤
       (n-w)*(∑ i:Fin 3,
         capAt agreementCap i*
           capAt (RCN170.geometricPairCost A g) i)+
         (e+1)*(a-w)*
           capAt (RCN170.geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g surfaceCap:=by
     intro i
     fin_cases i
     · exact (hfacdegree 0).trans hGY
     · exact (hfacdegree 1).trans hGGcaps.2.1
     · exact (hfacdegree 2).trans hGGcaps.2.2
   have hsurfaceSmall:∀ j,capAt surfaceCap j < p:=by
     intro j
     fin_cases j
     · simpa [surfaceCap,capAt] using hjYsmall
     · simpa [surfaceCap,capAt] using lt_of_le_of_lt hw hchar
     · simpa [surfaceCap,capAt] using hjZsmall
   have hgates:=actual_characteristic_gates g (surfaceMap φ A)
     surfaceCap cutCap p hgcaps hAcaps hsurfaceSmall
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitY] using hjZsmall)
     (by
       simp [RCN051.mixed,surfaceCap,cutCap,
         RCN051.unitR]
       rw [show jY*jZ+jZ*jY=2*jY*jZ by ring]
       exact hmixedSmall)
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitZ] using hjYsmall)
   have hreg:∀ γ∈seedsFor g,
       MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
         (RCN231.polynomialPoint (φ.comp Polynomial.C)
           (selected γ) γ (φ Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr
       (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps
       (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)) agreementCap:=by
     have h:=surface_agreement_caps φ G jY 1 jZ (by decide)
       hGY hGGcaps.2.1 hGGcaps.2.2 w
       (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i)
     simpa [agreementPolynomial,agreementCaps,agreementCap] using h
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (RCN170.geometric_factor_proper_cut
       A G hG hGR hproper g hg)
     selected (seedsFor g) nodes x u₀ u₁ hinj p w a e hw hchar hwa
     (by simpa [hnodes] using han) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w e (hsub g) hnoPencil)
     (capAt agreementCap) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=
     RCN170.coordinateMixedDegree_le_geometricPairCost
       φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hδ i))))
     (Nat.mul_le_mul_left ((e+1)*(a-w)) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,
       capAt (RCN170.geometricPairCost A g) i) ≤
         capAt (RCN170.pairCost A G) i:=
   RCN170.sum_geometricPairCost_le φ
     (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt agreementCap i*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*(a-w) ≤ (∑ g∈factors,(seedsFor g).card)*(a-w):=
     Nat.mul_le_mul_right (a-w) hcard
   _=∑ g∈factors,(seedsFor g).card*(a-w):=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)+
       (e+1)*(a-w)*
         capAt (RCN170.geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt agreementCap i*
       (∑ g∈factors,
         capAt (RCN170.geometricPairCost A g) i))+
       (e+1)*(a-w)*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*(∑ i:Fin 3,capAt agreementCap i*
       capAt (RCN170.pairCost A G) i)+
       (e+1)*(a-w)*
         capAt (RCN170.pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hbudget i))))
       (Nat.mul_le_mul_left ((e+1)*(a-w)) (hbudget 2))
   _=(n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
     simp [Fin.sum_univ_three,capAt,agreementCap,
       RCN170.pairCost]
end
end ProximityPrize.SubmissionLower.RCN172
end PackedLegacy_BW

/-! Packed from ProximityPrize.SubmissionLower.CD. -/
section PackedLegacy_CD
namespace ProximityPrize.SubmissionLower.RCN306
open scoped Classical BigOperators
open RCN051 RCN068 RCN136 RCN238 RCN243 RCN065 RCN231 RCN319 RCN001
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance _root_.ProximityPrize.SubmissionLower.RCN306.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN306.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
variable [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
 {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN306.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN306
end PackedLegacy_CD

/-! Packed from ProximityPrize.SubmissionLower.DB. -/
section PackedLegacy_DB
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate Matrix
open scoped BigOperators
variable {F:Type} [Field F]
public theorem natDegree_det_le_of_perm_products_le
   {ι:Type} [Fintype ι] [DecidableEq ι]
   (M:Matrix ι ι F[X]) {N:ℕ}
   (h:∀ σ:Equiv.Perm ι,(∏ i:ι,M (σ i) i).natDegree ≤ N):
   M.det.natDegree ≤ N:=by
 classical
 rw [Matrix.det_apply']
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro σ _
 exact (Polynomial.natDegree_C_mul_le
   ((Equiv.Perm.sign σ:ℤ):F) (∏ i:ι,M (σ i) i)).trans (h σ)
namespace CornerStaircase
end CornerStaircase
theorem bivariate_resultant_natDegree_le_totalDegree
   (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree ≤
     m*totalDegree B+n*totalDegree H-m*n:=by
 classical
 let M:Matrix (Fin (n+m)) (Fin (n+m)) F[X]:=
   Polynomial.sylvester B H n m
 rw [Polynomial.resultant]
 change M.det.natDegree ≤ _
 apply natDegree_det_le_of_perm_products_le (M:=M)
 intro σ
 by_cases hzero:∃ i:Fin (n+m),M (σ i) i=0
 · rcases hzero with ⟨i,hi⟩
   have hprod:(∏ i:Fin (n+m),M (σ i) i)=0:=
     Finset.prod_eq_zero (Finset.mem_univ i) hi
   simp [hprod]
 · have hne (i:Fin (n+m)):M (σ i) i≠0:=by
     intro hi
     exact hzero ⟨i,hi⟩
   let lidx:Fin n → ℕ:=fun j =>
     ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)
   let ridx:Fin m → ℕ:=fun j =>
     ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)
   let ldeg:Fin n → ℕ:=fun j =>
     (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree
   let rdeg:Fin m → ℕ:=fun j =>
     (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree
   have hleft_Icc (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+m)
         then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.castAdd m j) (by simp [hentry,hc])
   have hright_Icc (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+n)
         then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.natAdd n j) (by simp [hentry,hc])
   have hleft (j:Fin n):lidx j+ldeg j ≤ totalDegree H:=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
           if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+m)
           then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hleft_Icc j)]
     have hcoeff:H.coeff (lidx j)≠0:=by
       have hh:=hne (Fin.castAdd m j)
       rw [hentry] at hh
       simpa only [lidx] using hh
     have hsupp:lidx j∈H.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:ldeg j=(H.coeff (lidx j)).natDegree:=by
       dsimp [ldeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le H hsupp
   have hright (j:Fin m):ridx j+rdeg j ≤ totalDegree B:=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
           if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+n)
           then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hright_Icc j)]
     have hcoeff:B.coeff (ridx j)≠0:=by
       have hh:=hne (Fin.natAdd n j)
       rw [hentry] at hh
       simpa only [ridx] using hh
     have hsupp:ridx j∈B.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:rdeg j=(B.coeff (ridx j)).natDegree:=by
       dsimp [rdeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le B hsupp
   have hleft_sum:
       (∑ j:Fin n,(lidx j+ldeg j)) ≤ n*totalDegree H:=by
     calc
       _ ≤ ∑ _j:Fin n,totalDegree H:=
         Finset.sum_le_sum (fun j _ => hleft j)
       _=n*totalDegree H:=by simp
   have hright_sum:
       (∑ j:Fin m,(ridx j+rdeg j)) ≤ m*totalDegree B:=by
     calc
       _ ≤ ∑ _j:Fin m,totalDegree B:=
         Finset.sum_le_sum (fun j _ => hright j)
       _=m*totalDegree B:=by simp
   have hidxsum:
       (∑ j:Fin n,lidx j)+(∑ j:Fin m,ridx j)=m*n:=by
     have hleft_row (j:Fin n):
         ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)=(j:ℕ)+lidx j:=by
       dsimp [lidx]
       have hle:=(Set.mem_Icc.mp (hleft_Icc j)).1
       omega
     have hright_row (j:Fin m):
         ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)=(j:ℕ)+ridx j:=by
       dsimp [ridx]
       have hle:=(Set.mem_Icc.mp (hright_Icc j)).1
       omega
     have hsum_left_rows:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin n,lidx j):=by
       calc
         _=∑ j:Fin n,((j:ℕ)+lidx j):=
           Finset.sum_congr rfl (fun j _ => hleft_row j)
         _=_:=Finset.sum_add_distrib
     have hsum_right_rows:
         (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin m,(j:ℕ))+(∑ j:Fin m,ridx j):=by
       calc
         _=∑ j:Fin m,((j:ℕ)+ridx j):=
           Finset.sum_congr rfl (fun j _ => hright_row j)
         _=_:=Finset.sum_add_distrib
     have hperm_sum:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           ∑ i:Fin (n+m),(i:ℕ):=by
       simpa using (Equiv.sum_comp σ (fun i:Fin (n+m) => (i:ℕ)))
     have hrows_split:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ)):=by
       simpa using (Fin.sum_univ_add
         (fun i:Fin (n+m) => ((σ i:Fin (n+m)):ℕ)))
     have hcols_split:
         (∑ i:Fin (n+m),(i:ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin m,(n+(j:ℕ))):=by
       simpa using (Fin.sum_univ_add (fun i:Fin (n+m) => (i:ℕ)))
     have hright_cols:
         (∑ j:Fin m,(n+(j:ℕ)))=
           m*n+∑ j:Fin m,(j:ℕ):=by
       simp [Finset.sum_add_distrib,Finset.sum_const]
     have hmain:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+
             (m*n+∑ j:Fin m,(j:ℕ)):=by
       rw [←hrows_split,hperm_sum,hcols_split,hright_cols]
     omega
   have hsum:
       ((∑ j:Fin n,lidx j)+(∑ j:Fin n,ldeg j))+
           ((∑ j:Fin m,ridx j)+(∑ j:Fin m,rdeg j)) ≤
         n*totalDegree H+m*totalDegree B:=by
     simpa only [Finset.sum_add_distrib] using Nat.add_le_add hleft_sum hright_sum
   have hdeg_parts:
       (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j) ≤
         m*totalDegree B+n*totalDegree H-m*n:=by
     omega
   have hsum_deg_split:
       (∑ i:Fin (n+m),(M (σ i) i).natDegree)=
         (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=by
     simpa only [ldeg,rdeg] using
       (Fin.sum_univ_add (fun i:Fin (n+m) => (M (σ i) i).natDegree))
   calc
     (∏ i:Fin (n+m),M (σ i) i).natDegree ≤
         ∑ i:Fin (n+m),(M (σ i) i).natDegree:=by
       simpa using Polynomial.natDegree_prod_le Finset.univ
         (fun i:Fin (n+m) => M (σ i) i)
     _=(∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=hsum_deg_split
     _ ≤ _:=hdeg_parts
end ProximityPrize.SubmissionLower
end PackedLegacy_DB

/-! Packed from ProximityPrize.SubmissionLower.AY. -/
section PackedLegacy_AY
namespace ProximityPrize.SubmissionLower.RCN012
open Polynomial Polynomial.Bivariate RCN002 RCN005 RCN371 RCN011 RCN009 RCN013
noncomputable section
variable {A:Type} [Field A]
theorem bivariateEquiv_coeff_natDegree_le_of_support
   (f:MvPolynomial (Fin 2) A) (height:ℕ → ℕ)
   (hsupport:∀ d∈f.support,d 1 ≤ height (d 0)) (i:ℕ):
   ((bivariateEquiv A f).coeff i).natDegree ≤ height i:=by
 rw [show (bivariateEquiv A f).coeff i=
     MvPolynomial.uniqueAlgEquiv A (Fin 1)
       ((MvPolynomial.finSuccEquiv A 1 f).coeff i) by
   simp [bivariateEquiv]]
 apply (uniqueAlgEquiv_natDegree_le A _).trans
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=hsupport (d.cons i)
   (MvPolynomial.mem_support_coeff_finSuccEquiv.mp hd)
 simpa only [show (1:Fin 2)=(0:Fin 1).succ by decide,
   Finsupp.cons_succ,Finsupp.cons_zero] using hs
theorem bivariateEquiv_totalDegree_le_of_support
   (f:MvPolynomial (Fin 2) A) (cap:ℕ)
   (hsupport:∀ d∈f.support,d 0+d 1 ≤ cap):
   totalDegree (bivariateEquiv A f) ≤ cap:=by
 classical
 have houter:f.degreeOf 0 ≤ cap:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (Nat.le_add_right (d 0) (d 1)).trans (hsupport d hd)
 unfold totalDegree
 apply Finset.sup_le
 intro i hi
 have hiCap:i ≤ cap:=by
   exact (Polynomial.le_natDegree_of_mem_supp i hi).trans
     ((bivariateEquiv_natDegree A f).trans_le houter)
 have hcoeff:((bivariateEquiv A f).coeff i).natDegree ≤ cap-i:=by
   apply bivariateEquiv_coeff_natDegree_le_of_support f (fun j => cap-j)
   intro d hd
   have hs:=hsupport d hd
   omega
 omega
variable (K:Type) [Field K]
theorem planeMap_totalDegree_le_of_rational_support
   (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
   (hsupport:∀ d∈(rationalMap K order F).support,
     d 0+d 1 ≤ cap):
   totalDegree (planeMap K order F) ≤ cap:=by
 exact bivariateEquiv_totalDegree_le_of_support
   (rationalMap K order F) cap hsupport
theorem rationalMap_joint_support_of_original
   (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
   (hsupport:∀ d∈F.support,
     d (order 1)+d (order 2) ≤ cap):
   ∀ e∈(rationalMap K order F).support,e 0+e 1 ≤ cap:=by
 classical
 intro e he
 rw [rationalMap_eq_firstMap] at he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp
   (support_firstMap_subset K
     (algebraMap (Polynomial K) (RatFunc K))
     (MvPolynomial.rename order.symm F) he)
 rw [MvPolynomial.support_rename_of_injective order.symm.injective] at hd
 obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hd
 simpa only [Finsupp.tail_apply,Finsupp.mapDomain_equiv_apply,
   Equiv.symm_symm,
   show (0:Fin 2).succ=(1:Fin 3) by decide,
   show (1:Fin 2).succ=(2:Fin 3) by decide] using hsupport u hu
theorem ordinary_resultant_natDegree_le_totalDegree
   (B H:A[X][Y]) (n mCap totalB totalH cap:ℕ)
   (hHne:H≠0) (hBouter:B.natDegree ≤ n)
   (hHouter:H.natDegree ≤ mCap)
   (hBtotal:totalDegree B ≤ totalB)
   (hHtotal:totalDegree H ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalB+n*totalH-m*n ≤ cap):
   (Polynomial.resultant B H).natDegree ≤ cap:=by
 by_cases hres:Polynomial.resultant B H=0
 · simp [hres]
 · have hfixed:=bivariate_resultant_natDegree_le_totalDegree
     B H n H.natDegree
   have hdegreeCap:
       H.natDegree*totalDegree B+n*totalDegree H-H.natDegree*n ≤
         H.natDegree*totalB+n*totalH-H.natDegree*n:=by
     exact Nat.sub_le_sub_right
       (Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hBtotal)
         (Nat.mul_le_mul_left n hHtotal)) _
   have hfixedCap:
       (Polynomial.resultant B H n H.natDegree).natDegree ≤ cap:=
     hfixed.trans (hdegreeCap.trans (hbudget H.natDegree hHouter))
   have hcoeff:H.coeff H.natDegree≠0:=by
     rw [Polynomial.coeff_natDegree]
     exact Polynomial.leadingCoeff_ne_zero.mpr hHne
   let factor:A[X]:=
     (-1)^(H.natDegree*(n-B.natDegree))*
       H.coeff H.natDegree^(n-B.natDegree)
   have hfactor:factor≠0:=by
     apply _root_.mul_ne_zero
     · exact pow_ne_zero _ (by norm_num)
     · exact pow_ne_zero _ hcoeff
   have hpad:=Polynomial.resultant_add_left_deg
     (f:=B) (g:=H) (m:=B.natDegree)
     (k:=n-B.natDegree) (n:=H.natDegree) le_rfl
   have hsum:B.natDegree+(n-B.natDegree)=n:=
     Nat.add_sub_of_le hBouter
   rw [hsum] at hpad
   change Polynomial.resultant B H n H.natDegree=
     factor*Polynomial.resultant B H at hpad
   calc
     (Polynomial.resultant B H).natDegree ≤
         (factor*Polynomial.resultant B H).natDegree:=by
       rw [Polynomial.natDegree_mul hfactor hres]
       omega
     _=(Polynomial.resultant B H n H.natDegree).natDegree:=by rw [hpad]
     _ ≤ cap:=hfixedCap
theorem planeMap_trapezoid_resultant_natDegree_le
   (order:Fin 3 ≃ Fin 3) (G T:Original K)
   (n mCap totalG totalT cap:ℕ) (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hTouter:(planeMap K order T).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 0+d 1 ≤ totalT)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   (Polynomial.resultant (planeMap K order G)
     (planeMap K order T)).natDegree ≤ cap:=by
 apply ordinary_resultant_natDegree_le_totalDegree
   (planeMap K order G) (planeMap K order T)
     n mCap totalG totalT cap
 · intro hzero
   apply hTne
   apply planeMap_injective K order
   simpa only [map_zero] using hzero
 · exact hGouter
 · exact hTouter
 · exact planeMap_totalDegree_le_of_rational_support
     K order G totalG hGsupport
 · exact planeMap_totalDegree_le_of_rational_support
     K order T totalT hTsupport
 · exact hbudget
end
end ProximityPrize.SubmissionLower.RCN012
end PackedLegacy_AY

/-! Packed from ProximityPrize.SubmissionLower.Y. -/
section PackedLegacy_Y
namespace ProximityPrize.SubmissionLower.RCN003
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
 RCN004 RCN007 RCN001
open RCN012
noncomputable section
variable (K:Type) [Field K]
public def fieldsSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
theorem finite_separable_at_of_original_coordinate_gate
   (P:Ideal (Original K)) [P.IsPrime] (i:Fin 3)
   (hi:Transcendental K (coordinate K P i))
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:coordinateMixedDegree K G H i < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hmixed
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 change fieldsSummary K P (rationalBaseAlgebra K P i hi)
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end ProximityPrize.SubmissionLower.RCN003
end PackedLegacy_Y

/-! Packed from ProximityPrize.SubmissionLower.K8. -/
section PackedLegacy_K8
namespace ProximityPrize.SubmissionLower.RCN176
open RCN002 RCN007 RCN004 RCN001 RCN003 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance _root_.ProximityPrize.SubmissionLower.RCN176.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN176.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN176.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN176
end PackedLegacy_K8

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier10 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.K9. -/
section PackedLegacy_K9
namespace ProximityPrize.SubmissionLower.RCN177
open scoped BigOperators
open RCN174 RCN081 RCN313
 RCN136
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
end
end ProximityPrize.SubmissionLower.RCN177
end PackedLegacy_K9

/-! Packed from ProximityPrize.SubmissionLower.L0. -/
section PackedLegacy_L0
namespace ProximityPrize.SubmissionLower.RCN178
open scoped Classical BigOperators
open RCN051 RCN068 RCN136 RCN238 RCN243 RCN065 RCN231 RCN319 RCN001 RCN174 RCN306 RCN176 RCN177 RCN003 RCN012 RCN011 RCN009 RCN013 RCN371
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance _root_.ProximityPrize.SubmissionLower.RCN178.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN178.instDecidableEq_proximityPrize_1 :DecidableEq Ω:=Classical.decEq Ω
variable [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
 {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN178.instDecidableEq_proximityPrize_2 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN178
end PackedLegacy_L0

/-! Packed from ProximityPrize.SubmissionLower.Z9. -/
section PackedLegacy_Z9
namespace ProximityPrize.SubmissionLower.RCN222
open scoped Classical BigOperators
open RCN051 RCN068 RCN070 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN306 RCN238 RCN243 RCN231 RCN174 RCN319 RCN178 RCN177
noncomputable section
variable (K:Type) [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN222.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN222.instDecidableEqGenericField :DecidableEq (GenericField K):=Classical.decEq (GenericField K)
theorem selectedPoint_eq_initialPoint (selected:K → Polynomial K) (γ:K):
   selectedPoint (polynomialEmbedding K) selected γ=
     fun i:Fin 3 => initialPoint K (selected γ) γ i.succ:=rfl
theorem selectedPoint_surface_evaluation
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K):
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
     (surfaceMap (polynomialEmbedding K) F)=
       polynomialEmbedding K (specialization K (selected γ) γ F):=by
 rw [selectedPoint_eq_initialPoint]
 simpa only [canonical_geometricSurfaceMap] using
   eval_at_actual_generic_initial_point K (selected γ) γ F
theorem selectedPoint_regular_of_specialization
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K)
   (hregular:specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   MvPolynomial.eval₂Hom ((polynomialEmbedding K).comp Polynomial.C)
     (polynomialPoint ((polynomialEmbedding K).comp Polynomial.C)
       (selected γ) γ ((polynomialEmbedding K) Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0:=
 (initialPoint_regular_iff K F (selected γ) γ).mpr hregular
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
 {g:MvPolynomial (Fin 3) (GenericField K)//g∈surfaceFactors (polynomialEmbedding K) F}
def geometricSeeds (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):Finset K:=by
 classical
 exact Γ.filter (fun γ =>
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ) g.1=0)
theorem geometricSeeds_subset
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):geometricSeeds K F selected Γ g ⊆ Γ:=by
 classical
 exact Finset.filter_subset _ _
theorem card_le_sum_geometricSeeds
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (selected:K → Polynomial K) (Γ:Finset K)
   (hsolutions:∀ γ∈Γ,specialization K (selected γ) γ F=0):
   Γ.card ≤ ∑ g:GeometricFactor K F,(geometricSeeds K F selected Γ g).card:=by
 classical
 have hcover:Γ ⊆ Finset.univ.biUnion (geometricSeeds K F selected Γ):=by
   intro γ hγ
   have hz:MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
       (surfaceMap (polynomialEmbedding K) F)=0:=by
     rw [selectedPoint_surface_evaluation,hsolutions γ hγ,map_zero]
   obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F hF
     (selectedPoint (polynomialEmbedding K) selected γ) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hγ,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometricFactor_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (g:GeometricFactor K F) (i:Fin 3):
   g.1.degreeOf i ≤ F.degreeOf i.succ:=by
 have hdiv:=(surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).2
 exact (coordinate_degree_le_of_dvd i g.1 _ hdiv
   (surfaceMap_ne_zero (polynomialEmbedding K) (polynomialEmbedding_injective K) F hF)).trans
     (surfaceMap_degreeOf_le (polynomialEmbedding K) F i)
theorem geometricFactor_sum_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (i:Fin 3):
   (∑ g:GeometricFactor K F,g.1.degreeOf i) ≤ F.degreeOf i.succ:=by
 classical
 have hb:=surfaceFactors_degree_budget (polynomialEmbedding K)
   (polynomialEmbedding_injective K) F hF i
 rw [←Finset.sum_attach (surfaceFactors (polynomialEmbedding K) F)
   (fun g => g.degreeOf i)] at hb
 simpa only [Finset.attach_eq_univ] using hb
variable {ι:Type*}
local instance _root_.ProximityPrize.SubmissionLower.RCN222.instDecidableEq_proximityPrize_1 :DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN222
end PackedLegacy_Z9
end Compact_PackedLegacyCore1


