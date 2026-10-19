-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Separate
-- name    : MIPRE_Background_QLD_Separate
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:30:33.095161+00:00
-- url     : https://prove2.me/theorems/85bda494-c4b3-4ed9-92cf-d490088e685f
-- title:
--   Definitions of Separate: Separating the two point variables (`lem:qld-global-separate`) An outcome `g = α g₁ + β g₂` of the global measurement…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Separate` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Separating the two point variables (`lem:qld-global-separate`). An outcome `g = α g₁ + β g₂` of the global measurement that is linear in the combining coordinates (`IsLinAB`, `lem:qld-global-linear`) is *good* when `g₁` reads only the `x` block and `g₂` only the `z` block: `g = α g_X(x) + β g_Z(z)` (`IsGood`). This file bounds the weight of the linear outcomes that are not good, from the two ordered-product estimates of `lem:qld-global-products`: the order `X_a Z_b` controls the outcomes whose `g₂` reads a coordinate outside the `z` block, and the order `Z_b X_a` those whose `g₁` reads a…
--
--   **Definitions** (13): `MIPRE.LIDT.LowIndDegPoly.DepOutside` (**Dependence on a coordinate outside `T`**: some monomial of `g` has a nonzero exponent off `T`.); `MIPRE.LIDT.LowIndDegPoly.const` (The constant coefficient vector.); `MIPRE.LIDT.LowIndDegPoly.restrictOff` (**Substituting the coordinates in `T` by those of `z`**: the coefficient vector, in the variables off `T`, of `u ↦ g(z on T, u off T)`.); `MIPRE.LIDT.instDecidableDepOutsideOfDecidableEq`; `MIPRE.QLD.IsGood` (**The good outcomes**: `g = α g_X(x) + β g_Z(z)`, with `g_X` reading only the `x` block and `g_Z` only the `z` block.); `MIPRE.QLD.gA` (The coefficient of `α` in an outcome: a polynomial in the coordinates other than `α, β`.); `MIPRE.QLD.gB` (The coefficient of `β` in an outcome.); `MIPRE.QLD.instDecidablePredLowIndDegPolyIsGood`; `MIPRE.QLD.mixOn` (The point with the coordinates in `T` taken from `u'` and the others from `u`.); `MIPRE.QLD.mixOnSwap` (The involution of pairs of points that exchanges their coordinates in `T`.); `MIPRE.QLD.oneD` (The exponent `1`.); `MIPRE.QLD.xSet` (The positions of the `x` block.); `MIPRE.QLD.zSet` (The positions of the `z` block.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `mixOn_mixOn`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Separate` (`MIPRE/Background/QLD/Separate.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 82 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Separate.lean; blueprint lem:qld-global-separate

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Separate.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Definitions.Def_MIPRE_Background_QLD_WinMS
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Main
import Definitions.Def_MIPRE_Background_QLD_Ortho
import Definitions.Def_MIPRE_Background_QLD_Consistency
import Definitions.Def_MIPRE_Background_QLD_Commutation
import Definitions.Def_MIPRE_Background_QLD_Expanded
import Definitions.Def_MIPRE_Background_QLD_Swap
import Definitions.Def_MIPRE_Background_QLD_Combined
import Definitions.Def_MIPRE_Background_QLD_Lines
import Definitions.Def_MIPRE_Foundations_Blocks
import Definitions.Def_MIPRE_Background_QLD_Padded
import Definitions.Def_MIPRE_Background_QLD_Product
import Definitions.Def_MIPRE_Background_QLD_Combine
import Definitions.Def_MIPRE_Background_QLD_Legalize
import Definitions.Def_MIPRE_Background_QLD_PaddedLines
import Definitions.Def_MIPRE_Background_QLD_PaddedStrategy
import Definitions.Def_MIPRE_Background_QLD_Dummy
import Definitions.Def_MIPRE_Background_QLD_Products
import Definitions.Def_MIPRE_Background_QLD_Linear

/-!
# Separating the two point variables (`lem:qld-global-separate`)

An outcome `g = α g₁ + β g₂` of the global measurement that is linear in the combining
coordinates (`IsLinAB`, `lem:qld-global-linear`) is *good* when `g₁` reads only the `x` block and
`g₂` only the `z` block: `g = α g_X(x) + β g_Z(z)` (`IsGood`). This file bounds the weight of the
linear outcomes that are not good, from the two ordered-product estimates of
`lem:qld-global-products`: the order `X_a Z_b` controls the outcomes whose `g₂` reads a coordinate
outside the `z` block, and the order `Z_b X_a` those whose `g₁` reads a coordinate outside the `x`
block.

## The argument

For a linear outcome and a base point `u₀`, the fibre `{αa + βb = α g₁(u₀) + β g₂(u₀)}` always
contains the diagonal pair `(g₁(u₀), g₂(u₀))`, and contains any other pair for at most `q` of the
`q²` values of `(α, β)`. So the average over `(α, β)` of `‖(S ⊗ B_u(g(u))) Φ‖²` is at most
`2/q · ⟨S⟩ + W(g₁(u₀), g₂(u₀))`, with `W(a, b) = ‖(S ⊗ X_a Z_b) Φ‖² ≤ ⟨S ⊗ Z_b⟩`. Averaging over
`u₀`, read as a uniform `z` block with the other coordinates uniform and independent
(`sum_uniform_mixOn`): for fixed `z`, `u ↦ g₂(u)` is a polynomial in the other coordinates
(`LowIndDegPoly.restrictOff`) which, if `g₂` reads a coordinate outside the `z` block, is
non-constant except for a set of `z` of probability at most `4md/q` (Schwartz--Zippel on a
nonzero coefficient), and where it is non-constant each value `b` is taken with probability at
most `4md/q`, so `E ⟨S ⊗ Z_{g₂(u)}(z)⟩ ≤ 8md/q · ⟨S⟩`. Altogether
`E_u ‖(S ⊗ B_u(g(u))) Φ‖² ≤ η ⟨S⟩` with `η = (2 + 8md)/q`, and the assembly of
`lem:qld-global-linear` gives `(1 - 2η) · (weight of these outcomes) ≤ 2Δ`. The other block is
the mirror image, with the roles of `(X, a, α)` and `(Z, b, β)` exchanged.
-/

noncomputable section

/-! ## Coefficient vectors: constants, differences, restriction to a block -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n d : ℕ}

/-- The constant coefficient vector. -/
def LowIndDegPoly.const (c : F) : LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if e = 0 then c else 0

/-- **Substituting the coordinates in `T` by those of `z`**: the coefficient vector, in the
variables off `T`, of `u ↦ g(z on T, u off T)`. -/
def LowIndDegPoly.restrictOff (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n))
    (z : Point F n) : LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if ∀ k ∈ T, e k = 0 then (g.coef Tᶜ e).eval z else 0

/-- **Dependence on a coordinate outside `T`**: some monomial of `g` has a nonzero exponent off
`T`. -/
def LowIndDegPoly.DepOutside (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n)) :
    Prop :=
  ∃ e, g e ≠ 0 ∧ ∃ k ∉ T, e k ≠ 0

instance [DecidableEq F] (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n)) :
    Decidable (g.DepOutside T) :=
  inferInstanceAs (Decidable (∃ e, g e ≠ 0 ∧ ∃ k ∉ T, e k ≠ 0))

end MIPRE.LIDT

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Exchanging a block of coordinates -/

section Mix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

/-- The point with the coordinates in `T` taken from `u'` and the others from `u`. -/
def mixOn (T : Finset (Fin (4 * m))) (u u' : Point F (4 * m)) : Point F (4 * m) :=
  fun i => if i ∈ T then u' i else u i

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem mixOn_mixOn (T : Finset (Fin (4 * m))) (u u' : Point F (4 * m)) :
    mixOn T (mixOn T u u') (mixOn T u' u) = u := by
  funext i
  unfold mixOn
  split_ifs <;> rfl

/-- The involution of pairs of points that exchanges their coordinates in `T`. -/
def mixOnSwap (T : Finset (Fin (4 * m))) :
    Point F (4 * m) × Point F (4 * m) ≃ Point F (4 * m) × Point F (4 * m) where
  toFun p := (mixOn T p.1 p.2, mixOn T p.2 p.1)
  invFun p := (mixOn T p.1 p.2, mixOn T p.2 p.1)
  left_inv p := Prod.ext (mixOn_mixOn T p.1 p.2) (mixOn_mixOn T p.2 p.1)
  right_inv p := Prod.ext (mixOn_mixOn T p.1 p.2) (mixOn_mixOn T p.2 p.1)

/-- The positions of the `z` block. -/
def zSet : Finset (Fin (4 * m)) := univ.image (zIdx m)

/-- The positions of the `x` block. -/
def xSet : Finset (Fin (4 * m)) := univ.image (xIdx m)

end Mix

/-! ## The two coefficient polynomials of a linear outcome -/

section Lin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- The exponent `1`. -/
def oneD (hd : 1 ≤ d) : Fin (d + 1) := ⟨1, Nat.lt_succ_of_le hd⟩

/-- The coefficient of `α` in an outcome: a polynomial in the coordinates other than `α, β`. -/
def gA (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    LowIndDegPoly (F := F) (m := 4 * m) (d := d) :=
  g.coef abSet (patAB (oneD hd) 0)

/-- The coefficient of `β` in an outcome. -/
def gB (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    LowIndDegPoly (F := F) (m := 4 * m) (d := d) :=
  g.coef abSet (patAB 0 (oneD hd))

/-- **The good outcomes**: `g = α g_X(x) + β g_Z(z)`, with `g_X` reading only the `x` block and
`g_Z` only the `z` block. -/
def IsGood (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) : Prop :=
  ∀ e : Fin (4 * m) → Fin (d + 1), g e ≠ 0 →
    ((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0 ∧ ∀ k, k ∉ xSet → k ≠ aIdx m → e k = 0)
    ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1 ∧ ∀ k, k ∉ zSet → k ≠ bIdx m → e k = 0)

instance : DecidablePred (IsGood (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (∀ e : Fin (4 * m) → Fin (d + 1), g e ≠ 0 →
    ((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0 ∧ ∀ k, k ∉ xSet → k ≠ aIdx m → e k = 0)
    ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1 ∧ ∀ k, k ∉ zSet → k ≠ bIdx m → e k = 0)))

end Lin

/-! ## The linear fibre and the diagonal weight -/

section Fibre

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB] {X' Z' : F → Matrix RB RB ℂ}

end Fibre

/-! ## Conditioning on a block, the two averages and the assembly -/

section Blocks

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

variable {X Z : Point F m → F → Matrix RB RB ℂ}

end Blocks

end MIPRE.QLD

end


