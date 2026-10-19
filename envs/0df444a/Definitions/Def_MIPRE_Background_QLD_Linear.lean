-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Linear
-- name    : MIPRE_Background_QLD_Linear
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:28:51.662636+00:00
-- url     : https://prove2.me/theorems/9b3baa1b-a0ab-47ae-8d3d-c7169170022c
-- title:
--   Definitions of Linear: Linearity in the two combining coefficients (`lem:qld-global-linear`) An outcome `g` of the global measurement is a…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Linear` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Linearity in the two combining coefficients (`lem:qld-global-linear`). An outcome `g` of the global measurement is a polynomial on `F^{4m}`; read at the padded point `u = (x, z, α, β, w)` it is a polynomial in `(α, β)` whose coefficients are polynomials in the other coordinates. The good outcomes are those of the form `g = α g₁(x, z) + β g₂(x, z)`: linear in `(α, β)` with no constant term and no other monomial. This file bounds the weight of the others (`IsLinAB` fails) from the ordered-product estimate of `lem:qld-global-products` for the order `X_a Z_b`.
--
--   **Definitions** (10): `MIPRE.QLD.IsLinAB` (**Linear in `(α, β)`**: every monomial of `g` has exponents `(1, 0)` or `(0, 1)` on the two combining coordinates, so `g = α g₁ + β g₂`…); `MIPRE.QLD.abSet` (The two combining coordinates.); `MIPRE.QLD.e01` (The pattern `α^0 β^1`.); `MIPRE.QLD.e10` (The pattern `α^1 β^0`.); `MIPRE.QLD.fibMap` (The fibre `{αa + βb = c}` parametrized by `a`, for `β ≠ 0`.); `MIPRE.QLD.fin2Equiv` (Pairs as functions on two indices.); `MIPRE.QLD.instDecidablePredLowIndDegPolyIsLinAB`; `MIPRE.QLD.linAB` (**The linear form `α a + β b`**, as a coefficient vector on two variables.); `MIPRE.QLD.pAB` (**The outcome read at `(α, β)`**, with the other coordinates fixed at those of `u₀`: a polynomial in two variables, as a coefficient vector.); `MIPRE.QLD.patAB` (The pattern with exponents `i` at `α` and `j` at `β`.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `patAB_aIdx`, `patAB_bIdx`, `vec_two_eq`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Linear` (`MIPRE/Background/QLD/Linear.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 81 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Linear.lean; blueprint lem:qld-global-linear

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Linear.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LIDT_LowIndDegPoly_degreeOf_toMv_le
import Theorems.Thm_MIPRE_LIDT_card_eval_eq_zero_le

/-!
# Linearity in the two combining coefficients (`lem:qld-global-linear`)

An outcome `g` of the global measurement is a polynomial on `F^{4m}`; read at the padded point
`u = (x, z, α, β, w)` it is a polynomial in `(α, β)` whose coefficients are polynomials in the other
coordinates. The good outcomes are those of the form `g = α g₁(x, z) + β g₂(x, z)`: linear in
`(α, β)` with no constant term and no other monomial. This file bounds the weight of the others
(`IsLinAB` fails) from the ordered-product estimate of `lem:qld-global-products` for the order
`X_a Z_b`.

## The polynomial side

`LowIndDegPoly.coef g T t` is the coefficient vector, in the variables outside `T`, of the
monomial pattern `t` on the coordinates `T` (`eval_eq_sum_coef`): `g(u) = ∑_t u^t_T · coef(u)`.
Those generic facts are in `MIPRE/Background/LIDT/Coefficients.lean`.
With `T = {aIdx, bIdx}` the patterns are pairs `(i, j)`, and `pAB g u₀` is the bivariate
polynomial `(α, β) ↦ g(setAB u₀ α β)` as a coefficient vector on `Fin 2` (`eval_pAB`). If `g` is
not of the good form, some coefficient `G_{i₀ j₀}` with `(i₀, j₀) ∉ {(1, 0), (0, 1)}` is a nonzero
polynomial, so by Schwartz--Zippel it vanishes at a uniform `u₀` with probability at most
`4md/q` (`sum_uniform_eval_eq_zero_le`); where it does not vanish, `pAB g u₀` differs from every
linear form `α a + β b` (`pAB_ne_linAB`), so they agree at a uniform `(α, β)` with probability at
most `2d/q` (`sum_agree_two_le`).

## The operator side

For `β ≠ 0` the fibre `{αa + βb = c}` has one `b` per `a`, so
`‖(G_g ⊗ ∑_{fibre} X_a Z_b) Φ‖² = ∑_{fibre} ‖(G_g ⊗ X_a Z_b) Φ‖²` (Pythagoras, the `X_a` being
orthogonal projectors), and the weights `W_g(a, b) = ‖(G_g ⊗ X_a Z_b) Φ‖²` do not depend on
`(α, β)` and sum to `⟨G_g⟩`. Averaging over `(α, β)` and then over the other coordinates
(`sum_uniform_setAB` reads the uniform padded point as a uniform base point with a fresh uniform
pair), an outcome that is not of the good form has `E_u ‖(G_g ⊗ B_u(g(u))) Φ‖² ≤ η ⟨G_g⟩` with
`η = (1 + 2d + 4md)/q` (`sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB`). On the other hand
`⟨G_g⟩ ≤ 2 ‖(G_g ⊗ B_u) Φ‖² + 2 ‖(G_g ⊗ (1 - B_u)) Φ‖²` for every `u`, and the second terms are
what the product estimate bounds by `Δ` in total; hence
`(1 - 2η) · (weight of the bad outcomes) ≤ 2Δ` (`sum_bad_linear_mass_le`). This is the linear
bound the paper's `cnote` at `eq:qld-g-prime-bound` describes, rather than the displayed `√Δ`.
-/

noncomputable section

namespace MIPRE

open Matrix
open scoped ComplexOrder MatrixOrder

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The polynomial in the two combining coefficients -/

section AB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- The two combining coordinates. -/
def abSet : Finset (Fin (4 * m)) := {aIdx m, bIdx m}

/-- The pattern with exponents `i` at `α` and `j` at `β`. -/
def patAB (i j : Fin (d + 1)) : Fin (4 * m) → Fin (d + 1) :=
  fun k => if k = aIdx m then i else if k = bIdx m then j else 0

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem patAB_aIdx (i j : Fin (d + 1)) : patAB (m := m) i j (aIdx m) = i := if_pos rfl

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem patAB_bIdx (i j : Fin (d + 1)) : patAB (m := m) i j (bIdx m) = j := by
  rw [patAB, if_neg aIdx_ne_bIdx.symm, if_pos rfl]

/-- **The outcome read at `(α, β)`**, with the other coordinates fixed at those of `u₀`: a
polynomial in two variables, as a coefficient vector. -/
def pAB (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) (u₀ : Point F (4 * m)) :
    LowIndDegPoly (F := F) (m := 2) (d := d) :=
  fun t2 => (g.coef abSet (patAB (t2 0) (t2 1))).eval u₀

end AB

/-! ## Linear forms in the two combining coefficients -/

section Lin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

omit [Field F] [Fintype F] [DecidableEq F] in
theorem vec_two_eq {α : Type*} (v : Fin 2 → α) : ![v 0, v 1] = v := by
  funext i
  fin_cases i <;> rfl

/-- Pairs as functions on two indices. -/
def fin2Equiv (α : Type*) : (Fin 2 → α) ≃ α × α where
  toFun v := (v 0, v 1)
  invFun p := ![p.1, p.2]
  left_inv v := vec_two_eq v
  right_inv _ := rfl

/-- The pattern `α^1 β^0`. -/
def e10 (hd : 1 ≤ d) : Fin 2 → Fin (d + 1) := ![⟨1, Nat.lt_succ_of_le hd⟩, 0]

/-- The pattern `α^0 β^1`. -/
def e01 (hd : 1 ≤ d) : Fin 2 → Fin (d + 1) := ![0, ⟨1, Nat.lt_succ_of_le hd⟩]

/-- **The linear form `α a + β b`**, as a coefficient vector on two variables. -/
def linAB (hd : 1 ≤ d) (a b : F) : LowIndDegPoly (F := F) (m := 2) (d := d) :=
  fun t2 => if t2 = e10 hd then a else if t2 = e01 hd then b else 0

end Lin

/-! ## The linear outcomes and the two probability bounds -/

section LinAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- **Linear in `(α, β)`**: every monomial of `g` has exponents `(1, 0)` or `(0, 1)` on the two
combining coordinates, so `g = α g₁ + β g₂` with `g₁`, `g₂` not reading `α, β`. -/
def IsLinAB (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) : Prop :=
  ∀ e : Fin (4 * m) → Fin (d + 1),
    ¬ (((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0)
      ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1)) → g e = 0

instance : DecidablePred (IsLinAB (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (∀ e : Fin (4 * m) → Fin (d + 1),
    ¬ (((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0)
      ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1)) → g e = 0))

end LinAB

/-! ## The operator side: the fibre weights -/

section Weights

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]

variable {X' Z' : F → Matrix RB RB ℂ}

/-- The fibre `{αa + βb = c}` parametrized by `a`, for `β ≠ 0`. -/
def fibMap (α β c a : F) : F × F := (a, (c - α * a) * β⁻¹)

end Weights

/-! ## Reading a padded point as a base point and a fresh combining pair -/

section Reparam

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

end Reparam

/-! ## The two averages and the assembly -/

section Good

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

variable {X Z : Point F m → F → Matrix RB RB ℂ}

end Good

end MIPRE.QLD

end


