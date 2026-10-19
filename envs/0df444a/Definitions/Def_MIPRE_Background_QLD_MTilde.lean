-- Prove2me | Definitions.Def_MIPRE_Background_QLD_MTilde
-- name    : MIPRE_Background_QLD_MTilde
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:35:00.253491+00:00
-- url     : https://prove2.me/theorems/c8e60f2d-9d68-4d62-a4c5-07bbf8242867
-- title:
--   Definitions of MTilde: Item 1 of `lem:qld-exact-paulis`, read as `M~` (the paper's `eq:tilde_M`) `MIPRE/Background/QLD/Multilinear.lean`…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.MTilde` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Item 1 of `lem:qld-exact-paulis`, read as `M~` (the paper's `eq:tilde_M`). `MIPRE/Background/QLD/Multilinear.lean` proves the agreement the appendix's chain establishes, `E_u sum_g <S^W_g (x) M^(Point,W),u_{coded(g).ind_m(u)}> >= 1 - delta_S - 2 (mass off the good set)`, as a sum over the *outcomes* of the simultaneous measurement. The paper states the same thing as a closeness between two **measurements**: `M~^{W,ind_m(u)}_a`, an operator on one party, and the strategy's `(Point, W)` measurement on the other. This file is that reading.
--
--   **Definitions** (6): `MIPRE.QLD.SimulPair.mTildeAt` (**The paper's `M~^{W, ind_m(u)}_a`** (`eq:tilde_M`): the simultaneous pair measurement of `lem:qld-simultaneous` tensored with the…); `MIPRE.QLD.SimulPair.mVec` (**The state along the third cut.** `hatVec`'s cut puts the register the paper calls `A''` with the opposite party; this one puts it with…); `MIPRE.QLD.SimulPair.wTildeAt` (**The paper's `W~^e(u-tilde)`** (`eq:def-tildewj`) at the simultaneous pair measurement.); `MIPRE.QLD.ptAtPOVM` (The strategy's `(Point, W)` measurement at `u`, read as a field element.); `MIPRE.regroupEquiv` (**The regrouping** that moves the ancilla factor `T` from the second party to the first.); `MIPRE.regroupVec` (The state, read along the regrouped cut.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `isPVM_mTildeAt`, `isPVM_mTilde`, `mTilde_eq_sTensor`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.MTilde` (`MIPRE/Background/QLD/MTilde.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 90 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/MTilde.lean; blueprint lem:qld-exact-paulis

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/MTilde.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_BlockPoly
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
import Definitions.Def_MIPRE_Background_QLD_Separate
import Definitions.Def_MIPRE_Background_QLD_Simul
import Definitions.Def_MIPRE_Background_QLD_Complete
import Definitions.Def_MIPRE_Background_QLD_PauliBasis
import Definitions.Def_MIPRE_Background_QLD_Multilinear
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_QLD_kron_sum
import Theorems.Thm_MIPRE_QLD_mTilde_eq_sum
import Theorems.Thm_MIPRE_QLD_sTensor_conjTranspose
import Theorems.Thm_MIPRE_QLD_sTensor_mul
import Theorems.Thm_MIPRE_QLD_sTensor_one
import Theorems.Thm_MIPRE_Weyl_isPVM_syn

/-!
# Item 1 of `lem:qld-exact-paulis`, read as `M~` (the paper's `eq:tilde_M`)

`MIPRE/Background/QLD/Multilinear.lean` proves the agreement the appendix's chain establishes,

`E_u sum_g <S^W_g (x) M^(Point,W),u_{coded(g).ind_m(u)}> >= 1 - delta_S - 2 (mass off the good
set)`,

as a sum over the *outcomes* of the simultaneous measurement. The paper states the same thing as a
closeness between two **measurements**: `M~^{W,ind_m(u)}_a`, an operator on one party, and the
strategy's `(Point, W)` measurement on the other. This file is that reading.

## Why it is a reindexing and not a new estimate

The paper's expanded state is
`|psi-hat> = |psi>_{A B} (x) |EPR>_{A' A''} (x) |EPR>_{B' B''}`, with `A' A''` a maximally
entangled pair *local to Alice* and `B' B''` one local to Bob, and it is read along two cuts,
`A A' | B A''` and `B B' | A B''` --- one per orientation of `lem:qld-simultaneous`. Neither cut is
the physical one: each splits a local pair. `MIPRE.QLD.hatVec` is one such cut, and it is all
`lem:qld-simultaneous` and `lem:qld-helper` need, since each uses one orientation at a time.

`M~^{W,u-tilde}_a = sum_g S-hat^W_g (x) tau^W_{coded(g) . u-tilde - a}(u-tilde)` is different: it
wants the pair measurement and the generalized Pauli on *disjoint registers of one party*,
`A A'` and `A''`. In the `hatVec` cut the register `A''` sits with the opposite party. So writing
`M~` as a single matrix is a regrouping of the same six registers along a third cut,
`A A' A'' | B`, and every Born probability transports across it by `bornProb_regroupVec`, which is
one entry computation. No second entangled pair and no new estimate are involved.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Regrouping the two parties' registers -/

section Regroup

variable {R S T E : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- **The regrouping** that moves the ancilla factor `T` from the second party to the first. -/
def regroupEquiv : R × ((S × T) × E) ≃ (R × T) × (S × E) where
  toFun p := ((p.1, p.2.1.2), (p.2.1.1, p.2.2))
  invFun p := (p.1.1, ((p.2.1, p.1.2), p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The state, read along the regrouped cut. -/
def regroupVec (ψ : R × ((S × T) × E) → ℂ) : (R × T) × (S × E) → ℂ :=
  ψ ∘ (regroupEquiv (R := R) (S := S) (T := T) (E := E)).symm

end Regroup

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## `mTilde` is a projective measurement -/

section PVM

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Fintype G] [DecidableEq G]
  {dA : Type*} [Fintype dA] [DecidableEq dA]

/-- `mTilde` is block diagonal along the pair measurement, so `sTensor_mul` applies to it. -/
theorem mTilde_eq_sTensor (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
    (w : (n → F) → Matrix (n → F) (n → F) ℂ) (u : n → F) (a : F) :
    mTilde S pi cd w u a = sTensor S fun p => syn w u (dotF (cd (pi p)) u + a) :=
  mTilde_eq_sum S pi cd w u a

/-- **The measurement `M~^{W,u}` is projective.** Its elements multiply factorwise because the
pair measurement is projective, and factorwise they are the ancilla's syndrome projectors. -/
theorem isPVM_mTilde {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S) (pi : G × G → G)
    (cd : G → (n → F)) {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w)
    (u : n → F) : IsPVM (mTilde S pi cd w u) where
  isSelfAdjoint a := by
    rw [mTilde_eq_sTensor, sTensor_conjTranspose hS]
    exact congrArg (sTensor S) (funext fun _ => (isPVM_syn hw u).isSelfAdjoint _)
  idem a := by
    rw [mTilde_eq_sTensor, sTensor_mul hS]
    exact congrArg (sTensor S) (funext fun _ => (isPVM_syn hw u).idem _)
  sum_eq_one := by
    have hone : ∀ c : F, (∑ a : F, syn w u (c + a)) = 1 := fun c => by
      rw [← (isPVM_syn hw u).sum_eq_one]
      exact Equiv.sum_comp (Equiv.addLeft c) fun b => syn w u b
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => mTilde_eq_sTensor S pi cd w u a,
      show (∑ a : F, sTensor S fun p => syn w u (dotF (cd (pi p)) u + a))
          = sTensor S fun p => ∑ a : F, syn w u (dotF (cd (pi p)) u + a) from by
        show (∑ a : F, ∑ p, S p ⊗ₖ syn w u (dotF (cd (pi p)) u + a))
          = ∑ p, S p ⊗ₖ ∑ a : F, syn w u (dotF (cd (pi p)) u + a)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => (kron_sum univ _ _).symm,
      show (fun p => ∑ a : F, syn w u (dotF (cd (pi p)) u + a))
          = fun _ : G × G => (1 : Matrix (n → F) (n → F) ℂ) from
        funext fun p => hone _,
      sTensor_one hS]

end PVM

/-! ## The point measurement at a point, and the shift -/

section Shift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

variable {d' : Type} [Fintype d'] [DecidableEq d']

/-- The strategy's `(Point, W)` measurement at `u`, read as a field element. -/
def ptAtPOVM (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) : POVM F d' :=
  (M (.point W u)).map rdVal

end Shift

/-! ## Item 1, as a closeness of two measurements -/

section Item

/- The index of `mTilde`'s matrices is a four-fold product, `((dA x Anc) x EA) x Anc`, whose
`DecidableEq` runs past the default instance-size bound --- each half alone is found, the product
is not. Raised here and nowhere else. -/
set_option synthInstance.maxSize 1000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **The state along the third cut.** `hatVec`'s cut puts the register the paper calls `A''`
with the opposite party; this one puts it with Alice, which is where `mTilde` needs it. -/
def mVec : ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) → ℂ := regroupVec P.Φ

/-- **The paper's `M~^{W, ind_m(u)}_a`** (`eq:tilde_M`): the simultaneous pair measurement of
`lem:qld-simultaneous` tensored with the ancilla's generalized Pauli at the shifted syndrome. -/
def mTildeAt (W : Bas) (u : Point F m) (a : F) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  mTilde (fun p => ((P.SA.mats p).val)) (PolyPair.proj W) cubeData (weylOf W) (indVec u) a

/-- It is a projective measurement. -/
theorem isPVM_mTildeAt (W : Bas) (u : Point F m) : IsPVM (P.mTildeAt W u) :=
  isPVM_mTilde P.SA_proj (PolyPair.proj W) cubeData (isWeylFamily_weylOf W) (indVec u)

/-! ### The exact half, at the same data

`wTilde` and its three relations are proved in `MIPRE/Background/QLD/ExactPauli.lean` for an
abstract projective pair measurement and Weyl family. Instantiating them at the simultaneous
measurement of a `SimulPair` puts the exact half and the approximate half of
`lem:qld-exact-paulis` on the *same* objects, which is what the lemma asserts. -/

/-- **The paper's `W~^e(u-tilde)`** (`eq:def-tildewj`) at the simultaneous pair measurement. -/
def wTildeAt (W : Bas) (e : F) (v : Anc F m) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  wTilde (fun p => ((P.SA.mats p).val)) (PolyPair.proj W) cubeData (weylOf W) e v

end SimulPair

end Item

end MIPRE.QLD

end


