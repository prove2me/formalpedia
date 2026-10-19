-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Chain
-- name    : MIPRE_Background_QLD_Chain
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:46:48.616351+00:00
-- url     : https://prove2.me/theorems/f2cf89ef-87bb-45db-a89c-48ef8f5d46ad
-- title:
--   Definitions of Chain: The pulling chain's index algebra `lem:qld-pauli-selfcons` is proved by a chain of eleven displays that ends at ```…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Chain` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The pulling chain's index algebra. `lem:qld-pauli-selfcons` is proved by a chain of eleven displays that ends at ``` sum_{g,h,g',h' : g - g_h = g' - g_h', (cd(g) - h) . u-tilde = a} ((S-hat^W_g)_{A A'} (x) (tau^W_h)_{A''}) . ((S-hat^W_g')_{B B'} (x) (tau^W_h')_{B''}) ``` and concludes by the observation that **this expression is symmetric between `(g, h)` and `(g', h')`**, so that the analogous derivation starting from Bob's exact Pauli measurement reaches the same place, and the two are therefore close to each other. That observation is the whole reason the lemma holds, and the reason it is…
--
--   **Definitions** (35): `MIPRE.QLD.ChainCoupled` (**The chain's coupling condition.** The paper's `g - g_h = g' - g_{h'}`, with `g_h` the low-degree encoding of `h`.); `MIPRE.QLD.MirrorSimul.aliceChainOp` (**Alice's chain summand**, on `A A' Ea A''`: her pair measurement's `W`-marginal at `g`, tensored with the Weyl spectral projector at `h`.); `MIPRE.QLD.MirrorSimul.aliceHat` (**Alice's hatted point measurement**, on her physical register `A A' Ea A''`.); `MIPRE.QLD.MirrorSimul.bobAnc` (**The half of the appended pair that sits beside Bob's own space.**); `MIPRE.QLD.MirrorSimul.bobChainOp` (**Bob's**, on `B B' Eb B''` --- the mirror image, and the second cut's.); `MIPRE.QLD.MirrorSimul.bobHat` (**Bob's**, on his.); `MIPRE.QLD.MirrorSimul.bobLift` (**Bob's lift**: an operator of his on `B B' Eb`, extended by the identity on `B''` and on Alice.); `MIPRE.QLD.MirrorSimul.bobPairProj` (**The appended pair's matched Weyl projectors, on Bob's physical register.** The physical grouping gives him both halves, one beside his…); `MIPRE.QLD.MirrorSimul.bobPt` (**Bob's point measurement, on his whole physical register.**); `MIPRE.QLD.MirrorSimul.bobSand` (Bob's sandwiched pair-measurement marginal, on `B B' Eb`.); `MIPRE.QLD.MirrorSimul.bobTail` (**Bob's tail at `eq:qld-pulling-9a`**, at an arbitrary outcome: his point measurement, and nothing on Alice.); and 11 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `mem_chainIdx`, `mem_coupledIdx`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Chain` (`MIPRE/Background/QLD/Chain.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 98 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Chain.lean; blueprint lem:qld-pauli-selfcons

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Chain.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
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
import Definitions.Def_MIPRE_Background_QLD_MTilde
import Definitions.Def_MIPRE_Background_QLD_Pulling
import Definitions.Def_MIPRE_Background_QLD_SwapMeasure
import Definitions.Def_MIPRE_Background_QLD_ChainProbe
import Definitions.Def_MIPRE_Background_QLD_TwoPairs
import Definitions.Def_MIPRE_Background_QLD_Mirror
import Definitions.Def_MIPRE_Background_QLD_SwapState
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LIDT_LowIndDegPoly_degreeOf_toMv_le
import Theorems.Thm_MIPRE_LowDegree_prob_agree_le_individualDegree
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum

/-!
# The pulling chain's index algebra

`lem:qld-pauli-selfcons` is proved by a chain of eleven displays that ends at

```
sum_{g,h,g',h' : g - g_h = g' - g_h', (cd(g) - h) . u-tilde = a}
  ((S-hat^W_g)_{A A'} (x) (tau^W_h)_{A''}) . ((S-hat^W_g')_{B B'} (x) (tau^W_h')_{B''})
```

and concludes by the observation that **this expression is symmetric between `(g, h)` and
`(g', h')`**, so that the analogous derivation starting from Bob's exact Pauli measurement reaches
the same place, and the two are therefore close to each other. That observation is the whole reason
the lemma holds, and the reason it is not obvious is that the two conditions cutting out the index
set look asymmetric: the second mentions both pairs, but the first mentions only `g` and `h`.

The paper's sentence is that the conditions `(cd(g) - h) . u-tilde = a` and `g - g_h = g' - g_h'`
are together equivalent to `(cd(g') - h') . u-tilde = a` and `g - g_h = g' - g_h'`. This file is
that sentence, together with the rewriting of the exact Pauli measurement over the same index set
(`eq:qld-pulling-2` and `eq:qld-pulling-2b`). It is pure index algebra: no state, no estimate.

Subtraction is written as addition throughout, the field having characteristic two.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-! ## The label a pair of outcomes carries -/

/-- **The chain's label.** `cd(g) - h` is the paper's difference of the pair outcome's cube data
and the Weyl outcome; the chain's index set asks its pairing with the probe to be the measurement
outcome. -/
def chainLabel (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h : Anc F m) : Anc F m :=
  cubeData g + h

/-- **The chain's coupling condition.** The paper's `g - g_h = g' - g_{h'}`, with `g_h` the
low-degree encoding of `h`. -/
def ChainCoupled (g g' : LowIndDegPoly (F := F) (m := m) (d := d)) (h h' : Anc F m) : Prop :=
  g.toMv + ldEnc h = g'.toMv + ldEnc h'

instance decidableChainCoupled (g g' : LowIndDegPoly (F := F) (m := m) (d := d))
    (h h' : Anc F m) : Decidable (ChainCoupled g g' h h') :=
  inferInstanceAs (Decidable (g.toMv + ldEnc h = g'.toMv + ldEnc h'))

/-! ## The index set, and the exact Pauli measurement written over it -/

/-- **The chain's index set** at the probe `v` and the outcome `a`: the pairs whose label pairs
with the probe to give `a`. -/
def chainIdx (v : Anc F m) (a : F) :
    Finset (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :=
  univ.filter fun p => dotF (chainLabel p.1 p.2) v = a

omit [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mem_chainIdx {v : Anc F m} {a : F}
    {p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m} :
    p ∈ chainIdx v a ↔ dotF (chainLabel p.1 p.2) v = a := by
  rw [chainIdx, mem_filter]
  exact and_iff_right (mem_univ p)

/-! ## A reindexing, and the label filters

Two facts the assembly needs: a reindexing of the whole space carries `mulVec` the way
`qform_comp_equiv` carries the quadratic form, and the chain's label filters are products, the
label reading only the first pair. -/

section Probe

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-- **The chain's summand on one party**: the pair measurement's `W`-marginal at `g`, tensored with
the Weyl spectral projector at `h`, on that party's physical register. -/
def SimulPair.chainOp (P : SimulPair ψ MA MB δ) (W : Bas)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  ((polyMarg P.SA W).mats p.1).val ⊗ₖ proj (weylOf W) p.2

end Probe

/-! ## The chain's endpoint, and its symmetry

Display `eq:qld-pulling-12` is a sum over *pairs* of index pairs, one per party, coupled by
`g - g_h = g' - g_{h'}` and cut out by the pairing condition on the first. Both parties' derivations
end there, and that is only because the expression does not in fact depend on which party's pair
the condition is read off. -/

section Endpoint

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-- **The index set of `eq:qld-pulling-12`**: coupled pairs, with the label read off the first. -/
def coupledIdx (v : Anc F m) (a : F) :
    Finset ((LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :=
  univ.filter fun q => ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2 ∧ dotF (chainLabel q.1.1 q.1.2) v = a

omit [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mem_coupledIdx {v : Anc F m} {a : F}
    {q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)} :
    q ∈ coupledIdx v a
      ↔ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2 ∧ dotF (chainLabel q.1.1 q.1.2) v = a := by
  rw [coupledIdx, mem_filter]
  exact and_iff_right (mem_univ q)

/-- **The chain's endpoint**, an operator on the physical cut: Alice's pair against Bob's. -/
def MirrorSimul.endOp (M : MirrorSimul ψ MA MB δ) (W : Bas) (v : Anc F m) (a : F) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  ∑ q ∈ coupledIdx v a, (M.toFirst.chainOp W q.1) ⊗ₖ (M.toSecond.chainOp W q.2)

/-! ## Closing the chain

Both parties' derivations end at the endpoint, and what remains is arithmetic: the triangle
inequality for a family of deviations, which Foundations has as `sum_snorm_sq_triangle'`. The two
hypotheses below are exactly the two chains --- Alice's `eq:qld-pulling-0` through
`eq:qld-pulling-12`, and Bob's symmetric equivalent --- and nothing else stands between them and
`lem:qld-pauli-selfcons`. -/

section Close

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

end Close

/-! ## The chain's assembly: chaining and transport

Two facts the eleven displays have to be joined by. The first is the triangle inequality along a
chain rather than across one step; the second carries a statement about the first cut's state to
the physical one, since displays `eq:qld-pulling-1` to `-4` are local in the first cut's grouping
and everything from `-5` on is local in the physical one. -/

/-! ## The chain's first estimate

`eq:qld-pulling-0` to `eq:qld-pulling-1` right-multiplies the exact Pauli measurement by the
near-identity of `lem:qld-helper`. What makes the step cost the helper's bound and no more is
`sum_snorm_sq_sub_mul`: the measurement's outcomes are orthogonal, so summing over them leaves one
deviation rather than one per outcome. -/

variable {d' : Type} [Fintype d'] [DecidableEq d']

/-! ## The last two displays' common machinery

`eq:qld-pulling-5` to `-7` and `eq:qld-pulling-10` to `-12` are the chain's remaining estimates,
and they are the first of its steps to live on all six registers: both compare operators on the
physical cut, Alice's `A A' A''` against Bob's `B B' B''`. They share an outer shape and a way of
discharging the far party, collected here. -/

section LastTwo

variable {dA' dB' anc ι κ : Type*} [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB']
  [Fintype anc] [DecidableEq anc] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end LastTwo

section First

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

variable (P : SimulPair ψ MA MB δ)

/-- **The helper's near-identity**, read along the cut `mTilde` lives on. On `Phi`'s own cut it is
`agreeOp` of Alice's pair-measurement marginals against Bob's expanded point measurements, which is
what `lem:qld-helper` bounds; `regroupEquiv` carries it to the cut that has `A''` on Alice's
side. -/
def SimulPair.nearId (W : Bas) (u : Point F m) :
    Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB))
      ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) ℂ :=
  Matrix.reindex regroupEquiv regroupEquiv
    (agreeOp (fun g : LowIndDegPoly (F := F) (m := m) (d := d) =>
        ((polyMarg P.SA W).mats g).val)
      (fun g => (aOp (hatMats MB W u (g.eval u)) : Matrix ((dB × Anc F m) × P.EB) _ ℂ)))

namespace SimulPair

/-- **The outcome the chain's index pair carries**, the paper's `(g - g_h)(u)`: the pair outcome's
value at the sampled point, shifted by the Weyl outcome's own encoding there. -/
def chainShift (u : Point F m) (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) : F :=
  p.1.eval u + dotF p.2 (indVec u)

/-- Alice's copy of the point measurement, on her whole register. -/
def ptA (W : Bas) (u : Point F m) (k : F) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  aOp (aOp (aOp (((ptAtPOVM MA W u).mats k).val)))

/-- Bob's, on his. -/
def ptB (W : Bas) (u : Point F m) (k : F) : Matrix (dB × P.EB) (dB × P.EB) ℂ :=
  aOp (((ptAtPOVM MB W u).mats k).val)

/-! ## `eq:qld-pulling-13`, the chain's only Cauchy--Schwarz

The swap that completes `eq:qld-pulling-10`. It is stated on a `SimulPair`, on the cut that pair's
state lives on, because that is where both placements of the point measurement are local: the one
that sandwiches is the first party's own, the one that replaces it is the second party's. The
mirror then makes it Bob's. -/

/-! ## The chain's first four terms, and the three steps between them

The assembly proper. `chainS` names the terms displays `eq:qld-pulling-0` to `-3` run through, on
the cut `Phi` lives on, and the three lemmas below are those displays read as bounds on
consecutive deviations --- which is the form `sum_snorm_sq_chain_le` consumes. -/

/-- **The chain's first four terms, on the cut `Phi` lives on.** `eq:qld-pulling-0` through
`eq:qld-pulling-3`: the exact Pauli measurement, that measurement times the near-identity, the
same written over the chain's index, and the same with Alice's copy of the point measurement
inserted. -/
def chainS (W : Bas) (v : Anc F m) (u : Point F m) :
    ℕ → F → Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB))
      ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) ℂ
  | 0 => fun a => aOp (P.mTildeAnc W v a)
  | 1 => fun a => (aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ) * P.nearId W u
  | 2 => fun a => ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (aOp (P.chainOp W p) : Matrix _ _ ℂ) * bOp (P.ptB W u (chainShift u p))
  | _ => fun a => ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (aOp (P.chainOp W p) : Matrix _ _ ℂ)
        * (aOp (P.ptA W u (chainShift u p)) * bOp (P.ptB W u (chainShift u p)))

/-- Alice's half of the first pair, on her register of the cut `mVec` reads. -/
def ancA (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))

/-- The other half, which that cut also gives her. -/
def ancB (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  bOp (proj (weylOf W) h)

/-- **Alice's hatted point measurement**, on her register of the cut `mVec` reads. -/
def hatA (W : Bas) (u : Point F m) (c : F) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  aOp (aOp (hatMats MA W u c))

/-- **Display `eq:qld-pulling-3b`'s term**: the chain's third term with Alice's own hatted point
measurement in place of her copy of the point measurement. -/
def chainS3b (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB))
      ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) ℂ :=
  ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
    (aOp (P.chainOp W p * P.hatA W u (p.1.eval u)) : Matrix _ _ ℂ)
      * bOp (P.ptB W u (chainShift u p))

end SimulPair

end First

end Endpoint

/-! ## The physical cut's operators

What the last two displays sum over. -/

section Physical

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-! ## Each party's chain summand, on its own register

Every object of `eq:qld-pulling-5` onward carries a party's whole triple, and each is named in
that party's own spelling rather than reached through `toFirst` or `toSecond`: `toFirst.EA` is
`M.Ea` by definition, but the two spellings do not unify inside an elaborated product type, and a
single occurrence of the wrong one makes the product's `HMul` instance fail to synthesize. -/

/-- **Alice's chain summand**, on `A A' Ea A''`: her pair measurement's `W`-marginal at `g`,
tensored with the Weyl spectral projector at `h`. -/
def aliceChainOp (W : Bas)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.toFirst.chainOp W p

/-- **Bob's**, on `B B' Eb B''` --- the mirror image, and the second cut's. -/
def bobChainOp (W : Bas)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.toSecond.chainOp W p

/-- **Bob's Weyl projector**, on the half `B''` of the appended pair that the physical grouping
gives him --- the outermost factor of his register. -/
def bobWeyl (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  bOp (proj (weylOf W) h)

/-- **The chain's projective family on the physical cut**: Alice's pair outcome and Weyl outcome
together, against Bob's Weyl outcome. Displays `eq:qld-pulling-5` onward sum over this triple. -/
def chainP (W : Bas)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (M.aliceChainOp W t.1) * bOp (M.bobWeyl W t.2)

/-- **Alice's hatted point measurement**, on her physical register `A A' Ea A''`. -/
def aliceHat (W : Bas) (u : Point F m) (c : F) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  aOp (aOp (hatMats MA W u c))

/-- **Bob's**, on his. -/
def bobHat (W : Bas) (u : Point F m) (c : F) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  aOp (aOp (hatMats MB W u c))

/-- **The tail the chain carries at `eq:qld-pulling-5`**: Alice's gap from her own point
measurement, against Bob's point measurement at the shifted outcome `(g - g_h + g_h')(u)`. -/
def chainW (W : Bas) (u : Point F m)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (1 - M.aliceHat W u (t.1.1.eval u))
    * bOp (M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))

/-! ## The four-index family, and Bob's half of the chain for free

`eq:qld-pulling-9a` left-multiplies by Bob's own pair measurement, which is the identity, and from
there to `eq:qld-pulling-12` the chain runs over *both* parties' pairs. `chainQ` is that family,
and `endOp` --- the chain's endpoint, already in place --- is its restriction to the coupled index
set. What the mirror buys is the rest: Bob's derivation is Alice's, instantiated. -/

/-- **The chain's four-index family on the physical cut**: each party's pair outcome and Weyl
outcome together. -/
def chainQ (W : Bas)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (M.aliceChainOp W q.1) * bOp (M.bobChainOp W q.2)

/-! ## `eq:qld-pulling-10`, down to its Cauchy--Schwarz step

The second of the chain's two remaining estimates. It runs over the four-index family and over the
pairs whose outcomes *disagree* at the sampled point, and the reduction below is everything before
the swap: projectivity, one relaxation, and two completeness sums. -/

end MirrorSimul

/-- **The outcome the chain's four-index pair carries**, the paper's `(g - g_h + g_h')(u)`. -/
def chainQShift (u : Point F m)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) : F :=
  q.1.1.eval u + dotF q.1.2 (indVec u) + dotF q.2.2 (indVec u)

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **Bob's tail at `eq:qld-pulling-9a`**, at an arbitrary outcome: his point measurement, and
nothing on Alice. -/
def bobTail (W : Bas) (u : Point F m) (c : F) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (1 : Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ)
    * bOp (M.bobHat W u c)

/-- Bob's sandwiched pair-measurement marginal, on `B B' Eb`. -/
def bobSand (W : Bas) (u : Point F m) (c : F)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    Matrix ((dB × Anc F m) × M.Eb) ((dB × Anc F m) × M.Eb) ℂ :=
  (aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ)ᴴ
    * ((polyMarg M.SA' W).mats g).val
    * (aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ)

/-- **The tail at the chain's own outcome**, the paper's `(g - g_h + g_h')(u)`. -/
def chainV (W : Bas) (u : Point F m)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  M.bobTail W u (chainQShift u q)

/-! ## `eq:qld-pulling-11`, and the second cut's bridge

The last of the chain's estimates before Schwartz--Zippel. Everything here is Bob's, and
everything Bob's is Alice's at the mirror. -/

/-- **Bob's lift**: an operator of his on `B B' Eb`, extended by the identity on `B''` and on
Alice. Both remaining displays sandwich the four-index family with one of these; only which one
differs. -/
def bobLift (T : Matrix ((dB × Anc F m) × M.Eb) ((dB × Anc F m) × M.Eb) ℂ) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (1 : Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ)
    * bOp (aOp T)

end MirrorSimul

/-! ## `eq:qld-pulling-12`, Schwartz--Zippel

The chain's last display, and its only step that is not about operators: the constraint the chain
carries is an equality of polynomial *values* at the sampled point, and passing to equality of the
polynomials themselves discards only the tuples where distinct polynomials happen to agree
there. -/

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **The first cut's space, with the appended pair, regrouped as the physical cut.** The pair's
two halves go where the physical grouping wants them: one beside Bob's own space, one outermost. -/
def physLiftEquiv :
    (((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) × (Anc F m × Anc F m))
      ≃ ((((dA × Anc F m) × M.Ea) × Anc F m) × ((((dB × Anc F m) × M.Eb) × Anc F m))) where
  toFun p := (p.1.1, (((p.1.2.1, p.2.2), p.1.2.2), p.2.1))
  invFun q := ((q.1, (q.2.1.1.1, q.2.1.2)), (q.2.2, q.2.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **An operator of the first cut, lifted to the physical one**: the identity on the appended
pair, and the registers regrouped. -/
def physLift (U : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  Matrix.reindex M.physLiftEquiv M.physLiftEquiv
    (U ⊗ₖ (1 : Matrix (Anc F m × Anc F m) (Anc F m × Anc F m) ℂ))

/-! ## `eq:qld-pulling-4` on the physical cut

The step that brings the second pair's outcome into the chain. Both of that pair's halves are
Bob's in the physical grouping, so the matched Weyl projectors are one operator of his, and the
pair being maximally entangled they leave the state alone. -/

/-- **The appended pair's matched Weyl projectors, on Bob's physical register.** The physical
grouping gives him both halves, one beside his own space and one outermost. -/
def bobPairProj (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  aOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h)) * bOp (proj (weylOf W) h)

/-- **Bob's point measurement, on his whole physical register.** -/
def bobPt (W : Bas) (u : Point F m) (k : F) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  aOp (aOp (aOp (((ptAtPOVM MB W u).mats k).val)))

/-- **The half of the appended pair that sits beside Bob's own space.** -/
def bobAnc (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  aOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h))

/-- **Display `eq:qld-pulling-3b`'s term**, written in each party's own spelling. -/
def chainU3b (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ :=
  ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
    aOp (M.aliceChainOp W p * M.aliceHat W u (p.1.eval u))
      * bOp (aOp (((ptAtPOVM MB W u).mats (SimulPair.chainShift u p)).val))

end MirrorSimul

end Physical

end MIPRE.QLD

end


