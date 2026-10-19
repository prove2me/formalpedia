-- Prove2me | Definitions.Def_MIPRE_Background_QLD_SwapItemTwo
-- name    : MIPRE_Background_QLD_SwapItemTwo
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:54:50.170745+00:00
-- url     : https://prove2.me/theorems/b3b7039c-4808-4274-b85a-9407874774cf
-- title:
--   Definitions of SwapItemTwo: Item 2 of `lem:qld-swap`, and the lemma `MIPRE/Background/QLD/SwapItemOne.lean` proves item 1 of the swap isometry…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.SwapItemTwo` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Item 2 of `lem:qld-swap`, and the lemma. `MIPRE/Background/QLD/SwapItemOne.lean` proves item 1 of the swap isometry lemma with nothing assumed beyond the game (`MirrorSimul.exists_aux_close`): after the two swap unitaries the physical state is close to a product `|aux> ⊗ |EPR_q>^M`. This file proves item 2 --- conjugation by a party's swap unitary carries the strategy's total Pauli measurement `M^{(Pauli,W)}_h` to the honest projector `Id ⊗ tau^W_h` on that party's half of the pair, in the state-dependent distance relative to that product state --- for both parties, and puts the two items…
--
--   **Definitions** (12): `MIPRE.QLD.MirrorSimul.aliceConjPauli` (**Alice's conjugated Pauli measurement** `V_A M^{(Pauli,W)}_h V_A^dagger`.); `MIPRE.QLD.MirrorSimul.alicePauli` (**Alice's total Pauli measurement** `M^{(Pauli,W)}_h`, its outcomes the cube data `h` the answer reports, extended by the identity to her…); `MIPRE.QLD.MirrorSimul.aliceTau` (**The honest Pauli projector `tau^W_h` on Alice's half of the pair**, `Id ⊗ tau^W_h`.); `MIPRE.QLD.MirrorSimul.bobConjPauli` (**Bob's** `V_B M^{(Pauli,W)}_h V_B^dagger`.); `MIPRE.QLD.MirrorSimul.bobPauli` (**Bob's**, on `B B' Eb B''`.); `MIPRE.QLD.MirrorSimul.bobTau` (**And on Bob's.**); `MIPRE.QLD.MirrorSimul.physAux` (**The product state `|aux> ⊗ |EPR_q>^M` of item 1, read on the physical cut**: each party's half of the pair back at the end of its own…); `MIPRE.QLD.ancPoly` (**The low-degree encoding `g_h` of cube data `h`**, as a coefficient table of individual degree at most `d`.); `MIPRE.QLD.deltaItemTwo` (The constant of item 2: `eq:qld-unitary-5`'s `11 δ'`, Schwartz--Zippel's `md/q`, and the transport across item 1, which costs twice the…); `MIPRE.QLD.deltaLegs` (**The constant the three legs of `eq:qld-unitary-5` share**: item 1 of `lem:qld-exact-paulis` (`inconsistency_mTilde_le`) and the game's…); `MIPRE.QLD.etaItemOne` (**Item 1's bound**, named so that the joint statement fits.); `MIPRE.QLD.outerUnVec` (**A state on item 1's cut, read on the physical one.** The inverse of `outerVec`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.SwapItemTwo` (`MIPRE/Background/QLD/SwapItemTwo.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 102 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapItemTwo.lean; blueprint lem:qld-swap

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapItemTwo.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_QLD_Chain
import Definitions.Def_MIPRE_Background_QLD_ChainAssembly
import Definitions.Def_MIPRE_Background_QLD_SelfCons
import Definitions.Def_MIPRE_Background_QLD_SwapItemOne
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_aOp_sum

/-!
# Item 2 of `lem:qld-swap`, and the lemma

`MIPRE/Background/QLD/SwapItemOne.lean` proves item 1 of the swap isometry lemma with nothing
assumed beyond the game (`MirrorSimul.exists_aux_close`): after the two swap unitaries the
physical state is close to a product `|aux> ⊗ |EPR_q>^M`. This file proves item 2 --- conjugation
by a party's swap unitary carries the strategy's total Pauli measurement `M^{(Pauli,W)}_h` to the
honest projector `Id ⊗ tau^W_h` on that party's half of the pair, in the state-dependent distance
relative to that product state --- for both parties, and puts the two items together relative to
**one** auxiliary state: `MirrorSimul.swap_isometry`.

## The chain

No estimate here is new; every display of the paper's argument was already a lemma, and this file
is the threading. For Alice, on a state `Δ` that carries the pair on `A'' B''` and is within `r`
of the swapped physical state:

* `eq:qld-unitary-7`: both families are projective, so the summed deviation is twice the deficit
  of their agreement (`sum_snorm_sq_sub_le_of_agree`); and on the product state `tau^W_h` on `A''`
  acts as `tau^W_h` on `B''` (`mulVec_outerUnVec_auxVec`, from `stateVec_epr_proj`), which makes
  the agreement a bipartite Born probability across the physical cut.
* `eq:qld-unitary-8`: coarse-graining both families along `g_h(u)` raises the agreement by at most
  `md/q` (`sum_uniform_bornProb_fibre_le`).
* `eq:qld-unitary-6`, on **Bob's** side: the coarse-grained honest projector is a syndrome
  projector, which is Bob's exact Pauli measurement conjugated by his swap unitary
  (`bobSwap_conj_bobMTilde`), so the coarse agreement is `eq:qld-unitary-9`'s.
* The transport across item 1 (`sum_bornProb_conj_ge_of_close`): the conjugation moves onto the
  state, where it undoes the swap; the outcome sum is one projection, hence a contraction; and
  `abs_qform_sub_qform_le` costs `2 r`. With `r` the square root of item 1's bound on the squared
  distance, this is where `delta_S^{1/4}` enters.
* `eq:qld-unitary-5`, at the **mirror** instance (`sum_bornProb_physVec_ge`): on the physical state,
  Bob's exact Pauli measurement against Alice's `(Pauli, W)` reading is the second cut's `mTildeAt`
  against the swapped strategy's Pauli reading, and `inconsistency_mTilde_pauli_le_of_win` there,
  with its hypothesis discharged by item 1 of `lem:qld-exact-paulis` at the same instance
  (`inconsistency_mTilde_le`), bounds it.

## Three things that had to be said

* **The encoding as an outcome.** The Schwartz--Zippel packaging reads its index through
  coefficient tables of bounded individual degree. `ancPoly h` is the table of the low-degree
  encoding `ldEnc h`; it is faithful because the encoding is multilinear and `1 ≤ d`
  (`toMv_coeffTable`), and its value at `u` is the pairing `h . ind_m(u)` (`ancPoly_eval`).
* **The cut.** Item 1 concludes on its own cut, the two ancilla halves adjacent; the conjugated
  Pauli measurement lives on Alice's physical register. `outerUnVec` is the inverse of `outerVec`,
  so `physAux aux` is the product state read on the physical cut, and item 1's distance is the same
  number there (`norm_evec_physSwap_sub_physAux`).
* **Bob's half is Alice's at the mirror, relative to the same state.** The mirror's product state
  is this one's with the parties exchanged (`swapVec`), and so is its swapped physical state
  (`mirror_physSwap_mulVec`). The mirror's objects are spelled with `M.mirror.Ea` where Bob's are
  spelled with `M.Eb`; the two are definitionally equal but not reducibly so, so instance search
  cannot mix them. The rule that worked for item 1 works again: the state is named once, in the
  mirror's own spelling, and related to this one's by an equation.

## Constants

`deltaLegs` bounds each leg of `eq:qld-unitary-5`'s triangle, `11 * deltaLegs` the display (the
Lean triangle's `11` for the paper's `9`). Item 2's bound is
`deltaItemTwo = 2 (11 deltaLegs + md/q + 2 sqrt η)` for item 1's bound `η`; at `η = etaItemOne`,
which is `O(sqrt delta_S)`, that is `O(delta_S^{1/4} + md/q)`, the paper's `delta_qld`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

section Encoding

/-- **The low-degree encoding `g_h` of cube data `h`**, as a coefficient table of individual
degree at most `d`. It is multilinear, so this is faithful as soon as `1 ≤ d`. -/
def ancPoly (h : Anc F m) : LowIndDegPoly (F := F) (m := m) (d := d) :=
  fun e => (ldEnc h).coeff (expFinsupp e)

end Encoding

/-! ## Generic facts the threading uses -/

section Generic

end Generic

/-! ## The product state, read on the physical cut -/

section Outer

variable {A B T T' : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']

/-- **A state on item 1's cut, read on the physical one.** The inverse of `outerVec`. -/
def outerUnVec (χ : (A × B) × (T × T') → ℂ) : (A × T) × (B × T') → ℂ :=
  χ ∘ outerPairEquiv (A := A) (B := B) (T := T) (T' := T')

variable {n : Type*} [Fintype n] [DecidableEq n]

end Outer

/-! ## The objects item 2 is about -/

section Physical

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

set_option synthInstance.maxSize 1000

/-- **The constant the three legs of `eq:qld-unitary-5` share**: item 1 of
`lem:qld-exact-paulis` (`inconsistency_mTilde_le`) and the game's two consistencies at `86 ε`,
added so that one number bounds all three. -/
def deltaLegs (δ ε : ℝ) (m d q : ℕ) : ℝ :=
  δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / q) + 86 * ε

/-- The constant of item 2: `eq:qld-unitary-5`'s `11 δ'`, Schwartz--Zippel's `md/q`, and the
transport across item 1, which costs twice the square root of item 1's bound. -/
def deltaItemTwo (δ ε : ℝ) (m d q : ℕ) (η : ℝ) : ℝ :=
  2 * (11 * deltaLegs δ ε m d q + (m : ℝ) * d / q + 2 * Real.sqrt η)

/-- **Item 1's bound**, named so that the joint statement fits. -/
def etaItemOne (δ ε : ℝ) (m d q : ℕ) : ℝ :=
  2 - 2 * Real.sqrt (1 - (2 * Real.sqrt (deltaSelfCons δ ε m d q) + 2 * deltaSelfCons δ ε m d q))

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **Alice's total Pauli measurement** `M^{(Pauli,W)}_h`, its outcomes the cube data `h` the
answer reports, extended by the identity to her physical register `A A' Ea A''`. An answer that is
not a well-formed Pauli answer is read as `h = 0` by `rdPauliVec`; the paper assumes well-formed
answers, and this is a relabelling of outcomes, not a restriction. -/
def alicePauli (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  aOp (aOp (aOp ((((MA (.pauli W)).map rdPauliVec).mats h).val)))

/-- **Bob's**, on `B B' Eb B''`. -/
def bobPauli (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  aOp (aOp (aOp ((((MB (.pauli W)).map rdPauliVec).mats h).val)))

/-- **Alice's conjugated Pauli measurement** `V_A M^{(Pauli,W)}_h V_A^dagger`. -/
def aliceConjPauli (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.aliceSwap * M.alicePauli W h * M.aliceSwapᴴ

/-- **Bob's** `V_B M^{(Pauli,W)}_h V_B^dagger`. -/
def bobConjPauli (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.bobSwap * M.bobPauli W h * M.bobSwapᴴ

/-- **The honest Pauli projector `tau^W_h` on Alice's half of the pair**, `Id ⊗ tau^W_h`. -/
def aliceTau (W : Bas) (h : Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  bOp (proj (weylOf W) h)

/-- **And on Bob's.** -/
def bobTau (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  bOp (proj (weylOf W) h)

/-! ### The product state of item 1 -/

/-- **The product state `|aux> ⊗ |EPR_q>^M` of item 1, read on the physical cut**: each party's
half of the pair back at the end of its own register. -/
def physAux (aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ) :
    ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ :=
  outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux)

/-! ### Bob's half, through the mirror -/

/-! ### The joint lemma -/

end MirrorSimul

end Physical

end MIPRE.QLD

end


