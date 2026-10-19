-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Mirror
-- name    : MIPRE_Background_QLD_Mirror
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:44:31.063288+00:00
-- url     : https://prove2.me/theorems/f8445495-c327-47d4-9a77-9b5e8064346c
-- title:
--   Definitions of Mirror: The second cut, and why it is a second `SimulPair` `lem:qld-pauli-selfcons` and `lem:qld-swap` both compare *Alice's*…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Mirror` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The second cut, and why it is a second `SimulPair`. `lem:qld-pauli-selfcons` and `lem:qld-swap` both compare *Alice's* exact Pauli object with *Bob's*. Everything merged so far builds Alice's, from `SimulPair.SA`. This file supplies Bob's.
--
--   **Definitions** (11): `MIPRE.QLD.MirrorSimul` (**One physical state, read along both of the paper's cuts.** The fields come in two groups of the same shape, one per cut: the state, its…); `MIPRE.QLD.MirrorSimul.aliceMTilde` (**Alice's exact Pauli measurement at an arbitrary probe**, on her physical register `A A' Ea A''` --- named here only so that the two sit…); `MIPRE.QLD.MirrorSimul.bobMTilde` (**Bob's exact Pauli measurement at an arbitrary probe**, on his physical register `B B' Eb B''`.); `MIPRE.QLD.MirrorSimul.bobSwap` (**Bob's swap unitary** `V_B`, on the same register.); `MIPRE.QLD.MirrorSimul.mirror` (**The mirror of a `MirrorSimul` is a `MirrorSimul`**, at the swapped strategy with the two players' measurements exchanged and the two cuts…); `MIPRE.QLD.MirrorSimul.physVec` (**The state on all six registers, grouped as the two parties physically hold them**: Alice's `A A' Ea A''` against Bob's `B B' Eb B''`.); `MIPRE.QLD.MirrorSimul.selfConsGap` (**The two exact Pauli measurements lie on opposite sides of the physical cut.** The content is the typing: this expression is well formed,…); `MIPRE.QLD.MirrorSimul.toFirst` (**The first cut**, as a `SimulPair`: exactly the data stages 4a--4c deliver.); `MIPRE.QLD.MirrorSimul.toSecond` (**The second cut**, as a `SimulPair` at the swapped strategy.); `MIPRE.sndExtVec` (**A state with a further state appended to the second party.**); `MIPRE.sndPairEquiv` (The regrouping onto it.).
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `mirror_SA`, `mirror_toFirst`, `mirror_toSecond`, `mirror_Φ`, `toFirst_SA`, `toFirst_Φ`, `toSecond_SA`, `toSecond_Φ`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Mirror` (`MIPRE/Background/QLD/Mirror.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 96 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Mirror.lean; blueprint lem:qld-pauli-selfcons

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Mirror.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_QLD_mirrorVec_mirrorVec

/-!
# The second cut, and why it is a second `SimulPair`

`lem:qld-pauli-selfcons` and `lem:qld-swap` both compare *Alice's* exact Pauli object with *Bob's*.
Everything merged so far builds Alice's, from `SimulPair.SA`. This file supplies Bob's.

## Why `SB` is not it

The paper's `lem:qld-4-7` gives a pair measurement `S-hat` on `A A'` **and** one on `B B'`, with

* `(S-hat_{[eval_u = a]})_{A A'} ~ (M-hat^{(Point,W),u}_a)_{B A''}`,
* `(S-hat_{[eval_u = a]})_{B B'} ~ (M-hat^{(Point,W),u}_a)_{A B''}`,

and it is the second that Bob's swap unitary `V_B` conjugates by, because `V_B` acts on `B B' B''`.
`SimulPair.SB` is typed on `(dB x Anc F m) x EB`, and that `Anc F m` is the half of the *first*
pair that `hatVec` gives Bob --- the register the paper calls `A''`. So `SB` sits on `B A''`: it is
the second party of the *first* cut, a legitimate object (it is the symmetric equivalent
`M-hat_{A A'} ~ S-hat_{B A''}` of the first display) but not the one `V_B` is built from.

## What it is instead

`qld-commutation.tex` (`sec:expanding`, "Partitioning the registers, and symmetries") partitions
the six registers two ways --- `A A'` against `B A''`, and `B B'` against `A B''` --- and records
that every bipartite relation derived for one holds for the other with the registers changed. The
second partition is therefore not data of a new kind: it is the same kind as the first, so **the
mirror of a `SimulPair` is a `SimulPair`** --- at the swapped strategy, with the two players'
measurements exchanged, over the other reading of one physical state.

`MirrorSimul` is that pair of readings, and `toFirst` and `toSecond` are the two views. Every lemma
already proved about `SimulPair` --- `mVec`, `mTildeAnc`, `swapA`, `swapU_conj_mTildeAnc`,
`inconsistency_mTilde_pauli_le_of_win` --- then applies to Bob by instantiating it at `toSecond`,
with no mirror lemma to prove. That is the whole point of the shape.

## The state, and where the second pair goes

Each view carries the state its own cut sees: `Phi` on `(dA x Anc) x Ea` against
`(dB x Anc) x Eb`, which is exactly what stages 4a--4c produce and has only the pair `A' A''` in
it, and `Phi'` the same for `B' B''` with the players exchanged. The physical state is either of
them with the *other* pair appended, one half to each party, which is `expVec _ epr`; the field
`hmirror` says the two appendings agree. The appended halves are the outermost factor of each party
register, so a party register reads

```
((X x Anc) x E) x Anc
```

and `mTildeAnc`, which appends its Pauli register at the end of the register its pair measurement
lives on, lands on Alice's **physical** register `A A' Ea A''` with nothing to reindex --- and
`toSecond`'s lands on Bob's, `B B' Eb B''`. `physVec` is the state on those two, so `xSqNorm` of
the two exact Pauli objects against it is well formed. It is not well formed for any two objects
built inside one `SimulPair`, which is the concrete reason both cuts are needed at once.
-/

noncomputable section

universe u

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Appending a state to one party

The physical state is the first cut's state with the second entangled pair tensored on. Read along
the cut `mTilde` needs --- the one that has already moved `A''` to Alice --- **both** halves of
that pair are on Bob's side, so the appending is one-sided, and `expVec`, which puts one register
on each party, does not directly cover it. It does cover it with a trivial register on the first
party, which is all `sndExtVec` is. -/

section SndExt

variable {R S C : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C]

/-- **A state with a further state appended to the second party.** -/
def sndExtVec (ψ : R × S → ℂ) (χ : C → ℂ) : R × (S × C) → ℂ :=
  fun p => ψ (p.1, p.2.1) * χ p.2.2

/-! ## Bob's physical register

Bob's own space and padding, with the appended pair's two halves put where the physical grouping
wants them: the half his own cut gave him beside his space, the half pulled back from Alice
outermost, which is where `mTilde` writes the Weyl operator. -/

variable {T T2 : Type*} [Fintype T] [DecidableEq T] [Fintype T2] [DecidableEq T2]

/-- The regrouping onto it. -/
def sndPairEquiv : ((S × C) × (T × T2)) ≃ (((S × T2) × C) × T) where
  toFun p := (((p.1.1, p.2.2), p.1.2), p.2.1)
  invFun q := ((q.1.1.1, q.1.2), (q.2, q.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

end SndExt

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **One physical state, read along both of the paper's cuts.**

The fields come in two groups of the same shape, one per cut: the state, its reduction to the
expanded state, the two parties' pair measurements and the two consistencies of `lem:qld-4-7` and
their symmetric equivalents. The second group is the first with the players exchanged, which is
what `sec:expanding`'s symmetry paragraph licenses. `hmirror` is the only field that is not one of
those two groups: it says the two cuts read one state. -/
structure MirrorSimul (ψ : dA × dB → ℂ) (MA : Question F m → POVM (Answer F m d) dA)
    (MB : Question F m → POVM (Answer F m d) dB) (δ : ℝ) where
  /-- Alice's padding beyond the expansion. -/
  Ea : Type u
  [instFintypeEa : Fintype Ea]
  [instDecEqEa : DecidableEq Ea]
  /-- Bob's padding beyond the expansion. -/
  Eb : Type u
  [instFintypeEb : Fintype Eb]
  [instDecEqEb : DecidableEq Eb]
  /-- The state along the first cut, `A A' Ea` against `B A'' Eb`. -/
  Φ : ((dA × Anc F m) × Ea) × ((dB × Anc F m) × Eb) → ℂ
  Φ_unit : star Φ ⬝ᵥ Φ = 1
  Φ_reduced : ∀ (X : Matrix (dA × Anc F m) (dA × Anc F m) ℂ)
    (Y : Matrix (dB × Anc F m) (dB × Anc F m) ℂ),
    bornProb Φ (aOp X) (aOp Y) = bornProb (hatVec (F := F) (m := m) ψ) X Y
  /-- Alice's pair measurement, on `A A'`. -/
  SA : POVM (PolyPair F m d) ((dA × Anc F m) × Ea)
  SA_proj : IsPVM fun p => ((SA.mats p).val)
  /-- The first cut's second party's pair measurement, on `B A''`. -/
  SB : POVM (PolyPair F m d) ((dB × Anc F m) × Eb)
  SB_proj : IsPVM fun p => ((SB.mats p).val)
  consA : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ (fun u => evalMarg SA W u)
    (fun u => (hatPtPOVM MB W u).aOp) ≤ δ
  consB : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ (fun u => (hatPtPOVM MA W u).aOp)
    (fun u => evalMarg SB W u) ≤ δ
  /-- The state along the second cut, `B B' Eb` against `A B'' Ea`. -/
  Φ' : ((dB × Anc F m) × Eb) × ((dA × Anc F m) × Ea) → ℂ
  Φ'_unit : star Φ' ⬝ᵥ Φ' = 1
  Φ'_reduced : ∀ (X : Matrix (dB × Anc F m) (dB × Anc F m) ℂ)
    (Y : Matrix (dA × Anc F m) (dA × Anc F m) ℂ),
    bornProb Φ' (aOp X) (aOp Y) = bornProb (hatVec (F := F) (m := m) (ψ ∘ Prod.swap)) X Y
  /-- Bob's pair measurement, on `B B'` --- the one `V_B` is built from. -/
  SA' : POVM (PolyPair F m d) ((dB × Anc F m) × Eb)
  SA'_proj : IsPVM fun p => ((SA'.mats p).val)
  /-- The second cut's second party's pair measurement, on `A B''`. -/
  SB' : POVM (PolyPair F m d) ((dA × Anc F m) × Ea)
  SB'_proj : IsPVM fun p => ((SB'.mats p).val)
  consA' : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ' (fun u => evalMarg SA' W u)
    (fun u => (hatPtPOVM MA W u).aOp) ≤ δ
  consB' : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ' (fun u => (hatPtPOVM MB W u).aOp)
    (fun u => evalMarg SB' W u) ≤ δ
  /-- **The two cuts read one state.** Appending the pair the other cut carries --- one half to
  each party, which is what `expVec _ epr` does --- makes both into the same state on all six
  registers, up to the change of reading `mirrorVec`. -/
  hmirror : expVec Φ' (epr (F := F) (n := Fin m → Bool))
    = mirrorVec (expVec Φ (epr (F := F) (n := Fin m → Bool)))

attribute [instance] MIPRE.QLD.MirrorSimul.instFintypeEa MIPRE.QLD.MirrorSimul.instDecEqEa MIPRE.QLD.MirrorSimul.instFintypeEb MIPRE.QLD.MirrorSimul.instDecEqEb

namespace MirrorSimul

variable {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

variable (M : MirrorSimul ψ MA MB δ)

/- The same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-- **The first cut**, as a `SimulPair`: exactly the data stages 4a--4c deliver. -/
def toFirst : SimulPair ψ MA MB δ where
  EA := M.Ea
  EB := M.Eb
  Φ := M.Φ
  Φ_unit := M.Φ_unit
  Φ_reduced := M.Φ_reduced
  SA := M.SA
  SA_proj := M.SA_proj
  SB := M.SB
  SB_proj := M.SB_proj
  consA := M.consA
  consB := M.consB

/-- **The second cut**, as a `SimulPair` at the swapped strategy. Its `SA` is Bob's measurement on
`B B'`, so every construction the merged files make from `SimulPair.SA` --- `mTildeAnc` and `swapA`
above all --- is Bob's when instantiated here. -/
def toSecond : SimulPair (ψ ∘ Prod.swap) MB MA δ where
  EA := M.Eb
  EB := M.Ea
  Φ := M.Φ'
  Φ_unit := M.Φ'_unit
  Φ_reduced := M.Φ'_reduced
  SA := M.SA'
  SA_proj := M.SA'_proj
  SB := M.SB'
  SB_proj := M.SB'_proj
  consA := M.consA'
  consB := M.consB'

@[simp] theorem toFirst_Φ : M.toFirst.Φ = M.Φ := rfl

@[simp] theorem toSecond_Φ : M.toSecond.Φ = M.Φ' := rfl

@[simp] theorem toFirst_SA : M.toFirst.SA = M.SA := rfl

@[simp] theorem toSecond_SA : M.toSecond.SA = M.SA' := rfl

/-- **The mirror of a `MirrorSimul` is a `MirrorSimul`**, at the swapped strategy with the two
players' measurements exchanged and the two cuts exchanged. `toFirst` and `toSecond` give Bob's
objects as a `SimulPair`, which is enough for everything stated on one cut's state; this gives
Bob's objects on the *physical* state, which is what the chain's last displays compare. So every
lemma about the six-register cut becomes Bob's by instantiating here, with no mirror lemma to
prove --- the same economy `toSecond` buys one level down. The field saying the two cuts read one
state survives because `mirrorVec` is an involution (`mirrorVec_mirrorVec`). -/
def mirror : MirrorSimul (ψ ∘ Prod.swap) MB MA δ where
  Ea := M.Eb
  Eb := M.Ea
  Φ := M.Φ'
  Φ_unit := M.Φ'_unit
  Φ_reduced := M.Φ'_reduced
  SA := M.SA'
  SA_proj := M.SA'_proj
  SB := M.SB'
  SB_proj := M.SB'_proj
  consA := M.consA'
  consB := M.consB'
  Φ' := M.Φ
  Φ'_unit := M.Φ_unit
  Φ'_reduced := M.Φ_reduced
  SA' := M.SA
  SA'_proj := M.SA_proj
  SB' := M.SB
  SB'_proj := M.SB_proj
  consA' := M.consA
  consB' := M.consB
  hmirror := by rw [M.hmirror, mirrorVec_mirrorVec]

@[simp] theorem mirror_toFirst : M.mirror.toFirst = M.toSecond := rfl

@[simp] theorem mirror_toSecond : M.mirror.toSecond = M.toFirst := rfl

@[simp] theorem mirror_Φ : M.mirror.Φ = M.Φ' := rfl

@[simp] theorem mirror_SA : M.mirror.SA = M.SA' := rfl

/-! ## The physical state -/

/-- **The state on all six registers, grouped as the two parties physically hold them**: Alice's
`A A' Ea A''` against Bob's `B B' Eb B''`. It is the first cut's state with the second pair
appended and each party's far half pulled home. -/
def physVec : ((((dA × Anc F m) × M.Ea) × Anc F m)) × ((((dB × Anc F m) × M.Eb) × Anc F m)) → ℂ :=
  pairSwapVec (expVec M.Φ (epr (F := F) (n := Fin m → Bool)))

/-! ## Bob's objects, for free

Nothing below has a proof of its own: each is a merged lemma about `SimulPair` instantiated at
`toSecond`. They are stated because the typing is the point --- each of Bob's objects lands on the
second party of `physVec`, where Alice's lands on the first. -/

section Bob

/-- **Bob's exact Pauli measurement at an arbitrary probe**, on his physical register
`B B' Eb B''`. -/
def bobMTilde (W : Bas) (v : Anc F m) (a : F) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.toSecond.mTildeAnc W v a

/-- **Bob's swap unitary** `V_B`, on the same register. -/
def bobSwap : Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.toSecond.swapA

/-- **Alice's exact Pauli measurement at an arbitrary probe**, on her physical register
`A A' Ea A''` --- named here only so that the two sit side by side. -/
def aliceMTilde (W : Bas) (v : Anc F m) (a : F) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.toFirst.mTildeAnc W v a

/-- **The two exact Pauli measurements lie on opposite sides of the physical cut.** The content is
the typing: this expression is well formed, and no expression comparing two objects built inside a
single `SimulPair` is. It is the left-hand side of `lem:qld-pauli-selfcons`. -/
def selfConsGap (W : Bas) (v : Anc F m) (a : F) : ℝ :=
  xSqNorm M.physVec (M.aliceMTilde W v a) (M.bobMTilde W v a)

end Bob

end MirrorSimul

end MIPRE.QLD

end


