-- Prove2me | Definitions.Def_MIPRE_Background_QLD_PaddedStrategy
-- name    : MIPRE_Background_QLD_PaddedStrategy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:24:11.085006+00:00
-- url     : https://prove2.me/theorems/074fc69d-0072-4b91-b2b5-05e03861fac1
-- title:
--   Definitions of PaddedStrategy: The padded strategy for the seeded low individual degree test Stage 4 of the Pauli basis test's analysis…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.PaddedStrategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The padded strategy for the seeded low individual degree test. Stage 4 of the Pauli basis test's analysis (`lem:qld-global-setup`, `lem:qld-global-success`) assembles the padded point and line measurements of `lem:qld-padded-points` and `lem:qld-padded-lines` into a strategy for the seeded test `clGame` at parameters `(q, 4m, d, 1)`, and shows that it succeeds with probability `1 - O(δ_combine + δ_Q + md/q)`. This file defines the strategy and bounds its conditional failure at each of the seeded test's question pairs by an agreement defect of the measurements it is built from; the averages…
--
--   **Definitions** (16): `MIPRE.QLD.alineAns` (The answer a padded line outcome is read as, at an axis-parallel line question: the polynomial resized to degree `d`.); `MIPRE.QLD.dlineAns` (The answer a padded line outcome is read as, at a diagonal line question: the polynomial resized to degree `4 m d`, which loses nothing…); `MIPRE.QLD.lineAns` (The answer map of a line type.); `MIPRE.QLD.lineDir` (The direction of the line of type `ty` a seed and raw direction describe; `0` for the point type.); `MIPRE.QLD.lineMeas` (**The line measurement of the padded strategy**: the padded line POVM at the data `⟨u₀, s, raw⟩`, averaged over the raw directions in `S`.); `MIPRE.QLD.lineQ` (The line question of type `ty` the sample `(u, s, raw)` generates, as the seeded test computes it.); `MIPRE.QLD.lineTau` (The parameter of the sample's point on the line it generates.); `MIPRE.QLD.padComb` (The combining coefficients' reading of a pair outcome at a padded point: `(a, b) ↦ α a + β b`.); `MIPRE.QLD.padLinePOVM` (`padLineMats`, bundled as a POVM.); `MIPRE.QLD.padPt` (**The padded point measurement**: the sandwich read through the combining coefficients and extended by the identity to the coefficients'…); `MIPRE.QLD.padPtPair` (The sandwich `M^X_a M^Z_b M^X_a` of the hatted point measurements at the `X` and `Z` blocks of a padded point, as a POVM with outcomes the…); `MIPRE.QLD.padStrat` (**The padded strategy** of one player, as a family of POVMs indexed by the seeded test's questions at `(q, 4m, d, 1)`.); and -10 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `padLinePOVM_mats`, `padPtPair_mats`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.PaddedStrategy` (`MIPRE/Background/QLD/PaddedStrategy.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 75 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/PaddedStrategy.lean; blueprint lem:qld-global-setup

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PaddedStrategy.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
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
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_bornProb
import Theorems.Thm_MIPRE_QLD_isPVM_hatMats
import Theorems.Thm_MIPRE_QLD_posSemidef_padLineMats
import Theorems.Thm_MIPRE_QLD_sum_padLineMats

/-!
# The padded strategy for the seeded low individual degree test

Stage 4 of the Pauli basis test's analysis (`lem:qld-global-setup`, `lem:qld-global-success`)
assembles the padded point and line measurements of `lem:qld-padded-points` and
`lem:qld-padded-lines` into a strategy for the seeded test `clGame` at parameters
`(q, 4m, d, 1)`, and shows that it succeeds with probability `1 - O(δ_combine + δ_Q + md/q)`.
This file defines the strategy and bounds its conditional failure at each of the seeded test's
question pairs by an agreement defect of the measurements it is built from; the averages over the
verifier's samples, and the value bound, are in `PaddedValue.lean`.

## The registers, and why the strategy is a family of POVMs

The strategy lives on the registers `(dA × Anc F m) × (F × F)` of `extHat ψ`: the player's own
space, the expansion's ancilla, and the combining coefficients' ancilla that `lem:qld-padded-points`
dilates its sandwich with. Its point measurement is the *sandwich* `M^X_a M^Z_b M^X_a` of the
hatted point measurements, coarse-grained along `(a, b) ↦ α a + β b`, extended by the identity to
the last register; its line measurements are the padded line measurements `padLineMats`. Both are
POVMs and neither is projective, so the strategy is a family of POVMs, and one Naimark dilation at
the end (`clSoundness_ldc_one_deltaCL_of_povm`) makes it the projective strategy the soundness
theorem takes. The dilated point measurement of `lem:qld-padded-points` is not used: on the
extended state the Born rule sees only compressions (`bornProb_extVec2`), so every bound proved
for it is a bound for the sandwich.

## A function of the question

The seeded test asks for a measurement per *question*, while `padLineMats` is indexed by the
*data* `⟨pt, s, raw⟩` a sample generates the question from. A line question carries the canonical
base point `u₀` of the line, the seed, and for a diagonal line the truncated direction `v'`; the
strategy answers it with the padded line measurement at the data `⟨u₀, s, raw⟩`, **averaged over
the raw directions that produce the question** (`rawFiber`). Two things make this the right
choice. The decider reads the answer polynomial at the parameter of the sampled point relative to
`u₀`, and moving the data's point to the sampled point along the line does not change the padded
line measurement (`pasteLine_subPair_padShift`), so what the decider reads is `padLineMats` at the
sample's own data, coarse-grained by evaluation at the sample's point --- exactly the quantity
`lem:qld-padded-lines` controls (`lineMeas_map_eval_mats`). And the sample distribution averages
uniformly over the raw direction, so by linearity of the Born rule the strategy's failure at a
question is the average of the per-sample quantities.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}

/-! ## The padded point measurement -/

/-- The sandwich `M^X_a M^Z_b M^X_a` of the hatted point measurements at the `X` and `Z` blocks of
a padded point, as a POVM with outcomes the pairs `(a, b)`. -/
def padPtPair {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    POVM (F × F) (dA × Anc F m) :=
  sandPOVM (isPVM_hatMats hM .X (xBlk u)) (isPVM_hatMats hM .Z (zBlk u))

@[simp] theorem padPtPair_mats {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) (r : F × F) :
    (((padPtPair hM u).mats r).val) = sand (hatMats M .X (xBlk u)) (hatMats M .Z (zBlk u)) r :=
  rfl

/-- The combining coefficients' reading of a pair outcome at a padded point:
`(a, b) ↦ α a + β b`. -/
def padComb (u : Point F (4 * m)) (r : F × F) : F := alph u * r.1 + bet u * r.2

/-- **The padded point measurement**: the sandwich read through the combining coefficients and
extended by the identity to the coefficients' ancilla, the strategy's answer to a point question
as a POVM with outcomes in `F`. -/
def padPt {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    POVM F ((dA × Anc F m) × (F × F)) :=
  ((padPtPair hM u).aOp).map (padComb u)

/-! ## The padded line measurements, as POVMs -/

variable (hm4 : 4 * m ∣ Fintype.card F)

/-- `padLineMats`, bundled as a POVM. -/
def padLinePOVM (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (P : LPData F (4 * m)) : POVM (LinePoly F (m * d + 1)) ((dA × Anc F m) × (F × F)) :=
  POVM.ofPosSemidef (padLineMats hm4 ty PX PZ M P) (posSemidef_padLineMats hm4 ty PX PZ hM P)
    (sum_padLineMats hm4 ty PX PZ hM P)

@[simp] theorem padLinePOVM_mats (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (P : LPData F (4 * m)) (f : LinePoly F (m * d + 1)) :
    (((padLinePOVM hm4 ty PX PZ hM P).mats f).val) = padLineMats hm4 ty PX PZ M P f := rfl

variable (hm)

/-- The presentation of a line type on side `W`: the diagonal one for `dline`, the axis-parallel
one otherwise. -/
def presOf (ty : CL.Ty) (W : Bas) : LinePres F m hm W :=
  match ty with
  | .dline => dPres hm W
  | _ => aPres hm W

/-- **The line measurement of the padded strategy**: the padded line POVM at the data
`⟨u₀, s, raw⟩`, averaged over the raw directions in `S`. -/
def lineMeas (ty : CL.Ty) {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u₀ : Point F (4 * m)) (s : F)
    (S : Finset (Point F (4 * m))) : POVM (LinePoly F (m * d + 1)) ((dA × Anc F m) × (F × F)) :=
  POVM.avgOn S (fun raw => padLinePOVM hm4 ty (presOf hm ty .X) (presOf hm ty .Z) hM ⟨u₀, s, raw⟩) 0

/-- The raw directions a sample with seed `s` can carry so that its diagonal question shows the
truncated direction `v'`. -/
def rawFiber (s : F) (v' : Point F (4 * m)) : Finset (Point F (4 * m)) :=
  univ.filter fun raw => zeroBelow (chi hm4 s) raw = v'

/-! ## The questions of a sample -/

/-- The direction of the line of type `ty` a seed and raw direction describe; `0` for the point
type. -/
def lineDir (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) : Point F (4 * m) :=
  match ty with
  | .point => 0
  | .aline => Pi.single (chi hm4 s) 1
  | .dline => zeroBelow (chi hm4 s) raw

/-- The raw directions the strategy averages over at the line question of type `ty` a sample with
seed `s` and raw direction `raw` generates: all of them for an axis-parallel line, the fibre of
the truncated direction for a diagonal one. -/
def rawSet (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) : Finset (Point F (4 * m)) :=
  match ty with
  | .dline => rawFiber hm4 s (zeroBelow (chi hm4 s) raw)
  | _ => univ

/-- The line question of type `ty` the sample `(u, s, raw)` generates, as the seeded test
computes it. -/
def lineQ (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    CL.Question F (4 * m) :=
  (⟨ty, ty, u, s, raw⟩ : CL.Sample F (4 * m)).question hm4 ty

/-- The parameter of the sample's point on the line it generates. -/
def lineTau (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) : F :=
  CL.lineParam (CL.rep (lineDir hm4 ty s raw) u) (lineDir hm4 ty s raw) u

/-! ## The strategy -/

/-- The answer a padded line outcome is read as, at an axis-parallel line question: the polynomial
resized to degree `d`. On the support of a legally supported strategy this loses nothing
(`padLineMats_aline_eq_zero_of_not_degLE`). -/
def alineAns (f : LinePoly F (m * d + 1)) : CL.Answer F (4 * m) d 1 :=
  .apolys fun _ => padLine d f

/-- The answer a padded line outcome is read as, at a diagonal line question: the polynomial
resized to degree `4 m d`, which loses nothing since `m d + 1 ≤ 4 m d`. -/
def dlineAns (f : LinePoly F (m * d + 1)) : CL.Answer F (4 * m) d 1 :=
  .dpolys fun _ => padLine (4 * m * d) f

/-- The answer map of a line type. -/
def lineAns (ty : CL.Ty) (f : LinePoly F (m * d + 1)) : CL.Answer F (4 * m) d 1 :=
  match ty with
  | .dline => dlineAns f
  | _ => alineAns f

/-- The value a line answer takes at the parameter `t`; a point answer reads as `0`. -/
def rdEval (t : F) : CL.Answer F (4 * m) d 1 → F
  | .apolys p => (p 0).eval t
  | .dpolys p => (p 0).eval t
  | _ => 0

/-- **The padded strategy** of one player, as a family of POVMs indexed by the seeded test's
questions at `(q, 4m, d, 1)`. -/
def padStrat {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) :
    CL.Question F (4 * m) → POVM (CL.Answer F (4 * m) d 1) ((dA × Anc F m) × (F × F))
  | .point u => (padPt hM u).map fun a => .values fun _ => a
  | .aline u₀ s => (lineMeas hm hm4 .aline hM u₀ s univ).map (lineAns .aline)
  | .dline u₀ s v' => (lineMeas hm hm4 .dline hM u₀ s (rawFiber hm4 s v')).map (lineAns .dline)

/-! ## The support of the strategy's answers -/

/-! ## The line measurement read at the sampled point

`sum_filter_padLineMats` reads the padded line measurement at the parameter of a point of the
padded line as the pasted line measurement, at the data's *own* point, coarse-grained by the
combining map at the *shifted* point. The strategy's line data carries the canonical base point of
the line, while `lem:qld-padded-lines` is stated at the sample's point; the two are reconciled by
the invariance of the pasted line measurement under moving the padded point along the padded
line, which holds because each block of the padded point either moves along its own subline or
does not move at all (`xBlk_dir_sub`, `zBlk_dir_sub`). -/

section ShiftInvariance

variable {dB : Type} [Fintype dB] [DecidableEq dB] {M : Question F m → POVM (Answer F m d) dB}

end ShiftInvariance

/-! ## The conditional failures of the strategy, question pair by question pair -/

section Fail

variable {dB : Type} [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)

end Fail

/-! ## Polynomial separation

Two distinct line polynomials of degree at most `n` agree at at most `n` parameters
(`card_agree_linePoly_le`), so the disagreement of two polynomial-valued measurements is at most
their disagreement when both are read at a uniformly random parameter, plus `n / q`. This is the
paper's argument for the identical-line subtest. -/

section Separation

variable {dA' dB' : Type*} [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB']

end Separation

end MIPRE.QLD

end


