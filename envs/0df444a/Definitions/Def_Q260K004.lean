-- Prove2me | Definitions.Def_Q260K004
-- name    : Q260K004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:34:25.351434+00:00
-- url     : https://prove2.me/theorems/e9149629-ec22-49e7-a352-6d632a1e6749
-- title:
--   Definitions bundle Q260K004 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 270 declarations of OpenAI's Lean: 121 definitions, 7 inductive types or structures, 5 instances and 137 theorems. The definitions and types are `OAI.KadisonKastler.BimoduleMean`, `OAI.KadisonKastler.BlockAlgebraDecomposition`, `OAI.KadisonKastler.BorelCommonModel`, `OAI.KadisonKastler.CentralPairCommonSource`, `OAI.KadisonKastler.CommonRankSpace`, `OAI.KadisonKastler.CompletelyBoundedBy`, `OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap`, `OAI.KadisonKastler.CompletelyIsometric`, `OAI.KadisonKastler.CountableStrongTests`, `OAI.KadisonKastler.CuntzFamily`, `OAI.KadisonKastler.CuntzFamily.assemble`, `OAI.KadisonKastler.CuntzFamily.changeBasis`, `OAI.KadisonKastler.CuntzFamily.instPartialOrderContinuousLinearMapComplexId`, `OAI.KadisonKastler.CuntzFamily.matrix`, `OAI.KadisonKastler.CuntzFamily.matrixEquiv`, `OAI.KadisonKastler.CuntzFamily.matrixHom`, `OAI.KadisonKastler.CuntzFamily.matrixUnits`, `OAI.KadisonKastler.CuntzFamily.upperRightLinearMap`, `OAI.KadisonKastler.FullMatrixCorner.amplificationGapOrder`, `OAI.KadisonKastler.FullMatrixCorner.compressionOperatorOrder`, `OAI.KadisonKastler.FullMatrixCorner.finiteBlockOperatorOrder`, `OAI.KadisonKastler.FullMatrixCorner.signedCStarRepresentation`, `OAI.KadisonKastler.MeasuredHilbertStratum`, `OAI.KadisonKastler.MeasuredHilbertStratum.space`, `OAI.KadisonKastler.OperatorFieldDecomposition`, `OAI.KadisonKastler.PreservesProjectionNest`, `OAI.KadisonKastler.ProjectionStrataSpace`, `OAI.KadisonKastler.RandomWalkPath`, `OAI.KadisonKastler.RegularCoreHilbert`, `OAI.KadisonKastler.RepresentsBlockOperators`, `OAI.KadisonKastler.RepresentsOperatorField`, `OAI.KadisonKastler.ShiftBoundarySpace`, `OAI.KadisonKastler.SignedPermutation`, `OAI.KadisonKastler.TwoRatioSite`, `OAI.KadisonKastler.boundaryBoundedOrder`, `OAI.KadisonKastler.boundaryTranslate`, `OAI.KadisonKastler.boundedUnitaryFamily`, `OAI.KadisonKastler.commonModelProjection`, `OAI.KadisonKastler.commonRankBasis`, `OAI.KadisonKastler.concreteCenter` and 88 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AmenableEmbedding`, `KadisonKastler_AmplificationGap`, `KadisonKastler_BoundaryBoundedTransport`, `KadisonKastler_BoundaryImprovement`, `KadisonKastler_CanonicalAmplificationGap`, `KadisonKastler_CenterAlgebra`, `KadisonKastler_CentralPairCommonSource`, `KadisonKastler_Column`, `KadisonKastler_CommonRankCoordinates`, `KadisonKastler_CommonRankSourceModel`, `KadisonKastler_CompleteLinearLimits`, `KadisonKastler_CompletelyBounded`, `KadisonKastler_CornerStateConjugation`, `KadisonKastler_CornerUnitaryExtension`, `KadisonKastler_CountableAmplificationNormal`, `KadisonKastler_CountableConjugacyAssembly`, `KadisonKastler_CountableRandomWalkLaw`, `KadisonKastler_CountableSpatialTensor`, `KadisonKastler_CountableStrongMembership`, `KadisonKastler_CuntzChangeOfBasis`, `KadisonKastler_CuntzMatrices`, `KadisonKastler_DemodulatedPoisson`, `KadisonKastler_DirectIntegralConjugacy`, `KadisonKastler_FiniteBlockCompression`, `KadisonKastler_FiniteBlockExtension`, `KadisonKastler_FiniteCornerGroups`, `KadisonKastler_FiniteCornerRefinement`, `KadisonKastler_FiniteMatrixBounds`, `KadisonKastler_FiniteRowAverages`, `KadisonKastler_GraphReciprocal`, `KadisonKastler_HilbertPairRepresentation`, `KadisonKastler_MatrixAveraging`, `KadisonKastler_MatrixChainEmbedding`, `KadisonKastler_MatrixCommutant`, `KadisonKastler_MatrixCommutantLifts`, `KadisonKastler_MatrixCornerConjugation`, `KadisonKastler_MatrixLiftConjugation`, `KadisonKastler_MeasurableFiberRepresentations`, `KadisonKastler_MeasurableNatEnumeration`, `KadisonKastler_MeasurablePoisson`, `KadisonKastler_MeasurableProjectionFrame`, `KadisonKastler_NestAveraging`, `KadisonKastler_PairedRepresentations`, `KadisonKastler_PeriodicMatrixUnits`, `KadisonKastler_PoissonBoundaryLimit`, `KadisonKastler_PoissonVectorAverage`, `KadisonKastler_PreparedGraphRows`, `KadisonKastler_ProductInvariantL2`, `KadisonKastler_ProjectionDimensionStrata`, `KadisonKastler_ProjectionFrameCoordinates`, `KadisonKastler_ProjectionRangeFrame`, `KadisonKastler_ProjectionStrataSynthesis`, `KadisonKastler_ProjectionStratumOperators`, `KadisonKastler_PublishedCentralDecomposition`, `KadisonKastler_RandomWalkPathAction`, `KadisonKastler_RectangularCorner`, `KadisonKastler_RectangularRowNorm`, `KadisonKastler_ReducingCommutantCorner`, `KadisonKastler_RegularCoreOperators`, `KadisonKastler_RowReplication`, `KadisonKastler_ScalarPositiveLimit`, `KadisonKastler_ScalarPullbackWeakGraph`, `KadisonKastler_ShiftBoundarySpace`, `KadisonKastler_ShiftInvariantFunctions`, `KadisonKastler_ShiftInvariantSigma`, `KadisonKastler_SignedMatrixRefinement`, `KadisonKastler_SignedPermutation`, `KadisonKastler_SpatialConjugacyTransport`, `KadisonKastler_SpatialIsometry`, `KadisonKastler_SpatialMatrix`, `KadisonKastler_SpatialProduct`, `KadisonKastler_SpatialRightSlice`, `KadisonKastler_SymmetricSupportTransfer`, `KadisonKastler_TomitaPolarCoordinates`, `KadisonKastler_TwoRatioReindex`, `KadisonKastler_VectorCoreField`, `KadisonKastler_WeakHilbertConvexLimit`, `TracialSplitting_SpatialTensor`.
--
--   **Imports.** It imports the bundle `OAIQ075A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K010`, `Q260K012`, `Q260K013`, `Q260K014` and `Q260K015`; the statements `OAI.KadisonKastler.HaagerupBound.right_slice`, `OAI_KadisonKastler_commonRankSpace_separable`, `OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit`, `OAI_KadisonKastler_exists_ambient_product_state_of_simple`, `OAI.KadisonKastler.exists_block_field_decomposition`, `OAI.KadisonKastler.exists_centralPairCommonSource`, `OAI.KadisonKastler.exists_group_representation_of_mean`, `OAI.KadisonKastler.exists_unitary_boundary_intertwiner`, `OAI_KadisonKastler_rankClosureCoordinateSeparable`, `OAI.KadisonKastler.spatialLeft_injective_of_unit_vector` and `OAI.KadisonKastler.unitaryConjugateAlgebra_isII1`; the proof of `OAI.KadisonKastler.exists_centralPairCommonSource`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A017

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmenableEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moving an injective subalgebra into a nearby algebra

The published input is the one-sided assertion of Cameron--Christensen--
Sinclair--Smith--White--Wiggins, *Kadison--Kastler stable factors*, Duke
Math. J. 163 (2014), Theorem 3.3(i), arXiv:1209.4116v3, p. 13. Only
the inclusion and the displacement bound `150 * γ` are retained.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centralizer_image_starAlgEquiv
    (e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) :
    Set.centralizer (e '' S) = e '' Set.centralizer S := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    rw [map_mul, map_mul]
    change e y * e (e.symm x) = e (e.symm x) * e y
    rw [e.apply_symm_apply]
    exact hx (e y) ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg e (hy w hw)

/-- A concrete von Neumann algebra conjugated by an ambient unitary. -/
def unitaryConjugateAlgebra (w : unitary (H →L[ℂ] H)) (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra H where
  toStarSubalgebra := M.toStarSubalgebra.map (Unitary.conjStarAlgAut ℂ _ w).toStarAlgHom
  centralizer_centralizer' := by
    let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w
    change Set.centralizer (Set.centralizer (e '' (M : Set (H →L[ℂ] H)))) =
      e '' (M : Set (H →L[ℂ] H))
    rw [centralizer_image_starAlgEquiv, centralizer_image_starAlgEquiv,
      M.centralizer_centralizer]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Matrix bounds for perturbation maps

All norms here are the C*-matrix norms, including for rectangular matrices.
The rectangular formulation records exactly the estimates needed for the
Haagerup product norm in the multiplication-correction argument.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A complete bound, expressed on all finite rectangular matrix levels. -/
def CompletelyBoundedBy (F : A →ₗ[ℂ] B) (c : ℝ) : Prop :=
  ∀ (p q : ℕ) (X : CStarMatrix (Fin p) (Fin q) A),
    ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖

/-- Complete isometry in the same rectangular convention. -/
def CompletelyIsometric (F : A →ₗ[ℂ] B) : Prop :=
  ∀ (p q : ℕ) (X : CStarMatrix (Fin p) (Fin q) A),
    ‖CStarMatrix.mapₗ F X‖ = ‖X‖

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CuntzMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix amplification using common isometries

A finite Cuntz family gives an actual star equivalence between the ambient
operator algebra and its matrix amplification. If its isometries belong to
two concrete algebras, the same equivalence identifies both matrix unit
balls with their original unit balls.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H n : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype n] [DecidableEq n]

/-- A finite family of isometries with orthogonal ranges summing to one. -/
structure CuntzFamily (n : Type*) [Fintype n] [DecidableEq n] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  entry : n → (H →L[ℂ] H)
  orthogonal : ∀ i j, star (entry i) * entry j = if i = j then 1 else 0
  total : ∑ i, entry i * star (entry i) = 1

namespace CuntzFamily

local instance instPartialOrderContinuousLinearMapComplexId : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingContinuousLinearMapComplexId : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

variable (S : CuntzFamily n H)

def matrix (T : H →L[ℂ] H) : CStarMatrix n n (H →L[ℂ] H) :=
  fun i j => star (S.entry i) * T * S.entry j

def assemble (X : CStarMatrix n n (H →L[ℂ] H)) : H →L[ℂ] H :=
  ∑ i, ∑ j, S.entry i * X i j * star (S.entry j)

theorem assemble_matrix (T : H →L[ℂ] H) : S.assemble (S.matrix T) = T := by
  have hterm (i j : n) :
      S.entry i * (star (S.entry i) * T * S.entry j) * star (S.entry j) =
        (S.entry i * star (S.entry i)) * T * (S.entry j * star (S.entry j)) := by
    noncomm_ring
  simp only [assemble, matrix, hterm]
  simp_rw [← Finset.mul_sum, S.total, mul_one]
  rw [← Finset.sum_mul, S.total, one_mul]

theorem matrix_assemble (X : CStarMatrix n n (H →L[ℂ] H)) : S.matrix (S.assemble X) = X := by
  apply Matrix.ext
  intro i j
  change star (S.entry i) * (∑ k, ∑ l, S.entry k * X k l * star (S.entry l)) * S.entry j = X i j
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hterm (k l : n) : star (S.entry i) * (S.entry k * X k l * star (S.entry l)) * S.entry j =
      (star (S.entry i) * S.entry k) * X k l * (star (S.entry l) * S.entry j) := by
    noncomm_ring
  simp only [hterm, S.orthogonal]
  simp

theorem matrix_mul (T U : H →L[ℂ] H) : S.matrix (T * U) = S.matrix T * S.matrix U := by
  apply Matrix.ext
  intro i j
  change star (S.entry i) * (T * U) * S.entry j =
    ∑ k, (star (S.entry i) * T * S.entry k) * (star (S.entry k) * U * S.entry j)
  have hterm (k : n) :
      (star (S.entry i) * T * S.entry k) * (star (S.entry k) * U * S.entry j) =
        (star (S.entry i) * T) * (S.entry k * star (S.entry k)) * (U * S.entry j) := by
    noncomm_ring
  simp only [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, S.total, mul_one]
  noncomm_ring

def matrixHom : (H →L[ℂ] H) →⋆ₐ[ℂ] CStarMatrix n n (H →L[ℂ] H) where
  toFun := S.matrix
  map_one' := by ext i j; simp [matrix, S.orthogonal, CStarMatrix.one_apply]
  map_mul' := S.matrix_mul
  map_zero' := by ext i j; simp [matrix]
  map_add' T U := by ext i j; simp [matrix, mul_add, add_mul]
  commutes' c := by
    ext i j
    simp only [matrix, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, S.orthogonal, CStarMatrix.algebraMap_apply]
    split_ifs <;> simp
  map_star' T := by ext i j; simp [matrix, CStarMatrix.star_apply, star_mul, mul_assoc]

theorem matrixHom_injective : Function.Injective S.matrixHom := by
  intro T U h
  have hh := congrArg S.assemble h
  simpa only [matrixHom, StarAlgHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    S.assemble_matrix] using hh

def matrixEquiv : (H →L[ℂ] H) ≃⋆ₐ[ℂ] CStarMatrix n n (H →L[ℂ] H) :=
  StarAlgEquiv.ofBijective S.matrixHom
    ⟨S.matrixHom_injective, fun X => ⟨S.assemble X, S.matrix_assemble X⟩⟩

@[simp] theorem norm_matrix (T : H →L[ℂ] H) : ‖S.matrix T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map S.matrixHom S.matrixHom_injective T

@[simp] theorem norm_assemble (X : CStarMatrix n n (H →L[ℂ] H)) : ‖S.assemble X‖ = ‖X‖ := by
  rw [← S.norm_matrix, S.matrix_assemble]

end CuntzFamily

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBlockExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite blocks of a countable amplification

Finite operator matrices act on the first finitely many matrix summands.
Their extension is an isometric nonunital star homomorphism. These are the
bounded approximants used for the infinite-amplification gap estimate.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

local instance finiteBlockOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance finiteBlockOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBlockCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive finite compressions of the countable amplification -/

namespace KadisonKastler

open Filter
open scoped BigOperators CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

local instance compressionOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance compressionOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Isometric square corners of rectangular C⋆-matrices

The upper-right corner embeds a rectangular matrix into a square matrix
without changing its operator norm. We prove this directly on the finite
Hilbert C⋆-modules that define the matrix norms.
-/

namespace KadisonKastler

open scoped WithCStarModule InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Extension by zero into the left summand of a finite Hilbert C⋆-module. -/
def moduleExtendLeft (x : C⋆ᵐᵒᵈ(A, m → A)) : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A) :=
  (WithCStarModule.equiv _ _).symm (Sum.elim x fun _ => 0)

/-- Extension by zero into the right summand. -/
def moduleExtendRight (x : C⋆ᵐᵒᵈ(A, n → A)) : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A) :=
  (WithCStarModule.equiv _ _).symm (Sum.elim (fun _ => 0) x)

/-- Restriction to the left summand. -/
def moduleRestrictLeft (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) : C⋆ᵐᵒᵈ(A, m → A) :=
  (WithCStarModule.equiv _ _).symm (fun i => x (Sum.inl i))

@[simp]
theorem norm_moduleExtendLeft (x : C⋆ᵐᵒᵈ(A, m → A)) :
    ‖moduleExtendLeft (n := n) x‖ = ‖x‖ := by
  simp [WithCStarModule.pi_norm, moduleExtendLeft, Fintype.sum_sum_type,
    WithCStarModule.inner_def, Sum.elim]

@[simp]
theorem norm_moduleExtendRight (x : C⋆ᵐᵒᵈ(A, n → A)) :
    ‖moduleExtendRight (m := m) x‖ = ‖x‖ := by
  simp [WithCStarModule.pi_norm, moduleExtendRight, Fintype.sum_sum_type,
    WithCStarModule.inner_def, Sum.elim]

theorem norm_moduleRestrictLeft_le (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) :
    ‖moduleRestrictLeft x‖ ≤ ‖x‖ := by
  simp only [WithCStarModule.pi_norm, moduleRestrictLeft,
    WithCStarModule.equiv_symm_pi_apply, Fintype.sum_sum_type]
  apply Real.sqrt_le_sqrt
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      CStarModule.inner_self_nonneg)
  · exact Finset.sum_nonneg fun i _ => CStarModule.inner_self_nonneg

/-- A rectangular matrix as an upper-right corner of a square matrix. -/
def rectangularCorner (X : CStarMatrix m n A) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fun i j =>
    match i, j with
    | Sum.inl i, Sum.inr j => X i j
    | _, _ => 0

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangularCorner_toCLM (X : CStarMatrix m n A)
    (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) :
    CStarMatrix.toCLM (rectangularCorner X) x =
      moduleExtendRight (CStarMatrix.toCLM X (moduleRestrictLeft x)) := by
  ext j
  rcases j with j | j <;>
    simp [CStarMatrix.toCLM_apply_eq_sum, rectangularCorner, moduleExtendRight,
      moduleRestrictLeft, Fintype.sum_sum_type, Sum.elim]

/-- The square-corner embedding preserves the rectangular operator norm. -/
theorem norm_rectangularCorner (X : CStarMatrix m n A) :
    ‖rectangularCorner X‖ = ‖X‖ := by
  apply le_antisymm
  · change ‖CStarMatrix.toCLM (rectangularCorner X)‖ ≤ ‖X‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
    intro x
    rw [rectangularCorner_toCLM, norm_moduleExtendRight]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_moduleRestrictLeft_le x) (norm_nonneg X))
  · change ‖CStarMatrix.toCLM X‖ ≤ ‖rectangularCorner X‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := ContinuousLinearMap.le_opNorm (CStarMatrix.toCLM (rectangularCorner X))
      (moduleExtendLeft (n := n) x)
    rw [rectangularCorner_toCLM, norm_moduleExtendRight, norm_moduleExtendLeft] at h
    exact h

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n]
  [PartialOrder B] [StarOrderedRing B] in
theorem rectangularCorner_map (F : A →ₗ[ℂ] B) (X : CStarMatrix m n A) :
    rectangularCorner (CStarMatrix.mapₗ F X) =
      CStarMatrix.mapₗ F (rectangularCorner X) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [rectangularCorner]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplificationGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Passing matrix approximants to the infinite amplification

Finite compressions have norm at most one. Weak operator compactness gives
a single limiting approximant in the target amplification, retaining the
same error at every coefficient and therefore in operator norm.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

local instance amplificationGapOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance amplificationGapStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- A contractive, unital, star-preserving mean with both module identities.
The map `ι` includes fields independent of the averaged variable. -/
structure BimoduleMean (ι : B →⋆ₐ[ℂ] A) where
  toCLM : A →L[ℂ] B
  map_one : toCLM 1 = 1
  map_star : ∀ x, toCLM (star x) = star (toCLM x)
  norm_le : ∀ x, ‖toCLM x‖ ≤ ‖x‖
  map_left : ∀ b x, toCLM (ι b * x) = b * toCLM x
  map_right : ∀ x b, toCLM (x * ι b) = toCLM x * b

namespace BimoduleMean

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)

@[simp]
theorem fixed (b : B) : m.toCLM (ι b) = b := by
  simpa only [mul_one, m.map_one] using m.map_left b 1

end BimoduleMean

/-- A unitary is a contraction, including in the degenerate C-star algebra. -/
theorem norm_unitary_le_one (x : unitary A) : ‖(x : A)‖ ≤ 1 := by
  nontriviality A
  simp only [CStarRing.norm_coe_unitary, le_refl]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedCStar_r7efc64_1 : CStarAlgebra (G →ᵇ B) where
local instance boundaryBoundedComplete_r7efc64_1 : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
local instance boundaryBoundedOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryBoundedStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- Transport combines left translation of the group coordinate and the
original action on the value algebra. -/
def boundaryTranslate (α : G →* (B ≃⋆ₐ[ℂ] B)) (g : G) :
    (G →ᵇ B) ≃⋆ₐ[ℂ] (G →ᵇ B) where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => α g (f (g⁻¹ * t))) ‖f‖ (fun t => by
      rw [StarAlgEquiv.norm_map]
      exact f.norm_coe_le_norm _)
  invFun f := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => (α g).symm (f (g * t))) ‖f‖ (fun t => by
      rw [StarAlgEquiv.norm_map]
      exact f.norm_coe_le_norm _)
  left_inv f := by
    ext t
    change (α g).symm (α g (f (g⁻¹ * (g * t)))) = f t
    simp only [inv_mul_cancel_left, StarAlgEquiv.symm_apply_apply]
  right_inv f := by
    ext t
    change α g ((α g).symm (f (g * (g⁻¹ * t)))) = f t
    simp only [mul_inv_cancel_left, StarAlgEquiv.apply_symm_apply]
  map_mul' f h := by
    ext t
    exact map_mul (α g) _ _
  map_add' f h := by
    ext t
    exact map_add (α g) _ _
  map_smul' c f := by
    ext t
    exact map_smul (α g) c _
  map_star' f := by
    ext t
    exact map_star (α g) _

/-- Any family of unitaries is uniformly bounded, hence defines an actual
unitary of the bounded-function C-star algebra. -/
def boundedUnitaryFamily (V : G → unitary B) : unitary (G →ᵇ B) :=
  let f : G →ᵇ B := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => (V g : B)) 1 (fun g => norm_unitary_le_one (V g))
  ⟨f, by
    constructor
    · ext g
      exact Unitary.star_mul_self_of_mem (V g).property
    · ext g
      exact Unitary.mul_star_self_of_mem (V g).property⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplificationGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The canonical amplification gap from common matrix units

Actual countable matrix units transport under a Hilbert-space isometry.
Thus the common-matrix-unit gap estimate applies to the canonical Hilbert
sum of the original representation, retaining its original tolerance.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {D : Submodule ℂ H} [CompleteSpace D]

namespace FullMatrixCorner

omit [CompleteSpace H] [CompleteSpace K] in
instance spatialTransportSubspaceComplete (e : H ≃ₗᵢ[ℂ] K) :
    CompleteSpace (D.map e.toLinearEquiv.toLinearMap) :=
  e.toLinearIsometry.completeSpace_map D

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Close representations from the published commutant-distance formula

The explicit input `PublishedBlockCommutantApproximation` is the block
specialization of Arveson's distance formula, in the form of Christensen,
*Perturbations of operator algebras II*, Indiana Univ. Math. J. 26 (1977),
Proposition 2.1. See also Christensen--Sinclair--Smith--White,
*Perturbations of C*-algebraic invariants*, GAFA 20 (2010), equation (2.1),
and Cameron et al., *Kadison--Kastler stable factors* (2014), equation (2.2).

The 2010 formulation applies to represented C*-algebras. Passing through
the quotient by the representation kernel gives the formulation below
with the complete bound on the source algebra. No normality is required.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The spatial derivation implemented by `T`. -/
def innerDerivation (T : R) : R →ₗ[ℂ] R :=
  LinearMap.mulLeft ℂ T - LinearMap.mulRight ℂ T

@[simp]
theorem innerDerivation_apply (T x : R) : innerDerivation T x = T * x - x * T := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Column
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The triangular representation for the column estimate

The triangular representation is constructed and bounded directly.
Haagerup's cyclic similarity theorem is isolated as the precise published
input at the cyclic restriction step.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance columnOperatorPartialOrder_r7efc64_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance columnOperatorStarOrderedRing_r7efc64_1 : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
/-- The represented commutator, with its boundedness proved from multiplication. -/
def representedInnerDerivation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  ((innerDerivation h).comp ρ.toAlgHom.toLinearMap).mkContinuous (2 * ‖h‖) (fun a => by
    change ‖h * ρ a - ρ a * h‖ ≤ (2 * ‖h‖) * ‖a‖
    calc
      _ ≤ ‖h * ρ a‖ + ‖ρ a * h‖ := norm_sub_le _ _
      _ ≤ ‖h‖ * ‖ρ a‖ + ‖ρ a‖ * ‖h‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (2 * ‖h‖) * ‖ρ a‖ := by ring
      _ ≤ (2 * ‖h‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le ρ a) (by positivity))

@[simp]
theorem representedInnerDerivation_apply (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : H →L[ℂ] H) (a : A) :
    representedInnerDerivation ρ h a = innerDerivation h (ρ a) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedPermutation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A finite unitary group spanning a full matrix algebra -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Permutations act on diagonal signs by permuting their coordinates. -/
def permuteSigns : Equiv.Perm ι →* MulAut (ι → ℤˣ) where
  toFun σ := {
    toFun := fun d i => d (σ⁻¹ i)
    invFun := fun d i => d (σ i)
    left_inv := by intro d; funext i; simp
    right_inv := by intro d; funext i; simp
    map_mul' := by intros; rfl }
  map_one' := by ext d i; rfl
  map_mul' σ τ := by ext d i; rfl

abbrev SignedPermutation (ι : Type*) := (ι → ℤˣ) ⋊[permuteSigns] Equiv.Perm ι

instance instFintypeSignedPermutation : Fintype (SignedPermutation ι) :=
  Fintype.ofEquiv ((ι → ℤˣ) × Equiv.Perm ι) SemidirectProduct.equivProd.symm

def signDiagonal (d : ι → ℤˣ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ((d i : ℤ) : ℂ))

omit [Fintype ι] in
theorem signDiagonal_star (d : ι → ℤˣ) : star (signDiagonal d) = signDiagonal d := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [signDiagonal, Matrix.star_apply]
  · simp [signDiagonal, Matrix.star_apply, Matrix.diagonal, hij, Ne.symm hij]

theorem signDiagonal_mul (d e : ι → ℤˣ) :
    signDiagonal (d * e) = signDiagonal d * signDiagonal e := by
  simp [signDiagonal, Matrix.diagonal_mul_diagonal]

theorem signDiagonal_sq (d : ι → ℤˣ) : signDiagonal d * signDiagonal d = 1 := by
  rw [← signDiagonal_mul]
  have hd : d * d = 1 := by funext i; exact Int.units_mul_self (d i)
  rw [hd]
  simp [signDiagonal]

def signDiagonalUnitary (d : ι → ℤˣ) : unitary (Matrix ι ι ℂ) :=
  ⟨signDiagonal d, by
    change star (signDiagonal d) * signDiagonal d = 1 ∧ signDiagonal d * star (signDiagonal d) = 1
    rw [signDiagonal_star]
    exact ⟨signDiagonal_sq d, signDiagonal_sq d⟩⟩

def signDiagonalHom : (ι → ℤˣ) →* unitary (Matrix ι ι ℂ) where
  toFun := signDiagonalUnitary
  map_one' := by apply Subtype.ext; simp [signDiagonalUnitary, signDiagonal]
  map_mul' d e := Subtype.ext (signDiagonal_mul d e)

def permutationUnitary (σ : Equiv.Perm ι) : unitary (Matrix ι ι ℂ) :=
  ⟨Matrix.permMatrixHom (R := ℂ) σ, by
    change star (Matrix.permMatrixHom (R := ℂ) σ) * Matrix.permMatrixHom (R := ℂ) σ = 1 ∧
      Matrix.permMatrixHom (R := ℂ) σ * star (Matrix.permMatrixHom (R := ℂ) σ) = 1
    have hs : star (Matrix.permMatrixHom (R := ℂ) σ) = Matrix.permMatrixHom (R := ℂ) σ⁻¹ := by
      change star (σ⁻¹.permMatrix ℂ) = (σ⁻¹)⁻¹.permMatrix ℂ
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rw [hs, ← map_mul, ← map_mul]
    simp⟩

def permutationHom : Equiv.Perm ι →* unitary (Matrix ι ι ℂ) where
  toFun := permutationUnitary
  map_one' := Subtype.ext (map_one (Matrix.permMatrixHom (R := ℂ)))
  map_mul' σ τ := Subtype.ext (map_mul (Matrix.permMatrixHom (R := ℂ)) σ τ)

theorem permutationMatrix_apply (σ : Equiv.Perm ι) (i j : ι) :
    Matrix.permMatrixHom (R := ℂ) σ i j = if i = σ j then 1 else 0 := by
  change (if j ∈ (some (σ⁻¹ i) : Option ι) then (1 : ℂ) else 0) = _
  simp [Equiv.eq_symm_apply, eq_comm]


theorem permutation_signDiagonal (σ : Equiv.Perm ι) (d : ι → ℤˣ) :
    Matrix.permMatrixHom (R := ℂ) σ * signDiagonal d =
      signDiagonal (permuteSigns σ d) * Matrix.permMatrixHom (R := ℂ) σ := by
  ext i j
  simp only [signDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, permutationMatrix_apply]
  by_cases hij : i = σ j
  · subst i
    simp [permuteSigns]
  · simp [hij]

/-- The finite signed-permutation group acts by actual unitary matrices. -/
def signedPermutationHom : SignedPermutation ι →* unitary (Matrix ι ι ℂ) :=
  SemidirectProduct.lift signDiagonalHom permutationHom (fun σ => by
    apply MonoidHom.ext
    intro d
    apply Subtype.ext
    change signDiagonal (permuteSigns σ d) =
      Matrix.permMatrixHom (R := ℂ) σ * signDiagonal d * (↑((permutationHom σ)⁻¹) : Matrix ι ι ℂ)
    rw [permutation_signDiagonal, mul_assoc]
    have hi : Matrix.permMatrixHom (R := ℂ) σ * (↑((permutationHom σ)⁻¹) : Matrix ι ι ℂ) = 1 :=
      congrArg (fun u : unitary (Matrix ι ι ℂ) => u.val) (mul_inv_cancel (permutationHom σ))
    rw [hi, mul_one])

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging over a concrete finite matrix algebra

Signed permutation matrices give a finite unitary group whose commutant
is exactly the commutant of the matrix-unit system. Its uniform average
preserves the original scalar derivation bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The signed permutations of a given concrete matrix-unit system. -/
def matrixUnitSignedRepresentation (E : Generator.MatrixUnitSystem ι A) :
    SignedPermutation ι →* unitary A where
  toFun g := ⟨E.hom (signedPermutationHom g : Matrix ι ι ℂ),
    Unitary.map_mem E.hom (signedPermutationHom g).property⟩
  map_one' := by
    apply Subtype.ext
    change E.hom (signedPermutationHom (1 : SignedPermutation ι) : Matrix ι ι ℂ) = 1
    rw [map_one]
    exact map_one E.hom
  map_mul' g k := by
    apply Subtype.ext
    change E.hom (signedPermutationHom (g * k) : Matrix ι ι ℂ) =
      E.hom (signedPermutationHom g : Matrix ι ι ℂ) * E.hom (signedPermutationHom k : Matrix ι ι ℂ)
    rw [map_mul]
    exact map_mul E.hom _ _

theorem matrixUnitSignedRepresentation_inl (E : Generator.MatrixUnitSystem ι A)
    (d : ι → ℤˣ) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inl d) : A) = E.hom (signDiagonal d) := by
  change E.hom (signedPermutationHom (SemidirectProduct.inl d) : Matrix ι ι ℂ) = _
  congr 1
  simp [signedPermutationHom, signDiagonalHom, signDiagonalUnitary]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CenterAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering scalar centre from central projections

The centre is represented as the intersection with the concrete commutant.
Spectral approximation in this von Neumann algebra reduces scalarity of its
whole algebra to triviality of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The intersection of two concrete von Neumann algebras. -/
def vonNeumannIntersection (M N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := M.toStarSubalgebra ⊓ N.toStarSubalgebra
  centralizer_centralizer' := by
    apply Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
    intro x hx
    constructor
    · have h : Set.centralizer (Set.centralizer
          ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) :
            Set (H →L[ℂ] H))) ⊆ Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H))) :=
        Set.centralizer_subset (Set.centralizer_subset (fun _ hy => hy.1))
      exact M.centralizer_centralizer ▸ h hx
    · have h : Set.centralizer (Set.centralizer
          ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) :
            Set (H →L[ℂ] H))) ⊆ Set.centralizer (Set.centralizer (N : Set (H →L[ℂ] H))) :=
        Set.centralizer_subset (Set.centralizer_subset (fun _ hy => hy.2))
      exact N.centralizer_centralizer ▸ h hx

/-- The concrete centre, retaining its von Neumann structure. -/
def concreteCenter (N : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  vonNeumannIntersection N N.commutant

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralPairCommonSource
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # One norm-separable source for the common central decomposition -/

namespace KadisonKastler

open KadisonSimilarity TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure CentralPairCommonSource (M N : VonNeumannAlgebra H)
    (C : StarSubalgebra ℂ (H →L[ℂ] H)) where
  leftComm : StarSubalgebra ℂ (H →L[ℂ] H)
  rightComm : StarSubalgebra ℂ (H →L[ℂ] H)
  source : StarSubalgebra ℂ (H →L[ℂ] H)
  left_closed : IsClosed (leftComm : Set (H →L[ℂ] H))
  right_closed : IsClosed (rightComm : Set (H →L[ℂ] H))
  source_closed : IsClosed (source : Set (H →L[ℂ] H))
  left_separable : SeparableSpace leftComm
  right_separable : SeparableSpace rightComm
  source_separable : SeparableSpace source
  left_mem : leftComm ≤ M.commutant.toStarSubalgebra
  right_mem : rightComm ≤ N.commutant.toStarSubalgebra
  left_generates : (starSubalgebraCommutant leftComm).commutant = M.commutant
  right_generates : (starSubalgebraCommutant rightComm).commutant = N.commutant
  original_le : C ≤ source
  left_le : leftComm ≤ source
  right_le : rightComm ≤ source
  central : source ≤ (concreteCenter M).commutant.toStarSubalgebra

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableNatEnumeration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurably enumerating nonzero frame indices

The `n`th index of a point-dependent subset of the naturals is measurable
when each membership predicate is measurable. The library's value zero
outside the finite range is retained; dimension strata remove that case.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X]

noncomputable def measurableIndexCount (p : X → ℕ → Prop) (x : X) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (p x) n

/-- There are at least `k + 1` indices satisfying the predicate. -/
def frameIndexAvailable (p : ℕ → Prop) (k : ℕ) : Prop :=
  ∃ m, k < measurableIndexCount (fun _ : Unit => p) () m

theorem frameIndexAvailable_mono {p : ℕ → Prop} {k l : ℕ}
    (hkl : k ≤ l) (h : frameIndexAvailable p l) : frameIndexAvailable p k := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, lt_of_le_of_lt hkl hm⟩

omit [MeasurableSpace X] in
 theorem frameIndexAvailable_valid {p : ℕ → Prop} {k : ℕ}
    (h : frameIndexAvailable p k) :
    ∀ hf : (Set.ofPred p).Finite, k < hf.toFinset.card := by
  classical
  obtain ⟨m, hm⟩ := h
  intro hf
  exact lt_of_lt_of_le hm (Nat.count_le_card hf m)

omit [MeasurableSpace X] in
 theorem frameIndexAvailable_count {p : ℕ → Prop} {m : ℕ} (hm : p m) :
    frameIndexAvailable p (measurableIndexCount (fun _ : Unit => p) () m) := by
  classical
  refine ⟨m + 1, ?_⟩
  change Nat.count p m < Nat.count p (m + 1)
  exact Nat.count_lt_count_succ_iff.mpr hm

/-- The ascending enumeration, restricted to its genuine indices, is a bijection. -/
def frameIndexEquiv (p : ℕ → Prop) : {k // frameIndexAvailable p k} ≃ {m // p m} := by
  classical
  exact {
    toFun := fun k => ⟨Nat.nth p k, Nat.nth_mem _ (frameIndexAvailable_valid k.property)⟩
    invFun := fun m => ⟨Nat.count p m, frameIndexAvailable_count m.property⟩
    left_inv := fun k => Subtype.ext (Nat.count_nth (frameIndexAvailable_valid k.property))
    right_inv := fun m => Subtype.ext (Nat.nth_count m.property) }

/-- Index zero is the infinite-rank stratum; index `n + 1` is rank `n`. -/
def frameDimensionStratum (p : X → ℕ → Prop) : ℕ → Set X
  | 0 => {x | ∀ k, frameIndexAvailable (p x) k}
  | n + 1 => {x | (∀ k < n, frameIndexAvailable (p x) k) ∧
      ¬frameIndexAvailable (p x) n}

omit [MeasurableSpace X] in
theorem frameDimensionStratum_finite_iff (p : X → ℕ → Prop) {n : ℕ}
    {x : X} (hx : x ∈ frameDimensionStratum p (n + 1)) (k : ℕ) :
    frameIndexAvailable (p x) k ↔ k < n := by
  constructor
  · intro hk
    by_contra hn
    exact hx.2 (frameIndexAvailable_mono (Nat.le_of_not_gt hn) hk)
  · exact hx.1 k

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableProjectionFrame
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable orthogonal frames for projection fields

A countable family of measurable vectors can be orthogonalized measurably,
including at points where its rank changes. Zero vectors are retained until
the dimension strata are selected.
-/

namespace KadisonKastler

open MeasureTheory InnerProductSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The normalized Gram-Schmidt vectors of a measurable projection field. -/
def measurableProjectionFrame (P : X → H →L[ℂ] H) (b : ℕ → H) (x : X) (n : ℕ) : H :=
  gramSchmidtNormed ℂ (fun i => P x (b i)) n

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
 theorem projectedTotalSequence (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range fun n => P (b n))).topologicalClosure = P.range := by
  have he : (Submodule.span ℂ (Set.range b)).map P.toLinearMap =
      Submodule.span ℂ (Set.range fun n => P (b n)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hl := Submodule.topologicalClosure_map P (Submodule.span ℂ (Set.range b))
  rw [hb, Submodule.map_top, he] at hl
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact ⟨b n, rfl⟩
    · exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hP
  · exact hl

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
 theorem projectionFrame_total_of_total (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (fun n => P (b n))))).topologicalClosure =
      P.range := by
  rw [span_gramSchmidtNormed_range, span_gramSchmidt]
  exact projectedTotalSequence P hP b hb

/- Projecting a Hilbert basis gives a total family in the closed range. -/

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionRangeFrame
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Hilbert coordinates from measurable projection frames

The nonzero Gram-Schmidt vectors form a Hilbert basis of the actual range.
Their ascending enumeration is measurable before restricting to a rank stratum.
-/

namespace KadisonKastler

open MeasureTheory InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem frame_mem_range (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) (n : ℕ) :
    gramSchmidtNormed ℂ (fun i => P (b i)) n ∈ P.range := by
  rw [← projectionFrame_total_of_total P hP b hb]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

/-- The nonzero projected frame, as vectors of the genuine closed range. -/
def projectionRangeFrame (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (i : {n // gramSchmidtNormed ℂ (fun j => P (b j)) n ≠ 0}) : P.range :=
  ⟨gramSchmidtNormed ℂ (fun j => P (b j)) i, frame_mem_range P hP b hb i⟩

omit [CompleteSpace H] in
theorem projectionRangeFrame_orthonormal (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    Orthonormal ℂ (projectionRangeFrame P hP b hb) := by
  rw [← P.range.subtypeₗᵢ.orthonormal_comp_iff]
  exact gramSchmidtNormed_orthonormal' (fun j => P (b j))

omit [CompleteSpace H] in
theorem projectionRangeFrame_orthogonal_eq_bot (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (projectionRangeFrame P hP b hb)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  change z = 0
  apply Subtype.ext
  have hzero (n : ℕ) : inner ℂ (gramSchmidtNormed ℂ (fun j => P (b j)) n) (z : H) = 0 := by
    by_cases hn : gramSchmidtNormed ℂ (fun j => P (b j)) n = 0
    · simp only [hn, inner_zero_left]
    · have hmem : projectionRangeFrame P hP b hb ⟨n, hn⟩ ∈
          Submodule.span ℂ (Set.range (projectionRangeFrame P hP b hb)) :=
        Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      have hi : inner ℂ (projectionRangeFrame P hP b hb ⟨n, hn⟩) z = 0 :=
        Submodule.inner_right_of_mem_orthogonal hmem hz
      exact hi
  have ho : (z : H) ∈
      (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (fun j => P (b j)))))ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨n, rfl⟩ := hy; exact hzero n
    | zero => simp
    | add y w _ _ hy hw => simp only [inner_add_left, hy, hw, add_zero]
    | smul c y _ hy => simp only [inner_smul_left, hy, mul_zero]
  have hzorth : (z : H) ∈ P.rangeᗮ := by
    have he : P.rangeᗮ =
        (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (fun j => P (b j)))))ᗮ := by
      rw [← projectionFrame_total_of_total P hP b hb, Submodule.orthogonal_closure]
    exact he.symm ▸ ho
  exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal z.property hzorth)

/-- Every closed projection range has the basis given by its surviving frame. -/
def projectionRangeHilbertBasis (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    HilbertBasis {n // gramSchmidtNormed ℂ (fun j => P (b j)) n ≠ 0} ℂ P.range := by
  letI : CompleteSpace P.range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP).completeSpace_coe
  exact HilbertBasis.mkOfOrthogonalEqBot (projectionRangeFrame_orthonormal P hP b hb)
    (projectionRangeFrame_orthogonal_eq_bot P hP b hb)

@[simp] theorem projectionRangeHilbertBasis_apply (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (i : {n // gramSchmidtNormed ℂ (fun j => P (b j)) n ≠ 0}) :
    projectionRangeHilbertBasis P hP b hb i = projectionRangeFrame P hP b hb i := by
  simp only [projectionRangeHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

variable {X : Type*} [MeasurableSpace X]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Ascending enumeration of the nonzero projected frame, with a harmless
library default outside its genuine index range. -/
def enumeratedProjectionFrame (P : X → H →L[ℂ] H) (b : ℕ → H) (x : X) (k : ℕ) : H :=
  measurableProjectionFrame P b x (Nat.nth (fun n => measurableProjectionFrame P b x n ≠ 0) k)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFrameCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed Hilbert coordinates on each measurable rank stratum -/

namespace KadisonKastler

open MeasureTheory InnerProductSpace

noncomputable section

/-- Increasing enumeration identifies a finite rank stratum with `Fin n`. -/
def finiteFrameIndexEquiv (p : ℕ → Prop) (n : ℕ)
    (h : ∀ k, frameIndexAvailable p k ↔ k < n) : Fin n ≃ {m // p m} :=
  (show Fin n ≃ {k // frameIndexAvailable p k} from {
    toFun := fun i => ⟨i, (h i).mpr i.isLt⟩
    invFun := fun i => ⟨i, (h i).mp i.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (frameIndexEquiv p)

/-- Increasing enumeration identifies an infinite rank stratum with `ℕ`. -/
def infiniteFrameIndexEquiv (p : ℕ → Prop) (h : ∀ k, frameIndexAvailable p k) :
    ℕ ≃ {m // p m} :=
  (show ℕ ≃ {k // frameIndexAvailable p k} from {
    toFun := fun i => ⟨i, h i⟩
    invFun := fun i => i
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (frameIndexEquiv p)

@[simp] theorem finiteFrameIndexEquiv_val (p : ℕ → Prop) (n : ℕ)
    (h : ∀ k, frameIndexAvailable p k ↔ k < n) (i : Fin n) :
    (finiteFrameIndexEquiv p n h i).val = Nat.nth p i := rfl

@[simp] theorem infiniteFrameIndexEquiv_val (p : ℕ → Prop)
    (h : ∀ k, frameIndexAvailable p k) (i : ℕ) :
    (infiniteFrameIndexEquiv p h i).val = Nat.nth p i := rfl

variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Reindex a Hilbert basis while retaining its concrete vectors. -/
def reindexedHilbertBasis (b : HilbertBasis I ℂ H) (e : J ≃ I) : HilbertBasis J ℂ H :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    rw [e.surjective.range_comp b, b.dense_span])

@[simp] theorem reindexedHilbertBasis_apply (b : HilbertBasis I ℂ H) (e : J ≃ I) (j : J) :
    reindexedHilbertBasis b e j = b (e j) := by
  simp only [reindexedHilbertBasis, HilbertBasis.coe_mk, Function.comp_apply]

variable {X : Type*} (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

/-- The finite-dimensional coordinate basis on the rank `n` stratum. -/
def finiteProjectionBasis (n : ℕ) (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) (n + 1)) :
    HilbertBasis (Fin n) ℂ (P x).range := by
  letI : CompleteSpace (P x).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hP x)).completeSpace_coe
  exact reindexedHilbertBasis (projectionRangeHilbertBasis (P x) (hP x) b hb)
    (finiteFrameIndexEquiv _ n (frameDimensionStratum_finite_iff _ hx))

/-- The infinite-dimensional coordinate basis on the infinite rank stratum. -/
def infiniteProjectionBasis (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) 0) :
    HilbertBasis ℕ ℂ (P x).range := by
  letI : CompleteSpace (P x).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hP x)).completeSpace_coe
  exact reindexedHilbertBasis (projectionRangeHilbertBasis (P x) (hP x) b hb)
    (infiniteFrameIndexEquiv _ hx)

@[simp] theorem finiteProjectionBasis_coe (n : ℕ) (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) (n + 1))
    (i : Fin n) :
    (finiteProjectionBasis P hP b hb n x hx i : H) = enumeratedProjectionFrame P b x i := by
  simp only [finiteProjectionBasis, reindexedHilbertBasis_apply,
    projectionRangeHilbertBasis_apply, projectionRangeFrame,
    enumeratedProjectionFrame, measurableProjectionFrame]
  rfl

@[simp] theorem infiniteProjectionBasis_coe (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) 0)
    (i : ℕ) :
    (infiniteProjectionBasis P hP b hb x hx i : H) = enumeratedProjectionFrame P b x i := by
  simp only [infiniteProjectionBasis, reindexedHilbertBasis_apply,
    projectionRangeHilbertBasis_apply, projectionRangeFrame,
    enumeratedProjectionFrame, measurableProjectionFrame]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableStrongMembership
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable finite-vector tests for algebra membership

For contractions, approximation on finite prefixes of a dense vector
sequence is equivalent to membership in the strongly closed target
algebra, provided the test family is strongly dense in its unit ball.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def CountableStrongTests (ξ : ℕ → H) (F : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ m k : ℕ, ∃ S ∈ F, ∀ l ≤ m, ‖(T - S) (ξ l)‖ < 1 / (k + 1 : ℝ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionDimensionStrata
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable trivializations of projection ranges on dimension strata -/

namespace KadisonKastler

open MeasureTheory InnerProductSpace
open scoped lp

noncomputable section

/-- A fixed countable index type for each dimension stratum. -/
def projectionDimensionIndex : ℕ → Type
  | 0 => ℕ
  | n + 1 => Fin n

def projectionDimensionIndexNat : {n : ℕ} → projectionDimensionIndex n → ℕ
  | 0, i => i
  | n + 1, i => (show Fin n from i).val

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

def projectionRankStratum (n : ℕ) : Set X :=
  frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) n

/-- A basis with a fixed index set on the whole dimension stratum. -/
def projectionStratumBasis (n : ℕ) (x : projectionRankStratum P b n) :
    HilbertBasis (projectionDimensionIndex n) ℂ (P x.val).range := by
  cases n with
  | zero => exact infiniteProjectionBasis P hP b hb x.val x.property
  | succ n => exact finiteProjectionBasis P hP b hb n x.val x.property

@[simp] theorem projectionStratumBasis_coe (n : ℕ) (x : projectionRankStratum P b n)
    (i : projectionDimensionIndex n) :
    (projectionStratumBasis P hP b hb n x i : H) =
      enumeratedProjectionFrame P b x.val (projectionDimensionIndexNat i) := by
  cases n with
  | zero => exact infiniteProjectionBasis_coe P hP b hb x.val x.property i
  | succ n => exact finiteProjectionBasis_coe P hP b hb n x.val x.property i

/-- The coordinate unitary uses the same target Hilbert space throughout a stratum. -/
def projectionStratumCoordinates (n : ℕ) (x : projectionRankStratum P b n) :
    (P x.val).range ≃ₗᵢ[ℂ] ℓ²(projectionDimensionIndex n, ℂ) :=
  (projectionStratumBasis P hP b hb n x).repr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStratumOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting measurable operators to fixed dimension coordinates -/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction to an invariant projection range, retaining the original norm. -/
def projectionRangeRestriction (P T : H →L[ℂ] H)
    (hT : ∀ v ∈ P.range, T v ∈ P.range) : P.range →L[ℂ] P.range :=
  (T.comp P.range.subtypeL).codRestrict P.range (fun v => hT v v.property)

omit [CompleteSpace H] in
@[simp] theorem projectionRangeRestriction_coe (P T : H →L[ℂ] H)
    (hT : ∀ v ∈ P.range, T v ∈ P.range) (v : P.range) :
    (projectionRangeRestriction P T hT v : H) = T v := rfl

variable (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

/-- An invariant operator field in a fixed Hilbert space on each rank stratum. -/
def projectionStratumOperator (T : X → H →L[ℂ] H)
    (hT : ∀ x v, v ∈ (P x).range → T x v ∈ (P x).range)
    (n : ℕ) (x : projectionRankStratum P b n) :
    ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ) := by
  letI : CompleteSpace (P x.val).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hP x.val)).completeSpace_coe
  exact (projectionStratumCoordinates P hP b hb n x).conjStarAlgEquiv
    (projectionRangeRestriction (P x.val) (T x.val) (hT x.val))

@[simp] theorem projectionStratumOperator_apply (T : X → H →L[ℂ] H)
    (hT : ∀ x v, v ∈ (P x).range → T x v ∈ (P x).range)
    (n : ℕ) (x : projectionRankStratum P b n) (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    projectionStratumOperator P hP b hb T hT n x v =
      projectionStratumCoordinates P hP b hb n x
        (projectionRangeRestriction (P x.val) (T x.val) (hT x.val)
          ((projectionStratumCoordinates P hP b hb n x).symm v)) := by
  simp only [projectionStratumOperator, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableFiberRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed-coordinate representations on measurable rank strata -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {X A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

abbrev representationUnitProjection : X → H →L[ℂ] H := fun x => nonunitalUnitProjection (ρ x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStrataSynthesis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling the fixed-coordinate projection strata -/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  (μ : Measure X) (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
  (hPm : ∀ v, Measurable fun x => P x v)

abbrev projectionStratumMeasure (n : ℕ) : Measure (projectionRankStratum P b n) :=
  Measure.comap ((↑) : projectionRankStratum P b n → X) μ

abbrev ProjectionStrataSpace :=
  lp (fun n => Lp ℓ²(projectionDimensionIndex n, ℂ) 2 (projectionStratumMeasure μ P b n)) 2

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankCoordinates
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Fixed-rank coordinates for a represented common C-star source

The common spectral model and its Borel representations give a unitary
on each fixed-rank stratum.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankModelCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _

local instance rankModelCoordinateBorel_r7efc64_1 :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩
structure BorelCommonModel (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) where
  field : WeakDual.characterSpace ℂ A → B →⋆ₙₐ[ℂ]
    (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators)
  measurable : ∀ a v, Measurable fun x => field x a v
  action : ∀ a (f : CommonCyclicHilbert π D),
    isometricExtension (cyclicCommonEmbedding π D) (σ a) f =ᵐ[cyclicCommonBaseMeasure π D]
      fun x => field x a (f x)

def commonRankBasis : ℕ → ScalarHilbertCoordinates D.generators :=
  TopologicalSpace.denseSeq _

variable {π D} {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

def commonModelProjection := representationUnitProjection M.field

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operators on the actual regular Hilbert space

The regular core acts on `L²(ℝ,H)`, with a constant operator
representation and multiplication by a measurable unitary
field. The latter gives the gauge transformation used to write the core
embedding as a faithful conjugate of the constant representation.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {D H : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual real-line regular Hilbert space. -/
abbrev RegularCoreHilbert (H : Type*) [NormedAddCommGroup H] :=
  Lp H 2 (volume : Measure ℝ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling fiber conjugacies on the actual direct-integral space

`OperatorFieldDecomposition` records the decomposition and reconstruction
properties of a given constant-fiber direct integral. It is data, not a
published theorem or an existence assertion. The assembly argument below
uses actual multiplication unitaries on `L²(X,H)`.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def RepresentsOperatorField (μ : Measure X) (F : X → H →L[ℂ] H)
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) : Prop :=
  ∀ f : Lp H 2 μ, T f =ᵐ[μ] fun t => F t (f t)

structure OperatorFieldDecomposition (μ : Measure X) (M : X → VonNeumannAlgebra H)
    (A : VonNeumannAlgebra (Lp H 2 μ)) : Prop where
  decompose : ∀ T ∈ A, ∃ F : X → H →L[ℂ] H,
    (∀ x, AEStronglyMeasurable (fun t => F t x) μ) ∧
    (∀ᵐ t ∂μ, ‖F t‖ ≤ ‖T‖) ∧ (∀ᵐ t ∂μ, F t ∈ M t) ∧ RepresentsOperatorField μ F T
  reconstruct : ∀ (F : X → H →L[ℂ] H) (C : ℝ), 0 ≤ C →
    (∀ x, AEStronglyMeasurable (fun t => F t x) μ) →
    (∀ᵐ t ∂μ, ‖F t‖ ≤ C) → (∀ᵐ t ∂μ, F t ∈ M t) →
    ∃ T ∈ A, RepresentsOperatorField μ F T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankSourceModel
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Actual rank fields of a represented bicommutant member

Kaplansky approximation on the original representation, transported through
the constructed unitary, places the rank fields in the corresponding fiber
bicommutants. The common source may be larger than the algebra being closed.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

abbrev CommonRankSpace := ProjectionStrataSpace (H := ScalarHilbertCoordinates D.generators)
  (cyclicCommonBaseMeasure π D)
  (commonModelProjection M) (commonRankBasis π D)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteLinearLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar and limit consequences of complete bounds -/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The one-by-one matrix copy of the algebra. -/
def scalarMatrixCopy : A →⋆ₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) A where
  toFun a := CStarMatrix.ofMatrix fun _ _ => a
  map_one' := by ext i j; fin_cases i; fin_cases j; rfl
  map_mul' a b := by
    ext i j
    change a * b = ∑ _ : Fin 1, a * b
    simp
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by ext i j; fin_cases i; fin_cases j; rfl
  map_star' _ := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem scalarMatrixCopy_apply (a : A) (i j : Fin 1) :
    scalarMatrixCopy a i j = a := rfl

@[simp] theorem scalarMatrixCopy_norm (a : A) : ‖scalarMatrixCopy a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map scalarMatrixCopy
    (fun _ _ h => congrArg (fun X : CStarMatrix (Fin 1) (Fin 1) A => X 0 0) h) a

/-- A complete bound includes the ordinary operator bound with no loss. -/
theorem CompletelyBoundedBy.apply_norm_le {D : A →ₗ[ℂ] B} {c : ℝ}
    (hD : CompletelyBoundedBy D c) (x : A) : ‖D x‖ ≤ c * ‖x‖ := by
  have h := hD 1 1 (scalarMatrixCopy x)
  have he : CStarMatrix.mapₗ D (scalarMatrixCopy x) = scalarMatrixCopy (D x) := by
    ext i j
    rfl
  simpa only [he, scalarMatrixCopy_norm] using h

/-- Turn a completely bounded algebraic map into a continuous linear map. -/
def CompletelyBoundedBy.toContinuousLinearMap {D : A →ₗ[ℂ] B} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : A →L[ℂ] B :=
  D.mkContinuous c hD.apply_norm_le

@[simp] theorem CompletelyBoundedBy.toContinuousLinearMap_apply
    {D : A →ₗ[ℂ] B} {c : ℝ} (hD : CompletelyBoundedBy D c) (x : A) :
    hD.toContinuousLinearMap x = D x := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphReciprocal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reciprocal rescaling of closed Tomita graphs

Conjugating and interchanging the two coordinates sends the graph at c
to the graph at 1/c. This norm-preserving real-linear map transfers the
directional estimates to small positive scales.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem conjugation_real_smul (J : H ≃ₗᵢ⋆[ℂ] H) (r : ℝ) (ξ : H) :
    J (r • ξ) = r • J ξ := by
  change J ((r : ℂ) • ξ) = (r : ℂ) • J ξ
  rw [J.map_smulₛₗ]
  simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableConjugacyAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugacy on a countable Hilbert direct sum

The decomposition and reconstruction properties below describe a given
block decomposition. They do not assert that an arbitrary algebra admits
one. Coordinate conjugacies assemble without changing their uniform bound.
-/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

def RepresentsBlockOperators (F : ∀ n, E n →L[ℂ] E n)
    (T : lp E 2 →L[ℂ] lp E 2) : Prop :=
  ∀ f n, (T f) n = F n (f n)

structure BlockAlgebraDecomposition (M : ∀ n, VonNeumannAlgebra (E n))
    (A : VonNeumannAlgebra (lp E 2)) : Prop where
  decompose : ∀ T ∈ A, ∃ F : ∀ n, E n →L[ℂ] E n,
    (∀ n, ‖F n‖ ≤ ‖T‖) ∧ (∀ n, F n ∈ M n) ∧ RepresentsBlockOperators F T
  reconstruct : ∀ (F : ∀ n, E n →L[ℂ] E n) (C : ℝ), 0 ≤ C →
    (∀ n, ‖F n‖ ≤ C) → (∀ n, F n ∈ M n) →
    ∃ T ∈ A, RepresentsBlockOperators F T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialConjugacyTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting an implementer through Hilbert coordinates -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def spatialTransportUnitary (e : H ≃ₗᵢ[ℂ] K) (u : unitary (H →L[ℂ] H)) :
    unitary (K →L[ℂ] K) :=
  Unitary.map (StarMonoidHom.ofClass e.conjStarAlgEquiv) u

@[simp] theorem coe_spatialTransportUnitary (e : H ≃ₗᵢ[ℂ] K)
    (u : unitary (H →L[ℂ] H)) :
    (spatialTransportUnitary e u : K →L[ℂ] K) = e.conjStarAlgEquiv u := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedCentralDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published common central decomposition input

Blackadar, *Operator Algebras* (Springer, 2006), III.1.6.2--4 and
III.5.1.10--14: central decomposition on separable Hilbert space,
simultaneous decomposition of norm-separable C-star subalgebras, and
reconstruction of bounded measurable fields. The common C-star algebra is
required to commute with the common center so that it is decomposable. The dimension strata are
trivialized over standard Borel spaces with finite measures.

Only this structural input is retained. In particular, the proposition
below contains no distance estimate, implementer or stability conclusion.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

structure MeasuredHilbertStratum where
  X : Type u
  [measurableX : MeasurableSpace X]
  [standardX : StandardBorelSpace X]
  K : Type u
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  [separableK : SeparableSpace K]
  [measurableK : MeasurableSpace K]
  [borelK : BorelSpace K]
  μ : Measure X
  [finiteμ : IsFiniteMeasure μ]

attribute [instance] MeasuredHilbertStratum.measurableX MeasuredHilbertStratum.standardX
  MeasuredHilbertStratum.normedK MeasuredHilbertStratum.innerK MeasuredHilbertStratum.completeK
  MeasuredHilbertStratum.separableK MeasuredHilbertStratum.measurableK
  MeasuredHilbertStratum.borelK MeasuredHilbertStratum.finiteμ

abbrev MeasuredHilbertStratum.space (S : MeasuredHilbertStratum.{u}) := Lp S.K 2 S.μ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant of the scalar matrix copy

Commuting with all scalar matrix units forces a matrix over any complex
C⋆-algebra to be a constant diagonal matrix. The corresponding statement
for unitaries retains an actual unitary coefficient.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant diagonal copy of the coefficient algebra. -/
def matrixScalarHom : A →⋆ₐ[ℂ] CStarMatrix ι ι A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    { (Matrix.scalarAlgHom ι ℂ : A →ₐ[ℂ] Matrix ι ι A) with
      map_star' := by
        intro a
        ext i j
        change (if i = j then star a else 0) = star (if j = i then a else 0)
        by_cases hij : i = j <;> simp [hij, eq_comm] }

@[simp]
theorem matrixScalarHom_apply (a : A) (i j : ι) :
    matrixScalarHom a i j = if i = j then a else 0 := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommutantLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary lifts respecting the scalar matrix commutant

The matrix ultrapower equivalence identifies the scalar-matrix commutant
with the diagonal coefficient quotient. The proved coordinatewise finite
polar construction then gives a lift which is diagonal at every coordinate.
-/

namespace KadisonKastler

noncomputable section

variable {A B C ι : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [Fintype ι] [DecidableEq ι]

local instance diagonalLiftSourceOrder_r7efc64_1 : PartialOrder A := CStarAlgebra.spectralOrder _
local instance diagonalLiftSourceStarOrder_r7efc64_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance diagonalLiftTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder _
local instance diagonalLiftTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixLiftConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugating finite-matrix lifts by a diagonal unitary

Conjugating the inner matrix units changes only the finite matrix algebra
in which a representative lies. Both the concrete embedding and its
bounded sequence version respect this conjugation exactly.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B ι κ : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local instance matrixLiftScalarOrder_r7efc64_1 : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance matrixLiftScalarStarOrder_r7efc64_1 : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _
local instance matrixLiftSourceOrder_r7efc64_1 : PartialOrder A := CStarAlgebra.spectralOrder _
local instance matrixLiftSourceStarOrder_r7efc64_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance matrixLiftTargetOrder_r7efc64_1 : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixLiftTargetStarOrder_r7efc64_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
/-- Map the chosen matrix units under the inner star automorphism. -/
def conjugatedMatrixUnits (E : Generator.MatrixUnitSystem ι A) (z : unitary A) :
    Generator.MatrixUnitSystem ι A :=
  E.map (Unitary.conjStarAlgAut ℂ A z).toStarAlgHom

@[simp]
theorem conjugatedMatrixUnits_entry (E : Generator.MatrixUnitSystem ι A)
    (z : unitary A) (i j : ι) :
    (conjugatedMatrixUnits E z).entry i j = (z : A) * E.entry i j * star (z : A) := rfl

@[simp]
theorem matrixScalarHom_mul_apply (a : A) (x : CStarMatrix κ κ A) (i j : κ) :
    (matrixScalarHom (ι := κ) a * x) i j = a * x i j := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

@[simp]
theorem mul_matrixScalarHom_apply (x : CStarMatrix κ κ A) (a : A) (i j : κ) :
    (x * matrixScalarHom (ι := κ) a) i j = x i j * a := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PeriodicMatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite full matrix algebras from countable matrix units

The finite algebras need not be increasing. Their matrix units agree with
the countable matrix units on any fixed finite collection of columns once
the matrix size is large enough.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def CuntzFamily.matrixUnits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : CuntzFamily ι H) : Generator.MatrixUnitSystem ι (H →L[ℂ] H) where
  entry i j := S.entry i * star (S.entry j)
  star_entry i j := by simp only [star_mul, star_star]
  mul_entry i j k l := by
    calc
      _ = S.entry i * (star (S.entry j) * S.entry k) * star (S.entry l) := by
        simp only [mul_assoc]
      _ = _ := by rw [S.orthogonal]; split_ifs <;> simp
  total := S.total

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerStateConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A single state comparison from two corner conjugations

Normalized corner estimates combine under the unitary formed from
two complementary corner unitaries. The resulting state comparison
is bounded by the sum of the corner errors.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def sandwichFunctional (φ : A →L[ℂ] ℂ) (u : A) : A →L[ℂ] ℂ :=
  φ.comp (((ContinuousLinearMap.mul ℂ A).flip u).comp
    (ContinuousLinearMap.mul ℂ A (star u)))

@[simp] theorem sandwichFunctional_apply (φ : A →L[ℂ] ℂ) (u x : A) :
    sandwichFunctional φ u x = φ (star u*x*u) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerUnitaryExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending corner unitaries by the identity

Finite signed groups in a proper matrix corner act as the identity on
its complementary subspace. These algebraic identities retain that action.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A]
  [Ring B] [StarRing B] [_root_.Algebra ℂ B]

/-- Adding the complementary identity respects multiplication on the range
of a nonunital star homomorphism. -/
theorem add_complement_mul (φ : A →⋆ₙₐ[ℂ] B) (a b : A) :
    (φ a + (1 - φ 1)) * (φ b + (1 - φ 1)) = φ (a * b) + (1 - φ 1) := by
  have hl (x : A) : φ x * (1 - φ 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_one, sub_self]
  have hr (x : A) : (1 - φ 1) * φ x = 0 := by
    rw [sub_mul, one_mul, ← map_mul, one_mul, sub_self]
  have hp : (1 - φ 1) * (1 - φ 1) = 1 - φ 1 := by
    rw [sub_mul, one_mul, hl 1, sub_zero]
  rw [add_mul, mul_add, mul_add, hl, hr, hp, add_zero, zero_add, ← map_mul]

/-- A unitary in a represented corner is a unitary on the whole space after
adding the complementary identity. -/
def cornerUnitaryExtension (φ : A →⋆ₙₐ[ℂ] B) : unitary A →* unitary B where
  toFun u := ⟨φ u.val + (1 - φ 1), by
    constructor
    · change star (φ u.val + (1 - φ 1)) * (φ u.val + (1 - φ 1)) = 1
      rw [star_add, star_sub, star_one, ← map_star, ← map_star, star_one,
        add_complement_mul, u.property.1]
      abel
    · change (φ u.val + (1 - φ 1)) * star (φ u.val + (1 - φ 1)) = 1
      rw [star_add, star_sub, star_one, ← map_star, ← map_star, star_one,
        add_complement_mul, u.property.2]
      abel⟩
  map_one' := Subtype.ext (by change φ 1 + (1 - φ 1) = 1; abel)
  map_mul' u v := Subtype.ext (add_complement_mul φ u.val v.val).symm

@[simp]
theorem cornerUnitaryExtension_coe (φ : A →⋆ₙₐ[ℂ] B) (u : unitary A) :
    (cornerUnitaryExtension φ u : B) = φ u.val + (1 - φ 1) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableAmplificationNormal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normality and separating vectors for countable amplification

Bounded weak operator limits pass through the countable diagonal action.
A weighted dense sequence is a separating vector for that action. These
are the concrete ingredients for a faithful cyclic representation.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [SeparableSpace H]

def denseSequenceWeight (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (1 + ‖denseSeq H n‖)

omit [InnerProductSpace ℂ H] in
theorem denseSequenceWeight_pos (n : ℕ) : 0 < denseSequenceWeight (H := H) n := by
  unfold denseSequenceWeight
  positivity

theorem norm_weighted_denseSeq_le (n : ℕ) :
    ‖(denseSequenceWeight (H := H) n : ℂ) • denseSeq H n‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (denseSequenceWeight_pos n)]
  unfold denseSequenceWeight
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableRandomWalkLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A symmetric fully supported law for the boundary random walk

The boundary construction starts with a probability law that assigns positive
mass to every element of the countable group. A geometric enumeration gives
such a law, and averaging with its inverse image makes it symmetric.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkEnumeration (G : Type*) [Group G] [Countable G] : ℕ → G :=
  letI := Encodable.ofCountable G
  fun n => (Encodable.decode (α := G) n).getD 1

omit [MeasurableSpace G] [MeasurableSingletonClass G] in
theorem randomWalkEnumeration_surjective : Function.Surjective (randomWalkEnumeration G) := by
  let := Encodable.ofCountable G
  intro g
  exact ⟨Encodable.encode g, by simp [randomWalkEnumeration, Encodable.encodek]⟩

def randomWalkGeometricParameter : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

def enumeratedRandomWalkLaw (G : Type*) [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] : Measure G :=
  (geometricMeasure randomWalkGeometricParameter).map (randomWalkEnumeration G)

instance enumeratedRandomWalkLaw_probability : IsProbabilityMeasure (enumeratedRandomWalkLaw G) := by
  unfold enumeratedRandomWalkLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem enumeratedRandomWalkLaw_singleton_pos (g : G) :
    0 < enumeratedRandomWalkLaw G {g} := by
  obtain ⟨n, hn⟩ := randomWalkEnumeration_surjective (G := G) g
  rw [enumeratedRandomWalkLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton g)]
  have hs : {n} ⊆ randomWalkEnumeration G ⁻¹' {g} := by
    intro m hm
    obtain rfl := Set.mem_singleton_iff.mp hm
    exact hn
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [geometricMeasure_singleton (by norm_num [randomWalkGeometricParameter, Subtype.ext_iff] :
    randomWalkGeometricParameter ≠ 0)]
  apply ENNReal.ofReal_pos.mpr
  exact geometricMeasure_pos
    (by norm_num [randomWalkGeometricParameter, Subtype.ext_iff])
    (by norm_num [randomWalkGeometricParameter, Subtype.ext_iff]) n

def symmetricRandomWalkLaw (G : Type*) [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] : Measure G :=
  (2 : ℝ≥0∞)⁻¹ • enumeratedRandomWalkLaw G +
    (2 : ℝ≥0∞)⁻¹ • (enumeratedRandomWalkLaw G).map Inv.inv

instance symmetricRandomWalkLaw_probability : IsProbabilityMeasure (symmetricRandomWalkLaw G) := by
  have : IsProbabilityMeasure ((enumeratedRandomWalkLaw G).map Inv.inv) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  constructor
  simp only [symmetricRandomWalkLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem symmetricRandomWalkLaw_singleton_pos (g : G) :
    0 < symmetricRandomWalkLaw G {g} := by
  have hp := enumeratedRandomWalkLaw_singleton_pos g
  have hfirst : 0 < (2 : ℝ≥0∞)⁻¹ * enumeratedRandomWalkLaw G {g} :=
    ENNReal.mul_pos (by norm_num) hp.ne'
  exact hfirst.trans_le (le_add_right le_rfl)

theorem symmetricRandomWalkLaw_null_iff (s : Set G) :
    symmetricRandomWalkLaw G s = 0 ↔ s = ∅ := by
  constructor
  · intro hs
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have h := (symmetricRandomWalkLaw_singleton_pos g).trans_le
      (measure_mono (singleton_subset_iff.mpr hg))
    rw [hs] at h
    exact (lt_irrefl 0) h
  · rintro rfl
    exact measure_empty

theorem absolutelyContinuous_symmetricRandomWalkLaw (ν : Measure G) :
    ν ≪ symmetricRandomWalkLaw G := by
  intro s hs
  rw [(symmetricRandomWalkLaw_null_iff s).mp hs, measure_empty]

theorem symmetricRandomWalkLaw_quasi (f : G → G) :
    Measure.QuasiMeasurePreserving f (symmetricRandomWalkLaw G) (symmetricRandomWalkLaw G) :=
  ⟨measurable_of_countable f, absolutelyContinuous_symmetricRandomWalkLaw _⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_SpatialTensor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uE uF uH uK uι


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

namespace UnitalTomsWinter

variable {H : Type uH} {K : Type uK} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev SpatialHilbert (H : Type uH) (K : Type uK) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (H ⊗[ℂ] K)

def spatialTensorOp (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert H K :=
  (TensorProduct.mapL S T).completion

@[simp] lemma spatialTensorOp_coe (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    spatialTensorOp S T x = (TensorProduct.mapL S T x : SpatialHilbert H K) := by
  exact (TensorProduct.mapL S T).completion_apply_coe x

lemma spatialTensorOp_ext {S T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K}
    (h : ∀ x : H, ∀ y : K, S (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) = T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simpa [coe_add] using congrArg₂ (· + ·) hx hy

@[simp] lemma spatialTensorOp_zero_left (T : K →L[ℂ] K) : spatialTensorOp (0 : H →L[ℂ] H) T = 0 := by
  apply spatialTensorOp_ext; intro x y; simp

@[simp] lemma spatialTensorOp_zero_right (S : H →L[ℂ] H) : spatialTensorOp S (0 : K →L[ℂ] K) = 0 := by
  apply spatialTensorOp_ext; intro x y; simp

lemma spatialTensorOp_add_left (S₁ S₂ : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (S₁+S₂) T = spatialTensorOp S₁ T + spatialTensorOp S₂ T := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.add_tmul, coe_add]

lemma spatialTensorOp_add_right (S : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp S (T₁+T₂) = spatialTensorOp S T₁ + spatialTensorOp S T₂ := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.tmul_add, coe_add]

lemma spatialTensorOp_smul_left (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (c • S) T = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, smul_apply]
  rw [← TensorProduct.smul_tmul', coe_smul]

lemma spatialTensorOp_smul_right (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp S (c • T) = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp

lemma spatialTensorOp_mul (S₁ S₂ : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp (S₁*S₂) (T₁*T₂) = spatialTensorOp S₁ T₁ * spatialTensorOp S₂ T₂ := by
  apply spatialTensorOp_ext; intro x y; simp

variable [CompleteSpace H] [CompleteSpace K]

lemma spatialTensorOp_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (star S) (star T) = star (spatialTensorOp S T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    induction x using OAI.tensorInductionOn with
    | add x₁ x₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
    | tmul x₁ x₂ =>
      induction y using OAI.tensorInductionOn with
      | add y₁ y₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
      | tmul y₁ y₂ => simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

end UnitalTomsWinter

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialTensorOp_one : spatialTensorOp (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply spatialTensorOp_ext
  intro x y
  simp

def spatialLeftHom : A →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun a := spatialTensorOp (α a) 1
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_left]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_left,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' a := by rw [map_star,← spatialTensorOp_star,star_one]

def spatialRightHom : B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun b := spatialTensorOp 1 (β b)
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_right]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_right,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' b := by rw [map_star,← spatialTensorOp_star,star_one]

end Pureness

end

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialProduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete spatial tensor product used in the fixed-factor reduction

The spatial von Neumann algebra is the bicommutant of the bounded tensor
operators. Vector slices act on the completed tensor Hilbert space.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev spatialLeft : (H →L[ℂ] H) →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  Pureness.spatialLeftHom (K := K) (StarAlgHom.id ℂ (H →L[ℂ] H))

abbrev spatialRight : (K →L[ℂ] K) →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  Pureness.spatialRightHom (H := H) (StarAlgHom.id ℂ (K →L[ℂ] K))

/-- The map inserting a fixed vector in the second tensor leg. -/
def tensorVector (ξ : K) : H →L[ℂ] SpatialHilbert H K :=
  UniformSpace.Completion.toComplL.comp ((TensorProduct.mkL ℂ H K).flip ξ)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem tensorVector_apply (ξ : K) (x : H) :
    tensorVector ξ x = ((x ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : SpatialHilbert H K) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem norm_tensorVector_apply (ξ : K) (x : H) :
    ‖tensorVector ξ x‖ = ‖x‖ * ‖ξ‖ := by
  simp only [tensorVector_apply, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

/-- The vector slice is concrete compression by the tensor-vector map. -/
def tensorVectorSlice (ξ : K) :
    (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := (tensorVector ξ).adjoint ∘L T ∘L tensorVector ξ
  map_add' S T := by ext x; simp
  map_smul' c T := by ext x; simp

omit [CompleteSpace K] in
@[simp]
theorem tensorVectorSlice_apply (ξ : K)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (x : H) :
    tensorVectorSlice ξ T x = (tensorVector ξ).adjoint (T (tensorVector ξ x)) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableSpatialTensor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `LinearIsometry.fromCompletion` (port compat, absent from our Mathlib). -/
noncomputable def fromCompletionCompat {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : E →ₗᵢ[ℂ] F) : UniformSpace.Completion E →ₗᵢ[ℂ] F where
  toLinearMap := f.toContinuousLinearMap.fromCompletion.toLinearMap
  norm_map' := f.isometry.completion_extension.norm_map_of_map_zero
    f.toContinuousLinearMap.fromCompletion.map_zero

theorem fromCompletionCompat_apply_coe {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : E →ₗᵢ[ℂ] F) (x : E) : fromCompletionCompat f x = f x :=
  ContinuousLinearMap.fromCompletion_apply_coe f.toContinuousLinearMap x

/-! # Countable sums commute with the spatial Hilbert tensor product

The coordinate tensor map preserves inner products on algebraic tensors.
Its completion is onto because it contains every finitely supported tensor
vector. This is the concrete amplification bridge for the constructed
faithful cyclic representation.
-/

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CuntzChangeOfBasis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary change between two finite Cuntz families -/

namespace KadisonKastler.CuntzFamily

open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

theorem changeBasis_mul_star (S T : CuntzFamily ι H) :
    (∑ i, S.entry i*star (T.entry i))*star (∑ i, S.entry i*star (T.entry i))=1 := by
  rw [star_sum]
  simp only [star_mul,star_star,Finset.sum_mul,Finset.mul_sum]
  have he (i j : ι) : S.entry i*star (T.entry i)*(T.entry j*star (S.entry j)) =
      S.entry i*(star (T.entry i)*T.entry j)*star (S.entry j) := by simp only [mul_assoc]
  simp only [he,T.orthogonal]
  simpa using S.total

def changeBasis (S T : CuntzFamily ι H) : unitary (H →L[ℂ] H) :=
  ⟨∑ i, S.entry i*star (T.entry i),by
    constructor
    · have h := changeBasis_mul_star T S
      simpa only [star_sum,star_mul,star_star] using h
    · exact changeBasis_mul_star S T⟩

end

end KadisonKastler.CuntzFamily

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonVectorAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vector integration for Poisson smoothing

The averages are taken on each Hilbert-space vector. No norm measurability
of an operator-valued field is required. The fixed standard Cauchy measure
allows dominated convergence at every point of strong continuity.
-/

namespace KadisonKastler

open MeasureTheory Filter Topology

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integrable_vectorField (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    {C : ℝ} (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (x : H) :
    Integrable (fun s => F s x) μ := by
  apply (integrable_const (C * ‖x‖)).mono' (hm x)
  filter_upwards [hb] with s hs
  exact ((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x))

/-- An actual bounded operator obtained by integrating its values on vectors. -/
def probabilityOperatorIntegral (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ s, F s x ∂μ
      map_add' := fun x y => by
        simp only [map_add]
        exact integral_add (integrable_vectorField μ F hm hb x)
          (integrable_vectorField μ F hm hb y)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c (fun s => F s x) }
    C (fun x => by
      have h := norm_integral_le_of_norm_le_const (μ := μ) (C := C * ‖x‖)
        (by
          filter_upwards [hb] with s hs
          exact ((F s).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
      simpa using h)

omit [CompleteSpace H] in
@[simp] theorem probabilityOperatorIntegral_apply (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (x : H) :
    probabilityOperatorIntegral μ F hm C hb x = ∫ s, F s x ∂μ := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurablePoisson
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Poisson integration of bounded vector-measurable operator fields

The analytic multiplier fields need only be measurable on each vector.
These averages therefore use vector integrals, without asserting norm
measurability of a field valued in the bounded operators.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cauchyMeasure_absolutelyContinuous (t : ℝ) {r : ℝ} (hr : 0 < r) :
    cauchyMeasure t (NNReal.mk r hr.le) ≪ volume := by
  rw [cauchyMeasure_of_scale_ne_zero t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h))]
  exact withDensity_absolutelyContinuous _ _

def measurablePoissonAverage (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  probabilityOperatorIntegral (cauchyMeasure t (NNReal.mk r hr.le)) F
    (fun x => AEStronglyMeasurable.mono_ac (cauchyMeasure_absolutelyContinuous t hr) (hF x))
    C ((cauchyMeasure_absolutelyContinuous t hr).ae_le hC)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonBoundaryLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The strong-star boundary comparison used in modular smoothing

The demodulated Cauchy averages are actual bounded operators. Their products
converge strongly-* even though the polar smoothing paths need not converge.
-/

namespace KadisonKastler

open Filter MeasureTheory
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_unitary_le_one' (v : unitary (H →L[ℂ] H)) :
    ‖(v : H →L[ℂ] H)‖ ≤ 1 := by
  nontriviality (H →L[ℂ] H)
  exact (CStarRing.norm_coe_unitary v).le

def modulatedUnitaryField (W : ℝ → unitary (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  (Circle.exp t : ℂ) • (W t : H →L[ℂ] H)

theorem modulatedUnitaryField_continuous (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (x : H) :
    Continuous (fun t => modulatedUnitaryField W t x) :=
  (continuous_subtype_val.comp Circle.exp.continuous).smul (hW x)

theorem norm_modulatedUnitaryField_le_one (W : ℝ → unitary (H →L[ℂ] H)) (t : ℝ) :
    ‖modulatedUnitaryField W t‖ ≤ 1 := by
  simpa only [modulatedUnitaryField, norm_smul, Circle.norm_coe, one_mul] using
    norm_unitary_le_one' (W t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DemodulatedPoisson
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual demodulated smoothing fields

These are the fields used before polar decomposition. An essential bound
on the boundary, or an essential comparison with the modulated modular
unitaries, passes to a uniform norm bound at every positive height.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def demodulatedPoissonAverage (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  ((Real.exp r : ℂ) * star (Circle.exp t : ℂ)) •
    measurablePoissonAverage F hF C hC t r hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCornerGroups
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite signed groups in a countable matrix corner

Each finite group acts on the first finitely many matrix summands and as
the identity on their orthogonal complement.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

/-- The signed matrix representation with the C-star matrix type explicit. -/
def signedCStarRepresentation (n : ℕ) : SignedPermutation (Fin n) →*
    unitary (CStarMatrix (Fin n) (Fin n) ℂ) where
  toFun g := ⟨CStarMatrix.ofMatrix (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ), by
    change star (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) *
        (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) = 1 ∧
      (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) *
        star (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) = 1
    exact (signedPermutationHom g).property⟩
  map_one' := Subtype.ext (congrArg Subtype.val (map_one signedPermutationHom))
  map_mul' g h := Subtype.ext (congrArg Subtype.val (map_mul signedPermutationHom g h))

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCornerRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compatibility of finite signed corner groups -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Extend a finite permutation by fixing the added last coordinate. -/
def cornerSuccessorPermutation (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  σ.viaFintypeEmbedding ⟨Fin.castSucc, Fin.castSucc_injective n⟩

@[simp]
theorem cornerSuccessorPermutation_castSucc (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    cornerSuccessorPermutation σ i.castSucc = (σ i).castSucc :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _

@[simp]
theorem cornerSuccessorPermutation_last (σ : Equiv.Perm (Fin n)) :
    cornerSuccessorPermutation σ (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteMatrixBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite index changes for the rectangular matrix estimates used in row averaging. -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Complete bounds apply to arbitrary finite square index types. -/
theorem CompletelyBoundedBy.finite_square {F : A →ₗ[ℂ] B} {c : ℝ}
    (hF : CompletelyBoundedBy F c) {ι : Type*} [Fintype ι]
    (X : CStarMatrix ι ι A) : ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖ := by
  classical
  let e := Fintype.equivFin ι
  let eA := CStarMatrix.reindexₐ ℂ A e
  let eB := CStarMatrix.reindexₐ ℂ B e
  have h := hF (Fintype.card ι) (Fintype.card ι) (eA X)
  have he : CStarMatrix.mapₗ F (eA X) = eB (CStarMatrix.mapₗ F X) := rfl
  have hA : ‖eA X‖ = ‖X‖ := NonUnitalStarAlgHom.norm_map eA.toStarAlgHom eA.injective X
  have hB : ‖eB (CStarMatrix.mapₗ F X)‖ = ‖CStarMatrix.mapₗ F X‖ :=
    NonUnitalStarAlgHom.norm_map eB.toStarAlgHom eB.injective _
  rwa [he, hA, hB] at h

/-- Complete bounds apply to arbitrary finite rectangular index types. -/
theorem CompletelyBoundedBy.finite {F : A →ₗ[ℂ] B} {c : ℝ}
    (hF : CompletelyBoundedBy F c) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : CStarMatrix ι κ A) : ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖ := by
  have h := hF.finite_square (rectangularCorner X)
  rwa [← rectangularCorner_map, norm_rectangularCorner, norm_rectangularCorner] at h

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangular_toCLM_mul_finite {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    CStarMatrix.toCLM (X * Y) = (CStarMatrix.toCLM Y).comp (CStarMatrix.toCLM X) := by
  ext v i
  simp only [CStarMatrix.toCLM_apply, ContinuousLinearMap.comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v X Y).symm i

theorem rectangular_norm_mul_le_finite {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  simp only [CStarMatrix.norm_def, rectangular_toCLM_mul_finite]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteRowAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite row averages, their composition law, and the cochain identity.
These are the algebraic operations of Christensen--Sinclair row averaging.
No existence of an invariant averaging projection is assumed here. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Average a linear map by a finite row. -/
def finiteRightAverage (r : ι → A) : (A →ₗ[ℂ] A) →ₗ[ℂ] (A →ₗ[ℂ] A) where
  toFun F :=
    { toFun := fun x => ∑ i, F (x * r i) * star (r i)
      map_add' := by intros; simp [add_mul, map_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [map_smul, Finset.smul_sum] }
  map_add' := by intros; ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; ext x; simp [Finset.smul_sum]

@[simp] theorem finiteRightAverage_apply (r : ι → A) (F : A →ₗ[ℂ] A) (x : A) :
    finiteRightAverage r F x = ∑ i, F (x * r i) * star (r i) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertPairRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A pair of representations on its Hilbert direct sum -/

namespace KadisonKastler

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def hilbertPairOperator (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp
    ((a.prodMap b).comp (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toContinuousLinearMap)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertPairOperator_fst (a : E →L[ℂ] E) (b : F →L[ℂ] F)
    (x : WithLp 2 (E × F)) : (hilbertPairOperator a b x).fst = a x.fst := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertPairOperator_snd (a : E →L[ℂ] E) (b : F →L[ℂ] F)
    (x : WithLp 2 (E × F)) : (hilbertPairOperator a b x).snd = b x.snd := rfl

theorem hilbertPairOperator_star (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    star (hilbertPairOperator a b) = hilbertPairOperator (star a) (star b) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hilbertPairOperator a b).adjoint x) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (a y.fst) x.fst + inner ℂ (b y.snd) x.snd =
    inner ℂ y.fst (a.adjoint x.fst) + inner ℂ y.snd (b.adjoint x.snd)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]

variable {A : Type*} [Semiring A] [StarRing A] [_root_.Algebra ℂ A]

def hilbertPairRepresentation (ρ : A →⋆ₐ[ℂ] (E →L[ℂ] E))
    (σ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    A →⋆ₐ[ℂ] (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) where
  toFun a := hilbertPairOperator (ρ a) (σ a)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ 1 x.fst, σ 1 x.snd) = (x.fst, x.snd)
    simp only [map_one, one_apply_eq_self]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ (a * b) x.fst, σ (a * b) x.snd) =
      (ρ a (ρ b x.fst), σ a (σ b x.snd))
    simp only [map_mul, mul_apply_eq_comp]
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ 0 x.fst, σ 0 x.snd) = (0, 0)
    simp only [map_zero, zero_apply]
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ (a + b) x.fst, σ (a + b) x.snd) =
      (ρ a x.fst + ρ b x.fst, σ a x.snd + σ b x.snd)
    simp only [map_add, add_apply]
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ (algebraMap ℂ A r) x.fst, σ (algebraMap ℂ A r) x.snd) =
      (r • x.fst, r • x.snd)
    rw [AlgHomClass.commutes ρ, AlgHomClass.commutes σ]
    rfl
  map_star' a := by
    rw [map_star, map_star, hilbertPairOperator_star]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedMatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compatible finite signed groups under matrix refinement

Keeping the first matrix coordinates as sums over the new coordinates keeps
the old signed-permutation group inside the new finite group.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A ι κ : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The finite subgroup actually represented by the matrix units. -/
def matrixSignedGroup (E : Generator.MatrixUnitSystem ι A) : Subgroup (unitary A) :=
  (matrixUnitSignedRepresentation E).range

theorem signedRepresentation_diagonal (E : Generator.MatrixUnitSystem ι A) (d : ι → ℤˣ) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inl d) : A) =
      ∑ i, ((d i : ℤ) : ℂ) • E.entry i i := by
  rw [matrixUnitSignedRepresentation_inl]
  simp [Generator.MatrixUnitSystem.hom_apply, signDiagonal, Matrix.diagonal, ite_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixChainEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Embedding an increasing full-matrix closure

Compatible frames give an increasing sequence of finite unitary groups.
Their union generates the original von Neumann algebra, so its invariant
mean provides a single simultaneous embedding of the entire closure.
-/

namespace KadisonKastler

noncomputable section

variable {U : Type*} [Group U]

/-- The union of a monotone sequence of subgroups, as a subgroup. -/
def increasingSubgroupUnion (K : ℕ → Subgroup U) (hK : Monotone K) : Subgroup U where
  carrier := {u | ∃ n, u ∈ K n}
  one_mem' := ⟨0, (K 0).one_mem⟩
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨max n m, (K (max n m)).mul_mem
      (hK (Nat.le_max_left n m) hn) (hK (Nat.le_max_right n m) hm)⟩
  inv_mem' := by
    rintro a ⟨n, hn⟩
    exact ⟨n, (K n).inv_mem hn⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCornerConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independent unitary actions on an off-diagonal corner

Two orthogonal isometries identify the ambient algebra with its two-by-two
amplification. Block-diagonal conjugations then act independently on the
two sides of an off-diagonal coefficient. Convexity extends this action
to multiplication by small contractions.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CuntzFamily

variable (S : CuntzFamily (Fin 2) H)

def upperRightLinearMap : (H →L[ℂ] H) →ₗ[ℝ] (H →L[ℂ] H) :=
  { toFun T := S.matrix T 0 1
    map_add' T U := by simp [matrix, mul_add, add_mul]
    map_smul' t T := by simp [matrix] }

end CuntzFamily

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NestAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging operators preserving a projection nest

This is the algebraic averaging step after the nest distance estimate.
The projections may be indexed by any type; completeness of the nest is
needed by the distance theorem, not by these preservation calculations.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def PreservesProjectionNest (P : ι → H →L[ℂ] H) (T : H →L[ℂ] H) : Prop :=
  ∀ i, (1 - P i) * T * P i = 0

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedGraphRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prepared graph comparison from individual row approximants

Only a separate nearby row is required for each finite row in either
algebra. No global linear map selecting those approximants is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedGraphRowsOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftInvariantSigma
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The invariant sigma algebra of the nonsingular boundary shift

Using this measurable space directly avoids a redundant point-set coding of
the boundary. Its measurable sets are exactly the ambient measurable sets
fixed by the shift modulo null sets.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : X → X)

@[instance_reducible]
def shiftInvariantSigma : MeasurableSpace X where
  MeasurableSet' A := MeasurableSet A ∧ ∀ᵐ x ∂μ, S x ∈ A ↔ x ∈ A
  measurableSet_empty := ⟨MeasurableSet.empty, Filter.Eventually.of_forall (by simp)⟩
  measurableSet_compl A hA := ⟨hA.1.compl, hA.2.mono (fun _ h => not_congr h)⟩
  measurableSet_iUnion A hA := by
    refine ⟨MeasurableSet.iUnion (fun n => (hA n).1), ?_⟩
    filter_upwards [ae_all_iff.mpr (fun n => (hA n).2)] with x hx
    simpa only [Set.mem_iUnion] using exists_congr hx

theorem shiftInvariantSigma_le : shiftInvariantSigma μ S ≤ ‹MeasurableSpace X› :=
  fun _ h => h.1

def shiftInvariantMeasure : @Measure X (shiftInvariantSigma μ S) :=
  μ.trim (shiftInvariantSigma_le μ S)

theorem measurable_shiftInvariantSigma_of_commuting
    (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) :
    @Measurable X X (shiftInvariantSigma μ S) (shiftInvariantSigma μ S) T := by
  intro A hA
  refine ⟨hT.measurable hA.1, ?_⟩
  filter_upwards [hT.ae hA.2] with x hx
  change T (S x) ∈ A ↔ T x ∈ A
  rw [← hcomm]
  exact hx

theorem quasi_shiftInvariantSigma_of_commuting
    (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) :
    @Measure.QuasiMeasurePreserving X X (shiftInvariantSigma μ S) (shiftInvariantSigma μ S)
      T (shiftInvariantMeasure μ S) (shiftInvariantMeasure μ S) := by
  have hm := measurable_shiftInvariantSigma_of_commuting μ S T hT hcomm
  refine ⟨hm, Measure.AbsolutelyContinuous.mk ?_⟩
  intro A hA hzero
  have hzero' : μ A = 0 := by
    rwa [shiftInvariantMeasure, trim_measurableSet_eq _ hA] at hzero
  rw [Measure.map_apply hm hA, shiftInvariantMeasure,
    trim_measurableSet_eq _ (hm hA)]
  exact hT.preimage_null hzero'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakHilbertConvexLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closed convex constraints on weak scalar limits

Separation retains closed convex conditions under a bounded Hilbert-space
weak limit. Applied in L2, this retains almost-everywhere disk and positivity
conditions for the scalar boundary averages.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

theorem mem_closed_convex_of_dual_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} {l : Filter ι} [l.NeBot] {C : Set E} (hC : IsClosed C)
    (hc : Convex ℝ C) (v : ι → E) (x : E) (hv : ∀ i, v i ∈ C)
    (ht : ∀ f : E →L[ℂ] ℂ, Tendsto (fun i => f (v i)) l (𝓝 (f x))) : x ∈ C := by
  by_contra hx
  obtain ⟨f, a, hf, hax⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hc hC hx
  have hr := (Complex.continuous_re.tendsto _).comp (ht f)
  exact hax.not_ge (le_of_tendsto hr (Eventually.of_forall (fun i => (hf _ (hv i)).le)))

theorem dual_tendsto_of_inner_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} {l : Filter ι} (v : ι → H) (x : H)
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (v i)) l (𝓝 (inner ℂ y x)))
    (f : H →L[ℂ] ℂ) : Tendsto (fun i => f (v i)) l (𝓝 (f x)) := by
  let y := (InnerProductSpace.toDual ℂ H).symm f
  have hy (z : H) : inner ℂ y z = f z := InnerProductSpace.toDual_symm_apply
  simpa only [hy] using ht y

theorem mem_closed_convex_of_pair_inner_tendsto
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι} [l.NeBot] {C : Set (H × K)} (hC : IsClosed C)
    (hc : Convex ℝ C) (v : ι → H) (w : ι → K) (x : H) (y : K)
    (hv : ∀ i, (v i, w i) ∈ C)
    (ht : ∀ a, Tendsto (fun i => inner ℂ a (v i)) l (𝓝 (inner ℂ a x)))
    (hu : ∀ b, Tendsto (fun i => inner ℂ b (w i)) l (𝓝 (inner ℂ b y))) : (x, y) ∈ C := by
  apply mem_closed_convex_of_dual_tendsto (l := l) hC hc (fun i => (v i, w i)) (x, y) hv
  intro f
  have hs (a : H) (b : K) : f (a, b) =
      (f.comp (ContinuousLinearMap.inl ℂ H K)) a +
      (f.comp (ContinuousLinearMap.inr ℂ H K)) b := by
    change f (a, b) = f (a, 0) + f (0, b)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  simp_rw [hs]
  exact (dual_tendsto_of_inner_tendsto v x ht _).add
    (dual_tendsto_of_inner_tendsto w y hu _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftInvariantFunctions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar functions on the invariant sigma algebra

The invariant measurable structure has exactly the essentially bounded
scalar functions fixed by the shift. The countable rational cuts below
turn invariance of measurable sets into simultaneous pointwise equality.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : X → X}

theorem real_fixed_of_measurable_shiftInvariantSigma {f : X → ℝ}
    (hf : Measurable[shiftInvariantSigma μ S] f) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  have hc (q : ℚ) : ∀ᵐ x ∂μ, f (S x) < (q : ℝ) ↔ f x < (q : ℝ) :=
    (hf (measurableSet_Iio (a := (q : ℝ)))).2
  filter_upwards [ae_all_iff.mpr hc] with x hx
  apply le_antisymm
  · by_contra! h
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn h
    exact (not_lt_of_ge hq₂.le) ((hx q).mpr hq₁)
  · by_contra! h
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn h
    exact (not_lt_of_ge hq₂.le) ((hx q).mp hq₁)

theorem complex_fixed_of_measurable_shiftInvariantSigma {f : X → ℂ}
    (hf : Measurable[shiftInvariantSigma μ S] f) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  have hr := real_fixed_of_measurable_shiftInvariantSigma (Complex.measurable_re.comp hf)
  have hi := real_fixed_of_measurable_shiftInvariantSigma (Complex.measurable_im.comp hf)
  filter_upwards [hr, hi] with x hx hy
  exact Complex.ext hx hy

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductInvariantL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The product range of a one-coordinate invariant projection

An L2 function fixed by the shift in its first coordinate is measurable,
modulo null sets, for the product of the invariant and second sigma algebras.
The proof tests its orthogonal-projection remainder against rectangles.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {S : X → X}

def firstCoordinateShift (S : X → X) (z : X × Y) : X × Y := (S z.1, z.2)

@[instance_reducible]
def firstInvariantSigma (μ : Measure X) (S : X → X) : MeasurableSpace (X × Y) :=
  (shiftInvariantSigma μ S).prod ‹MeasurableSpace Y›

theorem firstCoordinateShift_quasi (hS : Measure.QuasiMeasurePreserving S μ μ) :
    Measure.QuasiMeasurePreserving (firstCoordinateShift (Y := Y) S) (μ.prod ν) (μ.prod ν) :=
  MeasureTheory.QuasiMeasurePreserving.prodMap hS (Measure.QuasiMeasurePreserving.id ν)

omit [IsFiniteMeasure μ] in
theorem firstInvariantSigma_le_shiftInvariantSigma :
    firstInvariantSigma (Y := Y) μ S ≤
      shiftInvariantSigma (μ.prod ν) (firstCoordinateShift S) := by
  have hfst : @Measurable (X × Y) X
      (shiftInvariantSigma (μ.prod ν) (firstCoordinateShift S)) (shiftInvariantSigma μ S)
      Prod.fst := by
    intro A hA
    refine ⟨hA.1.preimage measurable_fst, ?_⟩
    exact (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hA.2
  have hsnd : @Measurable (X × Y) Y
      (shiftInvariantSigma (μ.prod ν) (firstCoordinateShift S)) ‹MeasurableSpace Y›
      Prod.snd := by
    intro B hB
    exact ⟨hB.preimage measurable_snd, Filter.Eventually.of_forall (fun _ => Iff.rfl)⟩
  exact hfst.prodMk hsnd

theorem firstInvariantSigma_fixed (hS : Measure.QuasiMeasurePreserving S μ μ)
    {f : X × Y → ℂ} (hf : AEStronglyMeasurable[firstInvariantSigma μ S] f (μ.prod ν)) :
    ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z := by
  have hm := hf.mono (firstInvariantSigma_le_shiftInvariantSigma (ν := ν))
  have hi := complex_fixed_of_measurable_shiftInvariantSigma hm.stronglyMeasurable_mk.measurable
  filter_upwards [hm.ae_eq_mk, (firstCoordinateShift_quasi (ν := ν) hS).ae hm.ae_eq_mk, hi]
    with z hz hs hi
  exact hs.trans (hi.trans hz.symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkPathAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The nonsingular action on rooted random-walk paths

The root is separated from the sequence of increments. Left translation
changes only the root, and commutes with advancing the random walk.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

abbrev RandomWalkPath := G × (ℕ → G)

def randomWalkPathLaw : Measure (RandomWalkPath G) :=
  (symmetricRandomWalkLaw G).prod (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularRowNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Rectangular row norm estimates on finite Hilbert C-star modules. -/

namespace KadisonKastler

noncomputable section

open scoped WithCStarModule InnerProductSpace
open CStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The C-star norm lower bound holds for rectangular matrices. -/
theorem rectangular_norm_sq_le (X : CStarMatrix ι κ A) :
    ‖X‖ ^ 2 ≤ ‖X * X.conjTranspose‖ := by
  have hmain : ‖X‖ ≤ Real.sqrt ‖X * X.conjTranspose‖ := by
    change ‖CStarMatrix.toCLM X‖ ≤ _
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    rw [norm_eq_sqrt_norm_inner_self (A := A),
      ← CStarMatrix.inner_toCLM_conjTranspose_right]
    have h : ‖⟪v, (CStarMatrix.toCLM X.conjTranspose) (CStarMatrix.toCLM X v)⟫_A‖ ≤
        ‖X * X.conjTranspose‖ * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖v‖ * ‖(CStarMatrix.toCLM X.conjTranspose) (CStarMatrix.toCLM X v)‖ :=
          norm_inner_le (C⋆ᵐᵒᵈ(A, ι → A))
        _ = ‖v‖ * ‖CStarMatrix.toCLM (X * X.conjTranspose) v‖ := by
          rw [rectangular_toCLM_mul_finite]
          rfl
        _ ≤ ‖v‖ * (‖X * X.conjTranspose‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg v)
        _ = _ := by ring
    calc
      _ ≤ Real.sqrt (‖X * X.conjTranspose‖ * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt ‖X * X.conjTranspose‖ * ‖v‖ := by
        rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg v)]
  exact (sq_le_sq₀ (norm_nonneg X) (Real.sqrt_nonneg _)).2 hmain |>.trans_eq
    (Real.sq_sqrt (norm_nonneg _))

/-- A contractive row has a contractive adjoint column. -/
theorem rectangular_row_and_column_contract (X : CStarMatrix ι κ A)
    (h : ‖X * X.conjTranspose‖ ≤ 1) : ‖X‖ ≤ 1 ∧ ‖X.conjTranspose‖ ≤ 1 := by
  have hX : ‖X‖ ≤ 1 := by nlinarith [rectangular_norm_sq_le X, norm_nonneg X]
  have hs := rectangular_norm_sq_le X.conjTranspose
  have he : X.conjTranspose.conjTranspose = X := by ext i j; simp
  rw [he] at hs
  have hm := rectangular_norm_mul_le_finite X.conjTranspose X
  have hm' : ‖X.conjTranspose * X‖ ≤ ‖X.conjTranspose‖ :=
    hm.trans (by nlinarith [norm_nonneg X.conjTranspose])
  exact ⟨hX, by nlinarith [norm_nonneg X.conjTranspose]⟩


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingCommutantCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant on a reducing subspace is the represented corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

omit [CompleteSpace H] in
/-- An operator commuting with the subspace projection preserves the subspace. -/
theorem invariant_of_commutes_starProjection (T : H →L[ℂ] H)
    (hT : E.starProjection * T = T * E.starProjection) :
    ∀ x ∈ E, T x ∈ E := by
  intro x hx
  apply Submodule.starProjection_eq_self_iff.mp
  have hh := congrArg (fun A : H →L[ℂ] H => A x) hT
  change E.starProjection (T x) = T (E.starProjection x) at hh
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at hh
  exact hh

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowReplication
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The diagonal replication of a row and the matrix formula for averaging. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι]

/-- Place the same row along the diagonal of a rectangular matrix. -/
def rowReplication (r : κ → A) : CStarMatrix ι (ι × κ) A :=
  CStarMatrix.ofMatrix fun i jk => if i = jk.1 then r jk.2 else 0

omit [Fintype ι] [Fintype κ] in
@[simp] theorem rowReplication_apply (r : κ → A) (i : ι) (jk : ι × κ) :
    rowReplication r i jk = if i = jk.1 then r jk.2 else 0 := rfl

/-- Replicating a normalized row gives a coisometry. -/
theorem rowReplication_mul_star (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    rowReplication (ι := ι) r * (rowReplication (ι := ι) r).conjTranspose = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [CStarMatrix.mul_apply, Fintype.sum_prod_type, hr]
  · simp [CStarMatrix.mul_apply, Fintype.sum_prod_type, h, Ne.symm h]

omit [Fintype κ] [Fintype τ] in
/-- Multiplication by the replicated row appends its entries. -/
theorem mul_rowReplication_apply (X : CStarMatrix τ ι A) (r : κ → A)
    (i : τ) (jk : ι × κ) :
    (X * rowReplication (ι := ι) r : CStarMatrix τ (ι × κ) A) i jk = X i jk.1 * r jk.2 := by
  simp [CStarMatrix.mul_apply, mul_ite]

omit [Fintype τ] in
/-- The same row average operates at every matrix level. -/
theorem finiteRightAverage_matrix (r : κ → A) (F : A →ₗ[ℂ] A)
    (X : CStarMatrix τ ι A) :
    CStarMatrix.mapₗ (finiteRightAverage r F) X =
      CStarMatrix.mapₗ F (X * rowReplication r) * (rowReplication r).conjTranspose := by
  ext i j
  change (∑ k, F (X i j * r k) * star (r k)) =
    ∑ jk : ι × κ, F ((X * rowReplication r : CStarMatrix τ (ι × κ) A) i jk) *
      star (rowReplication r j jk)
  simp_rw [mul_rowReplication_apply]
  simp only [Fintype.sum_prod_type, rowReplication_apply]
  simp_rw [apply_ite star, star_zero, mul_ite, mul_zero]
  simp


variable [PartialOrder A] [StarOrderedRing A]

theorem rowReplication_norm_bounds (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    ‖rowReplication (ι := ι) r‖ ≤ 1 ∧ ‖(rowReplication (ι := ι) r).conjTranspose‖ ≤ 1 := by
  apply rectangular_row_and_column_contract
  rw [rowReplication_mul_star r hr]
  have h := CStarRing.norm_star_mul_self (x := (1 : CStarMatrix ι ι A))
  simp only [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : CStarMatrix ι ι A)]

/-- Finite normalized row averages contract the complete norm. -/
theorem CompletelyBoundedBy.finiteRightAverage {F : A →ₗ[ℂ] A} {c : ℝ}
    (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c)
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    CompletelyBoundedBy (finiteRightAverage r F) c := by
  intro p q X
  have hb := rowReplication_norm_bounds (ι := Fin q) r hr
  rw [finiteRightAverage_matrix]
  calc
    _ ≤ ‖CStarMatrix.mapₗ F (X * rowReplication r)‖ * ‖(rowReplication r).conjTranspose‖ :=
      rectangular_norm_mul_le_finite _ _
    _ ≤ (c * (‖X‖ * ‖rowReplication r‖)) * ‖(rowReplication r).conjTranspose‖ := by
      gcongr
      exact (hF.finite _).trans (mul_le_mul_of_nonneg_left (rectangular_norm_mul_le_finite _ _) hc)
    _ ≤ c * ‖X‖ := by
      calc
        _ ≤ (c * (‖X‖ * 1)) * 1 := by gcongr; exacts [hb.1, hb.2]
        _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPositiveLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity of scalar averages and their weak limit -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

def scalarPositiveCone : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}

theorem scalarPositiveCone_isClosed : IsClosed scalarPositiveCone :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPullbackWeakGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weak closure of the nonsingular pullback graph

Pullback need not be a bounded operator on L2. Its graph is nonetheless
closed: norm-convergent pairs have subsequences converging pointwise, and
nonsingularity transports the first almost-everywhere limit. Linearity then
makes this graph weakly closed. This suffices for the boundary averages.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)

def scalarL2PullbackGraph : Set (Lp ℂ 2 μ × Lp ℂ 2 μ) :=
  {p | ∀ᵐ x ∂μ, p.2 x = p.1 (T x)}

include hT in
theorem isClosed_scalarL2PullbackGraph : IsClosed (scalarL2PullbackGraph (μ := μ) T) := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns, hns, hn⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (continuous_fst.tendsto g |>.comp hfg)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hm⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      ((continuous_snd.tendsto g |>.comp hfg).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hf, hT.ae hn, hm] with x hx hnx hmx
  apply tendsto_nhds_unique hmx
  have he : (fun k => (f (ns (ms k))).2 x) = fun k => (f (ns (ms k))).1 (T x) := by
    funext k
    exact hx (ns (ms k))
  change Tendsto (fun k => (f (ns (ms k))).2 x) atTop (𝓝 (g.1 (T x)))
  rw [he]
  exact hnx.comp hms.tendsto_atTop

include hT in
theorem convex_scalarL2PullbackGraph : Convex ℝ (scalarL2PullbackGraph (μ := μ) T) := by
  intro f hf g hg a b _ha _hb _hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f.2) (b • g.2),
    Lp.coeFn_smul a f.2, Lp.coeFn_smul b g.2,
    hT.ae (Lp.coeFn_add (a • f.1) (b • g.1)),
    hT.ae (Lp.coeFn_smul a f.1), hT.ae (Lp.coeFn_smul b g.1)]
    with x hfx hgx hadd hfa hgb htadd htfa htgb
  change (a • f.2 + b • g.2) x = (a • f.1 + b • g.1) (T x)
  simp only [Pi.add_apply, Pi.smul_apply] at hadd hfa hgb htadd htfa htgb
  rw [hadd, hfa, hgb, htadd, htfa, htgb, hfx, hgx]

include hT in
theorem scalarL2PullbackGraph_of_inner_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (f g : ι → Lp ℂ 2 μ) (a b : Lp ℂ 2 μ)
    (hfg : ∀ i, ∀ᵐ x ∂μ, g i x = f i (T x))
    (hf : ∀ y, Tendsto (fun i => inner ℂ y (f i)) l (𝓝 (inner ℂ y a)))
    (hg : ∀ y, Tendsto (fun i => inner ℂ y (g i)) l (𝓝 (inner ℂ y b))) :
    ∀ᵐ x ∂μ, b x = a (T x) :=
  mem_closed_convex_of_pair_inner_tendsto (isClosed_scalarL2PullbackGraph T hT)
    (convex_scalarL2PullbackGraph T hT) f g a b hfg hf hg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftBoundarySpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The boundary as the invariant measurable space

Only its measurable structure enters the application. Keeping the original
points and restricting their sigma algebra gives the probability boundary
directly, with a nonsingular action induced by the rooted path action.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : X → X)

def ShiftBoundarySpace (_μ : Measure X) (_S : X → X) := X

instance instMeasurableSpaceShiftBoundarySpace : MeasurableSpace (ShiftBoundarySpace μ S) :=
  @shiftInvariantSigma X ‹MeasurableSpace X› μ S

def shiftBoundaryMeasure : Measure (ShiftBoundarySpace μ S) := shiftInvariantMeasure μ S

def shiftBoundaryMap : X → ShiftBoundarySpace μ S := id

theorem shiftBoundaryMap_measurePreserving :
    MeasurePreserving (shiftBoundaryMap μ S) μ (shiftBoundaryMeasure μ S) := by
  refine ⟨measurable_id'' (shiftInvariantSigma_le μ S), ?_⟩
  exact (trim_eq_map (shiftInvariantSigma_le μ S)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `LinearIsometry.toContinuousLinearMap_completion` (port compat). -/
theorem linearIsometryToCLMCompletionCompat {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) :
    f.completion.toContinuousLinearMap = f.toContinuousLinearMap.completion := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.completion.continuous f.toContinuousLinearMap.completion.continuous
  | ih x => simp

/-! # Bounded maps and isometries between spatial Hilbert tensors

The rectangular tensor map respects composition and adjoints. In particular,
the tensor of a closed-subspace inclusion is an isometry whose range
projection is the spatial amplification of the original projection.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K E F G J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]

theorem spatialLinearMap_ext {S T : SpatialHilbert H K →L[ℂ] E}
    (h : ∀ x : H, ∀ y : K,
      S ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      T ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul x y => exact h x y
    | add x y hx hy =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hx hy

def spatialMap (a : H →L[ℂ] E) (b : K →L[ℂ] F) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert E F :=
  (TensorProduct.mapL a b).completion

@[simp] theorem spatialMap_tmul (a : H →L[ℂ] E) (b : K →L[ℂ] F) (x : H) (y : K) :
    spatialMap a b ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      ((a x ⊗ₜ[ℂ] b y : E ⊗[ℂ] F) : SpatialHilbert E F) := by
  simp only [spatialMap, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

@[simp] theorem spatialMap_id :
    spatialMap (ContinuousLinearMap.id ℂ H) (ContinuousLinearMap.id ℂ K) =
      ContinuousLinearMap.id ℂ (SpatialHilbert H K) := by
  apply spatialLinearMap_ext
  intro x y
  simp

def spatialIsometry (a : H →ₗᵢ[ℂ] E) (b : K →ₗᵢ[ℂ] F) :
    SpatialHilbert H K →ₗᵢ[ℂ] SpatialHilbert E F :=
  (TensorProduct.mapIsometry a b).completion

theorem spatialIsometry_toContinuousLinearMap (a : H →ₗᵢ[ℂ] E) (b : K →ₗᵢ[ℂ] F) :
    (spatialIsometry a b).toContinuousLinearMap =
      spatialMap a.toContinuousLinearMap b.toContinuousLinearMap := by
  simp only [spatialIsometry, linearIsometryToCLMCompletionCompat,
    TensorProduct.toContinuousLinearMap_mapIsometry, spatialMap]

@[simp] theorem spatialIsometry_tmul (a : H →ₗᵢ[ℂ] E) (b : K →ₗᵢ[ℂ] F)
    (x : H) (y : K) :
    spatialIsometry a b ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      ((a x ⊗ₜ[ℂ] b y : E ⊗[ℂ] F) : SpatialHilbert E F) := by
  change (spatialIsometry a b).toContinuousLinearMap _ = _
  rw [spatialIsometry_toContinuousLinearMap]
  exact spatialMap_tmul _ _ _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix amplification in a spatial tensor product

An actual matrix-unit system in the second tensor factor gives a star
representation of operator-valued matrices. Its norm is the C-star matrix
norm: multiplying on both sides by matrix units recovers each coefficient,
so the representation is faithful whenever the second Hilbert space is
nonzero. No assertion about amplification of an ordinary algebra gap is
used here.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator
open scoped BigOperators TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance spatialMatrixOrder_r7efc64_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialMatrixStarOrder_r7efc64_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- Matrix units on the second tensor leg. -/
def spatialMatrixUnits (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    MatrixUnitSystem ι (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  E.map (spatialRight (H := H))

@[simp]
theorem spatialMatrixUnits_entry (E : MatrixUnitSystem ι (K →L[ℂ] K)) (i j : ι) :
    (spatialMatrixUnits (H := H) E).entry i j = spatialRight (H := H) (E.entry i j) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialRightSlice
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Right-leg slices and the relative commutant of a product centralizer -/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Insert a fixed vector in the first tensor leg. -/
def leftTensorVector (ξ : H) : K →L[ℂ] SpatialHilbert H K :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ H K ξ)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem leftTensorVector_apply (ξ : H) (η : K) :
    leftTensorVector ξ η = ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K) := rfl

/-- Compression in the first leg, with values in operators on the second. -/
def rightTensorSlice (ξ : H) :
    (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) →ₗ[ℂ] (K →L[ℂ] K) where
  toFun T := (leftTensorVector ξ).adjoint ∘L T ∘L leftTensorVector ξ
  map_add' S T := by ext η; simp
  map_smul' c T := by ext η; simp

omit [CompleteSpace H] in
@[simp]
theorem rightTensorSlice_apply (ξ : H)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (η : K) :
    rightTensorSlice ξ T η = (leftTensorVector ξ).adjoint (T (leftTensorVector ξ η)) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SymmetricSupportTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Support isometries for a symmetric vector in a type III factor -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_apply_of_operator_isometry (T : H →L[ℂ] H) (hT : star T * T = 1) (ξ : H) :
    ‖T ξ‖ = ‖ξ‖ := by
  have hi : inner ℂ (T ξ) (T ξ) = inner ℂ ξ ξ := by
    rw [← T.adjoint_inner_right]
    change inner ℂ ξ ((star T * T) ξ) = inner ℂ ξ ξ
    rw [hT,one_apply_eq_self]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),hi]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaPolarCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Polar coordinates for the closed Tomita graph

The first-coordinate map has dense range and zero kernel. Extending the
isometry between the ranges of its adjoint and the positive graph root
identifies the graph Hilbert space with the original Hilbert space.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem denseRange_of_adjoint_injective
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] K) (hA : Function.Injective A.adjoint) : DenseRange A := by
  change Dense (A.range : Set K)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, A.orthogonal_range]
  exact LinearMap.ker_eq_bot.mpr hA

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioReindex
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reindexing the extra family of lambda sites

Even and odd lambda sites absorb a second countable family. Mu sites
are unchanged. This is the explicit state-preserving bijection used in
the pointed infinite tensor-product absorption argument.
-/

namespace KadisonKastler

noncomputable section

abbrev TwoRatioSite := ℕ ⊕ ℕ

/-- The individual diagonal weights of the two-dimensional state. -/
def twoSiteWeight (ν : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then (1 + ν)⁻¹ else ν / (1 + ν)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorCoreField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable operator fields from a countable vector core

Pointwise bounded rational-linear maps commuting with multiplication by
`i` extend to complex-linear operators. Countability gives simultaneous
identities off one null set; dense coefficient tests give measurability.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance vectorCoreNormedSpace : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H

end

end KadisonKastler

end OAI
end


