-- Prove2me | Definitions.Def_Q260K019
-- name    : Q260K019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:56:33.210777+00:00
-- url     : https://prove2.me/theorems/d471974d-8823-477b-be7a-263468b307c0
-- title:
--   Definitions bundle Q260K019 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 133 declarations of OpenAI's Lean: 29 definitions, 2 instances and 102 theorems. The definitions and types are `OAI.KadisonKastler.commonRankFiberAlgebra`, `OAI.KadisonKastler.commonRankOperatorField`, `OAI.KadisonKastler.commonRankStratum`, `OAI.KadisonKastler.commonRankStratumEquiv`, `OAI.KadisonKastler.compressedStratumField`, `OAI.KadisonKastler.coreTraceFrequencyVector`, `OAI.KadisonKastler.doubleGaussianStateAverage`, `OAI.KadisonKastler.finiteGroupBimoduleMean`, `OAI.KadisonKastler.fixedFiberRepresentation`, `OAI.KadisonKastler.gaussianStateAverage`, `OAI.KadisonKastler.instPartialOrderSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence`, `OAI.KadisonKastler.l2CoordinateEquiv`, `OAI.KadisonKastler.l2CoordinateIsometry`, `OAI.KadisonKastler.l2ProjectionStratumAnalysis`, `OAI.KadisonKastler.l2ProjectionStratumSynthesis`, `OAI.KadisonKastler.randomWalkBoundaryMeasure`, `OAI.KadisonKastler.regularBasisSummand`, `OAI.KadisonKastler.regularFrequencyPacket`, `OAI.KadisonKastler.regularFrequencyWindow`, `OAI.KadisonKastler.regularHilbertCoordinates`, `OAI.KadisonKastler.regularPacketCoefficient`, `OAI.KadisonKastler.regularPacketOperator`, `OAI.KadisonKastler.resolventCoordinateOperator`, `OAI.KadisonKastler.resolventScalarMultiplier`, `OAI.KadisonKastler.scalarFourierCut`, `OAI.KadisonKastler.stateActionOrbit`, `OAI.KadisonKastler.twoStateCornerEmbedding`, `OAI.KadisonKastler.twoStateMatrixAlgebra`, `OAI.KadisonKastler.twoStateMatrixVector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CharacterAverageDescent`, `KadisonKastler_CommonRankOperatorFields`, `KadisonKastler_CommonRankSourceModel`, `KadisonKastler_CoreFrequencyCuts`, `KadisonKastler_CoreFrequencyVectors`, `KadisonKastler_CoreTraceFrequencyVector`, `KadisonKastler_CornerUnitary`, `KadisonKastler_DiagonalLocality`, `KadisonKastler_DoubleGaussianKMS`, `KadisonKastler_FiniteGroupAverage`, `KadisonKastler_FixedPointGap`, `KadisonKastler_FourierShiftedFields`, `KadisonKastler_GaussianStateAverage`, `KadisonKastler_L2CoordinateEquiv`, `KadisonKastler_L2Intertwining`, `KadisonKastler_L2LinearFields`, `KadisonKastler_L2ProjectionAnalysis`, `KadisonKastler_L2ProjectionSynthesis`, `KadisonKastler_LiftedRankStrata`, `KadisonKastler_MeasurableFiberRepresentations`, `KadisonKastler_MeasurableNatEnumeration`, `KadisonKastler_ModularRadonNikodym`, `KadisonKastler_NormUltraproduct`, `KadisonKastler_PointedLocalMatrix`, `KadisonKastler_PointedPowerMoments`, `KadisonKastler_ProductBoundaryLifts`, `KadisonKastler_ProjectionDimensionStrata`, `KadisonKastler_ProjectionStratumFields`, `KadisonKastler_RankStratumStandardBorel`, `KadisonKastler_RegularCommutantPackets`, `KadisonKastler_RegularConvolutionCoefficients`, `KadisonKastler_RegularConvolutionOperators`, `KadisonKastler_RegularCoreActions`, `KadisonKastler_RegularCoreAlgebra`, `KadisonKastler_RegularCoreCommutant`, `KadisonKastler_RegularCoreHilbertSum`, `KadisonKastler_RegularCoreRepresentation`, `KadisonKastler_RegularFourierTransport`, `KadisonKastler_RegularIntervalAverages`, `KadisonKastler_RegularIntervalCutoffs`, `KadisonKastler_RegularLocalizationReconstruction`, `KadisonKastler_RegularLocalizedPackets`, `KadisonKastler_RegularPacketAveraging`, `KadisonKastler_RegularPacketIntegrals`, `KadisonKastler_RegularPacketLocalization`, `KadisonKastler_ResolventCoordinateMultiplier`, `KadisonKastler_ResolventCutMeasurable`, `KadisonKastler_ResolventCyclicCuts`, `KadisonKastler_ResolventCyclicMultipliers`, `KadisonKastler_ResolventMeasureFaithful`, `KadisonKastler_ResolventMultiplierBounds`, `KadisonKastler_ResolventMultiplierLimit`, `KadisonKastler_ScalarSectionSelection`, `KadisonKastler_SelfAdjointVectorCompactness`, `KadisonKastler_ShiftBoundarySpace`, `KadisonKastler_SpatialSeparability`, `KadisonKastler_SpatialSlice`, `KadisonKastler_SpectralVectorMeasure`, `KadisonKastler_TwoStateCornerCompression`, `KadisonKastler_TwoStateCornerEmbedding`, `KadisonKastler_TwoStateMatrixAlgebra`, `KadisonKastler_TwoStateMatrixRepresentation`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K009`, `Q260K010`, `Q260K012`, `Q260K013`, `Q260K014` and `Q260K015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K023`, `Q260K024` and `Q260K025`; the statements `OAI.KadisonKastler.commonRankFiberAlgebra_le_commutant`, `OAI.KadisonKastler.commonRankOperatorField_aestronglyMeasurable`, `OAI.KadisonKastler.commonRankOperatorField_norm_le`, `OAI.KadisonKastler.commonRank_factor_fibers`, `OAI.KadisonKastler.commonRank_field_mem_of_closure`, `OAI.KadisonKastler.compressedStratumField_eq_fixedFiberRepresentation`, `OAI.KadisonKastler.coreTraceFrequencyVector_supported_scaling`, `OAI.KadisonKastler.core_kills_window_of_kills_trace_packet`, `OAI.KadisonKastler.normal_marginal_product_agreement`, `OAI_KadisonKastler_quadratic_cochain_of_asymptotic_rows`, `OAI.KadisonKastler.regularCoreEmbedding_symmetry_of_balance`, `OAI.KadisonKastler.regularReflectedConjugation_frequencyWindow` and `OAI.KadisonKastler.regularReflectedConjugation_real_packet`; the proofs of `OAI.KadisonKastler.commonRankFiberAlgebra_le_commutant`, `OAI.KadisonKastler.commonRankOperatorField_aestronglyMeasurable`, `OAI.KadisonKastler.commonRankOperatorField_norm_le`, `OAI_KadisonKastler_commonRank_algebra_decompose`, `OAI.KadisonKastler.commonRank_factor_fibers`, `OAI.KadisonKastler.compressedStratumField_eq_fixedFiberRepresentation`, `OAI.KadisonKastler.first_leg_field_of_product_centralizer`, `OAI.KadisonKastler.regularReflectedConjugation_frequencyWindow`, `OAI.KadisonKastler.regularReflectedConjugation_real_packet`, `OAI.KadisonKastler.scalarCenter_spatialProduct_of_local_swaps` and `OAI.KadisonKastler.spatial_relative_commutant_of_local_swaps`.
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
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Finsupp
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
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Analytic.IsolatedZeros
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
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
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
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.SeparableMeasure
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
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
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K009
import Definitions.Def_Q260K010
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013
import Definitions.Def_Q260K014
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FixedPointGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed-point algebras and the common-action gap

The fixed algebra is an actual von Neumann algebra, defined as a commutant.
The scalar invariant mean constructed in `InvariantOperatorMean` averages
ordinary unit-ball approximants into fixed-point approximants without
increasing either their norm or their error. No existence of a scalar mean
or fixed-point averaging map is postulated here.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {G H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_fixedPointAlgebra_iff (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    T ∈ fixedPointAlgebra U M ↔ T ∈ M ∧ ∀ g, unitaryConj (U g) T = T := by
  change T ∈ StarSubalgebra.centralizer ℂ
    ((M.commutant : Set (H →L[ℂ] H)) ∪ Set.range (fun g => (U g : H →L[ℂ] H))) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h
    constructor
    · have hM : T ∈ M.commutant.commutant :=
        VonNeumannAlgebra.mem_commutant_iff.mpr (fun S hS => (h S (Or.inl hS)).1)
      simpa only [VonNeumannAlgebra.commutant_commutant] using hM
    · intro g
      exact (commute_unitary_iff_star_right_conjugate (U g).property).mp
        (h (U g) (Or.inr ⟨g, rfl⟩)).1
  · rintro ⟨hM, hU⟩ S (hS | ⟨g, rfl⟩)
    · exact ⟨VonNeumannAlgebra.mem_commutant_iff.mp hS T hM |>.symm,
        VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hS) T hM |>.symm⟩
    · have hc (g : G) : (U g : H →L[ℂ] H) * T = T * (U g : H →L[ℂ] H) :=
        ((commute_unitary_iff_star_right_conjugate (U g).property).mpr (hU g)).eq
      refine ⟨hc g, ?_⟩
      have he : (U (g⁻¹) : H →L[ℂ] H) = star (U g : H →L[ℂ] H) := by
        rw [map_inv]
        rfl
      simpa only [he] using hc (g⁻¹)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CharacterAverageDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Descent by the character-action average

The concrete crossed-product representation identifies the joint fixed
algebra with the embedded original algebra. Once that actual identity is
available, the scalar character mean supplies the UCP map required for
descent. No statement that its entire ambient range is embedded is used.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section JointFixedPoints

variable {G L K : Type*} [Group G] [Group L]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Commuting conjugation actions restrict to each other's fixed algebra. -/
theorem normalizes_fixedPointAlgebra_of_commuting_actions
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (B : VonNeumannAlgebra K)
    (hB : ∀ l T, T ∈ B → unitaryConj (V l) T ∈ B)
    (hcomm : ∀ g l T, unitaryConj (U g) (unitaryConj (V l) T) =
      unitaryConj (V l) (unitaryConj (U g) T)) :
    ∀ l T, T ∈ fixedPointAlgebra U B →
      unitaryConj (V l) T ∈ fixedPointAlgebra U B := by
  intro l T hT
  obtain ⟨hTB, hTU⟩ := (mem_fixedPointAlgebra_iff U B T).mp hT
  rw [mem_fixedPointAlgebra_iff]
  refine ⟨hB l T hTB, ?_⟩
  intro g
  rw [hcomm, hTU]

end JointFixedPoints

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableNatEnumeration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem measurableSet_frameIndexAvailable (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (k : ℕ) :
    MeasurableSet {x | frameIndexAvailable (p x) k} := by
  have he : {x | frameIndexAvailable (p x) k} =
      ⋃ m : ℕ, {x | k < measurableIndexCount p x m} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, frameIndexAvailable, measurableIndexCount]
  rw [he]
  exact MeasurableSet.iUnion fun m =>
    measurableSet_lt measurable_const (measurable_indexCount p hp m)

theorem measurableSet_frameDimensionStratum (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (n : ℕ) :
    MeasurableSet (frameDimensionStratum p n) := by
  cases n with
  | zero =>
    simpa only [frameDimensionStratum, Set.ofPred_forall] using
      (MeasurableSet.iInter fun k => measurableSet_frameIndexAvailable p hp k)
  | succ n =>
    convert (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _hk : k < n =>
      measurableSet_frameIndexAvailable p hp k).inter
        (measurableSet_frameIndexAvailable p hp n).compl using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [frameDimensionStratum, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_ofPred_eq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionDimensionStrata
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [CompleteSpace H] in
theorem measurableSet_projectionRankStratum (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ) :
    MeasurableSet (projectionRankStratum P b n) :=
  measurableSet_frameDimensionStratum _ (fun i =>
    (measurableSet_eq_fun (measurableProjectionFrame_measurable P b hPm i)
      (measurable_const : Measurable fun _ : X => (0 : H))).compl) n

theorem projectionStratumCoordinates_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    [MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ)]
    [BorelSpace ℓ²(projectionDimensionIndex n, ℂ)]
    (v : ∀ x : projectionRankStratum P b n, (P x.val).range)
    (hv : Measurable fun x => (v x : H)) :
    Measurable fun x => projectionStratumCoordinates P hP b hb n x (v x) :=
  measurable_rangeHilbertCoordinates (fun x : projectionRankStratum P b n => P x.val)
    (projectionStratumBasis P hP b hb n) (projectionStratumBasis_measurable P hP b hb hPm n) v hv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableFiberRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- A nonunital ambient field acts unitally on each fixed-coordinate range. -/
def fixedFiberRepresentation (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n) :
    A →⋆ₐ[ℂ] (ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ)) := by
  letI : CompleteSpace (representationUnitProjection ρ x.val).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (representationUnitProjection_idempotent ρ x.val)).completeSpace_coe
  exact (projectionStratumCoordinates (representationUnitProjection ρ)
    (representationUnitProjection_idempotent ρ) b hb n x).conjStarAlgEquiv.toStarAlgHom.comp
      (nonunitalRangeRepresentation (ρ x.val))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2LinearFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Lifting fields of maps between different Hilbert spaces to L²

This supplies the varying synthesis maps used on a fixed dimension stratum.
Measurability is required only after evaluation on a vector.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (μ : Measure X)

theorem l2IsometryField_ae (U : X → E →ₗᵢ[ℂ] F)
    (hU : ∀ v, AEStronglyMeasurable (fun x => U x v) μ) (f : Lp E 2 μ) :
    l2IsometryField μ U hU f =ᵐ[μ] fun x => U x (f x) :=
  l2LinearFieldApply_ae μ _ hU 1 (isometryField_norm_bound μ U) f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2ProjectionSynthesis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # L² synthesis on a projection-rank stratum

The measurable orthonormal coordinates provide actual isometric inclusions
from the fixed-coordinate L² spaces into the original coefficient space.
-/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

theorem projectionStratumSynthesis_analysis (n : ℕ)
    (x : projectionRankStratum P b n) (v : H) :
    projectionStratumSynthesis P hP b hb n x
      (projectionStratumAnalysis P hP b hb n x v) = P x.val v := by
  change ((projectionStratumCoordinates P hP b hb n x).symm
    ((projectionStratumCoordinates P hP b hb n x) ⟨P x.val v, ⟨v, rfl⟩⟩) : H) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem projectionStratumSynthesis_fixed (n : ℕ)
    (x : projectionRankStratum P b n) (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    P x.val (projectionStratumSynthesis P hP b hb n x v) =
      projectionStratumSynthesis P hP b hb n x v := by
  obtain ⟨w, hw⟩ := ((projectionStratumCoordinates P hP b hb n x).symm v).property
  change P x.val (((projectionStratumCoordinates P hP b hb n x).symm v : (P x.val).range) : H) = _
  change P x.val (((projectionStratumCoordinates P hP b hb n x).symm v : (P x.val).range) : H) =
    (((projectionStratumCoordinates P hP b hb n x).symm v : (P x.val).range) : H)
  rw [← hw]
  exact congrArg (fun T : H →L[ℂ] H => T w) (hP x.val)

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem projectionStratumAnalysis_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    [MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ)]
    [BorelSpace ℓ²(projectionDimensionIndex n, ℂ)] (v : H) :
    Measurable fun x => projectionStratumAnalysis P hP b hb n x v := by
  exact projectionStratumCoordinates_measurable P hP b hb hPm n
    (fun x => ⟨P x.val v, ⟨v, rfl⟩⟩) ((hPm v).comp measurable_subtype_coe)

def l2ProjectionStratumSynthesis
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) :
    Lp ℓ²(projectionDimensionIndex n, ℂ) 2 μ →ₗᵢ[ℂ] Lp H 2 μ :=
  l2IsometryField μ (projectionStratumSynthesis P hP b hb n)
    (fun v => (projectionStratumSynthesis_measurable P hP b hb hPm n v).aestronglyMeasurable)

theorem l2ProjectionStratumSynthesis_ae
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (μ : Measure (projectionRankStratum P b n))
    (f : Lp ℓ²(projectionDimensionIndex n, ℂ) 2 μ) :
    l2ProjectionStratumSynthesis P hP b hb hPm n μ f =ᵐ[μ]
      fun x => projectionStratumSynthesis P hP b hb n x (f x) :=
  l2IsometryField_ae μ _ _ f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2ProjectionAnalysis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instSeparableSpaceSubtypePreLpPointedPowerConfigurationComplexMemAddSubgroupPointedPowerHilbert _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the L² sections of a projection field

On each rank stratum the synthesis range consists exactly of the sections
fixed by the original projection field.
-/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
  (hPm : ∀ v, Measurable fun x => P x v) (hPn : ∀ x, ‖P x‖ ≤ 1)

attribute [local instance] OAI.KadisonKastler.coordinateMeasurable
attribute [local instance] OAI.KadisonKastler.coordinateBorel
local instance coordinateSeparable (n : ℕ) :
    TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  separable_scalarHilbertCoordinates

def l2ProjectionStratumAnalysis (n : ℕ) (μ : Measure (projectionRankStratum P b n)) :
    Lp H 2 μ →L[ℂ] Lp ℓ²(projectionDimensionIndex n, ℂ) 2 μ :=
  l2LinearFieldMap μ (projectionStratumAnalysis P hP b hb n)
    (fun v => (projectionStratumAnalysis_measurable P hP b hb hPm n v).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall (projectionStratumAnalysis_norm_le P hP b hb hPn n))

theorem l2ProjectionStratumAnalysis_ae (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) (f : Lp H 2 μ) :
    l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f =ᵐ[μ]
      fun x => projectionStratumAnalysis P hP b hb n x (f x) :=
  l2LinearFieldApply_ae μ _
    (fun v => (projectionStratumAnalysis_measurable P hP b hb hPm n v).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall (projectionStratumAnalysis_norm_le P hP b hb hPn n)) f

theorem l2Projection_synthesis_analysis (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) (f : Lp H 2 μ) :
    l2ProjectionStratumSynthesis P hP b hb hPm n μ
      (l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f) =ᵐ[μ]
        fun x => P x.val (f x) := by
  filter_upwards [l2ProjectionStratumSynthesis_ae P hP b hb hPm n μ
      (l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f),
    l2ProjectionStratumAnalysis_ae P hP b hb hPm hPn n μ f] with x hs ha
  rw [hs, ha, projectionStratumSynthesis_analysis]

include hPn in
theorem l2ProjectionStratumSynthesis_range (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) (f : Lp H 2 μ) :
    f ∈ LinearMap.range (l2ProjectionStratumSynthesis P hP b hb hPm n μ).toLinearMap ↔
      ∀ᵐ x ∂μ, P x.val (f x) = f x := by
  constructor
  · rintro ⟨g, rfl⟩
    filter_upwards [l2ProjectionStratumSynthesis_ae P hP b hb hPm n μ g] with x hx
    change P x.val (l2ProjectionStratumSynthesis P hP b hb hPm n μ g x) =
      l2ProjectionStratumSynthesis P hP b hb hPm n μ g x
    rw [hx, projectionStratumSynthesis_fixed]
  · intro hf
    refine ⟨l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f, ?_⟩
    exact Lp.ext ((l2Projection_synthesis_analysis P hP b hb hPm hPn n μ f).trans hf)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStratumFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting actual operator fields to the fixed-coordinate strata -/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

def compressedStratumField (R : X → H →L[ℂ] H) (n : ℕ)
    (x : projectionRankStratum P b n) :
    ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ) :=
  (projectionStratumAnalysis P hP b hb n x).comp
    ((R x.val).comp (projectionStratumSynthesis P hP b hb n x).toContinuousLinearMap)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankOperatorFields
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Fields of all central-commutant operators in the rank coordinates -/

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

attribute [local instance] OAI.KadisonKastler.rankFieldCoordinateMeasurable
local instance rankFieldCoordinateBorel_r0269f8_1 :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩
def commonRankOperatorField
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) (n : ℕ) :=
  compressedStratumField (commonModelProjection M) (commonModelProjection_idempotent M)
    (commonRankBasis π D) (commonRankBasis_total π D) (commonCommutantField π D T) n

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankSourceModel
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

def commonRankFiberAlgebra {C : Type*} [CStarAlgebra C] (ι : C →⋆ₐ[ℂ] B)
    (n : ℕ) (x : projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n) :
    VonNeumannAlgebra ℓ²(projectionDimensionIndex n, ℂ) :=
  representationVonNeumannAlgebra ((fixedFiberRepresentation M.field (commonRankBasis π D)
    (commonRankBasis_total π D) n x).comp ι)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The real regular representation and the core embedding

The translation and gauge operators below act on `L²(ℝ,H)` itself. A
strongly continuous unitary group gives the faithful embedding
`π(x)(t) = U(t)* x U(t)`. No crossed-product or fixed-point identification
is assumed in these constructions.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem regularCoreAction_apply_ae (s : Multiplicative ℝ) (f : RegularCoreHilbert H) :
    (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => (U s : H →L[ℂ] H) (f (t + s.toAdd)) := by
  filter_upwards [regularConstantHom_apply_ae volume (U s : H →L[ℂ] H)
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f] with t hc ht
  change regularConstantHom volume (U s : H →L[ℂ] H)
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t = _
  rw [hc, ht]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiagonalLocality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise locality of operators commuting with scalar multipliers

Cutting down the operator norm inequality by every measurable indicator
gives the same inequality pointwise. This is the boundedness step in
constructing the diagonal field, before choosing any representatives.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem regular_setIntegral_norm_sq (s : Set ℝ) (hs : MeasurableSet s)
    (f : RegularCoreHilbert H) :
    (∫ t in s, ‖f t‖ ^ 2) = ‖regularIndicatorProjection s hs f‖ ^ 2 := by
  rw [← regular_integral_norm_sq]
  calc
    (∫ t in s, ‖f t‖ ^ 2) = ∫ t : ℝ, s.indicator (fun t => ‖f t‖ ^ 2) t :=
      (integral_indicator hs).symm
    _ = ∫ t : ℝ, ‖regularIndicatorProjection s hs f t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [regularIndicatorProjection_apply_ae s hs f] with t ht
      rw [ht]
      by_cases hts : t ∈ s <;> simp [hts]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending a corner unitary by the identity

A unitary on a closed subspace extends to a unitary on the ambient Hilbert
space, acting as the identity on the orthogonal complement. Its displacement
from the identity is exactly the displacement in the corner.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

variable [CompleteSpace H]

@[simp] theorem cornerUnitary_apply (v : unitary (E →L[ℂ] E)) (x : E) :
    (cornerUnitary E v : H →L[ℂ] H) (x : H) = ((v : E →L[ℂ] E) x : H) := by
  simp only [coe_cornerUnitary, add_apply, sub_apply, one_apply_eq_self,
    cornerExtension_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.starProjection_mem_subspace_eq_self, sub_self, add_zero]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete regular core and its first fixed-point inclusion

The tensor algebra is the commutant of the constant copy of `P'` on
`L²(ℝ,H)`. The regular core is the von Neumann algebra generated by the
concrete regular embedding and translations. Its generators lie in the
tensor algebra and are fixed by the common regular action. This proves
the first fixed-point inclusion without a crossed-product assumption.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularTranslation_mem_tensorAlgebra (P : VonNeumannAlgebra H)
    (s : Multiplicative ℝ) :
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈ regularTensorAlgebra P := by
  exact (mem_regularTensorAlgebra_iff P _).mpr
    (fun z _ => (regularConstant_commute_translation z s).eq)

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

/-- Translations are also fixed by the common action: both translation
groups are abelian, and constant operators commute with translations. -/
theorem regularTranslation_fixed (s t : Multiplicative ℝ) :
    unitaryConj (regularCoreAction U s)
      (regularRightTranslation (H := H) t :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := H) t :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply (commute_unitary_iff_star_right_conjugate (regularCoreAction U s).property).mp
  have hρ : Commute
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularRightTranslation (H := H) t :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    change (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularRightTranslation (H := H) t = _
    have he : regularRightTranslation (H := H) s * regularRightTranslation (H := H) t =
        regularRightTranslation (H := H) t * regularRightTranslation (H := H) s := by
      rw [← map_mul, ← map_mul, mul_comm]
    exact congrArg Subtype.val he
  exact (regularConstant_commute_translation (U s : H →L[ℂ] H) t).mul_left hρ

theorem regularCoreEmbedding_mem_core (P : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hT : T ∈ P) :
    regularCoreEmbedding U hU T ∈ regularCoreAlgebra U hU P := by
  exact subset_generatedVonNeumannAlgebra _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨T, hT, rfl⟩))

theorem regularTranslation_mem_core (P : VonNeumannAlgebra H)
    (s : Multiplicative ℝ) :
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈ regularCoreAlgebra U hU P := by
  exact subset_generatedVonNeumannAlgebra _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨s, rfl⟩))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularFourierTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-! # Fourier transport of constant operators and real translations -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem translate_toLp (s : ℝ) (f : SchwartzMap ℝ H) :
    (SchwartzMap.compSubConstCLM ℂ (-s) f).toLp 2 = regularTranslateApply s (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.compSubConstCLM ℂ (-s) f).coeFn_toLp 2,
    regularTranslateApply_ae s (f.toLp 2),
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2)]
    with t h₁ h₂ h₃
  simp only [Function.comp_def] at h₃
  rw [h₁, h₂, h₃]
  simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalization by the two actual regular actions

The translation and character formulas imply the required tensor-algebra
normalization. The two actions commute as conjugations, although their
implementing unitary groups commute only up to scalar characters.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_conjugated_of_conjugate_commute
    (u : unitary (H →L[ℂ] H)) (a b : H →L[ℂ] H)
    (h : Commute (unitaryConj (star u) a) b) :
    Commute a (unitaryConj u b) := by
  have he := congrArg (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) h.eq
  rw [map_mul, map_mul] at he
  change unitaryConj u (unitaryConj (star u) a) * unitaryConj u b =
    unitaryConj u b * unitaryConj u (unitaryConj (star u) a) at he
  have hi : unitaryConj u (unitaryConj (star u) a) = a := by
    simpa only [star_star] using unitaryConj_star_unitaryConj (star u) a
  change a * unitaryConj u b = unitaryConj u b * a
  simpa only [hi] using he

theorem unitaryConj_star_eq_of_commute
    (u : unitary (H →L[ℂ] H)) (a : H →L[ℂ] H)
    (h : Commute (u : H →L[ℂ] H) a) :
    unitaryConj (star u) a = a := by
  simpa only [unitaryConj, Unitary.coe_star, star_star] using
    (commute_unitary_iff_star_left_conjugate u.property).mp h

theorem tensor_mem_conjugate_of_constant_commute
    (P : VonNeumannAlgebra H)
    (u : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hu : ∀ z, Commute (u : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularConstantHom volume z))
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) : unitaryConj u T ∈ regularTensorAlgebra P := by
  apply (mem_regularTensorAlgebra_iff P _).mpr
  intro z hz
  apply commute_conjugated_of_conjugate_commute
  rw [unitaryConj_star_eq_of_commute u _ (hu z)]
  exact (mem_regularTensorAlgebra_iff P T).mp hT z hz

theorem conjugations_commute_of_scalar_product
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (u v : unitary (K →L[ℂ] K)) (c : ℂ) (hc : c * star c = 1)
    (huv : (u : K →L[ℂ] K) * v = c • ((v : K →L[ℂ] K) * u))
    (T : K →L[ℂ] K) :
    unitaryConj u (unitaryConj v T) = unitaryConj v (unitaryConj u T) := by
  rw [← unitaryConj_mul, ← unitaryConj_mul]
  change ((u : K →L[ℂ] K) * v) * T * star ((u : K →L[ℂ] K) * v) =
    ((v : K →L[ℂ] K) * u) * T * star ((v : K →L[ℂ] K) * u)
  rw [huv]
  have hc' : star c * c = 1 := by rwa [mul_comm]
  simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hc', one_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The regular crossed-product commutant and fixed algebra

The sole input is the commutant-generator theorem for a covariant
representation of a von Neumann algebra.  See Takesaki, *Theory of
Operator Algebras II* (2003), Theorem X.1.21, and Van Daele, *Continuous
Crossed Products and Type III von Neumann Algebras* (1978), Part I,
Theorem 3.11.  The exact covariant-implementation formula is also stated
in Takesaki's author notes *Structure of von Neumann Algebras of Type
III*, Lecture 1, Theorem 1.3(ii), pp. 10--11:
https://www.imsc.res.in/~sunder/mtnotes.pdf

Its generators here are constant operators from `P'` and the actual
operators `f(t) ↦ U(s) f(t+s)`.  The fixed-algebra equality is proved
below from this input and double commutants; it is not an input.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Each explicit commutant generator commutes with the fixed algebra;
the same therefore holds for the generated von Neumann algebra. -/
theorem regularCommutantAlgebra_le_fixed_commutant
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (P : VonNeumannAlgebra H) :
    regularCommutantAlgebra U P ≤
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)).commutant := by
  apply generated_le_vonNeumann
  rintro S (⟨z, hz, rfl⟩ | ⟨s, rfl⟩)
  · apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro T hT
    have h := ((mem_fixedPointAlgebra_iff _ _ _).mp hT).1
    exact ((mem_regularTensorAlgebra_iff P T).mp h z hz).symm
  · apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro T hT
    have h := ((mem_fixedPointAlgebra_iff _ _ _).mp hT).2 s
    exact ((commute_unitary_iff_star_right_conjugate
      (regularCoreAction U s).property).mpr h).eq.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralVectorMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite vector measures for real scalar multipliers

The squared pointwise norm of an L2 vector defines a finite measure.
Character commutation preserves its characteristic function and hence
the measure itself. This yields commutation with every scalar multiplier.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularScalarMultiplier_apply_ae
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C)
    (f : RegularCoreHilbert H) :
    regularScalarMultiplier φ hφ C hC f =ᵐ[volume] fun t => φ t • f t := by
  unfold regularScalarMultiplier
  filter_upwards [regularFieldOperator_represents volume
    (fun t => φ t • (1 : H →L[ℂ] H)) _ _ _ f] with t ht
  simpa only [smul_apply, one_apply_eq_self] using ht

omit [CompleteSpace H] in
theorem regularVectorMeasure_multiplier
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C)
    (f : RegularCoreHilbert H) :
    inner ℂ f (regularScalarMultiplier φ hφ C hC f) =
      ∫ t, φ t ∂regularVectorMeasure f := by
  rw [L2.inner_def, regularVectorMeasure_integral]
  apply integral_congr_ae
  filter_upwards [regularScalarMultiplier_apply_ae φ hφ C hC f] with t ht
  rw [ht, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.real_smul]
  rw [Complex.ofReal_pow]
  exact mul_comm _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Frequency windows in the concrete modular core

The translation generators and the proved real spectral commutant theorem
put the Fourier interval projections inside the actual generated core.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

/-- A bounded frequency interval, used for the finite-weight core corners. -/
def regularFrequencyWindow (a b : ℝ) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
    (regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc)

theorem regularFrequencyWindow_isStarProjection (a b : ℝ) :
    IsStarProjection (regularFrequencyWindow (H := H) a b) :=
  (regularIndicatorProjection_isStarProjection (H := H) _ measurableSet_Ioc).map
    (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreHilbertSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar Hilbert coordinates on the regular representation

A scalar Hilbert basis of `L²(ℝ)` gives an actual Hilbert direct-sum
decomposition of `L²(ℝ,H)`. Constant operators act on each summand by
their original action on `H`.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularTensorVector_apply_ae (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularTensorVector f x =ᵐ[volume] fun t => f t • x :=
  (ContinuousLinearMap.toSpanSingleton ℂ x).coeFn_compLp f

omit [CompleteSpace H] in
theorem inner_regularTensorVector
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) :
    inner ℂ (regularTensorVector f x) (regularTensorVector g y) =
      inner ℂ f g * inner ℂ x y := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ t, inner ℂ (regularTensorVector f x t) (regularTensorVector g y t)) =
        ∫ t, inner ℂ (f t) (g t) * inner ℂ x y := by
      apply integral_congr_ae
      filter_upwards [regularTensorVector_apply_ae f x,
        regularTensorVector_apply_ae g y] with t hf hg
      rw [hf, hg]
      simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply, mul_assoc]
    _ = (∫ t, inner ℂ (f t) (g t)) * inner ℂ x y := integral_mul_const _ _

omit [CompleteSpace H] in
theorem norm_regularTensorVector
    (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    ‖regularTensorVector f x‖ = ‖f‖ * ‖x‖ := by
  have hsq : ‖regularTensorVector f x‖ ^ 2 = (‖f‖ * ‖x‖) ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_regularTensorVector,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
    ring
  nlinarith [norm_nonneg (regularTensorVector f x), mul_nonneg (norm_nonneg f) (norm_nonneg x)]

variable {ι : Type*}

/-- The copy of `H` belonging to one scalar basis vector. -/
def regularBasisSummand (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (i : ι) : H →ₗᵢ[ℂ] RegularCoreHilbert H where
  __ := (regularTensorVector (b i)).toLinearMap
  norm_map' x := by
    change ‖regularTensorVector (b i) x‖ = ‖x‖
    rw [norm_regularTensorVector, b.orthonormal.norm_eq_one i, one_mul]

omit [CompleteSpace H] in
theorem regularBasisSummand_orthogonal
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    OrthogonalFamily ℂ (fun _ : ι => H) (regularBasisSummand b) := by
  intro i j hij x y
  change inner ℂ (regularTensorVector (b i) x) (regularTensorVector (b j) y) = 0
  rw [inner_regularTensorVector, b.orthonormal.inner_eq_zero hij, zero_mul]

omit [CompleteSpace H] in
theorem regularBasisSummand_total
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    ⊤ ≤ (⨆ i, LinearMap.range
      (regularBasisSummand (H := H) b i).toLinearMap).topologicalClosure := by
  let S : Submodule ℂ (RegularCoreHilbert H) :=
    ⨆ i, LinearMap.range (regularBasisSummand (H := H) b i).toLinearMap
  have hTensor (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
      regularTensorVector f x ∈ S.topologicalClosure := by
    have hsum := (regularTensorVector.flip x).hasSum (b.hasSum_repr f)
    apply S.isClosed_topologicalClosure.mem_of_tendsto hsum
    filter_upwards [] with s
    apply Submodule.le_topologicalClosure
    apply S.sum_mem
    intro i hi
    have hm : regularTensorVector (b i) x ∈ S :=
      (le_iSup (fun i => LinearMap.range
        (regularBasisSummand (H := H) b i).toLinearMap) i) ⟨x, rfl⟩
    simpa only [map_smul, ContinuousLinearMap.flip_apply] using S.smul_mem (b.repr f i) hm
  intro f hf
  clear hf
  change f ∈ S.topologicalClosure
  induction f using Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
  | @indicatorConst x s hs hfin =>
      have he : regularTensorVector (Lp.simpleFunc.indicatorConst 2 hs hfin.ne (1 : ℂ)) x =
          Lp.simpleFunc.indicatorConst 2 hs hfin.ne x := by
        apply Lp.ext
        filter_upwards [regularTensorVector_apply_ae
          (Lp.simpleFunc.indicatorConst 2 hs hfin.ne (1 : ℂ)) x,
          (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := (1 : ℂ))),
          (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := x))]
            with t ht h1 hx
        rw [ht]
        change indicatorConstLp 2 hs hfin.ne (1 : ℂ) t • x =
          indicatorConstLp 2 hs hfin.ne x t
        rw [h1, hx]
        by_cases hts : t ∈ s <;> simp [hts]
      rw [← he]
      exact hTensor _ x
  | @add f g hf hg hdis hF hG => exact S.topologicalClosure.add_mem hF hG
  | isClosed => exact S.isClosed_topologicalClosure

/-- The regular space is the Hilbert sum of the scalar-basis copies of `H`. -/
theorem regularHilbertSum (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    IsHilbertSum ℂ (fun _ : ι => H) (regularBasisSummand b) :=
  IsHilbertSum.mk (regularBasisSummand_orthogonal b) (regularBasisSummand_total b)

/-- Actual Hilbert coordinates on the regular representation. -/
def regularHilbertCoordinates (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    RegularCoreHilbert H ≃ₗᵢ[ℂ] lp (fun _ : ι => H) 2 :=
  (regularHilbertSum b).linearIsometryEquiv

theorem regularConstantHom_tensorVector (T : H →L[ℂ] H)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularConstantHom (volume : Measure ℝ) T (regularTensorVector f x) =
      regularTensorVector f (T x) := by
  apply Lp.ext
  filter_upwards [regularConstantHom_apply_ae (volume : Measure ℝ) T
    (regularTensorVector f x), regularTensorVector_apply_ae f x,
    regularTensorVector_apply_ae f (T x)] with t ht hx hTx
  rw [ht, hx, hTx, map_smul]

/-- In scalar Hilbert coordinates, the constant operator is exactly the
coordinatewise operator. -/
theorem regularHilbertCoordinates_constant
    (b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (T : H →L[ℂ] H) :
    (regularHilbertCoordinates b).conjStarAlgEquiv
      (regularConstantHom (volume : Measure ℝ) T) = l2Diagonal T := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  intro i
  apply ContinuousLinearMap.ext
  intro x
  change regularHilbertCoordinates b (regularConstantHom (volume : Measure ℝ) T
      ((regularHilbertCoordinates b).symm (lp.single 2 i x))) =
    l2Diagonal T (lp.single 2 i x)
  have hs (y : H) : (regularHilbertCoordinates b).symm (lp.single 2 i y) =
      regularTensorVector (b i) y :=
    (regularHilbertSum b).linearIsometryEquiv_symm_apply_single y
  rw [hs, regularConstantHom_tensorVector, l2Diagonal_single, ← hs]
  exact (regularHilbertCoordinates b).apply_symm_apply _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vectors supported in the bounded-frequency core corners -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularFrequencyPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) : RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H).symm (regularTensorVector φ ξ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceFrequencyVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded-frequency vector for the core trace

The scalar weight is exp(pi (s-1)) on (0,1], in the Fourier convention
exp(-2 pi i t s). The corresponding vector has explicit L2 bounds and frequency support.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coreTraceFrequencyVector (Ω : H) : RegularCoreHilbert H :=
  regularFrequencyPacket coreTraceFrequencyScalar Ω

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gaussian averages of strongly continuous algebra actions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def stateActionOrbit (a : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  unitaryConj (U (Multiplicative.ofAdd t)) a

include hU in
theorem stateActionOrbit_continuous (a : H →L[ℂ] H) (x : H) :
    Continuous (fun t => stateActionOrbit U a t x) := by
  have hs (y : H) : Continuous (fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) y) := by
    simp_rw [← Unitary.coe_star, regularGroup_star_eq]
    exact (hU y).comp continuous_neg
  exact continuous_unitary_field_apply _ hU _ (a.continuous.comp (hs x))

theorem stateActionOrbit_norm (a : H →L[ℂ] H) (t : ℝ) :
    ‖stateActionOrbit U a t‖ = ‖a‖ := norm_unitaryConj _ _

def gaussianStateAverage (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) : H →L[ℂ] H :=
  weightedOperatorIntegral volume (gaussianStateKernel r z) (gaussianStateKernel_integrable hr z)
    (stateActionOrbit U a) (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Filter.Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DoubleGaussianKMS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # KMS shifts in both coordinates of a doubly averaged element -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def doubleGaussianStateAverage (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z w : ℂ) : H →L[ℂ] H :=
  gaussianStateAverage U hU (gaussianStateAverage V hV a r hr w) r hr z

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteGroupAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The normalized finite-group mean

Finite averaging gives the equivariant bimodule mean needed by quadratic correction, for every C-star algebra of values.
-/

namespace KadisonKastler

open scoped BigOperators BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra B]

omit [Group G] [DiscreteTopology G] in
theorem finiteGroupAverage_left (b : B) (f : G →ᵇ B) :
    finiteGroupAverage (boundaryConstant b * f) = b * finiteGroupAverage f := by
  simp only [finiteGroupAverage_apply, BoundedContinuousFunction.mul_apply,
    boundaryConstant_apply, Finset.mul_sum, mul_smul_comm]

omit [Group G] [DiscreteTopology G] in
theorem finiteGroupAverage_right (f : G →ᵇ B) (b : B) :
    finiteGroupAverage (f * boundaryConstant b) = finiteGroupAverage f * b := by
  simp only [finiteGroupAverage_apply, BoundedContinuousFunction.mul_apply,
    boundaryConstant_apply, Finset.sum_mul, smul_mul_assoc]

/-- The finite-group mean, with both module identities. -/
def finiteGroupBimoduleMean : BimoduleMean (boundaryConstant (G := G) (B := B)) where
  toCLM := finiteGroupAverage
  map_one := finiteGroupAverage_const (G := G) (1 : B)
  map_star := finiteGroupAverage_star
  norm_le := finiteGroupAverage_norm_le
  map_left := finiteGroupAverage_left
  map_right := finiteGroupAverage_right

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2Intertwining
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transport of regular operators through a bounded intertwiner -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem compLp_regularFieldOperator {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : H →L[ℂ] K) (A : X → H →L[ℂ] H) (B : X → K →L[ℂ] K)
    (hA : ∀ x, AEStronglyMeasurable (fun t => A t x) μ)
    (hB : ∀ x, AEStronglyMeasurable (fun t => B t x) μ)
    (C D : ℝ) (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (hD : ∀ᵐ t ∂μ, ‖B t‖ ≤ D)
    (hL : ∀ t x, L (A t x) = B t (L x)) (f : Lp H 2 μ) :
    L.compLp (regularFieldOperator μ A hA C hC f) =
      regularFieldOperator μ B hB D hD (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (regularFieldOperator μ A hA C hC f),
    regularFieldOperator_represents μ A hA C hC f,
    regularFieldOperator_represents μ B hB D hD (L.compLp f),
    L.coeFn_compLp f] with t hl ha hb hf
  rw [hl, ha, hb, hf, hL]

omit [CompleteSpace H] [CompleteSpace K] in
theorem compLp_regularIndicatorProjection (L : H →L[ℂ] K) (s : Set ℝ) (hs : MeasurableSet s)
    (f : RegularCoreHilbert H) :
    L.compLp (regularIndicatorProjection s hs f) = regularIndicatorProjection s hs (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (regularIndicatorProjection s hs f),
    regularIndicatorProjection_apply_ae s hs f,
    regularIndicatorProjection_apply_ae s hs (L.compLp f), L.coeFn_compLp f] with t hl hp hq hf
  rw [hl, hp, hq]
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hf]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, map_zero]

theorem compLp_regularFrequencyProjection (L : H →L[ℂ] K) (a : ℝ) (f : RegularCoreHilbert H) :
    L.compLp (regularFrequencyProjection a f) = regularFrequencyProjection a (L.compLp f) := by
  change L.compLp ((Lp.fourierTransformₗᵢ ℝ H).symm
    (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi
      ((Lp.fourierTransformₗᵢ ℝ H) f))) =
    (Lp.fourierTransformₗᵢ ℝ K).symm
      (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi
        ((Lp.fourierTransformₗᵢ ℝ K) (L.compLp f)))
  rw [compLp_fourierInv, compLp_regularIndicatorProjection]
  exact congrArg (fun g => (Lp.fourierTransformₗᵢ ℝ K).symm
    (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi g))
    (fourier_compLp L f).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierShiftedFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier coordinates of the shifted frequency field -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

def scalarFourierCut (a : ℝ) : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv (regularFrequencyProjection a)

theorem scalarFourierCut_norm (a : ℝ) : ‖scalarFourierCut a‖ ≤ 1 := by
  rw [scalarFourierCut, StarAlgEquiv.norm_map]
  exact (regularFrequencyProjection_isStarProjection a).norm_le _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2CoordinateEquiv
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constant Hilbert-space coordinate changes on L²

This is used to lift the countable coordinate fibers into the universe of
the original representation without changing their operators or measures.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H K : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (μ : Measure X) (e : H ≃ₗᵢ[ℂ] K)

def l2CoordinateIsometry : Lp H 2 μ →ₗᵢ[ℂ] Lp K 2 μ :=
  l2IsometryField μ (fun _ => e.toLinearIsometry)
    (fun _ => stronglyMeasurable_const.aestronglyMeasurable)

theorem l2CoordinateIsometry_ae (f : Lp H 2 μ) :
    l2CoordinateIsometry μ e f =ᵐ[μ] fun x => e (f x) :=
  l2IsometryField_ae μ (fun _ => e.toLinearIsometry)
    (fun _ => stronglyMeasurable_const.aestronglyMeasurable) f

theorem l2CoordinateIsometry_surjective : Function.Surjective (l2CoordinateIsometry μ e) := by
  intro f
  refine ⟨l2CoordinateIsometry μ e.symm f, ?_⟩
  apply Lp.ext
  filter_upwards [l2CoordinateIsometry_ae μ e (l2CoordinateIsometry μ e.symm f),
    l2CoordinateIsometry_ae μ e.symm f] with x hx hy
  rw [hx, hy, LinearIsometryEquiv.apply_symm_apply]

def l2CoordinateEquiv : Lp H 2 μ ≃ₗᵢ[ℂ] Lp K 2 μ :=
  LinearIsometryEquiv.ofSurjective (l2CoordinateIsometry μ e) (l2CoordinateIsometry_surjective μ e)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RankStratumStandardBorel
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The common spectral rank strata are standard Borel spaces -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

attribute [local instance] OAI.KadisonKastler.rankStandardCoordinateMeasurable
attribute [local instance] OAI.KadisonKastler.rankStandardCoordinateBorel
omit [TopologicalSpace.SeparableSpace B] in
theorem commonRankStratum_standardBorel (n : ℕ) :
    StandardBorelSpace (projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n) := by
  let : StandardBorelSpace (WeakDual.characterSpace ℂ A) := commonSpectralBase_standardBorel
  exact (measurableSet_projectionRankStratum (commonModelProjection M)
    (commonRankBasis π D) (commonModelProjection_measurable M) n).standardBorel

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LiftedRankStrata
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Rank strata in the universe of the original Hilbert space -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

universe u

variable {A B H : Type u} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

def commonRankStratum (n : ℕ) : MeasuredHilbertStratum.{u} := by
  let : TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
    separable_scalarHilbertCoordinates
  let : TopologicalSpace.SeparableSpace (ULift.{u} ℓ²(projectionDimensionIndex n, ℂ)) :=
    hilbertULift_separable
  let : MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ) := borel _
  let : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩
  exact {
    X := projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n
    measurableX := inferInstance
    standardX := commonRankStratum_standardBorel M n
    K := ULift.{u} ℓ²(projectionDimensionIndex n, ℂ)
    normedK := inferInstance
    innerK := inferInstance
    completeK := inferInstance
    separableK := inferInstance
    measurableK := inferInstance
    borelK := inferInstance
    μ := projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D) n
    finiteμ := inferInstance }

def commonRankStratumEquiv (n : ℕ) :
    Lp ℓ²(projectionDimensionIndex n, ℂ) 2
      (projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
        (commonRankBasis π D) n) ≃ₗᵢ[ℂ] (commonRankStratum M n).space :=
  l2CoordinateEquiv _ (rankFiberLift n)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointVectorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weak compactness of self-adjoint vector balls

The bounded real vector images used in the modular Radon--Nikodym argument
are closed and convex in the Hilbert norm, by weak operator compactness.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wotSelfAdjointBall_compact (M : VonNeumannAlgebra H) :
    IsCompact (wotSelfAdjointBall M) := by
  apply (Generator.Tracial.weakOperatorBall_isCompact M 1).inter_right
  have he : {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} = {T | star T = T} := by
    ext T
    constructor
    · intro h
      exact DFunLike.ext _ _ (fun x => congrArg (fun A : H →L[ℂ] H => A x) h.star_eq)
    · intro h
      exact ContinuousLinearMap.ext (fun x => congrArg (fun A : H →WOT[ℂ] H => A x) h)
  rw [he]
  exact isClosed_eq continuous_star continuous_id

attribute [local instance] OAI.KadisonKastler.selfAdjointCompactReal
theorem selfAdjointVectorImage_closed (M : VonNeumannAlgebra H) (Ω : H) (P : H →L[ℝ] H) :
    IsClosed (selfAdjointVectorImage M Ω P) := by
  have hcompact := (wotSelfAdjointBall_compact M).image
    (wotVector_realMap_weak_continuous Ω P)
  have he : selfAdjointVectorImage M Ω P =
      (toWeakSpace ℝ H) ⁻¹' ((fun T : H →WOT[ℂ] H => toWeakSpace ℝ H (P (T Ω))) ''
        wotSelfAdjointBall M) := by
    ext v
    simp only [selfAdjointVectorImage, Set.mem_image, Set.mem_preimage]
    exact exists_congr fun T => and_congr_right fun _ => (toWeakSpace ℝ H).injective.eq_iff.symm
  rw [he]
  exact hcompact.isClosed.preimage (toWeakSpaceCLM ℝ H).continuous

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularRadonNikodym
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded modular Radon--Nikodym equation

The positive-contraction case of the real pairing equation in Rieffel--van
Daele, Pacific Journal of Mathematics 69 (1977), Lemma 4.3, pp.201--202.
Weak compactness and polar support tests construct the solution in the
original represented algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.modularRadonReal
/-- A positive commutant contraction has a self-adjoint contractive solution
for every normalized right-half-plane pairing parameter. -/
theorem modular_radon_nikodym_positive (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (z : ℂ) (hz : z.re = 1) :
    ∃ x : Algebra M, IsSelfAdjoint x ∧ ‖x‖ ≤ 1 ∧
      ∀ a : selfAdjoint (Algebra M),
        (inner ℂ (a.val.val Ω) (b Ω)).re =
          (z * inner ℂ (a.val.val Ω) (x.val Ω)).re := by
  let K := selfAdjointVectorSpace M Ω
  let P : H →L[ℝ] H := K.starProjection.comp ((z • ContinuousLinearMap.id ℂ H).restrictScalars ℝ)
  let C : Set K := {v | (v : H) ∈ selfAdjointVectorImage M Ω P}
  let y : K := K.orthogonalProjectionOnto (b Ω)
  have hclosed : IsClosed C := (selfAdjointVectorImage_closed M Ω P).preimage continuous_subtype_val
  have hconv : Convex ℝ C := (selfAdjointVectorImage_convex M Ω P).linear_preimage K.subtype
  have hbounded : ∀ v ∈ C, ‖v‖ ≤ ‖P‖ * ‖Ω‖ := by
    rintro v ⟨T, hT, he⟩
    change ‖(v : H)‖ ≤ _
    rw [← he]
    have hn : ‖T.toCLM Ω‖ ≤ ‖Ω‖ := by
      calc
        ‖T.toCLM Ω‖ ≤ ‖T.toCLM‖ * ‖Ω‖ := T.toCLM.le_opNorm Ω
        _ ≤ 1 * ‖Ω‖ := mul_le_mul_of_nonneg_right hT.1.2 (norm_nonneg Ω)
        _ = ‖Ω‖ := one_mul _
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg P))
  have htest : ∀ h ∈ Set.range (selfAdjointVectorInSpace M Ω),
      ∃ v ∈ C, inner ℝ h y ≤ inner ℝ h v := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, hu, hun, hle, him⟩ := commutant_positive_polar_support Ω a.val a.property b hb hb0 hb1
    let U := ContinuousLinearMapWOT.ofCLM u.val
    have hU : U ∈ wotSelfAdjointBall M := ⟨⟨u.property, hun⟩, congrArg Subtype.val hu.star_eq⟩
    let v : K := K.orthogonalProjectionOnto (z • u.val Ω)
    refine ⟨v, ⟨U, hU, rfl⟩, ?_⟩
    change inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (b Ω)) ≤
      inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (z • u.val Ω))
    rw [inner_selfAdjointVector_projection, inner_selfAdjointVector_projection]
    change (inner ℂ (a.val.val Ω) (b Ω)).re ≤ (inner ℂ (a.val.val Ω) (z • u.val Ω)).re
    rw [inner_smul_right, Complex.mul_re, hz, him, one_mul, mul_zero, sub_zero]
    exact hle
  have hy : y ∈ C := mem_closed_convex_of_dense_support hclosed hconv
    (selfAdjointVectorInSpace_dense M Ω) hbounded htest
  obtain ⟨T, hT, hTy⟩ := hy
  let x : Algebra M := ⟨T.toCLM, hT.1.1⟩
  refine ⟨x, ?_, hT.1.2, ?_⟩
  · exact Subtype.ext hT.2.star_eq
  · intro a
    have he := congrArg (fun v : H => inner ℝ (selfAdjointVectorMap M Ω a) v) hTy
    change inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (z • x.val Ω)) =
      inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (b Ω)) at he
    rw [inner_selfAdjointVector_projection, inner_selfAdjointVector_projection] at he
    simpa only [real_inner_eq_re_inner, RCLike.re_eq_complex_re, selfAdjointVectorMap,
      LinearMap.coe_mk, AddHom.coe_mk, inner_smul_right] using he.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual norm ultraproduct for the infinitesimal normalizer argument

The null sequences form a closed star ideal in the bounded product. Its
C-star quotient is the norm ultraproduct used in the infinitesimal
normalizer argument.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable (B : ℕ → Type*) [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

local instance instPartialOrderSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence : PartialOrder (VaryingBoundedSequence B) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialSlice
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete vector slices of the spatial von Neumann product -/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Slicing an element of the spatial product lands in the original
first algebra, by the bicommutant theorem. -/
theorem tensorVectorSlice_mem (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (ξ : K) (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D) : tensorVectorSlice ξ T ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hTcomm := spatialLeft_commutes_product M D a ha T hT
  have hV := spatialLeft_tensorVector ξ a
  have hVs := tensorVector_adjoint_spatialLeft ξ a
  apply ContinuousLinearMap.ext
  intro x
  have hVx := congrArg (fun L : H →L[ℂ] SpatialHilbert H K => L x) hV
  have hVsx := congrArg (fun L : SpatialHilbert H K →L[ℂ] H => L (T (tensorVector ξ x))) hVs
  have hc := congrArg (fun L : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    L (tensorVector ξ x)) hTcomm
  change a ((tensorVector ξ).adjoint (T (tensorVector ξ x))) =
    (tensorVector ξ).adjoint (T (tensorVector ξ (a x)))
  change (tensorVector ξ).adjoint (spatialLeft a (T (tensorVector ξ x))) =
    a ((tensorVector ξ).adjoint (T (tensorVector ξ x))) at hVsx
  change spatialLeft a (T (tensorVector ξ x)) = T (spatialLeft a (tensorVector ξ x)) at hc
  rw [← hVsx, hc]
  change spatialLeft a (tensorVector ξ x) = tensorVector ξ (a x) at hVx
  rw [hVx]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedLocalMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The four-dimensional pointed matrix state

Left and right matrix multiplication act on the Hilbert space of two by
two matrices. The square root of the diagonal density is cyclic for
both actions. An orthonormal basis beginning at that vector makes the
reference vector the zero-coordinate vacuum used by the infinite product.
-/

namespace KadisonKastler

noncomputable section

theorem twoSiteWeight_pos {ν : ℝ} (hν : 0 < ν) (i : Fin 2) : 0 < twoSiteWeight ν i := by
  fin_cases i <;> simp only [twoSiteWeight, Fin.zero_eta, ↓reduceIte]
  · positivity
  · positivity

theorem twoSiteWeight_sum {ν : ℝ} (hν : 0 < ν) :
    twoSiteWeight ν 0 + twoSiteWeight ν 1 = 1 := by
  simp only [twoSiteWeight, ↓reduceIte, _root_.one_ne_zero]
  field_simp

theorem pointedRawLeft_vacuum (ν : ℝ) (i j : Fin 2) :
    pointedRawLeft i j (pointedRawVacuum ν) =
      (Real.sqrt (twoSiteWeight ν j) : ℂ) • EuclideanSpace.single (i,j) 1 := by
  ext p
  rcases p with ⟨p,q⟩
  simp only [pointedRawLeft_apply, pointedRawVacuum_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Prod.mk.injEq]
  by_cases h : p = i <;> by_cases h' : q = j <;> simp_all [eq_comm]

theorem pointedRawRight_vacuum (ν : ℝ) (i j : Fin 2) :
    pointedRawRight i j (pointedRawVacuum ν) =
      (Real.sqrt (twoSiteWeight ν j) : ℂ) • EuclideanSpace.single (j,i) 1 := by
  ext p
  rcases p with ⟨p,q⟩
  simp only [pointedRawRight_apply, pointedRawVacuum_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Prod.mk.injEq]
  by_cases h : p = j <;> by_cases h' : q = i <;> simp_all

theorem pointedRawLeft_moment {ν : ℝ} (hν : 0 < ν) (i j : Fin 2) :
    inner ℂ (pointedRawVacuum ν) (pointedRawLeft i j (pointedRawVacuum ν)) =
      if i = j then (twoSiteWeight ν i : ℂ) else 0 := by
  rw [pointedRawLeft_vacuum, inner_smul_right, EuclideanSpace.inner_single_right]
  by_cases h : i = j
  · subst j
    simp only [pointedRawVacuum_apply, ↓reduceIte, one_mul,
      Complex.conj_ofReal]
    norm_cast
    exact Real.mul_self_sqrt (twoSiteWeight_pos hν i).le
  · simp [pointedRawVacuum_apply, h]

theorem pointedRawVacuum_norm {ν : ℝ} (hν : 0 < ν) : ‖pointedRawVacuum ν‖ = 1 := by
  have hn : ‖pointedRawVacuum ν‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, pointedRawVacuum_apply]
    simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (twoSiteWeight_pos hν 0).le,
      Real.sq_sqrt (twoSiteWeight_pos hν 1).le, twoSiteWeight_sum hν]
  nlinarith [norm_nonneg (pointedRawVacuum ν)]

theorem pointedRawLeft_spans {ν : ℝ} (hν : 0 < ν) :
    Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawLeft ij.1 ij.2 (pointedRawVacuum ν))) = ⊤ := by
  apply span_of_basis_mem (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ).toBasis
  rintro ⟨i,j⟩
  change (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ) (i,j) ∈ _
  rw [EuclideanSpace.basisFun_apply]
  have hc : (Real.sqrt (twoSiteWeight ν j) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (twoSiteWeight_pos hν j))
  have hm := Submodule.subset_span (R := ℂ) (Set.mem_range_self (i,j) :
    pointedRawLeft i j (pointedRawVacuum ν) ∈ Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawLeft ij.1 ij.2 (pointedRawVacuum ν)))
  rw [pointedRawLeft_vacuum] at hm
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using Submodule.smul_mem _ (Real.sqrt (twoSiteWeight ν j) : ℂ)⁻¹ hm

theorem pointedRawRight_spans {ν : ℝ} (hν : 0 < ν) :
    Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawRight ij.1 ij.2 (pointedRawVacuum ν))) = ⊤ := by
  apply span_of_basis_mem (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ).toBasis
  rintro ⟨i,j⟩
  change (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ) (i,j) ∈ _
  rw [EuclideanSpace.basisFun_apply]
  have hc : (Real.sqrt (twoSiteWeight ν i) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (twoSiteWeight_pos hν i))
  have hm := Submodule.subset_span (R := ℂ) (Set.mem_range_self (j,i) :
    pointedRawRight j i (pointedRawVacuum ν) ∈ Set.range (fun ij : Fin 2 × Fin 2 =>
      pointedRawRight ij.1 ij.2 (pointedRawVacuum ν)))
  rw [pointedRawRight_vacuum] at hm
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using Submodule.smul_mem _ (Real.sqrt (twoSiteWeight ν i) : ℂ)⁻¹ hm

theorem exists_pointedRaw_basis {ν : ℝ} (hν : 0 < ν) :
    ∃ b : OrthonormalBasis (Fin 4) ℂ PointedRawHilbert, b 0 = pointedRawVacuum ν := by
  have hv : Orthonormal ℂ (({0} : Set (Fin 4)).domRestrict
      (fun _ => pointedRawVacuum ν)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact pointedRawVacuum_norm hν
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [PointedRawHilbert])
  exact ⟨b, hb 0 (by simp)⟩

/-- The two faithful matrix actions with the designated vacuum vector. -/
theorem exists_pointedLocalMatrixData {ν : ℝ} (hν : 0 < ν) :
    Nonempty (PointedLocalMatrixData ν) := by
  obtain ⟨b,hb⟩ := exists_pointedRaw_basis hν
  let e : PointedRawHilbert ≃ₗᵢ[ℂ] PointedLocalHilbert := b.repr
  have he : e (pointedRawVacuum ν) = pointedLocalVacuum := by
    rw [← hb]
    exact b.repr_self 0
  have hs : e.symm pointedLocalVacuum = pointedRawVacuum ν := by
    rw [← he, e.symm_apply_apply]
  refine ⟨{
    left := pointedRawLeftUnits.map e.conjStarAlgEquiv.toStarAlgHom
    right := pointedRawRightUnits.map e.conjStarAlgEquiv.toStarAlgHom
    commutes := ?_
    left_spans := ?_
    right_spans := ?_
    moment := ?_ }⟩
  · intro i j k l
    exact (pointedRawUnits_commute i j k l).map e.conjStarAlgEquiv.toMonoidHom
  · change Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      e.conjStarAlgEquiv (pointedRawLeft ij.1 ij.2) pointedLocalVacuum)) = ⊤
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
    exact span_linearEquiv_image e.toLinearEquiv _ (pointedRawLeft_spans hν)
  · change Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 2 =>
      e.conjStarAlgEquiv (pointedRawRight ij.1 ij.2) pointedLocalVacuum)) = ⊤
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
    exact span_linearEquiv_image e.toLinearEquiv _ (pointedRawRight_spans hν)
  · intro i j
    change inner ℂ pointedLocalVacuum
      (e.conjStarAlgEquiv (pointedRawLeft i j) pointedLocalVacuum) = _
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs, ← he, e.inner_map_map]
    exact pointedRawLeft_moment hν i j

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independent-site vacuum moments in the countable product

The vacuum rank-one projection at one site commutes with all other
sites. Its corner is the local vector state, giving product moments.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

/-- The configuration representation has exactly the prescribed matrix-state moments. -/
theorem pointedPower_moments {ν : ℝ} (d : PointedLocalMatrixData ν)
    (l : List ℕ) (hl : l.Nodup) (r c : ℕ → Fin 2) :
    inner ℂ pointedPowerVacuum
      (((l.map fun i => (pointedPowerSite d.left i).entry (r i) (c i)).prod)
        pointedPowerVacuum) =
      (l.map fun i => if r i = c i then (twoSiteWeight ν (r i) : ℂ) else 0).prod := by
  simpa only [pointedPowerSite, MatrixUnitSystem.map_entry, d.moment] using
    pointedPower_product_moment (fun i => d.left.entry (r i) (c i)) l hl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftBoundarySpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {G : Type*} [Group G]

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkBoundaryMeasure : Measure (RandomWalkBoundary G) :=
  shiftBoundaryMeasure (randomWalkPathLaw G) (randomWalkAdvance G)

instance instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure : IsProbabilityMeasure (randomWalkBoundaryMeasure G) :=
  inferInstanceAs (IsProbabilityMeasure
    (shiftBoundaryMeasure (randomWalkPathLaw G) (randomWalkAdvance G)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Descent to the first boundary coordinate

The product invariant-range theorem supplies an actual L-infinity function
on the product boundary, with unchanged norm. Thus the first-coordinate
invariant projection descends as a bounded linear map.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (S : X → X) {ν : Measure Y}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem firstBoundaryMeasure_eq_trim :
    (μ.prod ν).trim (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S)) =
      (shiftBoundaryMeasure μ S).prod ν := by
  exact (trim_eq_map (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S))).trans
    (firstBoundaryMap_measurePreserving μ S).map_eq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCommutantPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gauged wave-packet coefficients

Compression between two scalar wave packets turns commutation with the
regular copy of `P` into membership in `P'`. Translation commutation
then gives the exact covariance of these coefficients. These are the
operator-valued coefficients used in the regular commutant argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- An operator coefficient between two wave packets. -/
def regularPacketCoefficient
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) : H →L[ℂ] H :=
  (regularGaugedPacket U hU φ).adjoint.comp (T.comp (regularGaugedPacket U hU ψ))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularConvolutionOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integrable convolution operators in the regular commutant

The common regular action is strongly continuous by its gauge
equivalence to translations. Its integrable scalar averages belong to
the generated commutant algebra. Products of two such averages with a
constant commutant coefficient give the finite packet averages used in
the reconstruction argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

theorem regularCoreAction_norm_le_one (t : ℝ) :
    ‖(regularCoreAction U (Multiplicative.ofAdd t) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp only [Unitary.norm_map, one_mul, le_refl]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularConvolutionCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Coefficients of the factored convolution operators

These formulas express the constructed action integrals as actual
single and double scalar integrals. They are the comparison formulas
for Haar averages of finite packet matrices.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

theorem regularAction_adjoint (t : ℝ) :
    (regularCoreAction U (Multiplicative.ofAdd t) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).adjoint =
      (regularCoreAction U (Multiplicative.ofAdd (-t)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star]
  exact congrArg (fun v : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =>
    (v : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
      (regularGroup_star_eq (regularCoreAction U) t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketLocalization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous frames from translated localizations

A finite-measure scalar cutoff has an exact Haar-averaged square norm.
This gives the uniform bound needed when averaging local matrix
compressions in the regular commutant proof.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem norm_local_translation_sq
    (s : Set ℝ) (hs : MeasurableSet s) (f : RegularCoreHilbert H) (r : ℝ) :
    ‖regularIndicatorProjection s hs
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)‖ ^ 2 =
      ∫ t in s, ‖f (t + r)‖ ^ 2 := by
  rw [← regular_setIntegral_norm_sq]
  apply integral_congr_ae
  filter_upwards [(regularRightTranslation_apply_ae
    (Multiplicative.ofAdd r) f).filter_mono (ae_restrict_le)] with t ht
  exact congrArg (fun x : H => ‖x‖ ^ 2) ht

/-- Translated cutoffs form a tight continuous frame. -/
theorem integral_norm_local_translation_sq
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (f : RegularCoreHilbert H) :
    (∫ r : ℝ, ‖regularIndicatorProjection s hs
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)‖ ^ 2) =
      (volume s).toReal * ‖f‖ ^ 2 := by
  simp_rw [norm_local_translation_sq]
  rw [integral_local_translates
    ((Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) s hfinite,
    regular_integral_norm_sq, smul_eq_mul]

/-- The continuous frame's square norms are integrable. -/
theorem integrable_norm_local_translation_sq
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (f : RegularCoreHilbert H) :
    Integrable (fun r : ℝ => ‖regularIndicatorProjection s hs
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)‖ ^ 2) volume := by
  simp_rw [norm_local_translation_sq]
  exact integrable_integral_local_translates
    ((Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) s hfinite

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularIntervalCutoffs
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compact interval cutoffs for regular vectors

These are elementary support and approximation facts for the actual
indicator projections. They do not require a commutant theorem.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularIndicator_translate_eq_of_support
    (s q : Set ℝ) (hs : MeasurableSet s) (hq : MeasurableSet q)
    (f : RegularCoreHilbert H) (hf : regularIndicatorProjection s hs f = f)
    (r : ℝ) (hsub : ∀ t, t + r ∈ s → t ∈ q) :
    regularIndicatorProjection q hq (regularTranslateApply r f) = regularTranslateApply r f := by
  have hsupport : ∀ᵐ t : ℝ, t ∉ s → f t = 0 := by
    filter_upwards [regularIndicatorProjection_apply_ae s hs f] with t ht hts
    rw [hf, Set.indicator_of_notMem hts] at ht
    exact ht
  have htranslated := (measurePreserving_add_right volume r).quasiMeasurePreserving.ae
    hsupport
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae q hq (regularTranslateApply r f),
    regularTranslateApply_ae r f, htranslated] with t hcut htrans hzero
  rw [hcut]
  by_cases ht : t ∈ q
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, htrans]
    exact (hzero (fun h => ht (hsub t h))).symm

omit [CompleteSpace H] in
theorem regularIndicator_translate_zero_of_support
    (s q : Set ℝ) (hs : MeasurableSet s) (hq : MeasurableSet q)
    (f : RegularCoreHilbert H) (hf : regularIndicatorProjection s hs f = f)
    (r : ℝ) (hdis : ∀ t, t ∈ q → t + r ∉ s) :
    regularIndicatorProjection q hq (regularTranslateApply r f) = 0 := by
  have hsupport : ∀ᵐ t : ℝ, t ∉ s → f t = 0 := by
    filter_upwards [regularIndicatorProjection_apply_ae s hs f] with t ht hts
    rw [hf, Set.indicator_of_notMem hts] at ht
    exact ht
  have htranslated := (measurePreserving_add_right volume r).quasiMeasurePreserving.ae
    hsupport
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae q hq (regularTranslateApply r f),
    regularTranslateApply_ae r f, htranslated, Lp.coeFn_zero H 2 (volume : Measure ℝ)]
    with t hcut htrans hzero hz
  rw [hcut, hz]
  by_cases ht : t ∈ q
  · rw [Set.indicator_of_mem ht, htrans]
    exact hzero (hdis t ht)
  · rw [Set.indicator_of_notMem ht]
    rfl

omit [CompleteSpace H] in
theorem regularInterval_translate_eq
    {A R r : ℝ} (h : |r| + A ≤ R)
    (f : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f) :
    regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc
      (regularTranslateApply r f) = regularTranslateApply r f := by
  apply regularIndicator_translate_eq_of_support _ _ measurableSet_Icc measurableSet_Icc f hf
  intro t ht
  have hr₁ := neg_abs_le r
  have hr₂ := le_abs_self r
  constructor <;> linarith [ht.1, ht.2]

omit [CompleteSpace H] in
theorem regularInterval_translate_zero
    {A R r : ℝ} (h : R + A < |r|)
    (f : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f) :
    regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc
      (regularTranslateApply r f) = 0 := by
  apply regularIndicator_translate_zero_of_support _ _ measurableSet_Icc measurableSet_Icc f hf
  intro t ht hs
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr] at h
    linarith [ht.1, hs.2]
  · rw [abs_of_nonpos hr] at h
    linarith [ht.2, hs.1]

omit [CompleteSpace H] in
/-- Symmetric interval projections converge strongly to the identity. -/
theorem regularIntervalProjection_tendsto (f : RegularCoreHilbert H) :
    Tendsto (fun n : ℕ => regularIndicatorProjection
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f) atTop (𝓝 f) := by
  let F (n : ℕ) (t : ℝ) : ℝ :=
    if t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) then 0 else ‖f t‖ ^ 2
  have hi := (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hm (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    exact aestronglyMeasurable_const.piecewise measurableSet_Icc
      (((Lp.aestronglyMeasurable f).norm.pow 2).restrict)
  have hb (n : ℕ) : ∀ᵐ t : ℝ, ‖F n t‖ ≤ ‖f t‖ ^ 2 := by
    apply Eventually.of_forall
    intro t
    dsimp only [F]
    split_ifs <;> simp
  have ht : ∀ᵐ t : ℝ, Tendsto (fun n : ℕ => F n t) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro t
    apply tendsto_const_nhds.congr'
    have he : ∀ᶠ n : ℕ in atTop, |t| ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |t|))
    filter_upwards [he] with n hn
    simp only [F]
    have hn' : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) :=
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    simp only [hn', ite_true, if_true]
  have hint := tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖f t‖ ^ 2)
    hm hi hb ht
  simp only [integral_zero] at hint
  have he (n : ℕ) : ‖regularIndicatorProjection
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f - f‖ ^ 2 = ∫ t : ℝ, F n t := by
    rw [← regular_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [regularIndicatorProjection_apply_ae
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f,
      Lp.coeFn_sub (regularIndicatorProjection
        (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f) f] with t hcut hsub
    rw [hsub]
    simp only [Pi.sub_apply, hcut]
    dsimp only [F]
    split_ifs with ht
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun n : ℕ => ‖regularIndicatorProjection
      (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc f - f‖ ^ 2) atTop (𝓝 0) :=
    hint.congr (fun n => (he n).symm)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketIntegrals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integral formulas for wave-packet compression

The adjoint of a scalar packet is its ordinary vector integral. The
gauged formula inserts the original unitary group inside that integral.
Both integrability assertions follow from the actual `L²` bounds.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Scalar packet compression is the usual vector-valued integral. -/
theorem regularTensorVector_adjoint_apply
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    (regularTensorVector φ).adjoint f = ∫ t : ℝ, star (φ t) • f t := by
  apply ext_inner_left ℂ
  intro η
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← integral_inner (integrable_scalarPacket_pair φ f), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularTensorVector_apply_ae φ η] with t ht
  rw [ht]
  simp only [inner_smul_left, inner_smul_right]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Haar averages of finite packet operators

The packet and convolution expressions are the same absolutely
integrable three-variable kernel, with the integrations reordered.
Thus every averaged packet matrix with a commutant coefficient belongs
to the concrete generated commutant algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

theorem action_coefficient_integral
    (q u : ℝ) (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    inner ℂ ((regularCoreAction U (Multiplicative.ofAdd q) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
      (regularConstantHom (volume : Measure ℝ) A
        ((regularCoreAction U (Multiplicative.ofAdd u) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g)) =
      ∫ r : ℝ, inner ℂ ((U (Multiplicative.ofAdd q) : H →L[ℂ] H) (f (r + q)))
        (A ((U (Multiplicative.ofAdd u) : H →L[ℂ] H) (g (r + u)))) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularCoreAction_apply_ae U (Multiplicative.ofAdd q) f,
    regularCoreAction_apply_ae U (Multiplicative.ofAdd u) g,
    regularConstantHom_apply_ae volume A
      ((regularCoreAction U (Multiplicative.ofAdd u) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g)] with r hq hu hA
  rw [hq, hA, hu]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizedPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Localization of finite packet matrices

Cutting off a packet cuts off its scalar coefficient. The localized
average of each packet matrix is consequently a product of the actual
convolution generators, not an assumed measurable operator integral.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem integrable_regularIndicatorPacket
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (regularIndicatorProjection (H := ℂ) s hs φ) volume := by
  let : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hfinite
  have h := ((Lp.memLp φ).restrict s).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  exact ((integrable_indicator_iff hs).mpr h).congr
    (regularIndicatorProjection_apply_ae s hs φ).symm

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- A rank-one scalar packet matrix with an arbitrary bounded vector coefficient. -/
def regularPacketOperator
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (regularGaugedPacket U hU φ).comp (A.comp (regularGaugedPacket U hU ψ).adjoint)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularIntervalAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalized interval averages

The boundary strip has fixed width for fixed compact test vectors.
Dividing the localization average by the interval length therefore
recovers every translation-invariant operator weakly.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem norm_regularCut_translate_le (s : Set ℝ) (hs : MeasurableSet s)
    (r : ℝ) (f : RegularCoreHilbert H) :
    ‖regularIndicatorProjection s hs (regularTranslateApply r f)‖ ≤ ‖f‖ := by
  have h := (regularIndicatorProjection (H := H) s hs).le_opNorm (regularTranslateApply r f)
  have hp := IsStarProjection.norm_le _ (regularIndicatorProjection_isStarProjection (H := H) s hs)
  have hn : ‖regularTranslateApply r f‖ = ‖f‖ :=
    Unitary.norm_map (regularRightTranslation (H := H) (Multiplicative.ofAdd r)) f
  exact h.trans (by rw [hn]; simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hp (norm_nonneg f))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizationReconstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reconstruction from localized Haar averages

Finite packet averages belong to the explicit commutant algebra. The
normalized interval limit recovers every operator commuting with the
regular core, and hence proves the published commutant formula.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem regularIndicatorProjection_larger
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (f : RegularCoreHilbert H) :
    regularIndicatorProjection t ht (regularIndicatorProjection s hs f) =
      regularIndicatorProjection s hs f := by
  have h := congrArg star (regularIndicatorProjection_mul_of_subset (H := H) s t hs ht hst)
  simp only [star_mul,
    (regularIndicatorProjection_isStarProjection (H := H) s hs).isSelfAdjoint.star_eq,
    (regularIndicatorProjection_isStarProjection (H := H) t ht).isSelfAdjoint.star_eq] at h
  exact congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => B f) h

universe u

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCyclicMultipliers
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Multipliers in the cyclic spectral model -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventScalarMultiplier (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (φ : spectrum ℝ R → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ s, ‖φ s‖ ≤ C) :
    ResolventCyclicL2 R hR x →L[ℂ] ResolventCyclicL2 R hR x :=
  regularFieldOperator (resolventVectorMeasure R hR x) (fun s => φ s • (1 : ℂ →L[ℂ] ℂ))
    (fun z => hφ.aestronglyMeasurable.smul_const z) C
    (Eventually.of_forall fun s => by
      apply le_trans _ (hC s)
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro z
      simp only [smul_apply, one_apply_eq_self, norm_smul]
      exact le_rfl)

theorem resolventScalarMultiplier_apply_ae (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (φ : spectrum ℝ R → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ s, ‖φ s‖ ≤ C)
    (v : ResolventCyclicL2 R hR x) :
    resolventScalarMultiplier R hR x φ hφ C hC v =ᵐ[resolventVectorMeasure R hR x]
      fun s => φ s * v s := by
  have h := regularFieldOperator_represents (resolventVectorMeasure R hR x)
    (fun s => φ s • (1 : ℂ →L[ℂ] ℂ))
    (fun z => hφ.aestronglyMeasurable.smul_const z) C
    (Eventually.of_forall fun s => by
      apply le_trans _ (hC s)
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro z
      simp only [smul_apply, one_apply_eq_self, norm_smul]
      exact le_rfl) v
  simpa only [resolventScalarMultiplier, smul_apply, one_apply_eq_self, smul_eq_mul] using h

theorem resolventScalarMultiplier_continuous (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (g f : C(spectrum ℝ R, ℂ)) :
    resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm
      (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f) =
    ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ (g * f) := by
  apply Lp.ext
  filter_upwards [resolventScalarMultiplier_apply_ae R hR x g g.continuous.measurable ‖g‖
    g.norm_coe_le_norm (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (resolventVectorMeasure R hR x) f,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (resolventVectorMeasure R hR x) (g * f)] with s hs hf hgf
  rw [hs, hf, hgf]
  rfl

theorem resolventCyclicIsometry_multiplier (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (g : C(spectrum ℝ R, ℂ)) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm v) =
    resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x v) := by
  have hd := ContinuousMap.toLp_denseRange ℂ (p := 2) (resolventVectorMeasure R hR x) ℂ
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  refine hd.induction_on (p := fun w : ResolventCyclicL2 R hR x =>
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm w) =
    resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x w)) v ?_ ?_
  · exact isClosed_eq
      ((resolventCyclicIsometry R hR x).continuous.comp
        (resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm).continuous)
      ((resolventContinuousCalculus R hR g).continuous.comp
        (resolventCyclicIsometry R hR x).continuous)
  · intro f
    rw [resolventScalarMultiplier_continuous, resolventCyclicIsometry_continuous,
      resolventCyclicIsometry_continuous, map_mul, mul_apply_eq_comp]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCoordinateMultiplier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The resolvent coordinate in its scalar cyclic model -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventCoordinateOperator (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    ResolventCyclicL2 R hR x →L[ℂ] ResolventCyclicL2 R hR x :=
  resolventScalarMultiplier R hR x (resolventCoordinateFunction R)
    (resolventCoordinateFunction R).continuous.measurable
    ‖resolventCoordinateFunction R‖ (resolventCoordinateFunction R).norm_coe_le_norm

theorem resolventCoordinateOperator_apply_ae (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    resolventCoordinateOperator R hR x v =ᵐ[resolventVectorMeasure R hR x]
      fun s => (s.val : ℂ) * v s :=
  resolventScalarMultiplier_apply_ae R hR x (resolventCoordinateFunction R)
    (resolventCoordinateFunction R).continuous.measurable
    ‖resolventCoordinateFunction R‖ (resolventCoordinateFunction R).norm_coe_le_norm v

theorem resolventCoordinateOperator_intertwines (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x (resolventCoordinateOperator R hR x v) =
      R (resolventCyclicIsometry R hR x v) := by
  have hc : resolventContinuousCalculus R hR (resolventCoordinateFunction R) = R :=
    (resolventContinuousCalculus_ofReal R hR
      ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)
  exact (resolventCyclicIsometry_multiplier R hR x (resolventCoordinateFunction R) v).trans
    (congrArg (fun T : H →L[ℂ] H => T (resolventCyclicIsometry R hR x v)) hc)

theorem one_sub_resolventCoordinateOperator_intertwines (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x ((1 - resolventCoordinateOperator R hR x) v) =
      (1 - R) (resolventCyclicIsometry R hR x v) := by
  simp only [sub_apply, one_apply_eq_self, map_sub, resolventCoordinateOperator_intertwines]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCutMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of resolvent cuts

Monotone projection norms make the diagonal coefficients measurable.
Polarization and the countable Hilbert coefficient criterion then give the
strong measurability needed for the regular-core field construction.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace.SeparableSpace H]

theorem resolventLowerCut_comp_aestronglyMeasurable (R : H →L[ℂ] H)
    (f : ℝ → ℝ) (hf : Measurable f) (x : H) :
    AEStronglyMeasurable (fun t : ℝ => resolventLowerCut R (f t) x) volume := by
  apply aestronglyMeasurable_of_inner
  intro y
  exact ((resolventLowerCut_coefficient_measurable R y x).comp hf).aestronglyMeasurable

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventMultiplierBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independence from the chosen scalar multiplier bound -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventScalarMultiplier_bound_independent (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (x : H) (φ : spectrum ℝ R → ℂ) (hφ : Measurable φ)
    (C D : ℝ) (hC : ∀ s, ‖φ s‖ ≤ C) (hD : ∀ s, ‖φ s‖ ≤ D) :
    resolventScalarMultiplier R hR x φ hφ C hC =
      resolventScalarMultiplier R hR x φ hφ D hD := by
  apply ContinuousLinearMap.ext
  intro v
  apply MeasureTheory.Lp.ext
  filter_upwards [resolventScalarMultiplier_apply_ae R hR x φ hφ C hC v,
    resolventScalarMultiplier_apply_ae R hR x φ hφ D hD v] with s hC hD
  rw [hC, hD]

theorem resolventCyclicIsometry_multiplier_of_bound (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (g : C(spectrum ℝ R, ℂ)) (C : ℝ) (hC : ∀ s, ‖g s‖ ≤ C)
    (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x g g.continuous.measurable C hC v) =
    resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x v) := by
  rw [resolventScalarMultiplier_bound_independent R hR x g g.continuous.measurable
    C ‖g‖ hC g.norm_coe_le_norm]
  exact resolventCyclicIsometry_multiplier R hR x g v

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventMultiplierLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong convergence of bounded spectral multipliers -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventScalarMultiplier_tendsto (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (φn : ℕ → spectrum ℝ R → ℂ) (φ : spectrum ℝ R → ℂ)
    (hn : ∀ n, Measurable (φn n)) (hφ : Measurable φ)
    (hbn : ∀ n s, ‖φn n s‖ ≤ 1) (hb : ∀ s, ‖φ s‖ ≤ 1)
    (ht : ∀ᵐ s ∂resolventVectorMeasure R hR x, Tendsto (fun n => φn n s) atTop (𝓝 (φ s)))
    (v : ResolventCyclicL2 R hR x) :
    Tendsto (fun n => resolventScalarMultiplier R hR x (φn n) (hn n) 1 (hbn n) v) atTop
      (𝓝 (resolventScalarMultiplier R hR x φ hφ 1 hb v)) := by
  let μ := resolventVectorMeasure R hR x
  let F := fun n s => ‖(φn n s - φ s) * v s‖ ^ 2
  have hi : Integrable (fun s => 4 * ‖v s‖ ^ 2) μ :=
    ((Lp.memLp v).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul 4
  have hlim : Tendsto (fun n => ∫ s, F n s ∂μ) atTop (𝓝 0) := by
    have hm (n : ℕ) : AEStronglyMeasurable (F n) μ :=
      (((hn n).aestronglyMeasurable.sub hφ.aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable v)).norm.pow 2
    have hbd (n : ℕ) : ∀ᵐ s ∂μ, ‖F n s‖ ≤ 4 * ‖v s‖ ^ 2 := by
      apply Eventually.of_forall
      intro s
      have he : ‖(φn n s - φ s) * v s‖ ≤ 2 * ‖v s‖ := by
        rw [norm_mul]
        apply (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)).trans
        nlinarith [hbn n s, hb s, norm_nonneg (v s)]
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg ((φn n s - φ s) * v s), norm_nonneg (v s)]
    have hpt : ∀ᵐ s ∂μ, Tendsto (fun n => F n s) atTop (𝓝 0) := by
      filter_upwards [ht] with s hs
      have h := (((hs.sub_const (φ s)).mul_const (v s)).norm).pow 2
      simpa only [sub_self, zero_mul, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (fun s => 4 * ‖v s‖ ^ 2) hm hi hbd hpt
  have he (n : ℕ) :
      ‖resolventScalarMultiplier R hR x (φn n) (hn n) 1 (hbn n) v -
        resolventScalarMultiplier R hR x φ hφ 1 hb v‖ ^ 2 = ∫ s, F n s ∂μ := by
    rw [← resolventCyclic_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [resolventScalarMultiplier_apply_ae R hR x (φn n) (hn n) 1 (hbn n) v,
      resolventScalarMultiplier_apply_ae R hR x φ hφ 1 hb v,
      Lp.coeFn_sub (resolventScalarMultiplier R hR x (φn n) (hn n) 1 (hbn n) v)
        (resolventScalarMultiplier R hR x φ hφ 1 hb v)] with s hn' hφ' hs
    rw [hs, Pi.sub_apply, hn', hφ', ← sub_mul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq := hlim.congr (fun n => (he n).symm)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCyclicCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cyclic model identifies the concrete cut projections -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventCyclicIsometry_cut (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (r : ℝ) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x (resolventCutIndicator R r)
        (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v) =
    resolventLowerCut R r (resolventCyclicIsometry R hR x v) := by
  let g : ℕ → C(spectrum ℝ R, ℝ) := fun n =>
    ⟨fun s => resolventCutScalar r (modularRegularizationScale n) s.val,
      (resolventCutScalar_continuous r (modularRegularizationScale_pos n)).comp
        continuous_subtype_val⟩
  let gc : ℕ → C(spectrum ℝ R, ℂ) := fun n =>
    ⟨fun s => (g n s : ℂ), Complex.continuous_ofReal.comp (g n).continuous⟩
  have hbn (n : ℕ) (s : spectrum ℝ R) : ‖gc n s‖ ≤ 1 := by
    change ‖(resolventCutScalar r (modularRegularizationScale n) s.val : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (resolventCutScalar_bounds r s.val (modularRegularizationScale_pos n)).1]
    exact (resolventCutScalar_bounds r s.val (modularRegularizationScale_pos n)).2
  have hpoint : ∀ s : spectrum ℝ R,
      Tendsto (fun n => gc n s) atTop (𝓝 (resolventCutIndicator R r s)) := by
    intro s
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (resolventCutScalar_tendsto r s.val)
    by_cases hs : s.val < r <;>
      simpa only [Function.comp_def, gc, g, ContinuousMap.coe_mk, resolventCutIndicator, Set.indicator,
        Set.mem_ofPred_eq, hs, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_zero] using h
  have hl := resolventScalarMultiplier_tendsto R hR x (fun n => gc n)
    (resolventCutIndicator R r) (fun n => (gc n).continuous.measurable)
    (resolventCutIndicator_measurable R r) hbn (resolventCutIndicator_bound R r)
    (Eventually.of_forall hpoint) v
  have hcalc (n : ℕ) : resolventContinuousCalculus R hR (gc n) =
      resolventCutRegularization R r (modularRegularizationScale n) := by
    rw [resolventContinuousCalculus_ofReal R hR (g n), resolventCutRegularization,
      cfc_apply _ R hR (resolventCutScalar_continuous r (modularRegularizationScale_pos n)).continuousOn]
    rfl
  have he (n : ℕ) : resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x (gc n) (gc n).continuous.measurable 1 (hbn n) v) =
      resolventCutRegularization R r (modularRegularizationScale n)
        (resolventCyclicIsometry R hR x v) := by
    rw [resolventCyclicIsometry_multiplier_of_bound, hcalc]
  have ht := (resolventCyclicIsometry R hR x).continuous.continuousAt.tendsto.comp hl
  exact tendsto_nhds_unique ht
    ((resolventCutRegularization_tendsto R hR r (resolventCyclicIsometry R hR x v)).congr
      (fun n => (he n).symm))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventMeasureFaithful
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithfulness removes scalar spectral mass at a kernel

An indicator of a zero set would give a kernel vector in the cyclic
spectral model. Injectivity of the represented operator excludes it.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventVectorMeasure_zero_set (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (g : C(spectrum ℝ R, ℂ))
    (hinj : Function.Injective (resolventContinuousCalculus R hR g)) :
    resolventVectorMeasure R hR x {s | g s = 0} = 0 := by
  let μ := resolventVectorMeasure R hR x
  let S : Set (spectrum ℝ R) := {s | g s = 0}
  have hS : MeasurableSet S := (isClosed_eq g.continuous continuous_const).measurableSet
  let v : ResolventCyclicL2 R hR x := indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ)
  have hz : resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm v = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [resolventScalarMultiplier_apply_ae R hR x g g.continuous.measurable ‖g‖
      g.norm_coe_le_norm v, indicatorConstLp_coeFn (p := 2) (hs := hS)
        (hμs := measure_ne_top μ S) (c := (1 : ℂ))]
      with s ha hv
    rw [ha, hv]
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs]
      change g s = 0 at hs
      simp only [hs, zero_mul, Pi.zero_apply]
    · rw [Set.indicator_of_notMem hs, mul_zero]
      rfl
  have hu : resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x v) = 0 := by
    rw [← resolventCyclicIsometry_multiplier, hz, map_zero]
  have hv0 : v = 0 := (resolventCyclicIsometry R hR x).injective
    ((hinj (hu.trans (map_zero _).symm)).trans (map_zero _).symm)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [Lp.eq_zero_iff_ae_eq_zero.mp hv0,
    indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := measure_ne_top μ S)
      (c := (1 : ℂ))] with s hv hs
  intro hmem
  have he : (1 : ℂ) = 0 := by
    have he := hs.symm.trans hv
    rw [Set.indicator_of_mem (show s ∈ S from hmem)] at he
    exact he
  exact _root_.one_ne_zero he

theorem resolventVectorMeasure_zero_endpoint (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) (x : H) :
    resolventVectorMeasure R hR x {s | s.val = 0} = 0 := by
  let g : C(spectrum ℝ R, ℂ) :=
    ⟨fun s => (s.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  have he : resolventContinuousCalculus R hR g = R := by
    exact (resolventContinuousCalculus_ofReal R hR
      ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)
  have h := resolventVectorMeasure_zero_set R hR x g (by rwa [he])
  simpa only [g, ContinuousMap.coe_mk, Complex.ofReal_eq_zero] using h

theorem resolventVectorMeasure_one_endpoint (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective ((1 : H →L[ℂ] H) - R)) (x : H) :
    resolventVectorMeasure R hR x {s | s.val = 1} = 0 := by
  let g : C(spectrum ℝ R, ℂ) :=
    ⟨fun s => (s.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  have he : resolventContinuousCalculus R hR g = R := by
    exact (resolventContinuousCalculus_ofReal R hR
      ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)
  have h := resolventVectorMeasure_zero_set R hR x (1 - g) (by
    simpa only [map_sub, map_one, he] using hinj)
  have hs : {s : spectrum ℝ R | (1 - g) s = 0} = {s | s.val = 1} := by
    ext s
    change (1 : ℂ) - (s.val : ℂ) = 0 ↔ s.val = 1
    rw [sub_eq_zero, eq_comm, Complex.ofReal_eq_one]
  rwa [hs] at h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarSectionSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Selecting a scalar section by a countable measurable coordinate

The rooted random walk evaluates a bounded boundary family at its root.
Countability makes the simultaneous almost-everywhere representative bounds
and linear identities legitimate.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X}
  [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

omit [MeasurableSpace G] [MeasurableSingletonClass G] [DiscreteTopology G] in
theorem scalarSectionSelect_ae_bound (F : G →ᵇ ScalarLInfinity μ) :
    ∀ᵐ x ∂μ, ‖F (r x) x‖ ≤ ‖F‖ := by
  filter_upwards [ae_all_iff.mpr (fun g => scalarInfinity_ae_norm_le (F g))] with x hx
  exact (hx (r x)).trans (F.norm_coe_le_norm (r x))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialSeparability
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Separability of the completed spatial tensor product -/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- A countable dense family in each leg gives a countable total family
of pure tensors in the completed Hilbert tensor product. -/
theorem dense_span_tensorVector {f : ℕ → H} {g : ℕ → K}
    (hf : DenseRange f) (hg : DenseRange g) :
    Dense (Submodule.span ℂ (Set.range (fun p : ℕ × ℕ => tensorVector (g p.2) (f p.1))) :
      Set (SpatialHilbert H K)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply bot_unique
  intro v hv
  change v = 0
  apply spatialTensor_vector_ext
  intro x y
  rw [inner_zero_right]
  have hfinite (i j : ℕ) : inner ℂ (tensorVector (g j) (f i)) v = 0 :=
    hv _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hy (i : ℕ) : inner ℂ (tensorVector y (f i)) v = 0 := by
    refine hg.induction_on (p := fun z => inner ℂ (tensorVector z (f i)) v = 0) y ?_ ?_
    · change IsClosed {z : K | inner ℂ (leftTensorVector (f i) z) v = 0}
      exact isClosed_eq (by fun_prop) continuous_const
    · exact hfinite i
  change inner ℂ (tensorVector y x) v = 0
  refine hf.induction_on (p := fun z => inner ℂ (tensorVector y z) v = 0) x ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact hy

instance spatialHilbert_separable [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace.SeparableSpace K] : TopologicalSpace.SeparableSpace (SpatialHilbert H K) := by
  let f := TopologicalSpace.denseSeq H
  let g := TopologicalSpace.denseSeq K
  have hd := dense_span_tensorVector (TopologicalSpace.denseRange_denseSeq H)
    (TopologicalSpace.denseRange_denseSeq K)
  apply hd.isSeparable_iff.mp
  exact (Set.countable_range (fun p : ℕ × ℕ => tensorVector (g p.2) (f p.1))).isSeparable.span
    (R := ℂ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateMatrixRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two-state matrix representation

The first matrix column acts on the cyclic vector for the first state;
the second column acts on the cyclic vector for the second state. Their
direct sum represents the diagonal state on the two-by-two matrix algebra.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

def twoStateMatrixVector (Ω : H) (ξ : K) : TwoStateMatrixHilbert H K :=
  WithLp.toLp 2 (tupleSingle 0 Ω, tupleSingle 1 ξ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateMatrixAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A von Neumann algebra carrying two diagonal vector states -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoStateMatrixAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (TwoStateMatrixHilbert H H) :=
  diagonalPairAlgebra (matrixVonNeumann (ι := Fin 2) M)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateCornerEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.finiteL2Basis_apply _root_.OAI.KadisonKastler.finiteLocalAmplificationValue_apply _root_.OAI.KadisonKastler.finiteLocalAmplification_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.pointedPowerFibreEquiv_basis _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Isometric embeddings of the two diagonal state spaces -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoStateCornerEmbedding (i : Fin 2) : H →ₗᵢ[ℂ] TwoStateMatrixHilbert H H where
  toFun x := if i = 0 then WithLp.toLp 2 (tupleSingle 0 x, 0)
    else WithLp.toLp 2 (0, tupleSingle 1 x)
  map_add' x y := by
    fin_cases i <;> simp [map_add, ← WithLp.toLp_add]
  map_smul' z x := by
    fin_cases i <;> simp [map_smul, ← WithLp.toLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    fin_cases i <;> simp

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_fst_zero (x : H) :
    (twoStateCornerEmbedding 0 x).fst = tupleSingle 0 x := rfl

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_snd_zero (x : H) :
    (twoStateCornerEmbedding 0 x).snd = 0 := rfl

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_fst_one (x : H) :
    (twoStateCornerEmbedding 1 x).fst = 0 := rfl

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_snd_one (x : H) :
    (twoStateCornerEmbedding 1 x).snd = tupleSingle 1 x := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateCornerCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.finiteL2Basis_apply _root_.OAI.KadisonKastler.finiteLocalAmplificationValue_apply _root_.OAI.KadisonKastler.finiteLocalAmplification_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.pointedPowerFibreEquiv_basis _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The matrix coefficient recovered by compressing a diagonal state space -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem twoStateCornerEmbedding_adjoint (i : Fin 2) (v : TwoStateMatrixHilbert H H) :
    (twoStateCornerEmbedding i).toContinuousLinearMap.adjoint v =
      if i = 0 then v.fst 0 else v.snd 1 := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  fin_cases i <;>
    simp [twoStateCornerEmbedding, WithLp.prod_inner_apply, PiLp.inner_apply,
      tupleSingle_apply, Fin.sum_univ_two]

end

end KadisonKastler

end OAI
end


