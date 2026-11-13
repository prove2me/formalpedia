-- Prove2me | Definitions.Def_Q260K025
-- name    : Q260K025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:19:36.295487+00:00
-- url     : https://prove2.me/theorems/0cea3bcd-8fe9-4fbe-ae1d-75f750871336
-- title:
--   Definitions bundle Q260K025 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 26 definitions and 82 theorems. The definitions and types are `OAI.KadisonKastler.firstBoundaryRootL`, `OAI.KadisonKastler.firstBoundaryScalarMean`, `OAI.KadisonKastler.gaussianStateAverageDeriv`, `OAI.KadisonKastler.hardyKernelCompression`, `OAI.KadisonKastler.hardyKernelInclusion`, `OAI.KadisonKastler.hardyKernelRow`, `OAI.KadisonKastler.hilbertBasisFullCorner`, `OAI.KadisonKastler.increasingFiniteScalarInvariantMean`, `OAI.KadisonKastler.liftedRankRepresentation`, `OAI.KadisonKastler.matrixSiteBlockScale`, `OAI.KadisonKastler.poissonActionApprox`, `OAI.KadisonKastler.randomWalkBoundaryAction`, `OAI.KadisonKastler.rootedScalarBoundaryMean`, `OAI.KadisonKastler.scalarBoundaryLiftL`, `OAI.KadisonKastler.scalarBoundaryRootL`, `OAI.KadisonKastler.scalarPacketAverage`, `OAI.KadisonKastler.scalarProductSwapL`, `OAI.KadisonKastler.scalarProjectionToBoundaryL`, `OAI.KadisonKastler.scalarSectionSelect`, `OAI.KadisonKastler.scalarSectionSelectL`, `OAI.KadisonKastler.scalarSwapFamilyL`, `OAI.KadisonKastler.spatialAmplificationTargetOrder`, `OAI.KadisonKastler.stateActionAverage`, `OAI.KadisonKastler.stateActionAverageMap`, `OAI.KadisonKastler.swappedScalarBoundaryMean`, `OAI.KadisonKastler.unitFrequencyVector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CoreFrequencyUnitWindow`, `KadisonKastler_CoreFrequencyVectors`, `KadisonKastler_CountableAmplificationNormal`, `KadisonKastler_FiniteGroupAverage`, `KadisonKastler_FrequencySupport`, `KadisonKastler_GaussianStateDerivative`, `KadisonKastler_HardyKernelRow`, `KadisonKastler_HardyKernelShift`, `KadisonKastler_HardyKernelVectors`, `KadisonKastler_HardyReproducingKernel`, `KadisonKastler_HardyUnitKernel`, `KadisonKastler_HilbertMatrixGeneration`, `KadisonKastler_IncreasingFiniteMean`, `KadisonKastler_LiftedRankStrata`, `KadisonKastler_NestedMeanEquivariance`, `KadisonKastler_PoissonActionApproximation`, `KadisonKastler_ProductBoundaryRoot`, `KadisonKastler_ProductScalingWords`, `KadisonKastler_RootBoundaryMeanConstruction`, `KadisonKastler_ScalarBoundaryRoot`, `KadisonKastler_ScalarFrequencySwap`, `KadisonKastler_ScalarPacketMeasure`, `KadisonKastler_ScalarPositiveLimit`, `KadisonKastler_ScalarProductSwap`, `KadisonKastler_ScalarSectionSelection`, `KadisonKastler_ScalarShiftCesaro`, `KadisonKastler_ScalarShiftLimit`, `KadisonKastler_ScalarWeakLimit`, `KadisonKastler_ShiftBoundaryScalarAlgebra`, `KadisonKastler_ShiftBoundaryScalarMaps`, `KadisonKastler_ShiftBoundarySpace`, `KadisonKastler_SpatialMatrixAmplification`, `KadisonKastler_StateActionAverages`, `KadisonKastler_SwappedBoundaryMean`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K016`, `Q260K017`, `Q260K018`, `Q260K019` and `Q260K020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K028`; the statements `OAI.KadisonKastler.exists_strongly_invariant_product_of_simple`, `OAI.KadisonKastler.exists_strongly_invariant_with_normal_marginals`, `OAI.KadisonKastler.liftedRankRepresentation_measurable`, `OAI.KadisonKastler.liftedRank_field_decomposition` and `OAI.KadisonKastler.liftedRank_scalarCenter`; the proofs of `OAI.KadisonKastler.coreTraceFrequencyVector_supported_scaling`, `OAI.KadisonKastler.exists_strongly_invariant_product_of_simple`, `OAI.KadisonKastler.exists_strongly_invariant_with_normal_marginals`, `OAI.KadisonKastler.liftedRankRepresentation_measurable`, `OAI.KadisonKastler.liftedRank_field_decomposition`, `OAI.KadisonKastler.liftedRank_scalarCenter`, `OAI.KadisonKastler.normal_marginal_product_agreement`, `OAI.KadisonKastler.regularCoreEmbedding_symmetry_of_balance` and `OAI.KadisonKastler.scalarGaugeWindowBalance`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Basic
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
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
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
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Find
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
import Mathlib.LinearAlgebra.Dimension.Finite
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
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
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
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K016
import Definitions.Def_Q260K017
import Definitions.Def_Q260K018
import Definitions.Def_Q260K019
import Definitions.Def_Q260K020

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

omit [CompleteSpace H] in
theorem regularIndicatorProjection_tensor (s : Set ℝ) (hs : MeasurableSet s)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularIndicatorProjection s hs (regularTensorVector φ ξ) =
      regularTensorVector (regularIndicatorProjection s hs φ) ξ := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae s hs (regularTensorVector φ ξ),
    regularTensorVector_apply_ae φ ξ,
    regularTensorVector_apply_ae (regularIndicatorProjection s hs φ) ξ,
    regularIndicatorProjection_apply_ae s hs φ] with t hp hφ ht hps
  rw [hp, ht]
  by_cases h : t ∈ s
  · simp only [Set.indicator_of_mem h] at hps ⊢
    rw [hφ, hps]
  · simp only [Set.indicator_of_notMem h] at hps ⊢
    rw [hps, zero_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyUnitWindow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A nonzero bounded frequency window in the modular core

The unit interval supplies an explicit isometric family of vectors fixed by
its frequency projection. No trace or finiteness assertion is used here.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitFrequencyVector (ξ : H) : RegularCoreHilbert H :=
  regularFrequencyPacket unitFrequencyScalar ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableAmplificationNormal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable [Nontrivial H]

theorem norm_denseSeparatingUnitVector : ‖denseSeparatingUnitVector (H := H)‖ = 1 := by
  rw [denseSeparatingUnitVector, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr weightedDenseVector_ne_zero)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteGroupAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Normalized counting measure is invariant under left translation. -/
theorem finiteGroupAverage_translate (g : G) (f : G →ᵇ B) :
    finiteGroupAverage (boundaryTranslate (1 : G →* (B ≃⋆ₐ[ℂ] B)) g f) =
      finiteGroupAverage f := by
  simp only [finiteGroupAverage_apply, boundaryTranslate_apply,
    MonoidHom.one_apply, StarAlgEquiv.one_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun _ => rfl)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencySupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Frequency-cut ranges as almost-everywhere support conditions -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Being fixed by the actual frequency projection is exactly the usual
almost-everywhere support condition on the `L²` Fourier transform. -/
theorem regularFrequencyProjection_fixed_iff (a : ℝ) (f : RegularCoreHilbert H) :
    regularFrequencyProjection a f = f ↔
      ∀ᵐ t : ℝ, t ≤ a / (2 * Real.pi) → (𝓕 f : RegularCoreHilbert H) t = 0 := by
  constructor
  · intro h
    have hp := regularFrequencyProjection_apply_fourier a f
    rw [h] at hp
    filter_upwards [hp] with t ht hle
    rw [ht, Set.indicator_of_notMem (show t ∉ Set.Ioi (a / (2 * Real.pi)) from not_lt.mpr hle)]
  · intro h
    apply (Lp.fourierTransformₗᵢ ℝ H).injective
    apply Lp.ext
    filter_upwards [regularFrequencyProjection_apply_fourier a f, h] with t hp ht
    change (𝓕 (regularFrequencyProjection a f) : RegularCoreHilbert H) t =
      (𝓕 f : RegularCoreHilbert H) t
    rw [hp]
    by_cases hmem : t ∈ Set.Ioi (a / (2 * Real.pi))
    · exact Set.indicator_of_mem hmem _
    · rw [Set.indicator_of_notMem hmem]
      exact (ht (le_of_not_gt hmem)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateDerivative
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded operators representing the derivative of Gaussian smearing -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def gaussianStateAverageDeriv (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) : H →L[ℂ] H :=
  weightedOperatorIntegral volume (gaussianStateKernelDeriv r z)
    (gaussianStateKernelDeriv_integrable hr z) (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyReproducingKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete Hardy reproducing vectors

The inverse Fourier transform of a one-sided exponential belongs to the
positive-frequency space. Its normalization is computed, not assumed.
-/

namespace KadisonKastler

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

theorem hardyReproducingKernel_positive (z : ℂ) (hz : 0 < z.re) :
    regularFrequencyProjection 0 (hardyReproducingKernel z hz) =
      hardyReproducingKernel z hz := by
  apply (regularFrequencyProjection_fixed_iff 0 _).mpr
  change ∀ᵐ s : ℝ, s ≤ 0 / (2 * Real.pi) →
    (𝓕 (𝓕⁻ (hardyFrequencyKernel z hz)) : RegularCoreHilbert ℂ) s = 0
  rw [fourier_fourierInv_eq]
  filter_upwards [(positiveLaplaceKernel_memLp hz).coeFn_toLp] with s hs hle
  change (positiveLaplaceKernel_memLp hz).toLp (positiveLaplaceKernel z) s = 0
  rw [hs]
  simp only [zero_div] at hle
  exact Set.indicator_of_notMem (not_lt.mpr hle) _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyUnitKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit Hardy kernels and their Poisson compression -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem hardyUnitKernel_positive (z : ℂ) (hz : 0 < z.re) :
    regularFrequencyProjection 0 (hardyUnitKernel z hz) = hardyUnitKernel z hz := by
  simp only [hardyUnitKernel, map_smul, hardyReproducingKernel_positive]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The isometric copy of the coefficient Hilbert space carried by a unit kernel. -/
def hardyKernelInclusion (z : ℂ) (hz : 0 < z.re) : H →ₗᵢ[ℂ] RegularCoreHilbert H where
  toLinearMap := (regularTensorVector (hardyUnitKernel z hz)).toLinearMap
  norm_map' x := by rw [ContinuousLinearMap.coe_coe, norm_regularTensorVector,
    hardyUnitKernel_norm, one_mul]

def hardyKernelCompression (z : ℂ) (hz : 0 < z.re)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) : H →L[ℂ] H :=
  (hardyKernelInclusion z hz).toContinuousLinearMap.adjoint.comp
    (T.comp (hardyKernelInclusion z hz).toContinuousLinearMap)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyKernelShift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Character shifts of the reproducing kernel

A backward shift followed by the positive-frequency projection is scalar on
an exponential kernel. Forward shifts preserve the positive-frequency space.
-/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacter_preserves_positive {b : ℝ} (hb : 0 ≤ b)
    (f : RegularCoreHilbert H) (hf : regularFrequencyProjection 0 f = f) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := H) (2 * Real.pi * b) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * b) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f := by
  apply (regularFrequencyProjection_fixed_iff 0 _).mpr
  rw [fourier_regularCharacterUnitary]
  have hs := (regularFrequencyProjection_fixed_iff 0 f).mp hf
  filter_upwards [regularTranslateApply_ae (-b) (𝓕 f),
    (measurePreserving_add_right volume (-b)).quasiMeasurePreserving.ae hs]
      with s ht hsupport hle
  rw [ht]
  apply hsupport
  simp only [zero_div] at hle ⊢
  linarith

/-- Projected negative character shifts act diagonally on a reproducing kernel. -/
theorem hardyReproducingKernel_backward_shift (z : ℂ) (hz : 0 < z.re)
    {b : ℝ} (hb : 0 ≤ b) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := ℂ) (2 * Real.pi * (-b)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (hardyReproducingKernel z hz)) =
        Complex.exp (-z * b) • hardyReproducingKernel z hz := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (regularFrequencyProjection 0
    ((regularCharacterUnitary (H := ℂ) (2 * Real.pi * (-b)) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (hardyReproducingKernel z hz))) =
        𝓕 (Complex.exp (-z * b) • hardyReproducingKernel z hz)
  rw [fourier_frequencyProjection_zero, fourier_regularCharacterUnitary, fourier_smul]
  simp only [hardyReproducingKernel, fourier_fourierInv_eq, neg_neg]
  exact positiveLaplace_shift_cut z hz hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyKernelVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reproducing-kernel vectors and their character tests -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyProjection_zero_tensor (φ : RegularCoreHilbert ℂ) (x : H) :
    regularFrequencyProjection 0 (regularTensorVector φ x) =
      regularTensorVector (regularFrequencyProjection 0 φ) x := by
  have hn (ψ : RegularCoreHilbert ℂ) :
      FourierTransform.fourier (regularTensorVector ψ x) =
        regularTensorVector (FourierTransform.fourier ψ) x :=
    fourier_regularTensorVector ψ x
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change FourierTransform.fourier (regularFrequencyProjection 0 (regularTensorVector φ x)) =
    FourierTransform.fourier (regularTensorVector (regularFrequencyProjection 0 φ) x)
  rw [fourier_frequencyProjection_zero, hn,
    regularIndicatorProjection_tensor, hn,
    fourier_frequencyProjection_zero]

theorem regularCharacter_tensor (a : ℝ) (φ : RegularCoreHilbert ℂ) (x : H) :
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularTensorVector φ x) =
    regularTensorVector
      ((regularCharacterUnitary (H := ℂ) a : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) φ) x := by
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae a (regularTensorVector φ x),
    regularTensorVector_apply_ae φ x,
    regularTensorVector_apply_ae ((regularCharacterUnitary (H := ℂ) a :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) φ) x,
    regularCharacterUnitary_apply_ae a φ] with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, smul_smul]
  rfl

theorem hardyKernelInclusion_positive (z : ℂ) (hz : 0 < z.re) (x : H) :
    regularFrequencyProjection 0 (hardyKernelInclusion z hz x) =
      hardyKernelInclusion z hz x := by
  change regularFrequencyProjection 0 (regularTensorVector (hardyUnitKernel z hz) x) = _
  rw [regularFrequencyProjection_zero_tensor, hardyUnitKernel_positive]
  rfl

theorem hardyUnitKernel_backward_shift (z : ℂ) (hz : 0 < z.re)
    {b : ℝ} (hb : 0 ≤ b) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := ℂ) (2 * Real.pi * (-b)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (hardyUnitKernel z hz)) =
        Complex.exp (-z * b) • hardyUnitKernel z hz := by
  simp only [hardyUnitKernel, map_smul, hardyReproducingKernel_backward_shift z hz hb,
    smul_smul]
  congr 1
  ring

theorem hardyKernelInclusion_backward_shift (z : ℂ) (hz : 0 < z.re)
    {b : ℝ} (hb : 0 ≤ b) (x : H) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
        Complex.exp (-z * b) • hardyKernelInclusion z hz x := by
  change regularFrequencyProjection 0
    ((regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularTensorVector (hardyUnitKernel z hz) x)) = _
  rw [regularCharacter_tensor, regularFrequencyProjection_zero_tensor,
    hardyUnitKernel_backward_shift z hz hb]
  rw [map_smul]
  rfl

theorem hardyKernelInclusion_adjoint_self (z : ℂ) (hz : 0 < z.re) :
    (hardyKernelInclusion (H := H) z hz).toContinuousLinearMap.adjoint.comp
      (hardyKernelInclusion z hz).toContinuousLinearMap = ContinuousLinearMap.id ℂ H := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint
    (hardyKernelInclusion z hz x)) = inner ℂ y x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (hardyKernelInclusion z hz).inner_map_map y x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyKernelRow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The reproducing row on the positive-frequency space -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hardyKernelRow (z : ℂ) (hz : 0 < z.re) : RegularCoreHilbert H →L[ℂ] H :=
  (hardyKernelInclusion z hz).toContinuousLinearMap.adjoint

theorem hardyKernelRow_inclusion (z : ℂ) (hz : 0 < z.re) (x : H) :
    hardyKernelRow z hz (hardyKernelInclusion z hz x) = x :=
  congrArg (fun T : H →L[ℂ] H => T x) (hardyKernelInclusion_adjoint_self z hz)

theorem hardyKernelRow_projection (z : ℂ) (hz : 0 < z.re) (f : RegularCoreHilbert H) :
    hardyKernelRow z hz (regularFrequencyProjection 0 f) = hardyKernelRow z hz f := by
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint
    (regularFrequencyProjection 0 f)) = inner ℂ x
      ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint f)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  have hs : inner ℂ (regularFrequencyProjection 0 (hardyKernelInclusion z hz x)) f =
      inner ℂ (hardyKernelInclusion z hz x) (regularFrequencyProjection 0 f) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (regularFrequencyProjection_isStarProjection (H := H) 0).isSelfAdjoint)
      (hardyKernelInclusion z hz x) f
  rw [hardyKernelInclusion_positive] at hs
  exact hs.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IncreasingFiniteMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Invariant means from increasing finite subgroups

Normalized counting averages have a simultaneous scalar ultralimit. Every
fixed group translation preserves all sufficiently late averages.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem finiteSubgroupFunctional_invariant [DiscreteTopology G] (K : Subgroup G) [Finite K]
    (g : G) (hg : g ∈ K) (f : G →ᵇ ℂ) :
    finiteSubgroupFunctional K (scalarMeanTranslate g f) = finiteSubgroupFunctional K f := by
  let := Fintype.ofFinite K
  let k : K := ⟨g, hg⟩
  have he : subgroupRestriction K (scalarMeanTranslate g f) =
      boundaryTranslate (1 : K →* (ℂ ≃⋆ₐ[ℂ] ℂ)) k (subgroupRestriction K f) := by
    ext t
    rfl
  change finiteGroupAverage (subgroupRestriction K (scalarMeanTranslate g f)) =
    finiteGroupAverage (subgroupRestriction K f)
  rw [he, finiteGroupAverage_translate]

variable (K : ℕ → Subgroup G) [∀ n, Finite (K n)]

theorem finiteChainMeanValue_invariant [DiscreteTopology G] (hmono : Monotone K)
    (hcover : ∀ g : G, ∃ n, g ∈ K n) (g : G) (f : G →ᵇ ℂ) :
    finiteChainMeanValue K (scalarMeanTranslate g f) = finiteChainMeanValue K f := by
  obtain ⟨n, hn⟩ := hcover g
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K _)
  apply (finiteChainMeanValue_tendsto K f).congr'
  apply Filter.Eventually.filter_mono finiteChainUltrafilter_le
  filter_upwards [eventually_ge_atTop n] with k hk
  exact (finiteSubgroupFunctional_invariant (K k) g (hmono hk hn) f).symm

/-- The scalar invariant mean for a group exhausted by an increasing sequence
of finite subgroups. -/
def increasingFiniteScalarInvariantMean [DiscreteTopology G] (hmono : Monotone K)
    (hcover : ∀ g : G, ∃ n, g ∈ K n) : ScalarInvariantMean G where
  toCLM := LinearMap.mkContinuous
    { toFun := finiteChainMeanValue K
      map_add' := finiteChainMeanValue_add K
      map_smul' := finiteChainMeanValue_smul K }
    1 (fun f => by
      change ‖finiteChainMeanValue K f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using finiteChainMeanValue_norm K f)
  map_const_one := finiteChainMeanValue_const K 1
  norm_le := finiteChainMeanValue_norm K
  positive := finiteChainMeanValue_positive K
  invariant := finiteChainMeanValue_invariant K hmono hcover

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertMatrixGeneration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite or countable matrix coordinates on separable Hilbert spaces -/

namespace KadisonKastler

open Generator
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Concrete full countable matrix units on the original Hilbert space. -/
def hilbertBasisFullCorner (b : HilbertBasis ℕ ℂ H) :
    FullMatrixCorner (hilbertBasisInitialSpace b) where
  entry i j := InnerProductSpace.rankOne ℂ (b i) (b j)
  star_entry i j := by
    rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
  mul_entry i j k l := by
    change (InnerProductSpace.rankOne ℂ (b i) (b j)).comp
      (InnerProductSpace.rankOne ℂ (b k) (b l)) = _
    rw [InnerProductSpace.rankOne_comp_rankOne,
      orthonormal_iff_ite.mp b.orthonormal]
    split_ifs <;> simp_all
  zero_zero := by
    obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp
      (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) (b.orthonormal.norm_eq_one 0))
    exact h
  total x := by
    simpa only [InnerProductSpace.rankOne_apply, ← b.repr_apply_apply] using b.hasSum_repr x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LiftedRankStrata
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

def liftedRankRepresentation (n : ℕ) (x : (commonRankStratum M n).X) :
    B →⋆ₐ[ℂ] ((commonRankStratum M n).K →L[ℂ] (commonRankStratum M n).K) :=
  (rankFiberLift n).conjStarAlgEquiv.toStarAlgHom.comp
    (fixedFiberRepresentation M.field (commonRankBasis π D) (commonRankBasis_total π D) n x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NestedMeanEquivariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equivariance of nested means for separate group actions -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]
  (α₁ α₂ : NonsingularAction G D μ) (β : NonsingularAction (G × G) D μ)
  (hβ : ∀ g z, β.toPerm g z = α₁.toPerm g.1 (α₂.toPerm g.2 z))

variable (m₁ : ScalarBoundaryMean α₁) (m₂ : ScalarBoundaryMean α₂)
  (hn₁ : ∀ g F, m₁.toCLM
    ((scalarInfinityPullbackL (α₂.toPerm g) (α₂.quasi g)).compLeftContinuousBounded G F) =
      scalarInfinityPullback (α₂.toPerm g) (α₂.quasi g) (m₁.toCLM F))
  (hn₂ : ∀ g F, m₂.toCLM
    ((scalarInfinityPullbackL (α₁.toPerm g) (α₁.quasi g)).compLeftContinuousBounded G F) =
      scalarInfinityPullback (α₁.toPerm g) (α₁.quasi g) (m₂.toCLM F))

include hβ hn₁ hn₂ in
theorem nestedScalarMeanL_equivariant (g : G × G)
    (F : (G × G) →ᵇ ScalarLInfinity μ) :
    nestedScalarMeanL m₁ m₂ (scalarBoundaryTranslate β g F) =
      scalarInfinityPullback (β.toPerm g⁻¹) (β.quasi g⁻¹) (nestedScalarMeanL m₁ m₂ F) := by
  have hrow (t : G) : boundedFamilyRow (scalarBoundaryTranslate β g F) t =
      scalarBoundaryTranslate α₂ g.2
        ((scalarInfinityPullbackL (α₁.toPerm g.1⁻¹) (α₁.quasi g.1⁻¹)).compLeftContinuousBounded G
          (boundedFamilyRow F (g.1⁻¹ * t))) := by
    apply BoundedContinuousFunction.ext
    intro s
    exact scalarSeparatePullback α₁ α₂ β hβ g⁻¹ (F (g.1⁻¹ * t, g.2⁻¹ * s))
  have hrows : nestedMeanRowsL m₂ (scalarBoundaryTranslate β g F) =
      (scalarInfinityPullbackL (α₂.toPerm g.2⁻¹) (α₂.quasi g.2⁻¹)).compLeftContinuousBounded G
        (scalarBoundaryTranslate α₁ g.1 (nestedMeanRowsL m₂ F)) := by
    apply BoundedContinuousFunction.ext
    intro t
    change m₂.toCLM (boundedFamilyRow (scalarBoundaryTranslate β g F) t) = _
    rw [hrow, m₂.equivariant, hn₂]
    rfl
  change m₁.toCLM (nestedMeanRowsL m₂ (scalarBoundaryTranslate β g F)) = _
  rw [hrows, hn₁, m₁.equivariant]
  exact (scalarSeparatePullback α₁ α₂ β hβ g⁻¹ (nestedScalarMeanL m₁ m₂ F)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateActionAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Probability averages of the implemented modular action

These maps are defined by vector integration. They are contractions and
preserve the reference vector state whenever the implementing group fixes
the reference vector.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def stateActionAverage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) : H →L[ℂ] H :=
  probabilityOperatorIntegral μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

theorem stateActionAverage_norm_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) : ‖stateActionAverage U hU μ a‖ ≤ ‖a‖ :=
  norm_probabilityOperatorIntegral_le μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    (norm_nonneg a) (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

@[simp] theorem stateActionAverage_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    stateActionAverage U hU μ (1 : H →L[ℂ] H)=1 := by
  ext x
  change (∫ t, stateActionOrbit U (1 : H →L[ℂ] H) t x ∂μ)=x
  have he (t : ℝ) : stateActionOrbit U (1 : H →L[ℂ] H) t=1 :=
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))).map_one
  simp only [he,one_apply_eq_self,integral_const,probReal_univ,one_smul]

def stateActionAverageMap (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := stateActionAverage U hU μ
      map_add' a b := by
        ext x
        change (∫ t, stateActionOrbit U (a+b) t x ∂μ)=
          (∫ t, stateActionOrbit U a t x ∂μ)+(∫ t, stateActionOrbit U b t x ∂μ)
        have he (t : ℝ) : stateActionOrbit U (a+b) t=
            stateActionOrbit U a t+stateActionOrbit U b t := by
          simp only [stateActionOrbit,unitaryConj,mul_add,add_mul]
        simp only [he,add_apply]
        exact integral_add
          (integrable_bounded_operator_vector μ (stateActionOrbit U a)
            (fun y => (stateActionOrbit_continuous U hU a y).aestronglyMeasurable)
            (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) x)
          (integrable_bounded_operator_vector μ (stateActionOrbit U b)
            (fun y => (stateActionOrbit_continuous U hU b y).aestronglyMeasurable)
            (Eventually.of_forall fun t => (stateActionOrbit_norm U b t).le) x)
      map_smul' c a := by
        ext x
        change (∫ t, stateActionOrbit U (c • a) t x ∂μ)=
          c • (∫ t, stateActionOrbit U a t x ∂μ)
        have he (t : ℝ) : stateActionOrbit U (c • a) t=c • stateActionOrbit U a t := by
          simp only [stateActionOrbit,unitaryConj,mul_smul_comm,smul_mul_assoc]
        simp only [he,smul_apply]
        exact integral_smul c _ }
    1 (fun a => by
      change ‖stateActionAverage U hU μ a‖ ≤ 1*‖a‖
      rw [one_mul]
      exact stateActionAverage_norm_le U hU μ a)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonActionApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded, norm-continuous approximations within invariant algebras -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def poissonActionApprox (a : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  poissonVectorAverage (stateActionOrbit U a) (stateActionOrbit_continuous U hU a)
    ‖a‖ (fun t => (stateActionOrbit_norm U a t).le) 0 r

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarWeakLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.scalarBoundaryStar_apply _root_.OAI.KadisonKastler.scalarInfinityMulL_apply _root_.OAI.KadisonKastler.scalarL2MulL_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded scalar weak limits

Uniformly bounded scalar functions have simultaneous weak L2 cluster points
on a probability space. Closed convex disk constraints retain the essential
bound, so the limits are actual L-infinity classes.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem exists_scalar_weak_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (f : ι → ScalarLInfinity μ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ∃ g : ScalarLInfinity μ, ‖g‖ ≤ C ∧ ∀ y : Lp ℂ 2 μ,
      Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) (ω : Filter ι)
        (𝓝 (inner ℂ y (scalarInfinityToL2 g))) := by
  obtain ⟨z, _, ht⟩ := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => scalarInfinityToL2 (f i)) C
    (fun i => (norm_scalarInfinityToL2_le (f i)).trans (hf i))
  have hz : ∀ᵐ x ∂μ, ‖z x‖ ≤ C := by
    have hb (i : ι) : ∀ᵐ x ∂μ, scalarInfinityToL2 (f i) x ∈ Metric.closedBall (0 : ℂ) C := by
      filter_upwards [scalarInfinityToL2_ae (f i), scalarInfinity_ae_norm_le (f i)] with x hx hn
      simpa only [Metric.mem_closedBall, dist_zero_right, hx] using hn.trans (hf i)
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      L2_ae_mem_of_inner_tendsto Metric.isClosed_closedBall (convex_closedBall (0 : ℂ) C)
        (fun i => scalarInfinityToL2 (f i)) z hb ht
  let g : ScalarLInfinity μ := (memLp_top_of_bound (Lp.aestronglyMeasurable z) C hz).toLp z
  have hg : g =ᵐ[μ] z := MemLp.coeFn_toLp _
  have he : scalarInfinityToL2 g = z := Lp.ext ((scalarInfinityToL2_ae g).trans hg)
  refine ⟨g, ?_, ?_⟩
  · have hbg : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
      filter_upwards [hg, hz] with x hx hb
      rwa [hx]
    simpa using Lp.norm_le_of_ae_bound hC hbg
  · simpa only [he] using ht

/-- One ultrafilter gives a simultaneous linear, contractive scalar limit. -/
theorem exists_scalar_linear_weak_ultralimit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (ω : Ultrafilter ι) (A : ι → E →L[ℂ] ScalarLInfinity μ)
    (hA : ∀ i x, ‖A i x‖ ≤ ‖x‖) :
    ∃ B : E →L[ℂ] ScalarLInfinity μ, (∀ x, ‖B x‖ ≤ ‖x‖) ∧
      ∀ x y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (A i x))) (ω : Filter ι)
        (𝓝 (inner ℂ y (scalarInfinityToL2 (B x)))) := by
  choose B hB ht using fun x : E =>
    exists_scalar_weak_ultralimit ω (fun i => A i x) ‖x‖ (norm_nonneg x) (fun i => hA i x)
  have hadd (x z : E) : B (x + z) = B x + B z := by
    apply scalarInfinityToL2_injective
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x + z) y)
    simpa only [map_add, scalarInfinityToL2_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : E) : B (c • x) = c • B x := by
    apply scalarInfinityToL2_injective
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, scalarInfinityToL2_smul, inner_smul_right] using (ht x y).const_mul c
  let L : E →L[ℂ] ScalarLInfinity μ := LinearMap.mkContinuous
    { toFun := B, map_add' := hadd, map_smul' := hsmul }
    1 (fun x => by simpa using hB x)
  exact ⟨L, hB, ht⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarShiftCesaro
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.scalarBoundaryStar_apply _root_.OAI.KadisonKastler.scalarInfinityMulL_apply _root_.OAI.KadisonKastler.scalarInfinityToL2L_apply _root_.OAI.KadisonKastler.scalarL2MulL_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive Cesaro averages for the nonsingular boundary shift -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  (S : D → D) (hS : Measure.QuasiMeasurePreserving S μ μ)

theorem scalarShiftCesaro_apply (n : ℕ) (f : ScalarLInfinity μ) :
    scalarShiftCesaro S hS n f = (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
      ∑ i ∈ Finset.range (n + 1), ((scalarInfinityPullbackL S hS) ^ i) f := by
  simp only [scalarShiftCesaro, smul_apply, sum_apply]

theorem scalarPullback_power_norm_le (n : ℕ) (f : ScalarLInfinity μ) :
    ‖((scalarInfinityPullbackL S hS) ^ n) f‖ ≤ ‖f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact (norm_scalarInfinityPullback_le S hS _).trans ih

theorem scalarShiftCesaro_norm_le (n : ℕ) (f : ScalarLInfinity μ) :
    ‖scalarShiftCesaro S hS n f‖ ≤ ‖f‖ := by
  have hp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [scalarShiftCesaro, smul_apply, sum_apply]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (n + 1))]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        ‖((scalarInfinityPullbackL S hS) ^ i) f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _i ∈ Finset.range (n + 1), ‖f‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => scalarPullback_power_norm_le S hS i f)
    _ = ‖f‖ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

theorem scalarShiftCesaro_difference (n : ℕ) (f : ScalarLInfinity μ) :
    scalarInfinityPullbackL S hS (scalarShiftCesaro S hS n f) - scalarShiftCesaro S hS n f =
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
        (((scalarInfinityPullbackL S hS) ^ (n + 1)) f - f) := by
  let U := scalarInfinityPullbackL S hS
  have hp (i : ℕ) : U ((U ^ i) f) = (U ^ (i + 1)) f :=
    congrArg (fun A : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ => A f) (pow_succ' U i).symm
  simp only [scalarShiftCesaro, smul_apply, sum_apply,
    map_smul, map_sum, ← smul_sub, ← Finset.sum_sub_distrib]
  change _ = (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) • ((U ^ (n + 1)) f - f)
  congr 1
  simp_rw [show ∀ i, scalarInfinityPullbackL S hS
      (((scalarInfinityPullbackL S hS) ^ i) f) = (U ^ (i + 1)) f from hp]
  simpa using Finset.sum_range_sub (fun i : ℕ => (U ^ i) f) (n + 1)

theorem scalarShiftCesaro_difference_norm_le (n : ℕ) (f : ScalarLInfinity μ) :
    ‖scalarInfinityPullbackL S hS (scalarShiftCesaro S hS n f) - scalarShiftCesaro S hS n f‖ ≤
      2 * ((n + 1 : ℕ) : ℝ)⁻¹ * ‖f‖ := by
  rw [scalarShiftCesaro_difference]
  exact norm_inv_nat_smul_sub_le n _ f (scalarPullback_power_norm_le S hS (n + 1) f)

theorem scalarShiftCesaro_fixed (n : ℕ) (f : ScalarLInfinity μ)
    (hf : scalarInfinityPullback S hS f = f) : scalarShiftCesaro S hS n f = f := by
  have hp (i : ℕ) : ((scalarInfinityPullbackL S hS) ^ i) f = f := by
    induction i with
    | zero => simp
    | succ i hi =>
      rw [pow_succ', mul_apply_eq_comp, hi]
      exact hf
  simp only [scalarShiftCesaro, smul_apply, sum_apply, hp, Finset.sum_const, Finset.card_range]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  change (((n + 1 : ℕ) : ℂ)⁻¹ * ((n + 1 : ℕ) : ℂ)) • f = f
  rw [inv_mul_cancel₀ hn, one_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarShiftLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The invariant scalar limit of shift averages

One common ultrafilter yields a contractive linear limit of the Cesaro
operators. The telescoping estimate and weak closure of the nonsingular
pullback graph force every value of the limit to be shift invariant.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (S : X → X) (hS : Measure.QuasiMeasurePreserving S μ μ)

theorem scalarShiftCesaro_difference_tendsto_zero (f : ScalarLInfinity μ) :
    Tendsto (fun n => scalarInfinityPullback S hS (scalarShiftCesaro S hS n f) -
      scalarShiftCesaro S hS n f) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hrate : Tendsto (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ)⁻¹ * ‖f‖) atTop (𝓝 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one, mul_zero, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2).mul_const ‖f‖
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => scalarShiftCesaro_difference_norm_le S hS n f)
    hrate

theorem scalarShiftCesaro_weak_limit_fixed
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (f b : ScalarLInfinity μ)
    (hb : ∀ y, Tendsto (fun n => inner ℂ y (scalarInfinityToL2 (scalarShiftCesaro S hS n f)))
      (ω : Filter ℕ) (𝓝 (inner ℂ y (scalarInfinityToL2 b)))) :
    scalarInfinityPullback S hS b = b := by
  have hd := (scalarInfinityToL2L (μ := μ)).continuous.tendsto 0 |>.comp
    ((scalarShiftCesaro_difference_tendsto_zero S hS f).mono_left hω)
  have hd' : Tendsto (fun n => scalarInfinityToL2
      (scalarInfinityPullback S hS (scalarShiftCesaro S hS n f)) -
        scalarInfinityToL2 (scalarShiftCesaro S hS n f)) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [Function.comp_def, map_sub, map_zero, scalarInfinityToL2L_apply] using hd
  have hg (y : Lp ℂ 2 μ) : Tendsto (fun n => inner ℂ y (scalarInfinityToL2
      (scalarInfinityPullback S hS (scalarShiftCesaro S hS n f)))) (ω : Filter ℕ)
      (𝓝 (inner ℂ y (scalarInfinityToL2 b))) := by
    have hc : Continuous (fun z : Lp ℂ 2 μ => inner ℂ y z) :=
      continuous_const.inner continuous_id
    have hh := (hc.tendsto (0 : Lp ℂ 2 μ)).comp hd'
    have hh' := hh.add (hb y)
    simpa only [Function.comp_def, inner_zero_right, zero_add, inner_sub_right, sub_add_cancel] using hh'
  exact scalarInfinityPullback_of_weak_limits S hS
    (fun n => scalarShiftCesaro S hS n f)
    (fun n => scalarInfinityPullback S hS (scalarShiftCesaro S hS n f)) b b
    (fun _ => rfl) hb hg

theorem exists_scalar_shift_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E →L[ℂ] ScalarLInfinity μ) (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) :
    ∃ B : E →L[ℂ] ScalarLInfinity μ, (∀ x, ‖B x‖ ≤ ‖x‖) ∧
      (∀ x, scalarInfinityPullback S hS (B x) = B x) ∧
      ∀ x y, Tendsto (fun n => inner ℂ y (scalarInfinityToL2 (scalarShiftCesaro S hS n (J x))))
        (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)
        (𝓝 (inner ℂ y (scalarInfinityToL2 (B x)))) := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨B, hB, ht⟩ := exists_scalar_linear_weak_ultralimit ω
    (fun n => (scalarShiftCesaro S hS n).comp J)
    (fun n x => (scalarShiftCesaro_norm_le S hS n (J x)).trans (hJ x))
  refine ⟨B, hB, ?_, ht⟩
  intro x
  exact scalarShiftCesaro_weak_limit_fixed S hS ω (Ultrafilter.of_le atTop) (J x) (B x) (ht x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPositiveLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem scalarNonnegative_real_smul {f : ScalarLInfinity μ} (hf : ScalarNonnegative f)
    {c : ℝ} (hc : 0 ≤ c) : ScalarNonnegative ((c : ℂ) • f) := by
  filter_upwards [Lp.coeFn_smul (c : ℂ) f, hf] with x hx hp
  simp only [Pi.smul_apply] at hx
  rw [hx]
  change (((c : ℂ) * f x).im = 0 ∧ 0 ≤ ((c : ℂ) * f x).re)
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    hp.1, mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_nonneg hc hp.2⟩

theorem scalarNonnegative_sum (s : Finset ℕ) (f : ℕ → ScalarLInfinity μ)
    (hf : ∀ n, ScalarNonnegative (f n)) : ScalarNonnegative (∑ n ∈ s, f n) := by
  filter_upwards [Lp.coeFn_finsetSum s f, ae_all_iff.mpr hf] with x hx hp
  have he : (∑ n ∈ s, f n) x = ∑ n ∈ s, f n x := by
    simpa only [Finset.sum_apply] using hx
  rw [he]
  constructor
  · change Complex.imLm (∑ n ∈ s, f n x) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun n _ => (hp n).1)
  · change 0 ≤ Complex.reLm (∑ n ∈ s, f n x)
    rw [map_sum]
    exact Finset.sum_nonneg (fun n _ => (hp n).2)

theorem scalarNonnegative_weighted_sum (F : ℕ → ScalarLInfinity μ)
    (hF : ∀ i, ScalarNonnegative (F i)) (s : Finset ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ScalarNonnegative ((c : ℂ) • ∑ i ∈ s, F i) :=
  scalarNonnegative_real_smul (μ := μ) (f := ∑ i ∈ s, F i) (c := c)
    (scalarNonnegative_sum s F hF) hc

variable [IsProbabilityMeasure μ]

theorem scalarNonnegative_of_weak_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    (f : ι → ScalarLInfinity μ) (b : ScalarLInfinity μ)
    (hf : ∀ i, ScalarNonnegative (f i))
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 b)))) : ScalarNonnegative b := by
  have hp (i : ι) : ∀ᵐ x ∂μ, scalarInfinityToL2 (f i) x ∈ scalarPositiveCone := by
    filter_upwards [scalarInfinityToL2_ae (f i), hf i] with x hx hf
    rwa [hx]
  have hl := L2_ae_mem_of_inner_tendsto scalarPositiveCone_isClosed scalarPositiveCone_convex
    (fun i => scalarInfinityToL2 (f i)) (scalarInfinityToL2 b) hp ht
  filter_upwards [scalarInfinityToL2_ae b, hl] with x hx hl
  rwa [← hx]

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

def randomWalkBoundaryAction :
    NonsingularAction G (RandomWalkBoundary G) (randomWalkBoundaryMeasure G) :=
  shiftBoundaryAction (randomWalkPathLaw G) (randomWalkAdvance G)
    (randomWalkPathAction G) (randomWalkAdvance_action G)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarSectionSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.scalarBoundaryStar_apply _root_.OAI.KadisonKastler.scalarInfinityMulL_apply _root_.OAI.KadisonKastler.scalarInfinityToL2L_apply _root_.OAI.KadisonKastler.scalarL2MulL_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def scalarSectionSelect (F : G →ᵇ ScalarLInfinity μ) : ScalarLInfinity μ :=
  (memLp_top_of_bound (measurable_scalarSectionSelect r hr F).stronglyMeasurable.aestronglyMeasurable
    ‖F‖ (scalarSectionSelect_ae_bound r F)).toLp (fun x => F (r x) x)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_ae (F : G →ᵇ ScalarLInfinity μ) :
    scalarSectionSelect r hr F =ᵐ[μ] fun x => F (r x) x := MemLp.coeFn_toLp _

omit [DiscreteTopology G] in
theorem scalarSectionSelect_add (F K : G →ᵇ ScalarLInfinity μ) :
    scalarSectionSelect r hr (F + K) = scalarSectionSelect r hr F + scalarSectionSelect r hr K := by
  apply Lp.ext
  filter_upwards [scalarSectionSelect_ae r hr (F + K), scalarSectionSelect_ae r hr F,
    scalarSectionSelect_ae r hr K,
    ae_all_iff.mpr (fun g => Lp.coeFn_add (F g) (K g)),
    Lp.coeFn_add (scalarSectionSelect r hr F) (scalarSectionSelect r hr K)]
    with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, he, hb, hc]
  exact hd (r x)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_smul (c : ℂ) (F : G →ᵇ ScalarLInfinity μ) :
    scalarSectionSelect r hr (c • F) = c • scalarSectionSelect r hr F := by
  apply Lp.ext
  filter_upwards [scalarSectionSelect_ae r hr (c • F), scalarSectionSelect_ae r hr F,
    ae_all_iff.mpr (fun g => Lp.coeFn_smul c (F g)),
    Lp.coeFn_smul c (scalarSectionSelect r hr F)] with x ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hd, hb]
  exact hc (r x)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_const (f : ScalarLInfinity μ) :
    scalarSectionSelect r hr (BoundedContinuousFunction.const G f) = f :=
  Lp.ext (scalarSectionSelect_ae r hr _)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_positive (F : G →ᵇ ScalarLInfinity μ)
    (hF : ∀ g, ∀ᵐ x ∂μ, (F g x).im = 0 ∧ 0 ≤ (F g x).re) :
    ∀ᵐ x ∂μ, (scalarSectionSelect r hr F x).im = 0 ∧
      0 ≤ (scalarSectionSelect r hr F x).re := by
  filter_upwards [scalarSectionSelect_ae r hr F, ae_all_iff.mpr hF] with x hx hfx
  rw [hx]
  exact hfx (r x)

variable [IsProbabilityMeasure μ]

omit [DiscreteTopology G] in
theorem norm_scalarSectionSelect_le (F : G →ᵇ ScalarLInfinity μ) :
    ‖scalarSectionSelect r hr F‖ ≤ ‖F‖ := by
  have hb : ∀ᵐ x ∂μ, ‖scalarSectionSelect r hr F x‖ ≤ ‖F‖ := by
    filter_upwards [scalarSectionSelect_ae r hr F, scalarSectionSelect_ae_bound r F]
      with x hx hf
    rwa [hx]
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg F) hb

def scalarSectionSelectL : (G →ᵇ ScalarLInfinity μ) →L[ℂ] ScalarLInfinity μ :=
  LinearMap.mkContinuous
    { toFun := scalarSectionSelect r hr
      map_add' := scalarSectionSelect_add r hr
      map_smul' := scalarSectionSelect_smul r hr }
    1 (fun F => by simpa using norm_scalarSectionSelect_le r hr F)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryRoot
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.scalarBoundaryStar_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Root selection with a passive boundary coordinate -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {S : X → X} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

def firstBoundaryRootL :
    (G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) →L[ℂ]
      ScalarLInfinity (μ.prod ν) :=
  (scalarSectionSelectL (fun z : X × Y => r z.1) (hr.comp measurable_fst)).comp
    ((firstBoundaryLiftL μ S).compLeftContinuousBounded G)

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_ae
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr F =ᵐ[μ.prod ν]
      fun z => F (r z.1) (firstBoundaryMap μ S z) := by
  have h := ae_all_iff.mpr (fun g : G => firstBoundaryLiftL_ae μ S (F g))
  filter_upwards [scalarSectionSelect_ae (fun z : X × Y => r z.1)
    (hr.comp measurable_fst) ((firstBoundaryLiftL μ S).compLeftContinuousBounded G F), h]
    with z hz hg
  exact hz.trans (hg (r z.1))

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_norm_le
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    ‖firstBoundaryRootL r hr F‖ ≤ ‖F‖ := by
  have h : ∀ᵐ z ∂μ.prod ν, ‖firstBoundaryRootL r hr F z‖ ≤ ‖F‖ := by
    have hb := ae_all_iff.mpr (fun g : G =>
      (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae (scalarInfinity_ae_norm_le (F g)))
    filter_upwards [firstBoundaryRootL_ae r hr F, hb] with z hz hg
    rw [hz]
    exact (hg (r z.1)).trans (F.norm_coe_le_norm _)
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg F) h

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_const
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr (BoundedContinuousFunction.const G f) = firstBoundaryLiftL μ S f := by
  exact Lp.ext ((firstBoundaryRootL_ae r hr _).trans (firstBoundaryLiftL_ae μ S f).symm)

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_positive
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν))
    (hF : ∀ g, ScalarNonnegative (F g)) : ScalarNonnegative (firstBoundaryRootL r hr F) := by
  have hp := ae_all_iff.mpr (fun g : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae (hF g))
  filter_upwards [firstBoundaryRootL_ae r hr F, hp] with z hz hp
  rw [hz]
  exact hp (r z.1)

omit [Group G] in
theorem firstBoundaryRootL_module
    (b : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν))
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr (scalarBoundaryModule b F) =
      scalarInfinityMul (firstBoundaryLiftL μ S b) (firstBoundaryRootL r hr F) := by
  have hm := ae_all_iff.mpr (fun g : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae (scalarInfinityMul_ae b (F g)))
  apply Lp.ext
  filter_upwards [firstBoundaryRootL_ae r hr (scalarBoundaryModule b F),
    firstBoundaryRootL_ae r hr F, firstBoundaryLiftL_ae μ S b,
    scalarInfinityMul_ae (firstBoundaryLiftL μ S b) (firstBoundaryRootL r hr F), hm]
    with z ha hb hc hd he
  rw [ha, hd, hc, hb]
  exact he (r z.1)

theorem firstBoundaryRootL_translate
    (α : NonsingularAction G (X × Y) (μ.prod ν))
    (β : NonsingularAction G (ShiftBoundarySpace μ S × Y) ((shiftBoundaryMeasure μ S).prod ν))
    (hq : ∀ g z, β.toPerm g (firstBoundaryMap μ S z) = firstBoundaryMap μ S (α.toPerm g z))
    (hroot : ∀ g z, r (α.toPerm g z).1 = g * r z.1)
    (g : G) (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr (scalarBoundaryTranslate β g F) =
      scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (firstBoundaryRootL r hr F) := by
  have hm := ae_all_iff.mpr (fun t : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae
      (scalarInfinityPullback_ae (β.toPerm g⁻¹) (β.quasi g⁻¹) (F (g⁻¹ * t))))
  apply Lp.ext
  filter_upwards [firstBoundaryRootL_ae r hr (scalarBoundaryTranslate β g F),
    scalarInfinityPullback_ae (α.toPerm g⁻¹) (α.quasi g⁻¹) (firstBoundaryRootL r hr F),
    (α.quasi g⁻¹).ae (firstBoundaryRootL_ae r hr F), hm] with z ha hb hc hd
  rw [ha, hb, hc, hroot]
  exact (hd (r z.1)).trans (congrArg (F (g⁻¹ * r z.1)) (hq g⁻¹ z))

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_natural
    (T : X × Y → X × Y) (U : ShiftBoundarySpace μ S × Y → ShiftBoundarySpace μ S × Y)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod ν) (μ.prod ν))
    (hU : Measure.QuasiMeasurePreserving U ((shiftBoundaryMeasure μ S).prod ν)
      ((shiftBoundaryMeasure μ S).prod ν))
    (hq : ∀ z, U (firstBoundaryMap μ S z) = firstBoundaryMap μ S (T z))
    (hrT : ∀ z, r (T z).1 = r z.1)
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr ((scalarInfinityPullbackL U hU).compLeftContinuousBounded G F) =
      scalarInfinityPullback T hT (firstBoundaryRootL r hr F) := by
  have hm := ae_all_iff.mpr (fun t : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae
      (scalarInfinityPullback_ae U hU (F t)))
  apply Lp.ext
  filter_upwards [firstBoundaryRootL_ae r hr
      ((scalarInfinityPullbackL U hU).compLeftContinuousBounded G F),
    scalarInfinityPullback_ae T hT (firstBoundaryRootL r hr F),
    hT.ae (firstBoundaryRootL_ae r hr F), hm] with z ha hb hc hd
  rw [ha, hb, hc, hrT]
  exact (hd (r z.1)).trans (congrArg (F (r z.1)) (hq z))

def firstBoundaryScalarMean
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS))
    (E : FirstBoundaryProjection (ν := ν) hS P)
    (α : NonsingularAction G (X × Y) (μ.prod ν))
    (β : NonsingularAction G (ShiftBoundarySpace μ S × Y) ((shiftBoundaryMeasure μ S).prod ν))
    (hq : ∀ g z, β.toPerm g (firstBoundaryMap μ S z) = firstBoundaryMap μ S (α.toPerm g z))
    (hroot : ∀ g z, r (α.toPerm g z).1 = g * r z.1)
    (hshift : ∀ g z, firstCoordinateShift S (α.toPerm g z) = α.toPerm g (firstCoordinateShift S z)) :
    ScalarBoundaryMean β where
  toCLM := E.toCLM.comp (firstBoundaryRootL r hr)
  map_one := by
    change E.toCLM (firstBoundaryRootL r hr (BoundedContinuousFunction.const G _)) = _
    rw [firstBoundaryRootL_const, E.lift_retract]
  norm_le F := (E.norm_le _).trans (firstBoundaryRootL_norm_le r hr F)
  positive F hF := E.positive _ (firstBoundaryRootL_positive r hr F hF)
  module_map b F := by
    change E.toCLM (firstBoundaryRootL r hr (scalarBoundaryModule b F)) = _
    rw [firstBoundaryRootL_module, E.module_map]
    rfl
  equivariant g F := by
    change E.toCLM (firstBoundaryRootL r hr (scalarBoundaryTranslate β g F)) = _
    rw [firstBoundaryRootL_translate r hr α β hq hroot,
      E.natural (α.toPerm g⁻¹) (β.toPerm g⁻¹) (α.quasi g⁻¹) (β.quasi g⁻¹)
        (hq g⁻¹) (hshift g⁻¹)]
    rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarFrequencySwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Frequency projections after the scalar variable swap -/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem l2ScalarSwap_frequency (μ : Measure X) (a : ℝ)
    (F : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ)) :
    l2ScalarSwap volume μ (regularFrequencyProjection a F) =
      (regularFrequencyProjection (H := ℂ) a).compLp (l2ScalarSwap volume μ F) := by
  apply l2ScalarSwap_intertwines_of_tensor (volume : Measure ℝ) μ
    (regularFrequencyProjection a) ((regularFrequencyProjection (H := ℂ) a).compLpL 2 μ)
  intro f v
  have ht : regularFrequencyProjection a (scalarLpTensor volume f v) =
      scalarLpTensor volume (regularFrequencyProjection a f) v :=
    (compLp_regularFrequencyProjection (ContinuousLinearMap.toSpanSingleton ℂ v) a f).symm
  calc
    _ = l2ScalarSwap volume μ (scalarLpTensor volume (regularFrequencyProjection a f) v) :=
      congrArg (l2ScalarSwap volume μ) ht
    _ = scalarLpTensor μ v (regularFrequencyProjection a f) := l2ScalarSwap_tensor volume μ _ _
    _ = _ := (compLp_scalarLpTensor μ (regularFrequencyProjection (H := ℂ) a) v f).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductScalingWords
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite product words as state-scaling partial isometries

All scale ratios here come from the actual two fixed site families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

def matrixSiteBlockScale (ν : TwoRatioSite → ℝ) :
    (l : List TwoRatioSite) → MatrixSiteBlockIndex l → MatrixSiteBlockIndex l → ℝ
  | [], _, _ => 1
  | i :: l, a, b => (twoSiteWeight (ν i) b.1 / twoSiteWeight (ν i) a.1) *
      matrixSiteBlockScale ν l a.2 b.2

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftBoundaryScalarMaps
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar maps between paths and the invariant boundary

The measurable-subspace isometry implements descent and inclusion on the
actual L-infinity classes. In particular the constructed invariant
projection gives a contraction from ambient functions to boundary functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X} {hS : Measure.QuasiMeasurePreserving S μ μ}

def scalarProjectionToBoundaryL (P : ScalarInvariantProjection S hS) :
    ScalarLInfinity μ →L[ℂ] ScalarLInfinity (shiftBoundaryMeasure μ S) :=
  (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).toLinearIsometry.toContinuousLinearMap.comp
    (P.toCLM.codRestrict (lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ)
      (fun f => scalarInfinity_fixed_mem_lpMeas hS (P.toCLM f) (P.invariant f)))

theorem scalarProjectionToBoundaryL_ae (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) :
    (fun x => scalarProjectionToBoundaryL P f (shiftBoundaryMap μ S x)) =ᵐ[μ] P.toCLM f :=
  lpMeasToLpTrim_ae_eq (shiftInvariantSigma_le μ S) _

theorem norm_scalarProjectionToBoundaryL (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) : ‖scalarProjectionToBoundaryL P f‖ = ‖P.toCLM f‖ :=
  lpMeasSubgroupToLpTrim_norm_map (shiftInvariantSigma_le μ S) _

theorem norm_scalarProjectionToBoundaryL_le (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) : ‖scalarProjectionToBoundaryL P f‖ ≤ ‖f‖ := by
  rw [norm_scalarProjectionToBoundaryL]
  exact P.norm_le f

def scalarBoundaryLiftL :
    ScalarLInfinity (shiftBoundaryMeasure μ S) →L[ℂ] ScalarLInfinity μ :=
  (lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ).subtypeL.comp
    (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm.toLinearIsometry.toContinuousLinearMap

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_ae (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryLiftL f =ᵐ[μ] fun x => f (shiftBoundaryMap μ S x) :=
  lpTrimToLpMeas_ae_eq (F := ℂ) (𝕜 := ℂ) (p := ⊤) (μ := μ)
    (shiftInvariantSigma_le μ S) f

omit [IsProbabilityMeasure μ] in
theorem norm_scalarBoundaryLiftL (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    ‖scalarBoundaryLiftL f‖ = ‖f‖ :=
  (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm.norm_map f

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_injective :
    Function.Injective (scalarBoundaryLiftL (μ := μ) (S := S)) := by
  intro f g he
  apply (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm.injective
  exact Subtype.ext he

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_fixed (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarInfinityPullback S hS (scalarBoundaryLiftL f) = scalarBoundaryLiftL f := by
  apply scalarInfinity_fixed_of_aestronglyMeasurable
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    ((lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm f).property

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_positive (f : ScalarLInfinity (shiftBoundaryMeasure μ S))
    (hf : ScalarNonnegative f) : ScalarNonnegative (scalarBoundaryLiftL f) := by
  have hp := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae hf
  filter_upwards [scalarBoundaryLiftL_ae f, hp] with x hx hp
  rwa [hx]

theorem scalarProjectionToBoundaryL_lift (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarProjectionToBoundaryL P (scalarBoundaryLiftL f) = f := by
  let e := lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)
  have hfix := P.fixed (scalarBoundaryLiftL f) (scalarBoundaryLiftL_fixed f)
  have hmem := scalarInfinity_fixed_mem_lpMeas hS (P.toCLM (scalarBoundaryLiftL f))
    (P.invariant (scalarBoundaryLiftL f))
  change e ⟨P.toCLM (scalarBoundaryLiftL f), hmem⟩ = f
  have he : (⟨P.toCLM (scalarBoundaryLiftL f), hmem⟩ :
      lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ) = e.symm f :=
    Subtype.ext hfix
  rw [he]
  exact e.apply_symm_apply f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarBoundaryRoot
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Evaluating a boundary family at the random-walk root -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X}
  [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

def scalarBoundaryRootL :
    (G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) →L[ℂ] ScalarLInfinity μ :=
  (scalarSectionSelectL r hr).comp
    ((scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G)

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_apply (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr F = scalarSectionSelect r hr
      ((scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G F) := rfl

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_ae (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr F =ᵐ[μ] fun x => F (r x) (shiftBoundaryMap μ S x) := by
  rw [scalarBoundaryRootL_apply]
  filter_upwards [scalarSectionSelect_ae r hr
    ((scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G F),
    ae_all_iff.mpr (fun g => scalarBoundaryLiftL_ae (F g))] with x hx hg
  exact hx.trans (hg (r x))

omit [DiscreteTopology G] in
theorem norm_scalarBoundaryRootL_le (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    ‖scalarBoundaryRootL r hr F‖ ≤ ‖F‖ := by
  rw [scalarBoundaryRootL_apply]
  apply (norm_scalarSectionSelect_le r hr _).trans
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro g
  rw [ContinuousLinearMap.compLeftContinuousBounded_apply, norm_scalarBoundaryLiftL]
  exact F.norm_coe_le_norm g

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_const (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr (BoundedContinuousFunction.const G f) = scalarBoundaryLiftL f := by
  rw [scalarBoundaryRootL_apply]
  have he : (scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G
      (BoundedContinuousFunction.const G f) =
      BoundedContinuousFunction.const G (scalarBoundaryLiftL f) := by
    ext g
    rfl
  rw [he, scalarSectionSelect_const]

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_positive (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S))
    (hF : ∀ g, ScalarNonnegative (F g)) : ScalarNonnegative (scalarBoundaryRootL r hr F) := by
  rw [scalarBoundaryRootL_apply]
  exact scalarSectionSelect_positive r hr _ (fun g => scalarBoundaryLiftL_positive (F g) (hF g))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftBoundaryScalarAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra and action compatibility of the invariant scalar inclusion -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X} {hS : Measure.QuasiMeasurePreserving S μ μ}

theorem scalarBoundaryLiftL_projection (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) : scalarBoundaryLiftL (scalarProjectionToBoundaryL P f) = P.toCLM f := by
  apply Lp.ext
  exact (scalarBoundaryLiftL_ae _).trans (scalarProjectionToBoundaryL_ae P f)

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_mul (f g : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryLiftL (scalarInfinityMul f g) =
      scalarInfinityMul (scalarBoundaryLiftL f) (scalarBoundaryLiftL g) := by
  apply Lp.ext
  have hp := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae f g)
  filter_upwards [scalarBoundaryLiftL_ae (scalarInfinityMul f g), hp,
    scalarBoundaryLiftL_ae f, scalarBoundaryLiftL_ae g,
    scalarInfinityMul_ae (scalarBoundaryLiftL f) (scalarBoundaryLiftL g)]
    with x ha hb hc hd he
  rw [ha, hb, he, hc, hd]

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_nonnegative_iff (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    ScalarNonnegative (scalarBoundaryLiftL f) ↔ ScalarNonnegative f := by
  refine ⟨?_, scalarBoundaryLiftL_positive f⟩
  intro hf
  have hm : MeasurableSet {x | f x ∈ scalarPositiveCone} :=
    scalarPositiveCone_isClosed.measurableSet.preimage (Lp.stronglyMeasurable f).measurable
  have hpre : ∀ᵐ x ∂μ, f (shiftBoundaryMap μ S x) ∈ scalarPositiveCone := by
    filter_upwards [scalarBoundaryLiftL_ae f, hf] with x hx hp
    rwa [← hx]
  have hmap := (ae_map_iff (shiftBoundaryMap_measurePreserving μ S).measurable.aemeasurable hm).mpr hpre
  change ∀ᵐ x ∂shiftBoundaryMeasure μ S, f x ∈ scalarPositiveCone
  simpa only [(shiftBoundaryMap_measurePreserving μ S).map_eq] using hmap

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_action {G : Type*} [Group G]
    (α : NonsingularAction G X μ)
    (hcomm : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x))
    (g : G) (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryLiftL (scalarInfinityPullback
      ((shiftBoundaryAction μ S α hcomm).toPerm g)
      ((shiftBoundaryAction μ S α hcomm).quasi g) f) =
      scalarInfinityPullback (α.toPerm g) (α.quasi g) (scalarBoundaryLiftL f) := by
  apply Lp.ext
  let β := shiftBoundaryAction μ S α hcomm
  have hp := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae (β.toPerm g) (β.quasi g) f)
  filter_upwards [scalarBoundaryLiftL_ae (scalarInfinityPullback (β.toPerm g) (β.quasi g) f),
    hp, scalarInfinityPullback_ae (α.toPerm g) (α.quasi g) (scalarBoundaryLiftL f),
    (α.quasi g).ae (scalarBoundaryLiftL_ae f)] with x ha hb hc hd
  rw [ha, hb, hc, hd]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RootBoundaryMeanConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar boundary mean from rooted shift averages

Selection at the root is equivariant because the root translates by left
multiplication. The positive invariant projection then descends the
averages to the invariant boundary, with the exact module and action
identities required by `ScalarBoundaryMean`.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

omit [Group G] in
theorem scalarBoundaryRootL_module
    (b : ScalarLInfinity (shiftBoundaryMeasure μ S))
    (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr (scalarBoundaryModule b F) =
      scalarInfinityMul (scalarBoundaryLiftL b) (scalarBoundaryRootL r hr F) := by
  have hm (g : G) := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae b (F g))
  apply Lp.ext
  filter_upwards [scalarBoundaryRootL_ae r hr (scalarBoundaryModule b F),
    scalarBoundaryRootL_ae r hr F, scalarBoundaryLiftL_ae b,
    scalarInfinityMul_ae (scalarBoundaryLiftL b) (scalarBoundaryRootL r hr F),
    ae_all_iff.mpr hm] with x ha hb hc hd he
  rw [ha, hd, hc, hb]
  exact he (r x)

theorem scalarBoundaryRootL_translate (α : NonsingularAction G X μ)
    (hcomm : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x))
    (hroot : ∀ g x, r (α.toPerm g x) = g * r x)
    (g : G) (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr (scalarBoundaryTranslate (shiftBoundaryAction μ S α hcomm) g F) =
      scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (scalarBoundaryRootL r hr F) := by
  let β := shiftBoundaryAction μ S α hcomm
  have hm (t : G) := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae (β.toPerm g⁻¹) (β.quasi g⁻¹) (F (g⁻¹ * t)))
  apply Lp.ext
  filter_upwards [scalarBoundaryRootL_ae r hr (scalarBoundaryTranslate β g F),
    scalarInfinityPullback_ae (α.toPerm g⁻¹) (α.quasi g⁻¹) (scalarBoundaryRootL r hr F),
    (α.quasi g⁻¹).ae (scalarBoundaryRootL_ae r hr F), ae_all_iff.mpr hm]
    with x ha hb hc hd
  rw [ha, hb, hc, hroot]
  exact hd (r x)

def rootedScalarBoundaryMean
    (hS : Measure.QuasiMeasurePreserving S μ μ) (P : ScalarInvariantProjection S hS)
    (α : NonsingularAction G X μ)
    (hcomm : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x))
    (hroot : ∀ g x, r (α.toPerm g x) = g * r x) :
    ScalarBoundaryMean (shiftBoundaryAction μ S α hcomm) where
  toCLM := (scalarProjectionToBoundaryL P).comp (scalarBoundaryRootL r hr)
  map_one := by
    change scalarProjectionToBoundaryL P
      (scalarBoundaryRootL r hr (BoundedContinuousFunction.const G
        (scalarInfinityConst (shiftBoundaryMeasure μ S) 1))) = _
    rw [scalarBoundaryRootL_const, scalarProjectionToBoundaryL_lift]
  norm_le F := (norm_scalarProjectionToBoundaryL_le P _).trans (norm_scalarBoundaryRootL_le r hr F)
  positive F hF := by
    apply (scalarBoundaryLiftL_nonnegative_iff _).mp
    change ScalarNonnegative (scalarBoundaryLiftL
      (scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr F)))
    rw [scalarBoundaryLiftL_projection]
    exact P.positive _ (scalarBoundaryRootL_positive r hr F hF)
  module_map b F := by
    change scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr (scalarBoundaryModule b F)) =
      scalarInfinityMul b (scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr F))
    apply scalarBoundaryLiftL_injective
    rw [scalarBoundaryLiftL_projection, scalarBoundaryRootL_module,
      P.module_map _ _ (scalarBoundaryLiftL_fixed b), scalarBoundaryLiftL_mul,
      scalarBoundaryLiftL_projection]
  equivariant g F := by
    change scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr
      (scalarBoundaryTranslate (shiftBoundaryAction μ S α hcomm) g F)) =
      scalarInfinityPullback ((shiftBoundaryAction μ S α hcomm).toPerm g⁻¹)
        ((shiftBoundaryAction μ S α hcomm).quasi g⁻¹)
        (scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr F))
    apply scalarBoundaryLiftL_injective
    rw [scalarBoundaryLiftL_projection, scalarBoundaryRootL_translate r hr α hcomm hroot,
      P.natural (α.toPerm g⁻¹) (α.quasi g⁻¹) (hcomm g⁻¹),
      scalarBoundaryLiftL_action, scalarBoundaryLiftL_projection]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPacketMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The probability measure and action average of a scalar packet -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def scalarPacketAverage (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1)
    (T : H →L[ℂ] H) : H →L[ℂ] H := by
  let : IsProbabilityMeasure (scalarPacketMeasure φ) := scalarPacketMeasure_probability φ hφ
  exact stateActionAverage U hU (scalarPacketMeasure φ) T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarProductSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Swapping the two probability coordinates on scalar classes -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {D : Type*} [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]

def scalarProductSwapL : ScalarLInfinity (μ.prod μ) →L[ℂ] ScalarLInfinity (μ.prod μ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ Prod.swap
    (Measure.measurePreserving_swap (μ := μ) (ν := μ))).toContinuousLinearMap

theorem scalarProductSwapL_ae (f : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL f =ᵐ[μ.prod μ] fun z => f z.swap :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_swap (μ := μ) (ν := μ))

theorem scalarProductSwapL_norm (f : ScalarLInfinity (μ.prod μ)) :
    ‖scalarProductSwapL f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (Measure.measurePreserving_swap (μ := μ) (ν := μ))

theorem scalarProductSwapL_involution (f : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL (scalarProductSwapL f) = f := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarProductSwapL_ae f)
  filter_upwards [scalarProductSwapL_ae (scalarProductSwapL f), hp] with z hz hp
  exact hz.trans hp

theorem scalarProductSwapL_const (z : ℂ) :
    scalarProductSwapL (scalarInfinityConst (μ.prod μ) z) = scalarInfinityConst (μ.prod μ) z := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarInfinityConst_ae (μ := μ.prod μ) z)
  filter_upwards [scalarProductSwapL_ae (scalarInfinityConst _ z), hp,
    scalarInfinityConst_ae (μ := μ.prod μ) z] with x hx hp hc
  exact hx.trans (hp.trans hc.symm)

theorem scalarProductSwapL_mul (f g : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL (scalarInfinityMul f g) =
      scalarInfinityMul (scalarProductSwapL f) (scalarProductSwapL g) := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae f g)
  filter_upwards [scalarProductSwapL_ae (scalarInfinityMul f g), hp,
    scalarProductSwapL_ae f, scalarProductSwapL_ae g,
    scalarInfinityMul_ae (scalarProductSwapL f) (scalarProductSwapL g)] with x ha hb hc hd he
  rw [ha, hb, he, hc, hd]

theorem scalarProductSwapL_positive (f : ScalarLInfinity (μ.prod μ))
    (hf : ScalarNonnegative f) : ScalarNonnegative (scalarProductSwapL f) := by
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hf
  filter_upwards [scalarProductSwapL_ae f, hp] with x hx hp
  rwa [hx]

theorem scalarProductSwapL_intertwine
    (T U : D × D → D × D)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod μ) (μ.prod μ))
    (hU : Measure.QuasiMeasurePreserving U (μ.prod μ) (μ.prod μ))
    (hcomm : ∀ z, T z.swap = (U z).swap) (f : ScalarLInfinity (μ.prod μ)) :
    scalarProductSwapL (scalarInfinityPullback T hT f) =
      scalarInfinityPullback U hU (scalarProductSwapL f) := by
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae T hT f)
  filter_upwards [scalarProductSwapL_ae (scalarInfinityPullback T hT f), hp,
    scalarInfinityPullback_ae U hU (scalarProductSwapL f), hU.ae (scalarProductSwapL_ae f)]
    with z ha hb hc hd
  rw [ha, hb, hc, hd, hcomm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrixAmplification
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix amplification of spatial matrix images

Finite matrices over a generated operator algebra generate the matrix
von Neumann algebra.  The proof uses the existing strong approximation
theorem entry by entry.  Flattening the two finite matrix indices then
preserves the complete unit-ball approximation constant.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.KadisonKastler.spatialAmplificationStarOrder
local instance spatialAmplificationTargetOrder :
    PartialOrder (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  CStarAlgebra.spectralOrder (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
attribute [local instance] OAI.KadisonKastler.spatialAmplificationOrder
local instance spatialAmplificationTargetStarOrder :
    StarOrderedRing (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  CStarAlgebra.spectralOrderedRing (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SwappedBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.toContinuous_apply _root_.OAI.KadisonKastler.UniformMeasurableOperators.coefficientFamily_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonKastler.scalarBoundaryStar_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting the scalar mean to the second coordinate -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]

def scalarSwapFamilyL : (G →ᵇ ScalarLInfinity (μ.prod μ)) →L[ℂ]
    (G →ᵇ ScalarLInfinity (μ.prod μ)) := scalarProductSwapL.compLeftContinuousBounded G

omit [Group G] [DiscreteTopology G] in
theorem scalarSwapFamilyL_norm_le (F : G →ᵇ ScalarLInfinity (μ.prod μ)) :
    ‖scalarSwapFamilyL F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro g
  change ‖scalarProductSwapL (F g)‖ ≤ ‖F‖
  rw [scalarProductSwapL_norm]
  exact F.norm_coe_le_norm g

omit [Group G] [DiscreteTopology G] in
theorem scalarSwapFamilyL_const (b : ScalarLInfinity (μ.prod μ)) :
    scalarSwapFamilyL (BoundedContinuousFunction.const G b) =
      BoundedContinuousFunction.const G (scalarProductSwapL b) := by ext; rfl

omit [Group G] in
theorem scalarSwapFamilyL_module (b : ScalarLInfinity (μ.prod μ))
    (F : G →ᵇ ScalarLInfinity (μ.prod μ)) :
    scalarSwapFamilyL (scalarBoundaryModule b F) =
      scalarBoundaryModule (scalarProductSwapL b) (scalarSwapFamilyL F) := by
  apply BoundedContinuousFunction.ext
  intro g
  exact scalarProductSwapL_mul b (F g)

theorem scalarSwapFamilyL_translate
    (α β : NonsingularAction G (D × D) (μ.prod μ))
    (hc : ∀ g z, β.toPerm g z.swap = (α.toPerm g z).swap)
    (g : G) (F : G →ᵇ ScalarLInfinity (μ.prod μ)) :
    scalarSwapFamilyL (scalarBoundaryTranslate β g F) =
      scalarBoundaryTranslate α g (scalarSwapFamilyL F) := by
  apply BoundedContinuousFunction.ext
  intro t
  exact scalarProductSwapL_intertwine (β.toPerm g⁻¹) (α.toPerm g⁻¹)
    (β.quasi g⁻¹) (α.quasi g⁻¹) (hc g⁻¹) (F (g⁻¹ * t))

def swappedScalarBoundaryMean
    {α : NonsingularAction G (D × D) (μ.prod μ)} (m : ScalarBoundaryMean α)
    (β : NonsingularAction G (D × D) (μ.prod μ))
    (hc : ∀ g z, β.toPerm g z.swap = (α.toPerm g z).swap) : ScalarBoundaryMean β where
  toCLM := scalarProductSwapL.comp (m.toCLM.comp scalarSwapFamilyL)
  map_one := by
    change scalarProductSwapL (m.toCLM (scalarSwapFamilyL (BoundedContinuousFunction.const G _))) = _
    rw [scalarSwapFamilyL_const, scalarProductSwapL_const, m.map_one, scalarProductSwapL_const]
  norm_le F := by
    change ‖scalarProductSwapL (m.toCLM (scalarSwapFamilyL F))‖ ≤ ‖F‖
    rw [scalarProductSwapL_norm]
    exact (m.norm_le _).trans (scalarSwapFamilyL_norm_le F)
  positive F hF := by
    apply scalarProductSwapL_positive
    apply m.positive
    intro g
    exact scalarProductSwapL_positive (F g) (hF g)
  module_map b F := by
    change scalarProductSwapL (m.toCLM (scalarSwapFamilyL (scalarBoundaryModule b F))) = _
    rw [scalarSwapFamilyL_module, m.module_map, scalarProductSwapL_mul, scalarProductSwapL_involution]
    rfl
  equivariant g F := by
    change scalarProductSwapL (m.toCLM (scalarSwapFamilyL (scalarBoundaryTranslate β g F))) = _
    rw [scalarSwapFamilyL_translate α β hc, m.equivariant]
    apply scalarProductSwapL_intertwine (α.toPerm g⁻¹) (β.toPerm g⁻¹)
      (α.quasi g⁻¹) (β.quasi g⁻¹)
    intro z
    have h := congrArg Prod.swap (hc g⁻¹ z.swap)
    simpa using h.symm

end

end KadisonKastler

end OAI
end


