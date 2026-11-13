-- Prove2me | Definitions.Def_Q260K006
-- name    : Q260K006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:35:27.506195+00:00
-- url     : https://prove2.me/theorems/d4ce2a62-3270-43d8-86df-f2c8817fbee9
-- title:
--   Definitions bundle Q260K006 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 257 declarations of OpenAI's Lean: 72 definitions, 1 instance and 184 theorems. The definitions and types are `OAI.KadisonKastler.characterDescentOperatorOrder`, `OAI.KadisonKastler.clippedGraphRow`, `OAI.KadisonKastler.clippingFunction`, `OAI.KadisonKastler.cochainColumn`, `OAI.KadisonKastler.cochainColumnEvaluation`, `OAI.KadisonKastler.cochainColumnOperatorOrder`, `OAI.KadisonKastler.cochainDifferential`, `OAI.KadisonKastler.coisometryBicentralizerRealInner`, `OAI.KadisonKastler.coisometryHomogeneityReal`, `OAI.KadisonKastler.commonPositionError`, `OAI.KadisonKastler.commutatorAlong`, `OAI.KadisonKastler.completeWeakOperatorOrder`, `OAI.KadisonKastler.completelyPositiveAmplification`, `OAI.KadisonKastler.compressionOperatorOrder`, `OAI.KadisonKastler.conjugateFunctional`, `OAI.KadisonKastler.conjugationPairUnitary`, `OAI.KadisonKastler.constructedFiniteFactorError`, `OAI.KadisonKastler.constructedFiniteOperatorOrder`, `OAI.KadisonKastler.constructedFiniteSpatialOperatorOrder`, `OAI.KadisonKastler.coreTraceFrequencyFunction`, `OAI.KadisonKastler.cstarMatrixComp`, `OAI.KadisonKastler.cutFactor`, `OAI.KadisonKastler.finiteLocalCoefficient`, `OAI.KadisonKastler.fixedPointAlgebra`, `OAI.KadisonKastler.graphComplementScalar`, `OAI.KadisonKastler.graphHighInverseScalar`, `OAI.KadisonKastler.graphLowFactorScalar`, `OAI.KadisonKastler.graphRowClipFactor`, `OAI.KadisonKastler.graphRowClipOrder`, `OAI.KadisonKastler.graphRowSquare`, `OAI.KadisonKastler.graphScaleScalar`, `OAI.KadisonKastler.hilbertSumIsometryMap`, `OAI.KadisonKastler.instNormedSpaceRealComplex_solutions`, `OAI.KadisonKastler.isometryRangeCoordinates`, `OAI.KadisonKastler.l2Extend`, `OAI.KadisonKastler.l2ExtensionFunction`, `OAI.KadisonKastler.l2Restrict`, `OAI.KadisonKastler.l2Restriction`, `OAI.KadisonKastler.l2ScalarSwap`, `OAI.KadisonKastler.l2TensorEmbedding` and 32 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CharacterAverageDescent`, `KadisonKastler_CharacterContinuity`, `KadisonKastler_CoisometryStateHomogeneity`, `KadisonKastler_CommonPositionSpatial`, `KadisonKastler_CompleteWeakLimits`, `KadisonKastler_CompletelyPositive`, `KadisonKastler_ConstructedFiniteAmplification`, `KadisonKastler_ConstructedFiniteFactorModulus`, `KadisonKastler_ConstructedFiniteFactorStability`, `KadisonKastler_ConstructedFiniteSpatial`, `KadisonKastler_ContinuousMapHolomorphic`, `KadisonKastler_CoreTraceFrequencyVector`, `KadisonKastler_DenseSupportSeparation`, `KadisonKastler_FiniteFactorModulus`, `KadisonKastler_FiniteRowAverages`, `KadisonKastler_FixedPointGap`, `KadisonKastler_FourierModulation`, `KadisonKastler_FourierSwapIdentity`, `KadisonKastler_GraphCutScalarBounds`, `KadisonKastler_GraphLowCutBound`, `KadisonKastler_GraphLowCutScalars`, `KadisonKastler_GraphRowClipping`, `KadisonKastler_GraphRowMoments`, `KadisonKastler_GraphScaleFunctionalCalculus`, `KadisonKastler_HermitianLinearExtension`, `KadisonKastler_HermitianSeparation`, `KadisonKastler_HilbertCompression`, `KadisonKastler_HilbertSpaceLift`, `KadisonKastler_HilbertSumIsometryMap`, `KadisonKastler_IsometryRangeCoordinates`, `KadisonKastler_L2FourierNaturality`, `KadisonKastler_L2KernelSwap`, `KadisonKastler_L2LinearFields`, `KadisonKastler_L2MeasurableExtension`, `KadisonKastler_L2MeasurableRestriction`, `KadisonKastler_L2StrataSum`, `KadisonKastler_L2SwapIntertwining`, `KadisonKastler_L2TensorCoordinates`, `KadisonKastler_MeasurableHilbertCoordinates`, `KadisonKastler_MeasurableProjectionFrame`, `KadisonKastler_ModularCoisometryBicentralizer`, `KadisonKastler_ModularCyclicCuts`, `KadisonKastler_ModularLogRegularization`, `KadisonKastler_ModularPhaseFunctionalCalculus`, `KadisonKastler_ModularRadonNikodym`, `KadisonKastler_ModularSpectralCuts`, `KadisonKastler_ModularSpectralPhase`, `KadisonKastler_ModularStateCoefficients`, `KadisonKastler_ModularStripBoundary`, `KadisonKastler_ModularStripBounds`, `KadisonKastler_ModularStripIntegral`, `KadisonKastler_ModularStripKernel`, `KadisonKastler_ModularStrongLimit`, `KadisonKastler_NormUltraproductDerivation`, `KadisonKastler_OperatorCochainColumn`, `KadisonKastler_PointedLocalMatrix`, `KadisonKastler_PointedPowerOperators`, `KadisonKastler_PolarConjugationComparison`, `KadisonKastler_RankStratumStandardBorel`, `KadisonKastler_RectangularFunctionalCalculus`, `KadisonKastler_RegularConvolutionCoefficients`, `KadisonKastler_RegularCoreBasis`, `KadisonKastler_RegularCoreIntersection`, `KadisonKastler_RegularIntervalAverageEstimate`, `KadisonKastler_RegularLocalizationAverage`, `KadisonKastler_RegularLocalizationReconstruction`, `KadisonKastler_RegularLocalizedPackets`, `KadisonKastler_RegularPacketAveraging`, `KadisonKastler_RegularPacketFubini`, `KadisonKastler_RegularPacketLocalization`, `KadisonKastler_RegularWeakApproximation`, `KadisonKastler_RegularWeightedIntegral`, `KadisonKastler_ResolventContinuousCalculus`, `KadisonKastler_ResolventCoordinateMultiplier`, `KadisonKastler_ResolventCutLimit`, `KadisonKastler_ResolventCutMeasurable`, `KadisonKastler_ResolventCutOrder`, `KadisonKastler_ResolventCutRegularization`, `KadisonKastler_ResolventCyclicCuts`, `KadisonKastler_ResolventSqrtCalculus`, `KadisonKastler_ResolventVectorCutMeasure`, `KadisonKastler_SelfAdjointVectorCompactness`, `KadisonKastler_SelfAdjointVectorSpace`, `KadisonKastler_SpectralClipStar`, `KadisonKastler_SpectralClipping`, `KadisonKastler_SpectralCommutant`, `KadisonKastler_StripContourBounds`, `KadisonKastler_StrongContractionLimits`, `KadisonKastler_TomitaResolventDenseRange`, `KadisonKastler_TomitaVectorFixed`, `KadisonKastler_WeakCPLimits`, `KadisonKastler_WeightedStripBoundary`, `KadisonKastler_WeightedStripContinuous`, `KadisonKastler_WeightedStripFactorization`, `KadisonKastler_WeightedStripKernel`, `KadisonKastler_WeightedStripOperator`, `KadisonSimilarity_Representation_SpectralBaseTopology`.
--
--   **Imports.** It imports the bundle `OAIQ075A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K013`, `Q260K014` and `Q260K015`; the proof of `OAI.KadisonKastler.exists_signed_cyclic_functional`.
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
import Mathlib.Algebra.QuadraticDiscriminant
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
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Analysis.Convex.Cone.Closure
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
import Mathlib.Analysis.Normed.Algebra.Exponential
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
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.MetricSpace.Contracting
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
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Complex.hasTemperateGrowth_exp_mul_I`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem hasTemperateGrowth_exp_mul_I : (fun x : ℝ => Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  have hit : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
      = fun x : ℝ => Complex.I ^ n * Complex.exp (Complex.I * (x:ℂ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
          (Complex.exp (Complex.I * (x:ℂ)) * Complex.I) x := by
        have := ((hasDerivAt_id x).ofReal_comp.const_mul Complex.I).cexp
        simpa using this
      have h2 := h1.const_mul (Complex.I ^ n)
      rw [h2.deriv]
      ring
  refine ⟨?_, fun n => ⟨0, 1, fun x => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  · have h : (fun x : ℝ => Complex.exp (x * Complex.I)) = fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)) := by
      funext x; rw [mul_comm]
    rw [h, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit]
    simp [norm_pow, Complex.norm_exp]
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyPositive
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Contractivity of unital completely positive maps

The proofs use Mathlib's completely positive maps and the spectral order
on C⋆-matrices. The Schwarz inequality is obtained from positivity of a
two-by-two Gram matrix.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Flattening blocks of C⋆-matrices is a star-algebra equivalence. -/
def cstarMatrixComp (I J : Type*) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    CStarMatrix I I (CStarMatrix J J A) ≃⋆ₐ[ℂ] CStarMatrix (I × J) (I × J) A :=
  { Matrix.compAlgEquiv I J A ℂ with
    map_smul' _ _ := rfl
    map_star' M := by
      ext i j
      rfl }

/-- A matrix amplification of a completely positive map is completely positive. -/
def completelyPositiveAmplification (φ : A →CP B) (n : Type*) [Fintype n] [DecidableEq n] :
    CStarMatrix n n A →CP CStarMatrix n n B where
  toLinearMap := CStarMatrix.mapₗ φ.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    let eA := cstarMatrixComp (A := A) (Fin k) n
    let eB := cstarMatrixComp (A := B) (Fin k) n
    have hflat := φ.map_cstarMatrix_nonneg (eA M) (map_nonneg eA hM)
    have hback := map_nonneg eB.symm hflat
    have heq : eB.symm ((eA M).map φ) = M.map (CStarMatrix.mapₗ φ.toLinearMap) := by
      ext i j v w
      rfl
    rw [heq] at hback
    exact hback

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Norm clipping with preserved support and quotient image

The cutoff multiplies an element on the right by a continuous function of
its absolute value. Both the clipped part and the discarded part have
star squares bounded by the original star square.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

def clippingFunction (β t : ℝ) : ℝ := β / max β t

theorem clippingFunction_continuous {β : ℝ} (hβ : 0 < β) :
    Continuous (clippingFunction β) :=
  continuous_const.div (continuous_const.max continuous_id)
    (fun t => ne_of_gt (hβ.trans_le (le_max_left β t)))

theorem mul_clippingFunction {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    t * clippingFunction β t = min t β := by
  by_cases ht : t ≤ β
  · simp [clippingFunction, max_eq_left ht, min_eq_left ht, ne_of_gt hβ]
  · have ht' : β ≤ t := (lt_of_not_ge ht).le
    have htpos : 0 < t := hβ.trans_le ht'
    rw [clippingFunction, max_eq_right ht', min_eq_right ht']
    field_simp

theorem clippingFunction_square_le_bound {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * clippingFunction β t) ^ 2 ≤ β ^ 2 := by
  rw [mul_clippingFunction hβ]
  have h0 : 0 ≤ min t β := le_min ht hβ.le
  have h1 := min_le_right t β
  nlinarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [CompleteSpace H] in
/-- Operator positivity is closed under convergence of every coefficient. -/
theorem isPositive_of_weak_limit (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hT : ∀ i, (T i).IsPositive)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    S.IsPositive := by
  constructor
  · intro x y
    change inner ℂ (S x) y = inner ℂ x (S y)
    have hleft := (ht x y).star
    have hright := ht y x
    have he (i : ι) : star (inner ℂ y (T i x)) = inner ℂ x (T i y) := by
      change (starRingEnd ℂ) (inner ℂ y (T i x)) = _
      rw [inner_conj_symm]
      exact (hT i).isSymmetric x y
    have hleft' := hleft.congr (fun i => he i)
    change Tendsto _ l (𝓝 ((starRingEnd ℂ) (inner ℂ y (S x)))) at hleft'
    simpa only [inner_conj_symm] using tendsto_nhds_unique hleft' hright
  · intro x
    change 0 ≤ (inner ℂ (S x) x).re
    have hr := (Complex.continuous_re.tendsto _).comp (ht x x)
    have h := ge_of_tendsto hr
      (Eventually.of_forall (fun i => (hT i).re_inner_nonneg_right x))
    rw [show (inner ℂ (S x) x).re = (inner ℂ x (S x)).re from
      inner_re_symm (𝕜 := ℂ) (S x) x]
    exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FixedPointGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Fixed points inside `M`, expressed as the commutant of `M'` together
with the given representation. -/
def fixedPointAlgebra (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    ((M.commutant : Set (H →L[ℂ] H)) ∪ Set.range (fun g => (U g : H →L[ℂ] H)))
  centralizer_centralizer' := by
    let S : Set (H →L[ℂ] H) := (M.commutant : Set (H →L[ℂ] H)) ∪
      Set.range (fun g => (U g : H →L[ℂ] H))
    change (S ∪ star S).centralizer.centralizer.centralizer =
      (S ∪ star S).centralizer
    exact Set.centralizer_centralizer_centralizer _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CharacterAverageDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

section Descent

universe u v w s

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {G : Type w} [Group G] {L : Type s} [Group L]
  [TopologicalSpace L] [DiscreteTopology L]
  {M N : VonNeumannAlgebra H}

local instance characterDescentOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance characterDescentOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end Descent

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralClipStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adjoint compatibility of the continuous spectral cutoff

A two-by-two block argument transports continuous functional calculus
through an intertwiner between selfadjoint elements. Applied twice to
`xx*` and `x*x`, it shows that the cutoff commutes with adjoints. This
provides the left-sided fourth-moment estimate from the right-sided one.
-/

namespace KadisonKastler

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance clipPiComplexCFC_r895f4a_1 : ContinuousFunctionalCalculus ℂ (Fin 2 → A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
local instance clipBlockComplexCFC :
    ContinuousFunctionalCalculus ℂ (CStarMatrix (Fin 2) (Fin 2) A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
local instance clipPiCFC_r895f4a_1 : ContinuousFunctionalCalculus ℝ (Fin 2 → A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
local instance clipBlockCFC :
    ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin 2) (Fin 2) A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphRowMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moments of a finite replicated graph row

The row consists of independently chosen left matrix translates of the
same clipped element. Its two fourth-moment sums reduce to the actual
matrix averages already shown to converge to the vector state.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The positive left square of an operator row. -/
def graphRowSquare {I : Type*} [Fintype I] (Y : I → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, Y i * star (Y i)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphRowClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A common spectral cutoff for a replicated graph row

The cutoff acts on the left square of the entire row. Its norm is bounded
independently of the number of columns, while its normalized graph error
is controlled by the two fourth-moment sums in `graphRowCost`.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {I : Type*} [Fintype I]

local instance graphRowClipOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance graphRowClipStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The common positive left multiplier used to clip the entire row. -/
def graphRowClipFactor (β : ℝ) (Y : I → H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (clippingFunction β) (CFC.sqrt (graphRowSquare Y))

/-- Spectral clipping of a rectangular row on its left square. -/
def clippedGraphRow (β : ℝ) (Y : I → H →L[ℂ] H) (i : I) : H →L[ℂ] H :=
  graphRowClipFactor β Y * Y i

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaVectorFixed
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The polar conjugation fixes the cyclic separating vector -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem positive_square_eigenvector (S : H →L[ℂ] H) (hS : S.IsPositive)
    (k : ℝ) (hk : 0 < k) (x : H) (hx : S (S x) = (k : ℂ) ^ 2 • x) :
    S x = (k : ℂ) • x := by
  let v := S x - (k : ℂ) • x
  have hSv : S v = (-k : ℂ) • v := by
    change S (S x - (k : ℂ) • x) = (-k : ℂ) • (S x - (k : ℂ) • x)
    rw [map_sub, map_smul, hx]
    module
  have hp0 := hS.re_inner_nonneg_left v
  rw [hSv] at hp0
  rw [← Complex.ofReal_neg, Complex.coe_smul, inner_smul_left_eq_smul] at hp0
  have hp : 0 ≤ -k * ‖v‖ ^ 2 := by
    change 0 ≤ (-k • inner ℂ v v).re at hp0
    rw [Complex.smul_re] at hp0
    change 0 ≤ -k * RCLike.re (inner ℂ v v) at hp0
    rwa [inner_self_eq_norm_sq] at hp0
  have hmul : k * ‖v‖ ^ 2 ≤ 0 := by linarith
  have hsq : ‖v‖ ^ 2 ≤ 0 := by
    by_contra hs
    exact (not_lt_of_ge hmul) (mul_pos hk (lt_of_not_ge hs))
  have hv : v = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg v]
  exact sub_eq_zero.mp hv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularLogRegularization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform weighted bounds for logarithmic regularization

Multiplication by `s(1-s)` removes both endpoint singularities of the
regularized modular logarithm. These estimates give strong convergence
of its exponential on the dense range of `R(1-R)`.
-/

namespace KadisonKastler

noncomputable section

/-- Scalar logarithmic generator at a positive regularization scale. -/
def regularizedLogScalar (ε s : ℝ) : ℝ :=
  Real.log (1 - s + ε) - Real.log (s + ε)

theorem weighted_log_difference_ordered (s ε δ : ℝ) (hs : 0 ≤ s)
    (hδ : 0 < δ) (hδε : δ ≤ ε) :
    s * (Real.log (s + ε) - Real.log (s + δ)) ≤ ε - δ := by
  have hd : 0 < s + δ := by positivity
  have he : 0 < s + ε := by linarith
  have hlog : 0 ≤ Real.log (s + ε) - Real.log (s + δ) :=
    sub_nonneg.mpr (Real.log_le_log hd (by linarith))
  have h := Real.log_le_sub_one_of_pos (div_pos he hd)
  rw [Real.log_div he.ne' hd.ne'] at h
  have hrat : (s + ε) / (s + δ) - 1 = (ε - δ) / (s + δ) := by
    field_simp
    ring
  rw [hrat] at h
  have hm := (le_div_iff₀ hd).mp h
  nlinarith [mul_nonneg hδ.le hlog]

theorem weighted_log_difference (s ε δ : ℝ) (hs : 0 ≤ s)
    (hε : 0 < ε) (hδ : 0 < δ) :
    s * |Real.log (s + ε) - Real.log (s + δ)| ≤ |ε - δ| := by
  rcases le_total δ ε with h | h
  · have hd : 0 < s + δ := by positivity
    have hl := Real.log_le_log hd (show s + δ ≤ s + ε by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonneg (sub_nonneg.mpr h)]
    exact weighted_log_difference_ordered s ε δ hs hδ h
  · have he : 0 < s + ε := by positivity
    have hl := Real.log_le_log he (show s + ε ≤ s + δ by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hl), abs_of_nonpos (sub_nonpos.mpr h), neg_sub, neg_sub]
    exact weighted_log_difference_ordered s δ ε hs hε h

theorem weighted_regularizedLog_difference (s ε δ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) :
    s * (1 - s) * |regularizedLogScalar ε s - regularizedLogScalar δ s| ≤ |ε - δ| := by
  have hc : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have ha := weighted_log_difference (1 - s) ε δ hc hε hδ
  have hb := weighted_log_difference s ε δ hs hε hδ
  have ht : |regularizedLogScalar ε s - regularizedLogScalar δ s| ≤
      |Real.log (1 - s + ε) - Real.log (1 - s + δ)| +
      |Real.log (s + ε) - Real.log (s + δ)| := by
    have heq : regularizedLogScalar ε s - regularizedLogScalar δ s =
        (Real.log (1 - s + ε) - Real.log (1 - s + δ)) -
        (Real.log (s + ε) - Real.log (s + δ)) := by
      unfold regularizedLogScalar
      ring
    rw [heq]
    exact abs_sub _ _
  calc
    _ ≤ s * (1 - s) *
        (|Real.log (1 - s + ε) - Real.log (1 - s + δ)| +
          |Real.log (s + ε) - Real.log (s + δ)|) :=
      mul_le_mul_of_nonneg_left ht (mul_nonneg hs hc)
    _ = s * ((1 - s) * |Real.log (1 - s + ε) - Real.log (1 - s + δ)|) +
        (1 - s) * (s * |Real.log (s + ε) - Real.log (s + δ)|) := by ring
    _ ≤ s * |ε - δ| + (1 - s) * |ε - δ| :=
      add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb hc)
    _ = |ε - δ| := by ring

theorem imaginary_exp_difference (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have heq : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
      Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have harg : Complex.I * (b : ℂ) + Complex.I * ((a - b : ℝ) : ℂ) =
        Complex.I * (a : ℂ) := by
      push_cast
      ring
    rw [harg]
  rw [heq, norm_mul]
  have hn : ‖Complex.exp (Complex.I * b)‖ = 1 := by simp [Complex.norm_exp]
  rw [hn, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

theorem weighted_modularPhase_difference (t s ε δ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) :
    s * (1 - s) * ‖Complex.exp (Complex.I * ((t * regularizedLogScalar ε s : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t * regularizedLogScalar δ s : ℝ) : ℂ))‖ ≤ |t| * |ε - δ| := by
  have hphase := imaginary_exp_difference (t * regularizedLogScalar ε s)
    (t * regularizedLogScalar δ s)
  conv at hphase => rhs; rw [← mul_sub, abs_mul]
  calc
    _ ≤ s * (1 - s) * (|t| * |regularizedLogScalar ε s - regularizedLogScalar δ s|) :=
      mul_le_mul_of_nonneg_left hphase (mul_nonneg hs (sub_nonneg.mpr hs1))
    _ = |t| * (s * (1 - s) * |regularizedLogScalar ε s - regularizedLogScalar δ s|) := by ring
    _ ≤ |t| * |ε - δ| := mul_le_mul_of_nonneg_left
      (weighted_regularizedLog_difference s ε δ hs hs1 hε hδ) (abs_nonneg t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaResolventDenseRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The dense range used for logarithmic approximation

The product `R(1-R)` of the graph resolvent and its complement has dense range.
This is the precise dense set on which the weighted scalar estimates apply.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem selfAdjoint_denseRange (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hinj : Function.Injective A) : DenseRange A := by
  change Dense (A.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, A.orthogonal_range]
  have hs : A.adjoint = A := hA.star_eq
  rw [hs]
  exact LinearMap.ker_eq_bot.mpr hinj

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPhaseFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weighted norm convergence of the modular phases

Complex continuous functional calculus turns the scalar phase bound into
an operator bound on the dense range of `R(1-R)`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def modularPhaseScalar (t ε : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((t : ℂ) * (regularizedLogScalar ε z.re : ℂ)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongContractionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering a strong contraction limit from countable coordinates -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Uniform contraction bounds permit a varying input vector. -/
theorem tendsto_apply_contractions {ι : Type*} {l : Filter ι}
    (A : ι → H →L[ℂ] H) (T : H →L[ℂ] H) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hT : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x)))
    {x : ι → H} {y : H} (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun i => A i (x i)) l (𝓝 (T y)) := by
  have hz : Tendsto (fun i => A i (x i - y)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) (by simpa using (hx.sub_const y).norm)
    exact ((A i).le_opNorm _).trans
      (by simpa using mul_le_mul_of_nonneg_right (hA i) (norm_nonneg (x i - y)))
  convert hz.add (hT y) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

omit [CompleteSpace H] in
theorem tendsto_mul_contractions {ι : Type*} {l : Filter ι}
    (A B : ι → H →L[ℂ] H) (T S : H →L[ℂ] H) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hT : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x)))
    (hS : ∀ x, Tendsto (fun i => B i x) l (𝓝 (S x))) (x : H) :
    Tendsto (fun i => (A i * B i) x) l (𝓝 ((T * S) x)) :=
  tendsto_apply_contractions A T hA hT (hS x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStrongLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The strong limit of the regularized modular groups

The weighted estimates make the approximants Cauchy on a dense range.
Their contraction bounds extend convergence to every vector. Group laws
and inverse operators then pass to the strong limit.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def modularRegularizationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem modularRegularizationScale_pos (n : ℕ) : 0 < modularRegularizationScale n := by
  unfold modularRegularizationScale
  positivity

theorem modularRegularizationScale_tendsto :
    Tendsto modularRegularizationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSpectralPhase
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar logarithmic phase on the resolvent spectrum -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

def modularSpectralPhase (t s : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (1 - s) - Real.log s : ℝ) : ℂ)))

theorem modularSpectralPhase_norm (t s : ℝ) : ‖modularSpectralPhase t s‖ = 1 := by
  rw [modularSpectralPhase, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem modularPhaseScalar_norm (t ε : ℝ) (z : ℂ) : ‖modularPhaseScalar t ε z‖ = 1 := by
  rw [modularPhaseScalar, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem modularSpectralPhase_measurable (t : ℝ) : Measurable (modularSpectralPhase t) := by
  apply Complex.continuous_exp.measurable.comp
  apply measurable_const.mul
  apply measurable_const.mul
  exact Complex.continuous_ofReal.measurable.comp
    ((Real.measurable_log.comp (measurable_const.sub measurable_id)).sub Real.measurable_log)

theorem regularizedLogScalar_tendsto {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => regularizedLogScalar (modularRegularizationScale n) s) atTop
      (𝓝 (Real.log (1 - s) - Real.log s)) := by
  have hp : Tendsto (fun n => s + modularRegularizationScale n) atTop (𝓝 s) := by
    simpa only [add_zero] using tendsto_const_nhds.add modularRegularizationScale_tendsto
  have hm : Tendsto (fun n => 1 - s + modularRegularizationScale n) atTop (𝓝 (1 - s)) := by
    simpa only [add_zero] using tendsto_const_nhds.add modularRegularizationScale_tendsto
  exact ((Real.continuousAt_log (sub_pos.mpr hs1).ne').tendsto.comp hm).sub
    ((Real.continuousAt_log hs.ne').tendsto.comp hp)

theorem modularPhaseScalar_tendsto (t : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => modularPhaseScalar t (modularRegularizationScale n) (s : ℂ)) atTop
      (𝓝 (modularSpectralPhase t s)) := by
  have hl := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (regularizedLogScalar_tendsto hs hs1)
  have hp := (hl.const_mul (t : ℂ)).const_mul Complex.I
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hp
  simpa only [Function.comp_def, modularPhaseScalar, modularSpectralPhase, Complex.ofReal_re] using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierModulation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier transforms of scalar character multipliers

The identity is established on Schwartz functions by the integral
formula, then on the actual `L²` space by density.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

local instance instNormedSpaceRealComplex_solutions : NormedSpace ℝ ℂ := NormedSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CharacterContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous character fields in the scalar spectral variable -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventLogFrequency (s : ℝ) : ℝ := Real.log (1 - s) - Real.log s

theorem resolventLogFrequency_measurable : Measurable resolventLogFrequency :=
  (Real.measurable_log.comp (measurable_const.sub measurable_id)).sub Real.measurable_log

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointVectorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance selfAdjointCompactReal : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

theorem wotVector_realMap_weak_continuous (Ω : H) (P : H →L[ℝ] H) :
    Continuous (fun T : H →WOT[ℂ] H => toWeakSpace ℝ H (P (T Ω))) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  let g := f.comp P
  let η := (InnerProductSpace.toDual ℝ H).symm g
  have hg (v : H) : g v = inner ℝ η v :=
    (InnerProductSpace.toDual_symm_apply (x := v) (y := g)).symm
  change Continuous (fun T : H →WOT[ℂ] H => g (T Ω))
  simp_rw [hg, real_inner_eq_re_inner]
  exact Complex.continuous_re.comp
    (ContinuousLinearMapWOT.continuous_inner_apply continuous_id Ω η)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded functional calculus formula for every graph scale -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def graphScaleScalar (c s : ℝ) : ℝ := s + c ^ 2 * (1 - s)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphCutScalarBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar functions for the separated graph cuts -/

namespace KadisonKastler

noncomputable section

/-- The inverse of the complementary graph resolvent, clipped at the cut. -/
def graphHighInverseScalar (c r s : ℝ) : ℝ :=
  graphScaleScalar c (min s r) / (c ^ 2 * (1 - min s r))

theorem graphHighInverseScalar_bound {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) :
    graphHighInverseScalar c r s ≤ graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
  have hm : 0 ≤ min s r := le_min hs hr
  have hm1 : min s r < 1 := (min_le_right s r).trans_lt hr1
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hd : 0 < c ^ 2 * (1 - r) := mul_pos hc2 (sub_pos.mpr hr1)
  have hdm : 0 < c ^ 2 * (1 - min s r) := mul_pos hc2 (sub_pos.mpr hm1)
  apply (div_le_div_iff₀ hdm hd).mpr
  unfold graphScaleScalar
  nlinarith [mul_nonneg hc2.le (sub_nonneg.mpr (min_le_right s r))]

theorem graphHighInverseScalar_continuousOn {c r : ℝ} (hc : c ≠ 0)
    (hr1 : r < 1) : ContinuousOn (graphHighInverseScalar c r) (Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div (by unfold graphScaleScalar; fun_prop) (by fun_prop)
  intro s _
  exact mul_ne_zero (pow_ne_zero _ hc) (ne_of_gt (sub_pos.mpr ((min_le_right s r).trans_lt hr1)))

theorem graphScale_exp_square (a : ℝ) : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSpectralCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete upper cuts for the logarithmic modular spectrum

An upper logarithmic cut is the support of the positive part of a scalar
minus the graph resolvent. These are actual orthogonal projections on the
original Hilbert space, with no assumed spectral measure.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def resolventCutGenerator (R : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  cfc (fun s : ℝ => max (r - s) 0) R

def resolventLowerCut (R : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  (resolventCutGenerator R r).range.topologicalClosure.starProjection

theorem resolventLowerCut_projection (R : H →L[ℂ] H) (r : ℝ) :
    IsStarProjection (resolventLowerCut R r) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem resolventLowerCut_mul_generator (R : H →L[ℂ] H) (r : ℝ) :
    resolventLowerCut R r * resolventCutGenerator R r = resolventCutGenerator R r := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem cut_range_invariant (R T : H →L[ℂ] H) (r : ℝ)
    (h : Commute (resolventCutGenerator R r) T) {x : H}
    (hx : x ∈ (resolventCutGenerator R r).range.topologicalClosure) :
    T x ∈ (resolventCutGenerator R r).range.topologicalClosure := by
  have hs : (resolventCutGenerator R r).range.topologicalClosure ≤
      ((resolventCutGenerator R r).range.topologicalClosure).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨y, rfl⟩
      apply Submodule.le_topologicalClosure
      exact ⟨T y, congrArg (fun A : H →L[ℂ] H => A y) h.eq⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact hs hx

theorem resolventLowerCut_commutes (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (r : ℝ) :
    Commute (resolventLowerCut R r) R := by
  have hc : Commute (resolventCutGenerator R r) R := (Commute.refl R).cfc_real _
  exact Generator.starProjection_commutes_of_invariant _ R
    (fun _ hx => cut_range_invariant R R r hc hx)
    (fun _ hx => cut_range_invariant R (star R) r (by rwa [hR.star_eq]) hx)

theorem resolventLowerCut_commutes_cfc (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (r : ℝ) (f : ℝ → ℝ) : Commute (resolventLowerCut R r) (cfc f R) :=
  ((resolventLowerCut_commutes R hR r).symm.cfc_real f).symm

def modularCutThreshold (a : ℝ) : ℝ := (1 + Real.exp a)⁻¹

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphLowCutScalars
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar clipping for the low logarithmic cut -/

namespace KadisonKastler

noncomputable section

def graphComplementScalar (c s : ℝ) : ℝ := 1 - s / graphScaleScalar c s

def graphLowFactorScalar (c r s : ℝ) : ℝ :=
  c ^ 2 / (graphScaleScalar c s * graphScaleScalar c r)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphLowCutBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complementary low-cut estimate

Clipping the decreasing resolvent complement at the cut changes it by a
multiple of the cut generator. This difference vanishes on the low cut.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem resolventCutGenerator_mul_complement (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (r : ℝ) :
    resolventCutGenerator R r * (1 - resolventLowerCut R r) = 0 := by
  have hc := resolventLowerCut_commutes_cfc R hR r (fun s : ℝ => max (r - s) 0)
  change Commute (resolventLowerCut R r) (resolventCutGenerator R r) at hc
  rw [mul_sub, mul_one, ← hc.eq, resolventLowerCut_mul_generator, sub_self]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2TensorCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar tensor coordinates for iterated L2 spaces

The scalar-vector tensor map preserves inner products and has dense range.
Swapping its two scalar factors therefore gives the L2 Fubini isometry
needed for the modular Fourier calculation.
-/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct InnerProductSpace ENNReal

noncomputable section

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarLpTensor (μ : Measure X) : Lp ℂ 2 μ →L[ℂ] H →L[ℂ] Lp H 2 μ :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip.compLpL₂ 2 μ).flip

omit [CompleteSpace H] in
theorem scalarLpTensor_apply_ae (μ : Measure X) (f : Lp ℂ 2 μ) (x : H) :
    scalarLpTensor μ f x =ᵐ[μ] fun s => f s • x :=
  (ContinuousLinearMap.toSpanSingleton ℂ x).coeFn_compLp f

omit [CompleteSpace H] in
theorem inner_scalarLpTensor (μ : Measure X) (f g : Lp ℂ 2 μ) (x y : H) :
    inner ℂ (scalarLpTensor μ f x) (scalarLpTensor μ g y) =
      inner ℂ f g * inner ℂ x y := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ s, inner ℂ (f s) (g s) * inner ℂ x y ∂μ := by
      apply integral_congr_ae
      filter_upwards [scalarLpTensor_apply_ae μ f x, scalarLpTensor_apply_ae μ g y]
        with s hf hg
      rw [hf, hg]
      simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply, mul_assoc]
    _ = _ := integral_mul_const _ _

def l2TensorLinearMap (μ : Measure X) : (Lp ℂ 2 μ ⊗[ℂ] H) →ₗ[ℂ] Lp H 2 μ :=
  TensorProduct.lift (scalarLpTensor (H := H) μ).toLinearMap₁₂

omit [CompleteSpace H] in
@[simp] theorem l2TensorLinearMap_tmul (μ : Measure X) (f : Lp ℂ 2 μ) (x : H) :
    l2TensorLinearMap μ (f ⊗ₜ[ℂ] x) = scalarLpTensor μ f x := rfl

omit [CompleteSpace H] in
theorem inner_l2TensorLinearMap (μ : Measure X) (z w : Lp ℂ 2 μ ⊗[ℂ] H) :
    inner ℂ (l2TensorLinearMap μ z) (l2TensorLinearMap μ w) = inner ℂ z w := by
  induction z using OAI.tensorInductionOn with
  | tmul f x =>
      induction w using OAI.tensorInductionOn with
      | tmul g y => exact inner_scalarLpTensor μ f g x y
      | add w₁ w₂ hw₁ hw₂ => simp only [map_add, inner_add_right, hw₁, hw₂]
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, inner_add_left, hz₁, hz₂]

def l2TensorEmbedding (μ : Measure X) : (Lp ℂ 2 μ ⊗[ℂ] H) →ₗᵢ[ℂ] Lp H 2 μ :=
  (l2TensorLinearMap μ).isometryOfInner (inner_l2TensorLinearMap μ)

omit [CompleteSpace H] in
theorem l2TensorEmbedding_dense (μ : Measure X) :
    DenseRange (l2TensorEmbedding (H := H) μ) := by
  let S := (l2TensorLinearMap (H := H) μ).range
  intro f
  change f ∈ S.topologicalClosure
  induction f using Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
  | @indicatorConst x s hs hfin =>
      apply Submodule.le_topologicalClosure
      refine ⟨(indicatorConstLp 2 hs hfin.ne (1 : ℂ)) ⊗ₜ[ℂ] x, ?_⟩
      change scalarLpTensor μ (indicatorConstLp 2 hs hfin.ne (1 : ℂ)) x =
        indicatorConstLp 2 hs hfin.ne x
      apply Lp.ext
      filter_upwards [scalarLpTensor_apply_ae μ (indicatorConstLp 2 hs hfin.ne (1 : ℂ)) x,
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := (1 : ℂ)),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := x)] with t ht h1 hx
      rw [ht, h1, hx]
      by_cases hts : t ∈ s <;> simp [hts]
  | @add f g hf hg hdis hF hG => exact S.topologicalClosure.add_mem hF hG
  | isClosed => exact S.isClosed_topologicalClosure

def l2ScalarSwap (μ : Measure X) (ν : Measure Y) :
    Lp (Lp ℂ 2 ν) 2 μ ≃ₗᵢ[ℂ] Lp (Lp ℂ 2 μ) 2 ν :=
  (TensorProduct.comm ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)).extendOfIsometry
    (l2TensorEmbedding μ).toLinearMap (l2TensorEmbedding ν).toLinearMap
    (l2TensorEmbedding_dense μ) (l2TensorEmbedding_dense ν) (fun z => by
      change ‖l2TensorEmbedding ν (TensorProduct.comm ℂ _ _ z)‖ = ‖l2TensorEmbedding μ z‖
      rw [LinearIsometry.norm_map, LinearIsometry.norm_map, TensorProduct.norm_comm])

theorem l2ScalarSwap_tensor (μ : Measure X) (ν : Measure Y)
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    l2ScalarSwap μ ν (scalarLpTensor μ f g) = scalarLpTensor ν g f := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (f ⊗ₜ[ℂ] g)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2KernelSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Kernel formulas for the L2 Fubini isometry

Testing against scalar tensors identifies the swap of any integrable
kernel represented by its rows and columns. The application uses bounded
phase and indicator kernels multiplied by two L2 vectors.
-/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem inner_scalarLpTensor_kernel (μ : Measure X) (ν : Measure Y)
    (K : X → Y → ℂ) (F : Lp (Lp ℂ 2 ν) 2 μ)
    (hF : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, F x y = K x y)
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    inner ℂ (scalarLpTensor μ f g) F =
      ∫ x, ∫ y, star (f x) * star (g y) * K x y ∂ν ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarLpTensor_apply_ae μ f g, hF] with x hx hrow
  rw [hx, inner_smul_left, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hrow] with y hy
  rw [hy]
  simp only [RCLike.inner_apply]
  change star (f x) * (K x y * star (g y)) = _
  ring

theorem l2ScalarSwap_of_kernel (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : X → Y → ℂ) (F : Lp (Lp ℂ 2 ν) 2 μ) (G : Lp (Lp ℂ 2 μ) 2 ν)
    (hF : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, F x y = K x y)
    (hG : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, G y x = K x y)
    (hint : ∀ (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν),
      Integrable (fun p : X × Y => star (f p.1) * star (g p.2) * K p.1 p.2) (μ.prod ν)) :
    l2ScalarSwap μ ν F = G := by
  apply ext_inner_left ℂ
  intro z
  refine (l2TensorEmbedding_dense ν).induction_on
    (p := fun z => inner ℂ z (l2ScalarSwap μ ν F) = inner ℂ z G) z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro z
    induction z using OAI.tensorInductionOn with
    | tmul g f =>
        change inner ℂ (scalarLpTensor ν g f) (l2ScalarSwap μ ν F) =
          inner ℂ (scalarLpTensor ν g f) G
        have hs := (l2ScalarSwap μ ν).inner_map_map (scalarLpTensor μ f g) F
        rw [l2ScalarSwap_tensor] at hs
        rw [hs,
          inner_scalarLpTensor_kernel μ ν K F hF,
          inner_scalarLpTensor_kernel ν μ (fun y x => K x y) G hG,
          integral_integral_swap (hint f g)]
        apply integral_congr_ae
        filter_upwards [] with y
        apply integral_congr_ae
        filter_upwards [] with x
        ring
    | add z w hz hw =>
        simpa only [map_add, inner_add_left] using congrArg₂ (· + ·) hz hw

theorem integrable_bounded_L2_kernel (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (k : X × Y → ℂ) (hk : Measurable k) (hbound : ∀ p, ‖k p‖ ≤ 1)
    (f f' : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    Integrable (fun p : X × Y =>
      star (f' p.1) * star (g' p.2) * (k p * f p.1 * g p.2)) (μ.prod ν) := by
  have hx := (Lp.memLp f').norm.integrable_mul (Lp.memLp f).norm
  have hy := (Lp.memLp g').norm.integrable_mul (Lp.memLp g).norm
  apply (hx.mul_prod hy).mono'
    (((Lp.stronglyMeasurable f').star.measurable.comp measurable_fst).aestronglyMeasurable.mul
      ((Lp.stronglyMeasurable g').star.measurable.comp measurable_snd).aestronglyMeasurable |>.mul
      ((hk.mul ((Lp.stronglyMeasurable f).measurable.comp measurable_fst)).mul
        ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖star (f' p.1) * star (g' p.2) * (k p * f p.1 * g p.2)‖ ≤
    (‖f' p.1‖ * ‖f p.1‖) * (‖g' p.2‖ * ‖g p.2‖)
  simp only [norm_mul, norm_star]
  calc
    _ ≤ ‖f' p.1‖ * ‖g' p.2‖ * (1 * ‖f p.1‖ * ‖g p.2‖) := by gcongr; exact hbound p
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCutRegularization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous approximations to the cut projections -/

namespace KadisonKastler

noncomputable section

def resolventCutScalar (r ε s : ℝ) : ℝ := max (r - s) 0 / (max (r - s) 0 + ε)

theorem resolventCutScalar_continuous (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (resolventCutScalar r ε) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right _ _) hε)

theorem resolventCutScalar_bounds (r s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ resolventCutScalar r ε s ∧ resolventCutScalar r ε s ≤ 1 := by
  have hm : 0 ≤ max (r - s) 0 := le_max_right _ _
  have hd : 0 < max (r - s) 0 + ε := add_pos_of_nonneg_of_pos hm hε
  exact ⟨div_nonneg hm hd.le, (div_le_one hd).mpr (by linarith)⟩

theorem resolventCutScalar_error (r s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |(resolventCutScalar r ε s - 1) * max (r - s) 0| ≤ ε := by
  have hm : 0 ≤ max (r - s) 0 := le_max_right _ _
  have hd : 0 < max (r - s) 0 + ε := add_pos_of_nonneg_of_pos hm hε
  have he : (resolventCutScalar r ε s - 1) * max (r - s) 0 =
      -ε * resolventCutScalar r ε s := by
    unfold resolventCutScalar
    field_simp
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos hε,
    abs_of_nonneg (resolventCutScalar_bounds r s hε).1]
  exact mul_le_of_le_one_right hε.le (resolventCutScalar_bounds r s hε).2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventCutRegularization (R : H →L[ℂ] H) (r ε : ℝ) : H →L[ℂ] H :=
  cfc (resolventCutScalar r ε) R

theorem resolventCutRegularization_contracts (R : H →L[ℂ] H) (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ‖resolventCutRegularization R r ε‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro s _
  rw [Real.norm_eq_abs, abs_of_nonneg (resolventCutScalar_bounds r s hε).1]
  exact (resolventCutScalar_bounds r s hε).2

theorem resolventCutRegularization_factor (R : H →L[ℂ] H) (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    resolventCutRegularization R r ε =
      cfc (fun s : ℝ => (max (r - s) 0 + ε)⁻¹) R * resolventCutGenerator R r := by
  have hi : Continuous (fun s : ℝ => (max (r - s) 0 + ε)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro s
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right _ _) hε)
  rw [resolventCutRegularization, resolventCutGenerator,
    ← cfc_mul _ _ R hi.continuousOn (by fun_prop)]
  apply cfc_congr
  intro s _
  simp only [resolventCutScalar, div_eq_mul_inv, mul_comm]

theorem resolventCutRegularization_support (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    resolventCutRegularization R r ε * resolventLowerCut R r =
      resolventCutRegularization R r ε := by
  have hz : resolventCutRegularization R r ε * (1 - resolventLowerCut R r) = 0 := by
    rw [resolventCutRegularization_factor R r hε, mul_assoc,
      resolventCutGenerator_mul_complement R hR r, mul_zero]
  rw [mul_sub, mul_one, sub_eq_zero] at hz
  exact hz.symm

theorem resolventCutRegularization_error (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(resolventCutRegularization R r ε - 1) * resolventCutGenerator R r‖ ≤ ε := by
  rw [resolventCutRegularization, resolventCutGenerator,
    ← cfc_const_one ℝ R hR, ← cfc_sub _ _ R
      (resolventCutScalar_continuous r hε).continuousOn continuousOn_const,
    ← cfc_mul (fun s : ℝ => resolventCutScalar r ε s - 1)
      (fun s : ℝ => max (r - s) 0) R ((resolventCutScalar_continuous r hε).continuousOn.sub
      continuousOn_const) (by fun_prop)]
  apply norm_cfc_le hε.le
  intro s _
  exact resolventCutScalar_error r s hε

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCutLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong convergence of continuous cut regularizations -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventCutRegularization_tendsto_range (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (r : ℝ) (x : H) :
    Tendsto (fun n => resolventCutRegularization R r (modularRegularizationScale n)
      (resolventCutGenerator R r x)) atTop (𝓝 (resolventCutGenerator R r x)) := by
  have hz : Tendsto (fun n => resolventCutRegularization R r (modularRegularizationScale n)
      (resolventCutGenerator R r x) - resolventCutGenerator R r x) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => modularRegularizationScale n * ‖x‖) atTop (𝓝 0) by
        simpa only [zero_mul] using modularRegularizationScale_tendsto.mul_const ‖x‖)
    have h := ((resolventCutRegularization R r (modularRegularizationScale n) - 1) *
      resolventCutGenerator R r).le_opNorm x
    have hb := mul_le_mul_of_nonneg_right
      (resolventCutRegularization_error R hR r (modularRegularizationScale_pos n))
      (norm_nonneg x)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using h.trans hb
  convert hz.add_const (resolventCutGenerator R r x) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

theorem resolventCutRegularization_tendsto (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (r : ℝ) (x : H) :
    Tendsto (fun n => resolventCutRegularization R r (modularRegularizationScale n) x)
      atTop (𝓝 (resolventLowerCut R r x)) := by
  let P := resolventLowerCut R r
  let B := resolventCutGenerator R r
  let A := fun n => resolventCutRegularization R r (modularRegularizationScale n)
  have hA (n : ℕ) : ‖A n‖ ≤ 1 :=
    resolventCutRegularization_contracts R r (modularRegularizationScale_pos n)
  have hAP (n : ℕ) : A n (P x) = A n x :=
    congrArg (fun T : H →L[ℂ] H => T x)
      (resolventCutRegularization_support R hR r (modularRegularizationScale_pos n))
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hx : P x ∈ closure (Set.range B) :=
    B.range.topologicalClosure.starProjection_apply_mem x
  obtain ⟨z, ⟨y, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp hx (δ / 4) (by positivity)
  have ht := resolventCutRegularization_tendsto_range R hR r y
  filter_upwards [Metric.tendsto_nhds.mp ht (δ / 2) (by positivity)] with n hn
  have he : dist (A n x) (A n (B y)) ≤ dist (P x) (B y) := by
    rw [← hAP n, dist_eq_norm, ← map_sub]
    exact ((A n).le_opNorm _).trans
      (by simpa only [one_mul, dist_eq_norm] using
        mul_le_mul_of_nonneg_right (hA n) (norm_nonneg (P x - B y)))
  have hb := (dist_triangle (A n x) (A n (B y)) (P x)).trans
    (add_le_add le_rfl (dist_triangle (A n (B y)) (B y) (P x)))
  rw [dist_comm (B y) (P x)] at hb
  change dist (A n (B y)) (B y) < δ / 2 at hn
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventContinuousCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous spectral coordinates on the real resolvent spectrum -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventContinuousCalculus (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    C(spectrum ℝ R, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (cfcHom hR.isStarNormal).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ
      ⟨fun z => ⟨z.val.re, hR.spectrumRestricts.subset_preimage z.property⟩,
        (Complex.continuous_re.comp continuous_subtype_val).subtype_mk _⟩)

theorem resolventContinuousCalculus_eq_cfc (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (f : ℝ → ℂ) (hf : ContinuousOn f (spectrum ℝ R)) :
    resolventContinuousCalculus R hR ⟨fun s => f s.val, hf.domRestrict⟩ =
      cfc (fun z : ℂ => f z.re) R := by
  exact (cfc_apply _ R hR.isStarNormal
    (hf.comp Complex.continuous_re.continuousOn hR.spectrumRestricts.subset_preimage)).symm

theorem resolventContinuousCalculus_ofReal (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (f : C(spectrum ℝ R, ℝ)) :
    resolventContinuousCalculus R hR
      ⟨fun s => (f s : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ = cfcHom hR f := by
  have hs : SpectrumRestricts R (⟨Complex.re, Complex.continuous_re⟩ : C(ℂ, ℝ)) :=
    hR.spectrumRestricts
  rw [SpectrumRestricts.cfcHom_eq_restrict _ hR hR.isStarNormal hs]
  rfl

def resolventContinuousVector (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    C(spectrum ℝ R, ℂ) →ₗ[ℂ] H where
  toFun f := resolventContinuousCalculus R hR f x
  map_add' f g := by rw [map_add, add_apply]
  map_smul' c f := by rw [map_smul, smul_apply, RingHom.id_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCutOrder
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Monotonicity of resolvent cuts

A smaller positive-part generator factors through every strictly larger
one. Its closed range is therefore contained in the larger closed range.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cutFactor (r t s : ℝ) : ℝ := max (r - s) 0 / max (t - s) (t - r)

theorem cutFactor_continuous {r t : ℝ} (hrt : r < t) :
    Continuous (cutFactor r t) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  exact ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hrt) (le_max_right _ _))

theorem cutFactor_identity {r t : ℝ} (hrt : r < t) (s : ℝ) :
    max (t - s) 0 * cutFactor r t s = max (r - s) 0 := by
  unfold cutFactor
  by_cases hs : s ≤ r
  · have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_lt hs hrt)
    rw [max_eq_left hts.le, max_eq_left (by linarith : t - r ≤ t - s)]
    exact mul_div_cancel₀ _ (ne_of_gt hts)
  · rw [max_eq_right (by linarith : r - s ≤ 0), zero_div, mul_zero]

theorem resolventCutGenerator_factor (R : H →L[ℂ] H) (r t : ℝ) (hrt : r < t) :
    resolventCutGenerator R r = resolventCutGenerator R t * cfc (cutFactor r t) R := by
  rw [resolventCutGenerator, resolventCutGenerator,
    ← cfc_mul (fun s : ℝ => max (t - s) 0) (cutFactor r t) R
      (by fun_prop) (cutFactor_continuous hrt).continuousOn]
  apply cfc_congr
  intro s _
  exact (cutFactor_identity hrt s).symm

theorem resolventCutGenerator_range_mono (R : H →L[ℂ] H) {r t : ℝ} (hrt : r ≤ t) :
    (resolventCutGenerator R r).range.topologicalClosure ≤
      (resolventCutGenerator R t).range.topologicalClosure := by
  rcases hrt.eq_or_lt with rfl | hrt
  · exact le_rfl
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨x, rfl⟩
  refine ⟨cfc (cutFactor r t) R x, ?_⟩
  exact congrArg (fun T : H →L[ℂ] H => T x) (resolventCutGenerator_factor R r t hrt).symm

theorem resolventLowerCut_mul_of_le (R : H →L[ℂ] H) {r t : ℝ} (hrt : r ≤ t) :
    resolventLowerCut R r * resolventLowerCut R t = resolventLowerCut R r :=
  Submodule.starProjection_comp_starProjection_of_le (resolventCutGenerator_range_mono R hrt)

theorem resolventLowerCut_norm_mono (R : H →L[ℂ] H) (x : H) :
    Monotone (fun r : ℝ => ‖resolventLowerCut R r x‖) := by
  intro r t hrt
  calc
    _ = ‖resolventLowerCut R r (resolventLowerCut R t x)‖ := by
      exact congrArg (fun T : H →L[ℂ] H => ‖T x‖) (resolventLowerCut_mul_of_le R hrt).symm
    _ ≤ ‖resolventLowerCut R t x‖ := by
      simpa only [one_mul] using (resolventLowerCut R r).le_of_opNorm_le
        ((resolventLowerCut_projection R r).norm_le _) (resolventLowerCut R t x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCutMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem resolventLowerCut_diagonal (R : H →L[ℂ] H) (r : ℝ) (x : H) :
    inner ℂ (resolventLowerCut R r x) x = (‖resolventLowerCut R r x‖ : ℂ) ^ 2 := by
  let K := (resolventCutGenerator R r).range.topologicalClosure
  have hp : K.starProjection (K.starProjection x) = K.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
  have hi := K.inner_starProjection_left_eq_right (K.starProjection x) x
  rw [hp] at hi
  exact hi.trans (inner_self_eq_norm_sq_to_K _)

theorem resolventLowerCut_diagonal_measurable (R : H →L[ℂ] H) (x : H) :
    Measurable (fun r : ℝ => inner ℂ (resolventLowerCut R r x) x) := by
  have hm := (resolventLowerCut_norm_mono R x).measurable
  have hc : Measurable (fun r : ℝ => (‖resolventLowerCut R r x‖ : ℂ) ^ 2) :=
    (Complex.continuous_ofReal.measurable.comp hm).pow_const 2
  simpa only [resolventLowerCut_diagonal] using hc

theorem resolventLowerCut_coefficient_measurable (R : H →L[ℂ] H) (x y : H) :
    Measurable (fun r : ℝ => inner ℂ x (resolventLowerCut R r y)) := by
  have hm : Measurable (fun r : ℝ => inner ℂ (resolventLowerCut R r y) x) := by
    have ha := resolventLowerCut_diagonal_measurable R (x + y)
    have hb := resolventLowerCut_diagonal_measurable R (x - y)
    have hc := resolventLowerCut_diagonal_measurable R (x + Complex.I • y)
    have hd := resolventLowerCut_diagonal_measurable R (x - Complex.I • y)
    have hI : Measurable (fun _ : ℝ => Complex.I) := measurable_const
    have h := ((ha.sub hb).add (hI.mul hc)).sub (hI.mul hd)
    have h' := h.div_const (4 : ℂ)
    convert h' using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    exact inner_map_polarization (resolventLowerCut R r).toLinearMap x y
  simpa only [Function.comp_def, inner_conj_symm] using
    Complex.continuous_conj.measurable.comp hm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventVectorCutMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The vector measure of a resolvent cut -/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace
open scoped Topology

noncomputable section

theorem resolventCutScalar_tendsto (r s : ℝ) :
    Tendsto (fun n => resolventCutScalar r (modularRegularizationScale n) s) atTop
      (𝓝 (if s < r then 1 else 0)) := by
  by_cases hs : s < r
  · have hm : 0 < r - s := sub_pos.mpr hs
    have hn : Tendsto (fun _ : ℕ => r - s) atTop (𝓝 (r - s)) := tendsto_const_nhds
    have ht := hn.div (hn.add modularRegularizationScale_tendsto) (by simpa using hm.ne')
    change Tendsto (fun n => (r - s) / (r - s + modularRegularizationScale n)) atTop
      (𝓝 ((r - s) / (r - s + 0))) at ht
    simpa only [resolventCutScalar, max_eq_left hm.le, ite_eq_left hs, add_zero,
      div_self hm.ne'] using ht
  · simpa only [resolventCutScalar, max_eq_right (sub_nonpos.mpr (le_of_not_gt hs)),
      zero_div, ite_eq_right hs] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCyclicCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def resolventCutIndicator (R : H →L[ℂ] H) (r : ℝ) : spectrum ℝ R → ℂ :=
  {s : spectrum ℝ R | s.val < r}.indicator (fun _ => 1)

omit [CompleteSpace H] in
theorem resolventCutIndicator_measurable (R : H →L[ℂ] H) (r : ℝ) :
    Measurable (resolventCutIndicator R r) :=
  measurable_const.indicator (isOpen_lt continuous_subtype_val continuous_const).measurableSet

omit [CompleteSpace H] in
theorem resolventCutIndicator_bound (R : H →L[ℂ] H) (r : ℝ) (s : spectrum ℝ R) :
    ‖resolventCutIndicator R r s‖ ≤ 1 := by
  by_cases hs : s.val < r <;> simp [resolventCutIndicator, hs]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCyclicCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable modular cut fields in the cyclic coordinates -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem lt_modularCutThreshold_iff {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (a : ℝ) :
    s < modularCutThreshold a ↔ a < resolventLogFrequency s := by
  unfold modularCutThreshold resolventLogFrequency
  rw [lt_sub_iff_add_lt, Real.lt_log_iff_exp_lt (sub_pos.mpr hs1), Real.exp_add, Real.exp_log hs]
  have hp : 0 < 1 + Real.exp a := by positivity
  rw [show (1 + Real.exp a)⁻¹ = (1 + Real.exp a)⁻¹ * 1 by rw [mul_one], lt_inv_mul_iff₀ hp]
  constructor <;> intro h <;> nlinarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2FourierNaturality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier transport through the cyclic spectral coordinates -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform TensorProduct

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem postcomp_toLp_p0 (L : H →L[ℂ] K) (f : SchwartzMap ℝ H) :
    (SchwartzMap.postcompCLM L f).toLp 2 = L.compLp (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.postcompCLM L f).coeFn_toLp 2,
    f.coeFn_toLp 2, L.coeFn_compLp (f.toLp 2)] with t h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  rfl

theorem fourier_postcomp_p0 (L : H →L[ℂ] K) (f : SchwartzMap ℝ H) (t : ℝ) :
    (𝓕 (SchwartzMap.postcompCLM L f)) t = L ((𝓕 f) t) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  simp only [Real.fourier_eq, SchwartzMap.postcompCLM_apply]
  rw [← L.integral_comp_comm ((Real.fourierIntegral_convergent_iff t).mpr f.integrable)]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [Circle.smul_def, map_smul]

theorem fourier_compLp (L : H →L[ℂ] K) (f : Lp H 2 (volume : Measure ℝ)) :
    (𝓕 (L.compLp f) : Lp K 2 (volume : Measure ℝ)) = L.compLp (𝓕 f) := by
  let A : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp K 2 (volume : Measure ℝ) :=
    (Lp.fourierTransformₗᵢ ℝ K).toContinuousLinearEquiv.toContinuousLinearMap.comp (L.compLpL 2 volume)
  let B : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp K 2 (volume : Measure ℝ) :=
    (L.compLpL 2 volume).comp (Lp.fourierTransformₗᵢ ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  have he : A = B := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer A.continuous B.continuous
    funext g
    change (𝓕 (L.compLp (g.toLp 2)) : Lp K 2 (volume : Measure ℝ)) = L.compLp (𝓕 (g.toLp 2))
    rw [← postcomp_toLp_p0, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(𝓕 (SchwartzMap.postcompCLM L g)).coeFn_toLp 2,
      (𝓕 g).coeFn_toLp 2, L.coeFn_compLp ((𝓕 g).toLp 2)] with t h₁ h₂ h₃
    rw [h₁, h₃, h₂]
    exact fourier_postcomp_p0 L g t
  exact congrArg (fun T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp K 2 (volume : Measure ℝ) => T f) he

theorem fourier_scalarLpTensor (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    (𝓕 (scalarLpTensor volume f x) : Lp H 2 (volume : Measure ℝ)) =
      scalarLpTensor volume (𝓕 f) x :=
  fourier_compLp (ContinuousLinearMap.toSpanSingleton ℂ x) f

omit [CompleteSpace H] [CompleteSpace K] in
theorem compLp_scalarLpTensor {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : H →L[ℂ] K) (f : Lp ℂ 2 μ) (x : H) :
    L.compLp (scalarLpTensor μ f x) = scalarLpTensor μ f (L x) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (scalarLpTensor μ f x), scalarLpTensor_apply_ae μ f x,
    scalarLpTensor_apply_ae μ f (L x)] with s hL hx hy
  rw [hL, hx, hy, map_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreIntersection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The joint fixed algebra in the concrete regular representation

The reverse tensor membership is proved from the actual multiplier
representation. The joint fixed-point identification then uses only the
two separate published spectral and diagonal decomposition inputs.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strong continuity of a unitary field permits a continuously varying
vector argument, because every member is an isometry. -/
theorem continuous_unitary_field_apply {X : Type*} [TopologicalSpace X]
    (V : X → unitary (H →L[ℂ] H))
    (hV : ∀ ξ, Continuous (fun x => (V x : H →L[ℂ] H) ξ))
    (f : X → H) (hf : Continuous f) :
    Continuous (fun x => (V x : H →L[ℂ] H) (f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [(Metric.tendsto_nhds.mp (hf.tendsto x)) (ε / 2) hhalf,
    (Metric.tendsto_nhds.mp ((hV (f x)).tendsto x)) (ε / 2) hhalf]
    with y hy hxy
  have hi : dist ((V y : H →L[ℂ] H) (f y)) ((V y : H →L[ℂ] H) (f x)) =
      dist (f y) (f x) :=
    (Unitary.linearIsometryEquiv (V y)).isometry.dist_eq _ _
  calc
    dist ((V y : H →L[ℂ] H) (f y)) ((V x : H →L[ℂ] H) (f x)) ≤
        dist ((V y : H →L[ℂ] H) (f y)) ((V y : H →L[ℂ] H) (f x)) +
        dist ((V y : H →L[ℂ] H) (f x)) ((V x : H →L[ℂ] H) (f x)) :=
      dist_triangle _ _ _
    _ < ε := by rw [hi]; linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2SwapIntertwining
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending tensor intertwining identities by density -/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem l2ScalarSwap_intertwines_of_tensor (μ : Measure X) (ν : Measure Y)
    (A : Lp (Lp ℂ 2 ν) 2 μ →L[ℂ] Lp (Lp ℂ 2 ν) 2 μ)
    (B : Lp (Lp ℂ 2 μ) 2 ν →L[ℂ] Lp (Lp ℂ 2 μ) 2 ν)
    (h : ∀ f v, l2ScalarSwap μ ν (A (scalarLpTensor μ f v)) = B (scalarLpTensor ν v f))
    (F : Lp (Lp ℂ 2 ν) 2 μ) :
    l2ScalarSwap μ ν (A F) = B (l2ScalarSwap μ ν F) := by
  let S := l2ScalarSwap μ ν
  refine (l2TensorEmbedding_dense μ).induction_on
    (p := fun F => S (A F) = B (S F)) F ?_ ?_
  · exact isClosed_eq (S.continuous.comp A.continuous) (B.continuous.comp S.continuous)
  · intro z
    induction z using OAI.tensorInductionOn with
    | tmul f v =>
        change S (A (scalarLpTensor μ f v)) = B (S (scalarLpTensor μ f v))
        exact (h f v).trans (congrArg B (l2ScalarSwap_tensor μ ν f v).symm)
    | add z w hz hw =>
        change S (A (l2TensorEmbedding μ z)) = B (S (l2TensorEmbedding μ z)) at hz
        change S (A (l2TensorEmbedding μ w)) = B (S (l2TensorEmbedding μ w)) at hw
        simpa only [map_add] using congrArg₂ (· + ·) hz hw

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem intertwines_unitary_star (L : E →L[ℂ] F)
    (A : unitary (E →L[ℂ] E)) (B : unitary (F →L[ℂ] F))
    (h : ∀ x, L ((A : E →L[ℂ] E) x) = (B : F →L[ℂ] F) (L x)) (x : E) :
    L ((star A : E →L[ℂ] E) x) = (star B : F →L[ℂ] F) (L x) := by
  have hi : (A : E →L[ℂ] E) ((star A : E →L[ℂ] E) x) = x :=
    congrArg (fun T : E →L[ℂ] E => T x) (Unitary.mul_star_self_of_mem A.property)
  have he := h ((star A : E →L[ℂ] E) x)
  rw [hi] at he
  have hj : (star B : F →L[ℂ] F) ((B : F →L[ℂ] F) (L ((star A : E →L[ℂ] E) x))) =
      L ((star A : E →L[ℂ] E) x) :=
    congrArg (fun T : F →L[ℂ] F => T (L ((star A : E →L[ℂ] E) x)))
      (Unitary.star_mul_self_of_mem B.property)
  exact (congrArg (fun y => (star B : F →L[ℂ] F) y) he).trans hj |>.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierSwapIdentity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier conjugacy from identities after swapping scalar variables -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {X : Type*} [MeasurableSpace X]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem linearIsometryEquiv_conjugate_of_intertwines (e : E ≃ₗᵢ[ℂ] F)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (h : ∀ x, e (A x) = B (e x)) :
    A = e.symm.conjStarAlgEquiv B := by
  apply ContinuousLinearMap.ext
  intro x
  apply e.injective
  change e (A x) = e (e.symm (B (e x)))
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact h x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStateCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix coefficients of a vector-fixing unitary action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem star_unitary_fixes (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) : star (u : H →L[ℂ] H) Ω = Ω := by
  calc
    _ = star (u : H →L[ℂ] H) ((u : H →L[ℂ] H) Ω) := by rw [hfix]
    _ = Ω := congrArg (fun T : H →L[ℂ] H => T Ω) (Unitary.star_mul_self_of_mem u.property)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStripKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded analytic kernel for modular matrix coefficients

The factor `s` absorbs the possible growth of the logarithmic modular
phase on the closed KMS strip. No modular algebra invariance is used.
-/

namespace KadisonKastler

noncomputable section

def modularStripKernel (z : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) * Complex.exp ((-Complex.I * z) * (resolventLogFrequency s : ℂ))

theorem modularStripKernel_differentiable (s : ℝ) :
    Differentiable ℂ (fun z => modularStripKernel z s) := by
  unfold modularStripKernel
  fun_prop

theorem modularStripKernel_hasDerivAt (s : ℝ) (z : ℂ) :
    HasDerivAt (fun w => modularStripKernel w s)
      ((-Complex.I * (resolventLogFrequency s : ℂ)) * modularStripKernel z s) z := by
  have h : HasDerivAt (fun w : ℂ => (-Complex.I * w) * (resolventLogFrequency s : ℂ))
      (-Complex.I * (resolventLogFrequency s : ℂ)) z := by
    convert (hasDerivAt_const_mul (x := z) (-Complex.I * (resolventLogFrequency s : ℂ))) using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    ring
  convert h.cexp.const_mul (s : ℂ) using 1 <;> first | (with_reducible_and_instances rfl) | (unfold modularStripKernel <;> ring)

theorem modularStripKernel_norm {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ‖modularStripKernel z s‖ = Real.exp
      ((1 - z.im) * Real.log s + z.im * Real.log (1 - s)) := by
  have hre : ((-Complex.I * z) * (resolventLogFrequency s : ℂ)).re =
      z.im * resolventLogFrequency s := by
    simp [Complex.mul_re, Complex.mul_im]
  calc
    _ = s * Real.exp (z.im * resolventLogFrequency s) := by
      rw [modularStripKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, Complex.norm_exp, hre]
    _ = Real.exp (Real.log s + z.im * resolventLogFrequency s) := by
      rw [Real.exp_add, Real.exp_log hs]
    _ = _ := by
      congr 1
      unfold resolventLogFrequency
      ring

theorem modularStripKernel_norm_le_one {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 1) :
    ‖modularStripKernel z s‖ ≤ 1 := by
  rw [modularStripKernel_norm hs]
  have hlog : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1.le
  have hlog' : Real.log (1 - s) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hz1) hlog
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hz0 hlog'
  calc
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (add_nonpos h₁ h₂)
    _ = 1 := Real.exp_zero

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStripBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local derivative bounds in the open modular strip -/

namespace KadisonKastler

noncomputable section

theorem modularStripKernel_decay {s δ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hy0 : δ ≤ z.im) (hy1 : z.im ≤ 1 - δ) :
    ‖modularStripKernel z s‖ ≤ Real.exp (-δ * |resolventLogFrequency s|) := by
  rw [modularStripKernel_norm hs]
  apply Real.exp_le_exp.mpr
  have ha : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1.le
  have hb : Real.log (1 - s) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  rcases le_total 0 (resolventLogFrequency s) with hlam | hlam
  · rw [abs_of_nonneg hlam]
    have hp := mul_nonneg (sub_nonneg.mpr hy1) hlam
    unfold resolventLogFrequency at *
    nlinarith
  · rw [abs_of_nonpos hlam]
    have hp := mul_nonneg (sub_nonneg.mpr hy0) (neg_nonneg.mpr hlam)
    unfold resolventLogFrequency at *
    nlinarith

theorem modularStripKernel_deriv_bound {s δ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hδ : 0 < δ) {z : ℂ} (hy0 : δ ≤ z.im) (hy1 : z.im ≤ 1 - δ) :
    ‖(-Complex.I * (resolventLogFrequency s : ℂ)) * modularStripKernel z s‖ ≤ 1 / δ := by
  have he := modularStripKernel_decay hs hs1 hy0 hy1
  have hsmall : (δ * |resolventLogFrequency s|) *
      Real.exp (-(δ * |resolventLogFrequency s|)) ≤ 1 := by
    have ht : δ * |resolventLogFrequency s| ≤ Real.exp (δ * |resolventLogFrequency s|) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    calc
      _ ≤ Real.exp (δ * |resolventLogFrequency s|) *
          Real.exp (-(δ * |resolventLogFrequency s|)) :=
        mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply (le_div_iff₀ hδ).mpr
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |resolventLogFrequency s| * ‖modularStripKernel z s‖ * δ ≤
        |resolventLogFrequency s| * Real.exp (-δ * |resolventLogFrequency s|) * δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (abs_nonneg _)) hδ.le
    _ = (δ * |resolventLogFrequency s|) * Real.exp (-(δ * |resolventLogFrequency s|)) := by rw [neg_mul]; ring
    _ ≤ 1 := hsmall

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStripIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integrating the bounded modular strip kernel -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (r : X → ℝ)
  (hr : Measurable r) (f : X → ℂ) (hf : Integrable f μ)
  (hint : ∀ᵐ s ∂μ, 0 < r s ∧ r s < 1)

def modularStripIntegral (z : ℂ) : ℂ := ∫ s, f s * modularStripKernel z (r s) ∂μ

include hr in
theorem modularStripKernel_comp_measurable (z : ℂ) :
    Measurable (fun s => modularStripKernel z (r s)) := by
  unfold modularStripKernel
  exact (Complex.continuous_ofReal.measurable.comp hr).mul
    (Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp (resolventLogFrequency_measurable.comp hr))))

include hr hf in
theorem modularStripIntegrand_measurable (z : ℂ) :
    AEStronglyMeasurable (fun s => f s * modularStripKernel z (r s)) μ :=
  hf.aestronglyMeasurable.mul (modularStripKernel_comp_measurable r hr z).aestronglyMeasurable

include hint in
theorem modularStripIntegrand_bound {z : ℂ} (hz : 0 ≤ z.im ∧ z.im ≤ 1) :
    ∀ᵐ s ∂μ, ‖f s * modularStripKernel z (r s)‖ ≤ ‖f s‖ := by
  filter_upwards [hint] with s hs
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (modularStripKernel_norm_le_one hs.1 hs.2 hz.1 hz.2)
    (norm_nonneg _)).trans_eq (mul_one _)

include hr hf hint in
theorem modularStripIntegral_continuousOn :
    ContinuousOn (modularStripIntegral μ r f) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ 1} := by
  apply continuousOn_of_dominated
    (fun z _ => modularStripIntegrand_measurable μ r hr f hf z)
    (fun _ hz => modularStripIntegrand_bound μ r f hint hz) hf.norm
  filter_upwards [] with s
  exact (continuous_const.mul (modularStripKernel_differentiable (r s)).continuous).continuousOn

include hf hint in
theorem modularStripIntegral_bound {z : ℂ} (hz : 0 ≤ z.im ∧ z.im ≤ 1) :
    ‖modularStripIntegral μ r f z‖ ≤ ∫ s, ‖f s‖ ∂μ :=
  norm_integral_le_of_norm_le hf.norm (modularStripIntegrand_bound μ r f hint hz)

include hr hf hint in
theorem modularStripIntegral_differentiableOn :
    DifferentiableOn ℂ (modularStripIntegral μ r f) {z : ℂ | 0 < z.im ∧ z.im < 1} := by
  intro z hz
  change 0 < z.im ∧ z.im < 1 at hz
  let δ : ℝ := min z.im (1 - z.im) / 2
  have hδ : 0 < δ := div_pos (lt_min hz.1 (sub_pos.mpr hz.2)) (by norm_num)
  have hδ₀ : δ < z.im := by
    have h := min_le_left z.im (1 - z.im)
    dsimp [δ]
    linarith [hz.1]
  have hδ₁ : z.im < 1 - δ := by
    have h := min_le_right z.im (1 - z.im)
    dsimp [δ]
    linarith [hz.2]
  let S : Set ℂ := {w | δ < w.im ∧ w.im < 1 - δ}
  have hS : S ∈ 𝓝 z :=
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds ⟨hδ₀, hδ₁⟩
  let F' : ℂ → X → ℂ := fun w s =>
    f s * ((-Complex.I * (resolventLogFrequency (r s) : ℂ)) * modularStripKernel w (r s))
  have hm (w : ℂ) : AEStronglyMeasurable (F' w) μ := by
    exact hf.aestronglyMeasurable.mul
      ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (resolventLogFrequency_measurable.comp hr))).mul
        (modularStripKernel_comp_measurable r hr w)).aestronglyMeasurable
  have hI : Integrable (fun s => f s * modularStripKernel z (r s)) μ :=
    hf.norm.mono' (modularStripIntegrand_measurable μ r hr f hf z)
      (modularStripIntegrand_bound μ r f hint ⟨hz.1.le, hz.2.le⟩)
  have hB : ∀ᵐ s ∂μ, ∀ w ∈ S, ‖F' w s‖ ≤ ‖f s‖ * (1 / δ) := by
    filter_upwards [hint] with s hs w hw
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left
      (modularStripKernel_deriv_bound hs.1 hs.2 hδ hw.1.le hw.2.le) (norm_nonneg _))
  have hD : ∀ᵐ s ∂μ, ∀ w ∈ S,
      HasDerivAt (fun w => f s * modularStripKernel w (r s)) (F' w s) w := by
    filter_upwards [] with s w _
    exact (modularStripKernel_hasDerivAt (r s) w).const_mul (f s)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun w => modularStripIntegrand_measurable μ r hr f hf w) hI
    (hm z) hB (hf.norm.mul_const (1 / δ)) hD).2.differentiableAt.differentiableWithinAt

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStripBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary values of the modular strip kernel -/

namespace KadisonKastler

noncomputable section

theorem negative_phase_exp (t s : ℝ) :
    Complex.exp ((-Complex.I * (t : ℂ)) * (resolventLogFrequency s : ℂ)) =
      modularSpectralPhase (-t) s := by
  unfold modularSpectralPhase resolventLogFrequency
  congr 1
  push_cast
  ring

theorem modularStripKernel_bottom (t s : ℝ) :
    modularStripKernel (t : ℂ) s = (s : ℂ) * modularSpectralPhase (-t) s := by
  unfold modularStripKernel
  rw [negative_phase_exp]

theorem modularStripKernel_top {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (t : ℝ) :
    modularStripKernel ((t : ℂ) + Complex.I) s =
      ((1 - s : ℝ) : ℂ) * modularSpectralPhase (-t) s := by
  have he : (-Complex.I * ((t : ℂ) + Complex.I)) * (resolventLogFrequency s : ℂ) =
      (resolventLogFrequency s : ℂ) + (-Complex.I * (t : ℂ)) * (resolventLogFrequency s : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hr : s * Real.exp (resolventLogFrequency s) = 1 - s := by
    unfold resolventLogFrequency
    rw [Real.exp_sub, Real.exp_log (sub_pos.mpr hs1), Real.exp_log hs]
    field_simp
  have hc := congrArg (fun q : ℝ => (q : ℂ)) hr
  push_cast at hc
  rw [modularStripKernel, he, Complex.exp_add, ← mul_assoc, hc,
    negative_phase_exp]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCoordinateMultiplier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def resolventCoordinateFunction (R : H →L[ℂ] H) : C(spectrum ℝ R, ℂ) :=
  ⟨fun s => (s.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HermitianLinearExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complexification of self-adjoint pairing identities -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem complexLinear_eq_of_selfAdjoint (F G : A →ₗ[ℂ] ℂ)
    (h : ∀ x : selfAdjoint A, F x.val = G x.val) : F = G := by
  ext x
  rw [← realPart_add_I_smul_imaginaryPart x, map_add, map_add, map_smul, map_smul,
    h (realPart x), h (imaginaryPart x)]

theorem hermitianLinear_eq_of_selfAdjoint_real (F G : A →ₗ[ℂ] ℂ)
    (hF : ∀ x, F (star x) = star (F x))
    (hG : ∀ x, G (star x) = star (G x))
    (h : ∀ x : selfAdjoint A, (F x.val).re = (G x.val).re) : F = G := by
  apply complexLinear_eq_of_selfAdjoint F G
  intro x
  have hf := congrArg Complex.im (hF x.val)
  have hg := congrArg Complex.im (hG x.val)
  rw [x.property.star_eq, Complex.star_def, Complex.conj_im] at hf hg
  apply Complex.ext (h x)
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointVectorSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The closed real space of self-adjoint algebra vectors -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance selfAdjointSpaceReal : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DenseSupportSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Dense support tests for a bounded closed convex set

A dense family of Hilbert-space support tests suffices when the candidate
set is uniformly bounded. This is used for self-adjoint operator balls.
-/

namespace KadisonKastler

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The uniform bound lets dense tests recover every separating functional. -/
theorem mem_closed_convex_of_dense_support {C D : Set E} {y : E} {B : ℝ}
    (hC : IsClosed C) (hconv : Convex ℝ C) (hD : Dense D)
    (hB : ∀ x ∈ C, ‖x‖ ≤ B)
    (htest : ∀ h ∈ D, ∃ x ∈ C, inner ℝ h y ≤ inner ℝ h x) : y ∈ C := by
  classical
  by_contra hy
  obtain ⟨f, u, hfu, huy⟩ := geometric_hahn_banach_closed_point hconv hC hy
  let h := (InnerProductSpace.toDual ℝ E).symm f
  have hf (v : E) : f v = inner ℝ h v :=
    (InnerProductSpace.toDual_symm_apply (x := v) (y := f)).symm
  obtain ⟨v, hvD, hv⟩ := mem_closure_iff_seq_limit.mp (hD h)
  have hb (n : ℕ) : inner ℝ (v n) y ≤ u + ‖v n - h‖ * B := by
    obtain ⟨x, hx, hxy⟩ := htest (v n) (hvD n)
    have hi := real_inner_le_norm (v n - h) x
    have hm := mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg (v n - h))
    have hu := (hfu x hx).le
    rw [hf] at hu
    rw [inner_sub_left] at hi
    linarith
  have hl : Tendsto (fun n => inner ℝ (v n) y) atTop (𝓝 (f y)) := by
    rw [hf]
    exact hv.inner tendsto_const_nhds
  have hr : Tendsto (fun n => u + ‖v n - h‖ * B) atTop (𝓝 u) := by
    have hd : Tendsto (fun n => ‖v n - h‖) atTop (𝓝 0) := by
      simpa using (hv.sub (tendsto_const_nhds (x := h))).norm
    simpa using tendsto_const_nhds.add (hd.mul_const B)
  exact huy.not_ge (le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hb))

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularRadonNikodym
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance modularRadonReal : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularWeightedIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integrable scalar weights on bounded operator fields

Vectorwise integration needs only strong measurability on each vector.
An integrable scalar weight therefore defines a bounded operator, and
commutation and von Neumann algebra membership pass to this operator.
This applies in particular to the compactly weighted convolution
operators in the regular representation.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integrable_weighted_operator_vector
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (x : H) :
    Integrable (fun t => w t • F t x) μ := by
  apply (hw.norm.mul_const (C * ‖x‖)).mono'
    (hw.aestronglyMeasurable.smul (hm x))
  filter_upwards [hb] with t ht
  change ‖w t • F t x‖ ≤ ‖w t‖ * (C * ‖x‖)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (((F t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg x))) (norm_nonneg _)

omit [CompleteSpace H] in
theorem norm_integral_weighted_operator_vector_le
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H) (C : ℝ)
    (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (x : H) :
    ‖∫ t, w t • F t x ∂μ‖ ≤ (∫ t, ‖w t‖ ∂μ) * C * ‖x‖ := by
  calc
    ‖∫ t, w t • F t x ∂μ‖ ≤ ∫ t, ‖w t‖ * (C * ‖x‖) ∂μ := by
      apply norm_integral_le_of_norm_le (hw.norm.mul_const (C * ‖x‖))
      filter_upwards [hb] with t ht
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (((F t).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right ht (norm_nonneg x))) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

/-- Integrating an integrably weighted, uniformly bounded field on vectors. -/
def weightedOperatorIntegral
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ t, w t • F t x ∂μ
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_weighted_operator_vector μ w hw F hm C hb x)
          (integrable_weighted_operator_vector μ w hw F hm C hb y)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (w _) c]
        exact integral_smul c (fun t => w t • F t x) }
    ((∫ t, ‖w t‖ ∂μ) * C)
    (norm_integral_weighted_operator_vector_le μ w hw F C hb)

omit [CompleteSpace H] in
@[simp] theorem weightedOperatorIntegral_apply
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (x : H) :
    weightedOperatorIntegral μ w hw F hm C hb x = ∫ t, w t • F t x ∂μ := rfl

theorem weightedOperatorIntegral_commutes
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (A : H →L[ℂ] H)
    (hA : ∀ᵐ t ∂μ, F t * A = A * F t) :
    weightedOperatorIntegral μ w hw F hm C hb * A =
      A * weightedOperatorIntegral μ w hw F hm C hb := by
  ext x
  change (∫ t, w t • F t (A x) ∂μ) = A (∫ t, w t • F t x ∂μ)
  rw [← A.integral_comp_comm (integrable_weighted_operator_vector μ w hw F hm C hb x)]
  apply integral_congr_ae
  filter_upwards [hA] with t ht
  rw [map_smul]
  exact congrArg (fun y : H => w t • y)
    (congrArg (fun B : H →L[ℂ] H => B x) ht)

/-- Membership is checked against the commutant, with no norm-topology
measurability assumption on the operator field. -/
theorem weightedOperatorIntegral_mem
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (M : VonNeumannAlgebra H)
    (hM : ∀ᵐ t ∂μ, F t ∈ M) :
    weightedOperatorIntegral μ w hw F hm C hb ∈ M := by
  change weightedOperatorIntegral μ w hw F hm C hb ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro A hA
  apply (weightedOperatorIntegral_commutes μ w hw F hm C hb A ?_).symm
  filter_upwards [hM] with t ht
  exact hA (F t) ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripContourBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Decay on the horizontal edges of the modular contour -/

namespace KadisonKastler

noncomputable section

theorem norm_complex_sin_lower (z : ℂ) :
    (Real.exp |z.im| - Real.exp (-|z.im|)) / 2 ≤ ‖Complex.sin z‖ := by
  have h₁ : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h₂ : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num only [Complex.norm_ofNat]
  rcases le_total 0 z.im with hi | hi
  · rw [abs_of_nonneg hi]
    exact div_le_div_of_nonneg_right
      (by simpa only [h₁, h₂] using (norm_sub_norm_le
        (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I)))) (by norm_num)
  · rw [abs_of_nonpos hi, neg_neg]
    have h := norm_sub_norm_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
    rw [h₂, h₁, norm_sub_rev] at h
    exact div_le_div_of_nonneg_right h (by norm_num)

theorem strip_sine_exponential_lower (x t : ℝ) (ht : 1 ≤ Real.pi * |t|) :
    Real.exp (Real.pi * |t|) / 4 ≤
      ‖Complex.sin (Real.pi * ((x : ℂ) + t * Complex.I))‖ := by
  have hs := norm_complex_sin_lower (Real.pi * ((x : ℂ) + t * Complex.I))
  have he : (Real.pi * ((x : ℂ) + t * Complex.I)).im = Real.pi * t := by simp
  rw [he, abs_mul, abs_of_pos Real.pi_pos] at hs
  have hp : 2 ≤ Real.exp (Real.pi * |t|) := by
    linarith [Real.add_one_le_exp (Real.pi * |t|)]
  have hm : Real.exp (-(Real.pi * |t|)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ContinuousMapHolomorphic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

section CircleCompat
open MeasureTheory Set Metric Filter Complex Real Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem normCircleMapSubLeCompat (c : ℂ) (R : ℝ) (θ : ℝ) (x : ℂ) :
    ‖circleMap c R θ - x‖ ≤ |R| + dist c x := by
  rw [← dist_eq_norm, ← mem_sphere.1 (circleMap_mem_sphere' c R θ)]
  exact dist_triangle _ _ _

theorem existsBallForallLeNormCircleMapSubCompat {R : ℝ} {c w : ℂ} (hw : w ∉ sphere c |R|) :
    ∃ d > 0, ∀ x ∈ ball w d, ∀ θ : ℝ, d ≤ ‖circleMap c R θ - x‖ := by
  have hd₀ : 0 < abs (dist w c - |R|) :=
    abs_pos.2 (sub_ne_zero.2 fun h ↦ hw (mem_sphere.2 h))
  refine ⟨abs (dist w c - |R|) / 2, by positivity, fun x hx θ ↦ ?_⟩
  rw [mem_ball] at hx
  have h₁ : dist (circleMap c R θ) c = |R| := mem_sphere.1 (circleMap_mem_sphere' c R θ)
  have h₂ : abs (dist w c - |R|) ≤ dist (circleMap c R θ) w := by
    calc abs (dist w c - |R|) = |dist (circleMap c R θ) c - dist w c| := by rw [h₁, abs_sub_comm]
      _ ≤ dist (circleMap c R θ) w := abs_dist_sub_le _ _ _
  have h₃ := dist_triangle (circleMap c R θ) x w
  rw [← dist_eq_norm]
  linarith

theorem circleIntegrableSubZpowSmulCompat {f : ℂ → E} {c w : ℂ} {R : ℝ} (n : ℤ)
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    CircleIntegrable (fun z ↦ (z - w) ^ n • f z) c R :=
  hf.continuousOn_smul <| (continuousOn_id.sub continuousOn_const).zpow₀ n
    fun _ hz ↦ Or.inl (sub_ne_zero.2 (ne_of_mem_of_not_mem hz hw))

theorem hasDerivAtCircleIntegralSubZpowSmulCompat {f : ℂ → E} {R : ℝ} {c w : ℂ} {n : ℤ}
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun w ↦ ∮ z in C(c, R), (z - w) ^ n • f z)
      ((-n : ℂ) • ∮ z in C(c, R), (z - w) ^ (n - 1) • f z) w := by
  obtain ⟨d, hd, hdist⟩ := existsBallForallLeNormCircleMapSubCompat hw
  have hfm : AEStronglyMeasurable (fun θ ↦ f (circleMap c R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hf).aestronglyMeasurable
  simp only [circleIntegral, deriv_circleMap]
  rw [← intervalIntegral.integral_smul]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ ↦ (-n : ℂ) • ((circleMap 0 R θ * I)
      • (circleMap c R θ - x) ^ (n - 1) • f (circleMap c R θ)))
    (bound := fun θ ↦ |(n : ℝ)| * |R| * max (d ^ (n - 1)) ((|R| + dist c w + d) ^ (n - 1)) *
      ‖f (circleMap c R θ)‖)
    (ball_mem_nhds w hd) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with x
    exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
      ((Measurable.aestronglyMeasurable (by fun_prop)).smul hfm)
  · simpa only [deriv_circleMap] using (circleIntegrableSubZpowSmulCompat n hf hw).out
  · exact ((Continuous.aestronglyMeasurable (by fun_prop)).smul
      ((Measurable.aestronglyMeasurable (by fun_prop)).smul hfm)).const_smul _
  · filter_upwards with θ _ x hx
    have hlb := hdist x hx θ
    have hub : ‖circleMap c R θ - x‖ ≤ |R| + dist c w + d := by
      have := mem_ball.1 hx
      linarith [normCircleMapSubLeCompat c R θ x, dist_triangle_right c x w]
    have key : ‖circleMap c R θ - x‖ ^ (n - 1)
        ≤ max (d ^ (n - 1)) ((|R| + dist c w + d) ^ (n - 1)) := by
      rcases le_or_gt 0 (n - 1) with h | h
      · exact le_max_of_le_right (zpow_le_zpow_left₀ h (norm_nonneg _) hub)
      · refine le_max_of_le_left ?_
        rw [show n - 1 = -(1 - n) by ring, zpow_neg, zpow_neg]
        exact inv_anti₀ (zpow_pos hd _) (zpow_le_zpow_left₀ (by omega) hd.le hlb)
    have norm_eq : ‖(-n : ℂ) • ((circleMap 0 R θ * I)
        • (circleMap c R θ - x) ^ (n - 1) • f (circleMap c R θ))‖
        = |(n : ℝ)| * |R| * ‖circleMap c R θ - x‖ ^ (n - 1) * ‖f (circleMap c R θ)‖ := by
      rw [norm_smul, norm_smul, norm_smul, norm_neg, Complex.norm_intCast, norm_zpow, norm_mul,
        Complex.norm_I, mul_one, norm_circleMap_zero]
      ring
    rw [norm_eq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (by positivity))
      (norm_nonneg _)
  · exact (IntervalIntegrable.norm hf).const_mul _
  · filter_upwards with θ _ x hx
    have hne : circleMap c R θ - x ≠ 0 := norm_pos_iff.mp (hd.trans_le (hdist x hx θ))
    have h₁ : HasDerivAt (fun y : ℂ ↦ (circleMap c R θ - y) ^ n)
        (-((n : ℂ) * (circleMap c R θ - x) ^ (n - 1))) x :=
      (hasDerivAt_zpow n _ (Or.inl hne)).comp_const_sub (circleMap c R θ) x
    exact ((h₁.smul_const (f (circleMap c R θ))).const_smul (circleMap 0 R θ * I)).congr_deriv
      (by module)


theorem hasDerivAtCircleIntegralSubInvSmulCompat {f : ℂ → E} {R : ℝ} {c w : ℂ}
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • f z)
      (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z) w := by
  simpa only [show (-1 : ℤ) - 1 = -2 by norm_num, zpow_neg_one, Int.cast_neg, Int.cast_one,
    neg_neg, one_smul]
    using hasDerivAtCircleIntegralSubZpowSmulCompat (n := -1) hf hw
end CircleCompat


/-! # Holomorphic continuous spectral functions

On a compact spectrum, a continuous family of continuous functions is
holomorphic once each scalar evaluation is holomorphic. The Cauchy integral
formula proves the required uniform derivative without enlarging Lean limits.
-/

namespace KadisonKastler

open MeasureTheory Set Metric Filter Complex
open scoped Topology

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem circleIntegral_evaluation (F : ℂ → C(K, ℂ)) (c : ℂ) (r : ℝ)
    (hF : CircleIntegrable F c r) (k : K) :
    (∮ z in C(c, r), F z) k = ∮ z in C(c, r), F z k := by
  have he := (ContinuousMap.evalCLM ℂ k).intervalIntegral_comp_comm hF.out
  simpa only [circleIntegral, Function.comp_def, map_smul,
    ContinuousMap.evalCLM_apply] using he.symm

theorem continuousMap_differentiableOn_of_evaluations (F : ℂ → C(K, ℂ))
    {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn F U)
    (hd : ∀ k : K, DifferentiableOn ℂ (fun z => F z k) U) :
    DifferentiableOn ℂ F U := by
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hclosed : closedBall z r ⊆ U := by
    intro w hw
    apply hball
    change dist w z ≤ r at hw
    change dist w z < ε
    exact lt_of_le_of_lt hw (by dsimp [r] <;> linarith)
  have hFc : ContinuousOn F (closedBall z r) := hc.mono hclosed
  have hFi : CircleIntegrable F z r := (hFc.mono sphere_subset_closedBall).circleIntegrable hr.le
  let G : ℂ → C(K, ℂ) := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ ζ in C(z, r), (ζ - w)⁻¹ • F ζ
  have hG : HasDerivAt G
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z, r), (ζ - z) ^ (-2 : ℤ) • F ζ) z := by
    have hn : z ∉ sphere z |r| := by
      rw [abs_of_pos hr]
      exact sphere_disjoint_ball.notMem_of_mem_right (mem_ball_self hr)
    exact (hasDerivAtCircleIntegralSubInvSmulCompat hFi hn).const_smul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  have heq : ∀ w ∈ ball z r, G w = F w := by
    intro w hw
    have hwn : w ∉ sphere z |r| := by
      rw [abs_of_pos hr]
      exact sphere_disjoint_ball.notMem_of_mem_right hw
    apply ContinuousMap.ext
    intro k
    change ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ ζ in C(z, r), (ζ - w)⁻¹ • F ζ)) k = F w k
    rw [ContinuousMap.smul_apply]
    rw [circleIntegral_evaluation _ _ _ (by
      simpa only [zpow_neg_one] using circleIntegrableSubZpowSmulCompat (-1) hFi hwn)]
    apply Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw
    · exact ((ContinuousMap.evalCLM ℂ k).continuous.comp_continuousOn hFc)
    · intro v hv
      exact (hd k).differentiableAt (hU.mem_nhds (hclosed (ball_subset_closedBall hv.1)))
  have hnb : ∀ᶠ w in 𝓝 z, w ∈ ball z r := ball_mem_nhds z hr
  have hEq : G =ᶠ[𝓝 z] F := hnb.mono (fun w hw => heq w hw)
  exact (hG.congr_of_eventuallyEq hEq.symm).differentiableAt.differentiableWithinAt

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # An endpoint-continuous modular strip kernel

The extra factor `s (1-s)^2` makes both boundary functions continuous on
the closed resolvent spectrum. It will cancel on a dense operator range.
-/

namespace KadisonKastler

open Set

noncomputable section

def weightedStripKernel (z : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ ((3 / 2 : ℂ) - z) * ((1 - s : ℝ) : ℂ) ^ ((5 / 2 : ℂ) + z)

theorem weighted_exponents_pos {z : ℂ} (hz : |z.re| < 1) :
    0 < ((3 / 2 : ℂ) - z).re ∧ 0 < ((5 / 2 : ℂ) + z).re := by
  have h := abs_lt.mp hz
  constructor <;> norm_num <;> linarith

theorem weightedStripKernel_continuousAt {z : ℂ} {s : ℝ} (hz : |z.re| < 1) :
    ContinuousAt (fun p : ℂ × ℝ => weightedStripKernel p.1 p.2) (z, s) := by
  obtain ⟨h₁, h₂⟩ := weighted_exponents_pos hz
  have ha : ContinuousAt (fun p : ℂ × ℝ => (p.2 : ℂ) ^ ((3 / 2 : ℂ) - p.1)) (z, s) :=
    (Complex.continuousAt_ofReal_cpow s ((3 / 2 : ℂ) - z) (Or.inl h₁)).comp_of_eq
    (by fun_prop : ContinuousAt (fun p : ℂ × ℝ => (p.2, (3 / 2 : ℂ) - p.1)) (z, s)) rfl
  have hb : ContinuousAt (fun p : ℂ × ℝ => ((1 - p.2 : ℝ) : ℂ) ^ ((5 / 2 : ℂ) + p.1)) (z, s) :=
    (Complex.continuousAt_ofReal_cpow (1 - s) ((5 / 2 : ℂ) + z) (Or.inl h₂)).comp_of_eq
    (by fun_prop : ContinuousAt (fun p : ℂ × ℝ => (1 - p.2, (5 / 2 : ℂ) + p.1)) (z, s)) rfl
  exact ha.mul hb

theorem weightedStripKernel_differentiableAt (s : ℝ) {z : ℂ} (hz : |z.re| < 1) :
    DifferentiableAt ℂ (fun z => weightedStripKernel z s) z := by
  obtain ⟨h₁, h₂⟩ := weighted_exponents_pos hz
  have hd₁ : DifferentiableAt ℂ (fun w : ℂ => (3 / 2 : ℂ) - w) z := by fun_prop
  have hd₂ : DifferentiableAt ℂ (fun w : ℂ => (5 / 2 : ℂ) + w) z := by fun_prop
  apply DifferentiableAt.mul
  · exact hd₁.const_cpow
      (Or.inr (ne_of_apply_ne Complex.re h₁.ne'))
  · exact hd₂.const_cpow
      (Or.inr (ne_of_apply_ne Complex.re h₂.ne'))

theorem weightedStripKernel_norm_le_one {z : ℂ} {s : ℝ}
    (hz : |z.re| ≤ 1 / 2) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖weightedStripKernel z s‖ ≤ 1 := by
  have hh := abs_le.mp hz
  have he₁ : 0 < ((3 / 2 : ℂ) - z).re := by norm_num <;> linarith
  have he₂ : 0 < ((5 / 2 : ℂ) + z).re := by norm_num <;> linarith
  unfold weightedStripKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg hs he₁.ne',
    Complex.norm_cpow_eq_rpow_re_of_nonneg (sub_nonneg.mpr hs1) he₂.ne']
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (Real.rpow_le_one hs hs1 he₁.le)
      (Real.rpow_le_one (sub_nonneg.mpr hs1) (by linarith) he₂.le)
      (Real.rpow_nonneg (sub_nonneg.mpr hs1) _) zero_le_one
    _ = 1 := one_mul _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripContinuous
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The weighted strip as a holomorphic continuous spectral function -/

namespace KadisonKastler

open Set Filter
open scoped Topology

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem weightedStripKernel_continuous_s {z : ℂ} (hz : |z.re| < 1) :
    Continuous (weightedStripKernel z) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (weightedStripKernel_continuousAt (s := s) hz).comp
    (by fun_prop : ContinuousAt (fun t : ℝ => (z, t)) s)

def weightedStripContinuous (r : C(K, ℝ)) (z : ℂ) : C(K, ℂ) :=
  if hz : |z.re| < 1 then
    ⟨fun k => weightedStripKernel z (r k), (weightedStripKernel_continuous_s hz).comp r.continuous⟩
  else 0

omit [CompactSpace K] in
theorem weightedStripContinuous_apply (r : C(K, ℝ)) {z : ℂ} (hz : |z.re| < 1) (k : K) :
    weightedStripContinuous r z k = weightedStripKernel z (r k) := by
  simp only [weightedStripContinuous, dite_eq_left hz, ContinuousMap.coe_mk]

omit [CompactSpace K] in
theorem weightedStripContinuous_continuousOn (r : C(K, ℝ)) :
    ContinuousOn (weightedStripContinuous r) {z : ℂ | |z.re| < 1} := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  intro p hp
  have hp' : |p.1.re| < 1 := hp.1
  have hc : ContinuousAt (fun q : ℂ × K => weightedStripKernel q.1 (r q.2)) p :=
    (weightedStripKernel_continuousAt hp').comp_of_eq
      (continuous_fst.prodMk (r.continuous.comp continuous_snd)).continuousAt rfl
  have hn : ∀ᶠ q : ℂ × K in 𝓝 p, |q.1.re| < 1 := by
    exact ((isOpen_lt (Complex.continuous_re.comp continuous_fst).abs
      continuous_const).mem_nhds hp')
  have he : (fun q : ℂ × K => weightedStripContinuous r q.1 q.2) =ᶠ[𝓝 p]
      (fun q => weightedStripKernel q.1 (r q.2)) :=
    hn.mono (fun q hq => weightedStripContinuous_apply r hq q.2)
  exact (hc.congr_of_eventuallyEq he).continuousWithinAt

theorem weightedStripContinuous_differentiableOn (r : C(K, ℝ)) :
    DifferentiableOn ℂ (weightedStripContinuous r) {z : ℂ | |z.re| < 1} := by
  apply continuousMap_differentiableOn_of_evaluations _
    (isOpen_lt Complex.continuous_re.abs continuous_const)
    (weightedStripContinuous_continuousOn r)
  intro k z hz
  have hn : ∀ᶠ w in 𝓝 z, |w.re| < 1 :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds hz
  have he : (fun w => weightedStripContinuous r w k) =ᶠ[𝓝 z]
      (fun w => weightedStripKernel w (r k)) :=
    hn.mono (fun w hw => weightedStripContinuous_apply r hw k)
  exact ((weightedStripKernel_differentiableAt (r k) hz).congr_of_eventuallyEq he).differentiableWithinAt

theorem weightedStripContinuous_norm_le (r : C(K, ℝ))
    (hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖weightedStripContinuous r z‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro k
  rw [weightedStripContinuous_apply r (lt_of_le_of_lt hz (by norm_num))]
  exact weightedStripKernel_norm_le_one hz (hr k).1 (hr k).2

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded holomorphic modular strip on the original space -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def resolventContinuousCalculusLinear (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    C(spectrum ℝ R, ℂ) →L[ℂ] (H →L[ℂ] H) :=
  (resolventContinuousCalculus R hR).toAlgHom.toLinearMap.mkContinuous 1
    (fun f => by change ‖resolventContinuousCalculus R hR f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using
      NonUnitalStarAlgHom.norm_apply_le (resolventContinuousCalculus R hR) f)

def resolventRealCoordinate (R : H →L[ℂ] H) : C(spectrum ℝ R, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventSqrtCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Square-root functions in the real resolvent calculus -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventSqrtFunction (R : H →L[ℂ] H) : C(spectrum ℝ R, ℂ) :=
  ⟨fun s => (Real.sqrt s.val : ℂ), by fun_prop⟩

def resolventComplementSqrtFunction (R : H →L[ℂ] H) : C(spectrum ℝ R, ℂ) :=
  ⟨fun s => (Real.sqrt (1 - s.val) : ℂ), by fun_prop⟩

theorem resolventContinuousCalculus_coordinate (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    resolventContinuousCalculus R hR (resolventCoordinateFunction R) = R :=
  (resolventContinuousCalculus_ofReal R hR
    ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)

theorem resolventContinuousCalculus_sqrt (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hp : 0 ≤ R) :
    resolventContinuousCalculus R hR (resolventSqrtFunction R) = CFC.sqrt R := by
  let f : C(spectrum ℝ R, ℝ) := ⟨fun s => Real.sqrt s.val, by fun_prop⟩
  change resolventContinuousCalculus R hR
    ⟨fun s => (f s : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ = _
  rw [resolventContinuousCalculus_ofReal]
  rw [CFC.sqrt_eq_real_sqrt R hp, cfcₙ_eq_cfc]
  exact (cfc_apply Real.sqrt R hR (by fun_prop)).symm

theorem resolventContinuousCalculus_complement_sqrt (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hp : 0 ≤ 1 - R) :
    resolventContinuousCalculus R hR (resolventComplementSqrtFunction R) = CFC.sqrt (1 - R) := by
  let f : C(spectrum ℝ R, ℝ) := ⟨fun s => Real.sqrt (1 - s.val), by fun_prop⟩
  change resolventContinuousCalculus R hR
    ⟨fun s => (f s : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ = _
  rw [resolventContinuousCalculus_ofReal]
  have he : cfc (fun s : ℝ => 1 - s) R = 1 - R := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) R (by fun_prop) (by fun_prop),
      cfc_const_one ℝ R hR, cfc_id' ℝ R hR]
  rw [CFC.sqrt_eq_real_sqrt (1 - R) hp, cfcₙ_eq_cfc, ← he,
    ← cfc_comp Real.sqrt (fun s : ℝ => 1 - s) R (ha := hR)]
  exact (cfc_apply (fun s : ℝ => Real.sqrt (1 - s)) R hR (by fun_prop)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary values of the endpoint-weighted spectral strip -/

namespace KadisonKastler

noncomputable section

theorem weightedStripKernel_vertical {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (x t : ℝ) :
    weightedStripKernel ((x : ℂ) + t * Complex.I) s =
      weightedStripKernel (x : ℂ) s * modularSpectralPhase t s := by
  have hsn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hqn : ((1 - s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_pos.mpr hs1).ne'
  have h₁ : (3 / 2 : ℂ) - (x + t * Complex.I) = ((3 / 2 : ℂ) - x) + -(t * Complex.I) := by ring
  have h₂ : (5 / 2 : ℂ) + (x + t * Complex.I) = ((5 / 2 : ℂ) + x) + t * Complex.I := by ring
  unfold weightedStripKernel modularSpectralPhase
  rw [h₁, h₂, Complex.cpow_add _ _ hsn, Complex.cpow_add _ _ hqn]
  rw [Complex.cpow_def_of_ne_zero hsn (-(t * Complex.I)),
    Complex.cpow_def_of_ne_zero hqn (t * Complex.I)]
  rw [← Complex.ofReal_log hs.le, ← Complex.ofReal_log (sub_nonneg.mpr hs1.le)]
  push_cast
  have he : Complex.exp ((Real.log s : ℂ) * -(t * Complex.I)) *
      Complex.exp ((Real.log (1 - s) : ℂ) * (t * Complex.I)) =
      Complex.exp (Complex.I * (t * ((Real.log (1 - s) : ℂ) - (Real.log s : ℂ)))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = ((s : ℂ) ^ ((3 / 2 : ℂ) - x) * ((1 - (s : ℂ)) ^ ((5 / 2 : ℂ) + x))) *
        (Complex.exp ((Real.log s : ℂ) * -(t * Complex.I)) *
          Complex.exp ((Real.log (1 - s) : ℂ) * (t * Complex.I))) := by ring
    _ = _ := by rw [he]

theorem weightedStripKernel_right {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (t : ℝ) :
    weightedStripKernel ((1 / 2 : ℂ) + t * Complex.I) s =
      (s : ℂ) * ((1 - s : ℝ) : ℂ) ^ 3 * modularSpectralPhase t s := by
  have h := weightedStripKernel_vertical hs hs1 (1 / 2) t
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast)
  · congr 1
  · unfold weightedStripKernel
    norm_num [Complex.cpow_ofNat]

theorem weightedStripKernel_left {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (t : ℝ) :
    weightedStripKernel ((-1 / 2 : ℂ) + t * Complex.I) s =
      (s : ℂ) ^ 2 * ((1 - s : ℝ) : ℂ) ^ 2 * modularSpectralPhase t s := by
  have h := weightedStripKernel_vertical hs hs1 (-1 / 2) t
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast)
  · congr 1
  · unfold weightedStripKernel
    norm_num [Complex.cpow_ofNat]


theorem weightedStripKernel_center {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    weightedStripKernel 0 s =
      (s : ℂ) * ((1 - s : ℝ) : ℂ) ^ 2 *
        ((Real.sqrt s : ℂ) * (Real.sqrt (1 - s) : ℂ)) := by
  have hsn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hqn : ((1 - s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_pos.mpr hs1).ne'
  have hsqrt (x : ℝ) (hx : 0 ≤ x) :
      (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow hx (1 / 2)).symm
  unfold weightedStripKernel
  rw [sub_zero, add_zero, show (3 / 2 : ℂ) = 1 + 1 / 2 by ring,
    show (5 / 2 : ℂ) = 2 + 1 / 2 by ring,
    Complex.cpow_add _ _ hsn, Complex.cpow_add _ _ hqn,
    Complex.cpow_one, Complex.cpow_two, hsqrt s hs.le,
    hsqrt (1 - s) (sub_nonneg.mpr hs1.le)]
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factoring the weighted strip boundaries through the middle operator -/

namespace KadisonKastler

noncomputable section

theorem sandwich_reorder {A : Type*} [Ring A] (d r q u v x : A)
    (hrv : Commute r v) (hdq : Commute d q) (hdu : Commute d u) :
    (d * r * v) * x * (d * q * u) = d * v * (r * x * q) * u * d := by
  have hl : d * r * v = d * v * r := by
    rw [mul_assoc, hrv.eq, ← mul_assoc]
  have hh : d * q * u = q * u * d := by
    rw [hdq.eq, mul_assoc, hdu.eq, ← mul_assoc]
  rw [hl, hh]
  simp only [mul_assoc]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PolarConjugationComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The linear unitary comparing two conjugations

If both conjugations exchange an algebra and its commutant, their
composition is a spatial symmetry of the original algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def conjugationPairUnitary (J K : H ≃ₗᵢ⋆[ℂ] H) : unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm (K.trans J)

@[simp] theorem conjugationPairUnitary_apply (J K : H ≃ₗᵢ⋆[ℂ] H) (x : H) :
    (conjugationPairUnitary J K : H →L[ℂ] H) x=J (K x) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete positivity of compression between two Hilbert spaces -/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance compressionOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance compressionOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproductDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Innerness in the norm ultraproduct gives uniform commutator control

This proves the analytic core of the infinitesimal-normalizer contradiction.
The hypotheses are simplicity of the type III ultraproduct and invariance
under the commutator.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u v

variable {A : Type u} {E : Type v} [CStarAlgebra A] [CStarAlgebra E]

/-- A spatial commutator along a star representation, as a bounded map. -/
def commutatorAlong (φ : A →⋆ₐ[ℂ] E) (T : E) : A →L[ℂ] E :=
  ((ContinuousLinearMap.mul ℂ E T - (ContinuousLinearMap.mul ℂ E).flip T)).comp
    (φ.toLinearMap.mkContinuous 1 (fun x => by
      change ‖φ x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ x))

@[simp] theorem commutatorAlong_apply (φ : A →⋆ₐ[ℂ] E) (T : E) (x : A) :
    commutatorAlong φ T x = T * φ x - φ x * T := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral commutation for real character multipliers

Character commutation passes to every unitary of their commutant.
Finite vector measures then give scalar-multiplier commutation, and
the linear span of unitaries gives the assertion for every operator.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commutation on the unitary generators extends by their linear span. -/
theorem commute_map_of_unitaries {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (T : B)
    (h : ∀ u : unitary A, Commute (f u) T) (a : A) : Commute (f a) T := by
  let L : A →ₗ[ℂ] B :=
    ((LinearMap.mulRight ℂ T) - (LinearMap.mulLeft ℂ T)).comp f.toAlgHom.toLinearMap
  have hspan : Submodule.span ℂ (unitary A : Set A) ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro u hu
    exact sub_eq_zero.mpr (h ⟨u, hu⟩).eq
  have ha : a ∈ Submodule.span ℂ (unitary A : Set A) := by
    rw [CStarAlgebra.span_unitary]
    trivial
  exact sub_eq_zero.mp (hspan ha)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreBasis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A countable scalar basis for the real regular space

Disjoint unit intervals supply an infinite orthonormal set. A maximal
orthonormal extension is countable by separability, hence can be indexed
by the natural numbers. No representation-theoretic input is used.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology InnerProductSpace ENNReal

noncomputable section

def regularIntervalVector (n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (s := Set.Ioc (n : ℝ) ((n : ℝ) + 1)) measurableSet_Ioc
    (by simp [Real.volume_Ioc]) (1 : ℂ)

theorem regularIntervalVector_orthonormal :
    Orthonormal ℂ regularIntervalVector := by
  constructor
  · intro n
    rw [regularIntervalVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [measureReal_def, Real.volume_Ioc]
  · intro i j hij
    have hd : Disjoint (Set.Ioc (i : ℝ) ((i : ℝ) + 1))
        (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) := by
      simpa only [zero_add] using Set.pairwise_disjoint_Ioc_add_intCast (0 : ℝ) hij
    rw [regularIntervalVector, regularIntervalVector,
      L2.inner_indicatorConstLp_one_indicatorConstLp_one measurableSet_Ioc measurableSet_Ioc
        (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioc])]
    simp [Set.disjoint_iff_inter_eq_empty.mp hd]

theorem orthonormal_countable
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [TopologicalSpace.SeparableSpace E] {v : ι → E} (hv : Orthonormal ℂ v) :
    Countable ι := by
  have hsep (i j : ι) (hij : i ≠ j) : 1 ≤ dist (v i) (v j) := by
    have hs : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hv.norm_eq_one i, hv.norm_eq_one j,
        hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1 / 2 : ℝ))
      (Metric.ball (v j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using hsep i j hij
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- The scalar real-line `L²` space has an actual natural-number Hilbert basis. -/
theorem exists_regularScalarBasis :
    Nonempty (HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨w, b, hsub, _hb⟩ :=
    regularIntervalVector_orthonormal.toSubtypeRange.exists_hilbertBasis_extension
  let : Countable w := orthonormal_countable b.orthonormal
  have hw : w.Infinite :=
    (Set.infinite_range_of_injective
      regularIntervalVector_orthonormal.linearIndependent.injective).mono hsub
  let : Infinite w := hw.to_subtype
  let : Encodable w := Encodable.ofCountable w
  let : Denumerable w := Denumerable.ofEncodableOfInfinite w
  let e : ℕ ≃ w := (Denumerable.eqv w).symm
  have ho : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e e.injective
  refine ⟨HilbertBasis.mk ho ?_⟩
  have hr : Set.range (b ∘ e) = Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  rw [hr, b.dense_span]

/-- One fixed scalar basis; its only role is to select Hilbert coordinates. -/
def regularScalarBasis : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  Classical.choice exists_regularScalarBasis

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketLocalization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem integrable_local_translates {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg : Integrable g volume)
    (s : Set ℝ) (hs : volume s ≠ ⊤) :
    Integrable (fun p : ℝ × ℝ => g (p.1 + p.2))
      ((volume.restrict s).prod volume) := by
  let : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs
  have hp := (measurePreserving_prod_add_right (volume.restrict s)
    (volume : Measure ℝ)).integrable_comp_of_integrable
      (hg.comp_snd (volume.restrict s))
  simpa only [Function.comp_def, add_comm] using hp

/-- Integrating all translates of a local integral counts every point
exactly by the measure of the localization set. -/
theorem integral_local_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : Integrable g volume)
    (s : Set ℝ) (hs : volume s ≠ ⊤) :
    (∫ r : ℝ, ∫ t in s, g (t + r)) = (volume s).toReal • ∫ t : ℝ, g t := by
  have hp := integrable_local_translates hg s hs
  rw [← integral_integral_swap hp]
  simp_rw [integral_add_left_eq_self]
  rw [integral_const, measureReal_def, Measure.restrict_apply_univ]

theorem integrable_integral_local_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Integrable g volume)
    (s : Set ℝ) (hs : volume s ≠ ⊤) :
    Integrable (fun r : ℝ => ∫ t in s, g (t + r)) volume :=
  (integrable_local_translates hg s hs).integral_prod_right

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonPositionSpatial
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial stability after a common injective subfactor is fixed

The published change of representation, the constructed boundary
isomorphism and the actual paired-factor amplification are joined here.
The unitary acts on the original Hilbert space.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {M N R : VonNeumannAlgebra H}

local instance commonOperatorOrder_r895f4a_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance commonOperatorStarOrder_r895f4a_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- Explicit common-position error after returning to the original space. -/
def commonPositionError (g : ℝ) : ℝ := 1135 * 50948 * Real.sqrt g + 2 * g

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedFiniteAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The constructed finite-factor estimate in the stability notation

The finite-factor commutator estimate is uniform over separable
representations. Square matrix estimates imply the rectangular
complete bound used in strong stability.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance constructedFiniteOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance constructedFiniteOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedFiniteSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial implementation using the constructed finite-factor estimate -/

namespace KadisonKastler
noncomputable section
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

local instance constructedFiniteSpatialOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance constructedFiniteSpatialOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

end
end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedFiniteFactorStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the common-subfactor restriction

First move a constructed injective subfactor into the neighbor, then apply
common-position stability, and compose the two actual ambient unitaries.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {M N R : VonNeumannAlgebra H}

local instance constructedFiniteFactorStabilityFiniteStabilityOperatorOrder_r895f4a_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance constructedFiniteFactorStabilityFiniteStabilityOperatorStarOrder_r895f4a_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- Displacement from the initial embedding and the proved finite-factor estimate. -/
def constructedFiniteFactorError (t : ℝ) : ℝ :=
  150 * t + 4000000 * commonPositionError (302 * t)


end
end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteFactorModulus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform tolerance for the finite-factor displacement estimate -/

namespace KadisonKastler

open Filter Topology

noncomputable section

@[simp] theorem commonPositionError_zero : commonPositionError 0 = 0 := by
  simp [commonPositionError]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedFiniteFactorModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform tolerance for the finite-factor displacement estimate -/

namespace KadisonKastler

open Filter Topology

noncomputable section

@[simp] theorem constructedFiniteFactorError_zero : constructedFiniteFactorError 0 = 0 := by
  simp [constructedFiniteFactorError]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous functional calculus through a rectangular intertwiner -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Functional calculus preserves a bounded intertwiner of selfadjoint operators,
even when the two operators act on different Hilbert spaces. -/
theorem cfc_rectangular_intertwines
    (a : K →L[ℂ] K) (b : H →L[ℂ] H) (T : H →L[ℂ] K)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hT : a.comp T = T.comp b) (f : ℂ → ℂ)
    (hfa : ContinuousOn f (spectrum ℂ a)) (hfb : ContinuousOn f (spectrum ℂ b)) :
    (cfc f a).comp T = T.comp (cfc f b) := by
  let S := spectrum ℂ a ∪ spectrum ℂ b
  have hS : IsCompact S := (spectrum.isCompact a).union (spectrum.isCompact b)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let φ := cfcHomSuperset ha.isStarNormal (Set.subset_union_left : spectrum ℂ a ⊆ S)
  let ψ := cfcHomSuperset hb.isStarNormal (Set.subset_union_right : spectrum ℂ b ⊆ S)
  have hφ : Continuous φ := cfcHomSuperset_continuous _ _
  have hψ : Continuous ψ := cfcHomSuperset_continuous _ _
  have he (g : C(S, ℂ)) : (φ g).comp T = T.comp (ψ g) := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const z =>
      change (φ (algebraMap ℂ _ z)).comp T = T.comp (ψ (algebraMap ℂ _ z))
      rw [AlgHomClass.commutes, AlgHomClass.commutes]
      ext x
      simp
    | id =>
      change (cfcHomSuperset ha.isStarNormal _ (.restrict S (.id ℂ))).comp T =
        T.comp (cfcHomSuperset hb.isStarNormal _ (.restrict S (.id ℂ)))
      rw [cfcHomSuperset_id, cfcHomSuperset_id]
      exact hT
    | star_id =>
      rw [map_star, map_star]
      change (star (cfcHomSuperset ha.isStarNormal _ (.restrict S (.id ℂ)))).comp T =
        T.comp (star (cfcHomSuperset hb.isStarNormal _ (.restrict S (.id ℂ))))
      rw [cfcHomSuperset_id, cfcHomSuperset_id, ha.star_eq, hb.star_eq]
      exact hT
    | add g h hg hh =>
      simp only [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hg, hh]
    | mul g h hg hh =>
      change (φ (g * h)).comp T = T.comp (ψ (g * h))
      rw [map_mul, map_mul]
      change (φ g).comp ((φ h).comp T) = T.comp ((ψ g).comp (ψ h))
      rw [hh, ← ContinuousLinearMap.comp_assoc, hg, ContinuousLinearMap.comp_assoc]
    | frequently g hg =>
      exact hg.mem_of_closed (isClosed_eq (hφ.clm_comp continuous_const)
        (continuous_const.clm_comp hψ))
  have hf : ContinuousOn f S := hfa.union_of_isClosed hfb (spectrum.isCompact a).isClosed (spectrum.isCompact b).isClosed
  rw [cfc_apply f a ha.isStarNormal hfa, cfc_apply f b hb.isStarNormal hfb]
  exact he ⟨_, hf.domRestrict⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceFrequencyVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def coreTraceFrequencyFunction (t : ℝ) : ℂ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun s => (Real.exp (Real.pi * (s - 1)) : ℂ)) t

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedLocalMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem span_of_basis_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (b : Module.Basis ι ℂ V) (W : Submodule ℂ V) (h : ∀ i, b i ∈ W) :
    W = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)

theorem span_linearEquiv_image {V W ι : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (v : ι → V) (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range (fun i => e (v i))) = ⊤ := by
  have hr : Set.range (fun i => e (v i)) = e.toLinearMap '' Set.range v := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨v i, ⟨i,rfl⟩, rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [hr, ← Submodule.map_span, hv]
  exact (Submodule.map_top e.toLinearMap).trans
    (LinearMap.range_eq_top.mpr e.surjective)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local operators on the configuration Hilbert space

Finite matrix coefficients act on one configuration coordinate. The
construction is a star homomorphism, so the local matrix-unit relations
hold as actual bounded operator identities.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

section FiniteAmplification

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def finiteLocalCoefficient (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (i j : ι) : ℂ := A (EuclideanSpace.single j 1) i

theorem finiteLocalCoefficient_star
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (i j : ι) :
    finiteLocalCoefficient (star A) i j = star (finiteLocalCoefficient A j i) := by
  change (star A) (EuclideanSpace.single j 1) i = _
  rw [← EuclideanSpace.basisFun_inner]
  simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_conj_symm, ← EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_inner]
  rfl

end FiniteAmplification

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoisometryStateHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful state homogeneity from the constructed modular coisometries

This is the state homogeneity needed by the two-ratio product application;
no homogeneity theorem for arbitrary type III₁ factors is assumed.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance coisometryHomogeneityReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end
end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteWeakLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Completely bounded maps into a concrete von Neumann algebra have weak ultralimits. -/

namespace KadisonKastler

noncomputable section

open Filter Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance completeWeakOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteRowAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The scalar Hochschild differential of a bilinear cochain. -/
def cochainDifferential (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y z : A) : A :=
  x * f y z - f (x * y) z + f x (y * z) - f x y * z

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HermitianSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Separating a self-adjoint element from a closed star subalgebra

Hahn–Banach on the Banach-space quotient gives a norm-one functional
annihilating the source. Its Hermitian part still separates a self-adjoint
element. The compact annihilator ball then supplies an extreme separator.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def conjugateFunctional (f : B →L[ℂ] ℂ) : B →L[ℂ] ℂ where
  toFun b := star (f (star b))
  map_add' x y := by simp
  map_smul' c x := by simp
  cont := continuous_star.comp (f.continuous.comp continuous_star)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertSpaceLift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complex Hilbert structure on a universe lift -/

namespace KadisonKastler

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance hilbertULiftInner : InnerProductSpace ℂ (ULift.{v} H) where
  toNormedSpace := inferInstance
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner x.down
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.down y.down
  add_left x y z := InnerProductSpace.add_left x.down y.down z.down
  smul_left x y r := InnerProductSpace.smul_left x.down y.down r

theorem hilbertULift_separable [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (ULift.{v} H) :=
  DenseRange.separableSpace (α := H) (β := ULift.{v} H)
    (f := (LinearIsometryEquiv.ulift ℂ H).symm)
    (LinearIsometryEquiv.ulift ℂ H).symm.surjective.denseRange
    (LinearIsometryEquiv.ulift ℂ H).symm.continuous

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertSumIsometryMap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Applying coordinate isometries to a Hilbert sum -/

namespace KadisonKastler

noncomputable section

variable {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]

def hilbertSumIsometryMap (S : ∀ n, E n →ₗᵢ[ℂ] F n) : lp E 2 →ₗᵢ[ℂ] lp F 2 where
  toFun f := ⟨fun n => S n (f n), (lp.memℓp f).mono' (fun n => (S n).norm_map (f n) |>.le)⟩
  map_add' f g := by
    apply lp.ext
    funext n
    exact (S n).map_add (f n) (g n)
  map_smul' c f := by
    apply lp.ext
    funext n
    exact (S n).map_smul c (f n)
  norm_map' f := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun n => (S n).norm_map (f n) |>.le)
    · exact lp.norm_mono (by norm_num) (fun n => (S n).norm_map (f n) |>.symm.le)

@[simp] theorem hilbertSumIsometryMap_apply (S : ∀ n, E n →ₗᵢ[ℂ] F n)
    (f : lp E 2) (n : ℕ) : hilbertSumIsometryMap S f n = S n (f n) := rfl

theorem hilbertSumIsometryMap_range (S : ∀ n, E n →ₗᵢ[ℂ] F n) (g : lp F 2) :
    g ∈ LinearMap.range (hilbertSumIsometryMap S).toLinearMap ↔
      ∀ n, g n ∈ LinearMap.range (S n).toLinearMap := by
  constructor
  · rintro ⟨f, rfl⟩ n
    exact ⟨f n, rfl⟩
  · intro hg
    choose f hf using hg
    have he (n : ℕ) : S n (f n) = g n := hf n
    have hm : Memℓp f 2 := (lp.memℓp g).mono' (fun n => by
      rw [← (S n).norm_map, he n])
    refine ⟨⟨f, hm⟩, ?_⟩
    apply lp.ext
    funext n
    exact hf n

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometryRangeCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.unitalizedExtension_inr _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Coordinates from two isometric embeddings with the same range -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometry_adjoint_self_apply (J : E →ₗᵢ[ℂ] K) (v : E) :
    J.toContinuousLinearMap.adjoint (J v) = v :=
  congrArg (fun T : E →L[ℂ] E => T v) J.adjoint_comp_self

/-- The adjoint of the second embedding gives coordinates for the first. -/
def isometryRangeCoordinates (J : E →ₗᵢ[ℂ] K) (W : F →ₗᵢ[ℂ] K)
    (h : LinearMap.range J.toLinearMap = LinearMap.range W.toLinearMap) : E ≃ₗᵢ[ℂ] F := by
  let T : E →ₗᵢ[ℂ] F := {
    toLinearMap := (W.toContinuousLinearMap.adjoint.comp J.toContinuousLinearMap).toLinearMap
    norm_map' := by
      intro v
      obtain ⟨w, hw⟩ := show J v ∈ LinearMap.range W.toLinearMap from h ▸ ⟨v, rfl⟩
      have hw' : W w = J v := hw
      change ‖W.toContinuousLinearMap.adjoint (J v)‖ = ‖v‖
      rw [← hw', isometry_adjoint_self_apply]
      exact (W.norm_map w).symm.trans ((congrArg norm hw').trans (J.norm_map v)) }
  apply LinearIsometryEquiv.ofSurjective T
  intro w
  obtain ⟨v, hv⟩ := show W w ∈ LinearMap.range J.toLinearMap from h.symm ▸ ⟨w, rfl⟩
  refine ⟨v, ?_⟩
  have hv' : J v = W w := hv
  change W.toContinuousLinearMap.adjoint (J v) = w
  rw [hv', isometry_adjoint_self_apply]

omit [CompleteSpace E] in
@[simp] theorem isometryRangeCoordinates_apply (J : E →ₗᵢ[ℂ] K) (W : F →ₗᵢ[ℂ] K)
    (h : LinearMap.range J.toLinearMap = LinearMap.range W.toLinearMap) (v : E) :
    isometryRangeCoordinates J W h v = W.toContinuousLinearMap.adjoint (J v) := rfl

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) (J : E →ₗᵢ[ℂ] Lp H 2 μ) (P : X → H →L[ℂ] H)

theorem isometry_range_iff_field_fixed
    (hJ : ∀ f : Lp H 2 μ, isometricExtension J 1 f =ᵐ[μ] fun x => P x (f x))
    (f : Lp H 2 μ) :
    f ∈ LinearMap.range J.toLinearMap ↔ ∀ᵐ x ∂μ, P x (f x) = f x := by
  constructor
  · rintro ⟨v, rfl⟩
    have he : isometricExtension J 1 (J v) = J v := by
      simpa using isometricExtension_on_range J 1 v
    filter_upwards [hJ (J v)] with x hx
    rw [he] at hx
    exact hx.symm
  · intro hf
    refine ⟨J.toContinuousLinearMap.adjoint f, ?_⟩
    apply Lp.ext
    filter_upwards [hJ f, hf] with x hJx hx
    exact hJx.trans hx

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2LinearFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem isometryField_norm_bound (U : X → E →ₗᵢ[ℂ] F) :
    ∀ᵐ x ∂μ, ‖(U x).toContinuousLinearMap‖ ≤ 1 :=
  Eventually.of_forall fun x => (U x).norm_toContinuousLinearMap_le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2MeasurableRestriction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting L² vectors to a measurable stratum

The measure on a stratum is the comap of the restricted ambient measure.
The restriction operator uses the original representative and is contractive.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H]
  (μ : Measure X) (s : Set X) (hs : MeasurableSet s)

include hs

theorem l2RestrictMemLp (f : Lp H 2 μ) :
    MemLp (fun x : s => f x.val) 2 (Measure.comap ((↑) : s → X) μ) := by
  exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).comp_measurePreserving
    (measurePreserving_subtype_coe hs)

def l2Restrict (f : Lp H 2 μ) : Lp H 2 (Measure.comap ((↑) : s → X) μ) :=
  (l2RestrictMemLp μ s hs f).toLp (fun x : s => f x.val)

theorem l2Restrict_apply_ae (f : Lp H 2 μ) :
    l2Restrict μ s hs f =ᵐ[Measure.comap ((↑) : s → X) μ] fun x : s => f x.val :=
  MemLp.coeFn_toLp (l2RestrictMemLp μ s hs f)

theorem l2Restrict_norm_le (f : Lp H 2 μ) : ‖l2Restrict μ s hs f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  rw [eLpNorm_congr_ae (l2Restrict_apply_ae μ s hs f)]
  calc
    _ = eLpNorm f 2 (μ.restrict s) :=
      eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f).restrict
        (measurePreserving_subtype_coe hs)
    _ ≤ eLpNorm f 2 μ := eLpNorm_mono_measure f Measure.restrict_le_self

 theorem l2Restrict_add (f g : Lp H 2 μ) :
    l2Restrict μ s hs (f + g) = l2Restrict μ s hs f + l2Restrict μ s hs g := by
  apply Lp.ext
  have ha := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (Lp.coeFn_add f g))
  filter_upwards [l2Restrict_apply_ae μ s hs (f + g), l2Restrict_apply_ae μ s hs f,
    l2Restrict_apply_ae μ s hs g,
    Lp.coeFn_add (l2Restrict μ s hs f) (l2Restrict μ s hs g), ha] with x hsum hf hg hr ha
  simp only [Pi.add_apply] at hr ha
  rw [hsum, hr, hf, hg]
  exact ha

variable [NormedSpace ℂ H]

 theorem l2Restrict_smul (c : ℂ) (f : Lp H 2 μ) :
    l2Restrict μ s hs (c • f) = c • l2Restrict μ s hs f := by
  apply Lp.ext
  have ha := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (Lp.coeFn_smul c f))
  filter_upwards [l2Restrict_apply_ae μ s hs (c • f), l2Restrict_apply_ae μ s hs f,
    Lp.coeFn_smul c (l2Restrict μ s hs f), ha] with x hsmul hf hr ha
  simp only [Pi.smul_apply] at hr ha
  rw [hsmul, hr, hf]
  exact ha

/-- The contractive linear restriction map to a measurable stratum. -/
def l2Restriction : Lp H 2 μ →L[ℂ] Lp H 2 (Measure.comap ((↑) : s → X) μ) :=
  LinearMap.mkContinuous {
    toFun := l2Restrict μ s hs
    map_add' := l2Restrict_add μ s hs
    map_smul' := l2Restrict_smul μ s hs } 1 (by
      intro f
      change ‖l2Restrict μ s hs f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using l2Restrict_norm_le μ s hs f)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2MeasurableExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extension by zero from a measurable L² stratum -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H]
  (μ : Measure X) (s : Set X) (hs : MeasurableSet s)

def l2ExtensionFunction (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) (x : X) : H := by
  classical
  exact if hx : x ∈ s then f ⟨x, hx⟩ else 0

@[simp] theorem l2ExtensionFunction_coe
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) (x : s) :
    l2ExtensionFunction μ s f x.val = f x := by
  simp [l2ExtensionFunction, x.property]

 theorem indicator_l2ExtensionFunction
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    s.indicator (l2ExtensionFunction μ s f) = l2ExtensionFunction μ s f := by
  classical
  funext x
  by_cases hx : x ∈ s <;> simp [l2ExtensionFunction, hx]

include hs in
 theorem l2ExtensionMemLp (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    MemLp (l2ExtensionFunction μ s f) 2 μ := by
  have hm : MemLp (l2ExtensionFunction μ s f) 2 (μ.restrict s) := by
    rw [← map_comap_subtype_coe hs]
    apply (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff.mpr
    simpa only [Function.comp_def, l2ExtensionFunction_coe] using Lp.memLp f
  have hi := (memLp_indicator_iff_restrict hs).mpr hm
  rw [indicator_l2ExtensionFunction] at hi
  exact hi

def l2Extend (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) : Lp H 2 μ :=
  (l2ExtensionMemLp μ s hs f).toLp (l2ExtensionFunction μ s f)

 theorem l2Extend_apply_ae (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Extend μ s hs f =ᵐ[μ] l2ExtensionFunction μ s f :=
  MemLp.coeFn_toLp (l2ExtensionMemLp μ s hs f)

 theorem l2Extend_norm (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    ‖l2Extend μ s hs f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (l2Extend_apply_ae μ s hs f)]
  congr 1
  calc
    _ = eLpNorm (s.indicator (l2ExtensionFunction μ s f)) 2 μ := by
      rw [indicator_l2ExtensionFunction]
    _ = eLpNorm (l2ExtensionFunction μ s f) 2 (μ.restrict s) :=
      eLpNorm_indicator_eq_eLpNorm_restrict hs
    _ = eLpNorm ((l2ExtensionFunction μ s f) ∘ ((↑) : s → X)) 2
        (Measure.comap ((↑) : s → X) μ) := by
      rw [← map_comap_subtype_coe hs]
      exact (MeasurableEmbedding.subtype_coe hs).eLpNorm_map_measure
    _ = eLpNorm f 2 (Measure.comap ((↑) : s → X) μ) := by
      congr 1
      funext x
      exact l2ExtensionFunction_coe μ s f x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2StrataSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # L² as the Hilbert sum of measurable strata

Restriction and extension by zero identify the L² space on a countable
measurable partition with the Hilbert sum of its individual L² spaces.
-/

namespace KadisonKastler

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X)

variable {ι : Type*} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))

omit [InnerProductSpace ℂ H] in
theorem l2_eq_zero_of_restrictions [Countable ι] (hcover : ⋃ i, s i = Set.univ)
    (g : Lp H 2 μ) (hg : ∀ i, l2Restrict μ (s i) (hs i) g = 0) : g = 0 := by
  have hzero (i : ι) : ∀ᵐ x ∂μ, x ∈ s i → g x = 0 := by
    apply (ae_restrict_iff' (hs i)).mp
    apply (ae_restrict_iff_subtype (hs i)).mpr
    filter_upwards [l2Restrict_apply_ae μ (s i) (hs i) g,
      Lp.coeFn_zero (E := H) (p := 2) (Measure.comap ((↑) : s i → X) μ)] with x hx hz
    rw [hg i] at hx
    exact hx.symm.trans hz
  apply Lp.ext
  filter_upwards [eventually_countable_forall.mpr hzero,
    Lp.coeFn_zero (E := H) (p := 2) μ] with x hx hz
  rw [hz]
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
  exact hx i hi

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableProjectionFrame
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem measurable_gramSchmidt_sequence (v : X → ℕ → H)
    (hv : ∀ n, Measurable fun x => v x n) (n : ℕ) :
    Measurable fun x => gramSchmidt ℂ (v x) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp_rw [gramSchmidt_def ℂ _ n]
    simp_rw [Submodule.starProjection_singleton]
    apply (hv n).sub
    apply Finset.measurable_sum
    intro i hi
    have hm := ih i (Finset.mem_Iio.mp hi)
    exact ((hm.inner (hv n)).div
      (Complex.continuous_ofReal.measurable.comp (hm.norm.pow_const 2))).smul hm

theorem measurable_gramSchmidtNormed_sequence (v : X → ℕ → H)
    (hv : ∀ n, Measurable fun x => v x n) (n : ℕ) :
    Measurable fun x => gramSchmidtNormed ℂ (v x) n := by
  have hm := measurable_gramSchmidt_sequence v hv n
  exact ((Complex.continuous_ofReal.measurable.comp hm.norm).inv).smul hm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableHilbertCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurability of countable Hilbert coordinates

Coordinatewise measurability implies norm-Borel measurability in a countable
scalar Hilbert sum. Finite-coordinate sums give the required approximations.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace
open scoped Topology lp

noncomputable section

variable {I X : Type*} [Countable I]

/-- The scalar Hilbert coordinate space for a countable index set is separable. -/
theorem separable_scalarHilbertCoordinates : SeparableSpace ℓ²(I, ℂ) := by
  classical
  let b : HilbertBasis I ℂ ℓ²(I, ℂ) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs : IsSeparable (Submodule.span ℂ (Set.range b) : Set ℓ²(I, ℂ)) :=
    (Set.countable_range b).isSeparable.span
  have hd : closure (Submodule.span ℂ (Set.range b) : Set ℓ²(I, ℂ)) = Set.univ :=
    congrArg (fun S : Submodule ℂ ℓ²(I, ℂ) => (S : Set ℓ²(I, ℂ))) b.dense_span
  exact isSeparable_univ_iff.mp (hd ▸ hs.closure)

variable [MeasurableSpace X] [MeasurableSpace ℓ²(I, ℂ)] [BorelSpace ℓ²(I, ℂ)]

/-- A field of Hilbert coordinate vectors is measurable if each scalar coordinate is. -/
theorem measurable_hilbertCoordinates (f : X → ℓ²(I, ℂ))
    (hf : ∀ i, Measurable fun x => f x i) : Measurable f := by
  classical
  let : SeparableSpace ℓ²(I, ℂ) := separable_scalarHilbertCoordinates
  let g : Finset I → X → ℓ²(I, ℂ) := fun s x => ∑ i ∈ s, lp.single 2 i (f x i)
  apply measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset I)) (f := g)
  · intro s
    apply Finset.measurable_sum
    intro i _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : I => ℂ) 2 i).continuous.measurable.comp (hf i)
  · rw [tendsto_pi_nhds]
    intro x
    exact lp.hasSum_single ENNReal.ofNat_ne_top (f x)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Measurable columns make analysis in a variable range basis measurable. -/
theorem measurable_rangeHilbertCoordinates (P : X → H →L[ℂ] H)
    (B : ∀ x, HilbertBasis I ℂ (P x).range)
    (hB : ∀ i, Measurable fun x => (B x i : H))
    (v : ∀ x, (P x).range) (hv : Measurable fun x => (v x : H)) :
    Measurable fun x => (B x).repr (v x) := by
  apply measurable_hilbertCoordinates
  intro i
  simp only [HilbertBasis.repr_apply_apply]
  exact (hB i).inner hv

/- Measurable columns also make synthesis in a variable range basis measurable. -/
omit [MeasurableSpace ℓ²(I, ℂ)] [BorelSpace ℓ²(I, ℂ)] in
theorem measurable_rangeHilbertSynthesis (P : X → H →L[ℂ] H)
    (B : ∀ x, HilbertBasis I ℂ (P x).range)
    (hB : ∀ i, Measurable fun x => (B x i : H))
    (f : X → ℓ²(I, ℂ)) (hf : ∀ i, Measurable fun x => f x i) :
    Measurable fun x => ((B x).repr.symm (f x) : H) := by
  classical
  let g : Finset I → X → H := fun s x => ∑ i ∈ s, f x i • (B x i : H)
  apply measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset I)) (f := g)
  · intro s
    exact Finset.measurable_sum _ (fun i _ => (hf i).smul (hB i))
  · rw [tendsto_pi_nhds]
    intro x
    have ht := ((P x).range.subtypeL).hasSum ((B x).hasSum_repr_symm (f x))
    change HasSum (fun i : I => f x i • (B x i : H)) ((B x).repr.symm (f x) : H)
    simpa only [map_smul, Submodule.subtypeL_apply] using ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCoisometryBicentralizer
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar bicentralizers from the constructed modular coisometries

Only the fixed reference state is used. No state homogeneity, absorption
classification, or scalar-bicentralizer premise enters this implication.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance coisometryBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorCochainColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A completely bounded cochain contraction on the full operator algebra

The rank-one last column realizes the usual Hochschild contraction while
retaining its norm at every matrix level.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance cochainColumnOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance cochainColumnOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

def cochainColumn (φ : H →L[ℂ] ℂ) : H →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.smulRightL ℂ H H φ

omit [CompleteSpace H] in
@[simp] theorem cochainColumn_apply (φ : H →L[ℂ] ℂ) (x y : H) :
    cochainColumn φ x y = φ y • x := rfl

def cochainColumnEvaluation (φ : H →L[ℂ] ℂ) (ξ : H) :
    ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) →L[ℂ] (H →L[ℂ] H) :=
  (ContinuousLinearMap.compL ℂ H (H →L[ℂ] H) H (ContinuousLinearMap.apply ℂ H ξ)).comp
    ((ContinuousLinearMap.compL ℂ H (H →L[ℂ] H) (H →L[ℂ] H)).flip (cochainColumn φ))

@[simp] theorem cochainColumnEvaluation_apply (φ : H →L[ℂ] ℂ) (ξ : H)
    (F : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (y : H) :
    cochainColumnEvaluation φ ξ F y = F (cochainColumn φ y) ξ := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralBaseTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! The spectrum of a norm-separable commutative C-star algebra is a
compact metrizable base for its vector spectral measures. -/

noncomputable section
namespace KadisonSimilarity

variable (A : Type*) [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]

theorem characterSpace_secondCountable :
    SecondCountableTopology (WeakDual.characterSpace ℂ A) := by
  let : TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) :=
    characterSpace_metrizable A
  infer_instance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RankStratumStandardBorel
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner
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

variable {A B H : Type*}
  [CommCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B]
  [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
  {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankStandardCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
local instance rankStandardCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

theorem commonSpectralBase_standardBorel :
    StandardBorelSpace (WeakDual.characterSpace ℂ A) := by
  let : TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) := characterSpace_metrizable A
  let : MetricSpace (WeakDual.characterSpace ℂ A) := TopologicalSpace.metrizableSpaceMetric _
  let : SecondCountableTopology (WeakDual.characterSpace ℂ A) := characterSpace_secondCountable A
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularConvolutionCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem integral_inner_left {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℝ → E} (hF : Integrable F volume) (y : E) :
    (∫ t : ℝ, inner ℂ (F t) y) = inner ℂ (∫ t : ℝ, F t) y := by
  have h := congrArg (fun z : ℂ => star z) (integral_inner hF y)
  change (starRingEnd ℂ) (∫ t : ℝ, inner ℂ y (F t)) =
    (starRingEnd ℂ) (inner ℂ y (∫ t : ℝ, F t)) at h
  rw [← integral_conj] at h
  simpa only [inner_conj_symm] using h

theorem integrable_star_weight (w : ℝ → ℂ) (hw : Integrable w volume) :
    Integrable (fun t => star (w t)) volume := by
  apply hw.norm.mono' hw.aestronglyMeasurable.star
  filter_upwards [] with t
  change ‖star (w t)‖ ≤ ‖w t‖
  exact (norm_star (w t)).le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizationAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded Haar averages of localized operators

The translated-cutoff analysis map takes values in an actual Hilbert
space of square-integrable vectors. Sandwiching a constant amplification
by this map constructs the Haar average without requiring operator-norm
measurability.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)

theorem norm_frame_sandwich_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) (A : F →L[ℂ] F) (c d : ℝ)
    (hc : 0 ≤ c) (hV : ‖V‖ ≤ c) (hA : ‖A‖ ≤ d) :
    ‖V.adjoint.comp (A.comp V)‖ ≤ c ^ 2 * d := by
  have hadj : ‖V.adjoint‖ = ‖V‖ := ContinuousLinearMap.adjoint.norm_map V
  calc
    ‖V.adjoint.comp (A.comp V)‖ ≤ ‖V.adjoint‖ * (‖A‖ * ‖V‖) :=
      (V.adjoint.opNorm_comp_le (A.comp V)).trans
        (mul_le_mul_of_nonneg_left (A.opNorm_comp_le V) (norm_nonneg _))
    _ ≤ c * (d * c) := by
      rw [hadj]
      have hd : 0 ≤ d := (norm_nonneg A).trans hA
      exact mul_le_mul hV (mul_le_mul hA hV (norm_nonneg _) hd)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc
    _ = c ^ 2 * d := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularIntervalAverageEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The boundary estimate for interval localization

An integrable coefficient which equals its invariant value on the
interior interval and vanishes beyond the enlarged interval has an
error controlled by the fixed-width boundary strip.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

theorem regular_interval_boundary_estimate
    {A R C : ℝ} (hA : 0 ≤ A) (hR : A ≤ R) (hC : 0 ≤ C)
    (F : ℝ → ℂ) (hF : Integrable F volume) (c : ℂ)
    (hc : ‖c‖ ≤ C) (hb : ∀ r, ‖F r‖ ≤ C)
    (hinner : ∀ r, |r| + A ≤ R → F r = c)
    (houter : ∀ r, R + A < |r| → F r = 0) :
    ‖(∫ r : ℝ, F r) - (2 * R : ℝ) • c‖ ≤ 8 * A * C := by
  let I : Set ℝ := Set.Icc (-R + A) (R - A)
  let J : Set ℝ := Set.Icc (-R - A) (R + A)
  let B : Set ℝ := Set.Icc (-R) R
  let D : Set ℝ := J \ I
  have hRI : -R + A ≤ R - A := by linarith
  have hRJ : -R - A ≤ R + A := by linarith
  have hRB : -R ≤ R := by linarith
  have hIJ : I ⊆ J := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hIB : I ⊆ B := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hBJ : B ⊆ J := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hJfin : volume J ≠ ⊤ := by simp [J, Real.volume_Icc]
  have hBfin : volume B ≠ ⊤ := by simp [B, Real.volume_Icc]
  have hDfin : volume D < ⊤ := lt_top_iff_ne_top.mpr
    (measure_ne_top_of_subset Set.sdiff_subset hJfin)
  have hDmeas : MeasurableSet D := measurableSet_Icc.diff measurableSet_Icc
  have hDmass : (volume D).toReal = 4 * A := by
    change volume.real (J \ I) = _
    rw [measureReal_sdiff hIJ measurableSet_Icc hJfin]
    simp only [I, J, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal
      (sub_nonneg.mpr hRI), ENNReal.toReal_ofReal (sub_nonneg.mpr hRJ)]
    ring
  have hBmass : (volume B).toReal = 2 * R := by
    simp only [B, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hRB)]
    ring
  let E : ℝ → ℂ := fun r => F r - B.indicator (fun _ => c) r
  have hzero : ∀ r, r ∉ D → E r = 0 := by
    intro r hr
    by_cases hrI : r ∈ I
    · have habs : |r| + A ≤ R := by
        have ha : |r| ≤ R - A := abs_le.mpr
          ⟨by linarith [hrI.1], by linarith [hrI.2]⟩
        linarith
      simp only [E, hinner r habs, Set.indicator_of_mem (hIB hrI), sub_self]
    · have hrJ : r ∉ J := fun hj => hr ⟨hj, hrI⟩
      have habs : R + A < |r| := by
        by_contra hh
        have hh' := le_of_not_gt hh
        have he := abs_le.mp hh'
        exact hrJ ⟨by linarith [he.1], he.2⟩
      simp only [E, houter r habs, Set.indicator_of_notMem (fun hb => hrJ (hBJ hb)), sub_self]
  have hE : E = D.indicator E := by
    funext r
    by_cases hr : r ∈ D
    · exact (Set.indicator_of_mem hr E).symm
    · rw [Set.indicator_of_notMem hr, hzero r hr]
  have hbound : ∀ r, ‖E r‖ ≤ 2 * C := by
    intro r
    apply (norm_sub_le _ _).trans
    have hb' : ‖B.indicator (fun _ => c) r‖ ≤ C := by
      by_cases hr : r ∈ B
      · simpa only [Set.indicator_of_mem hr] using hc
      · simpa only [Set.indicator_of_notMem hr, norm_zero] using hC
    linarith [hb r, hb']
  have hnorm : ‖∫ r : ℝ, E r‖ ≤ 8 * A * C := by
    conv_lhs => rw [hE, integral_indicator hDmeas]
    have he := norm_setIntegral_le_of_norm_le_const_ae' hDfin
      (Eventually.of_forall fun r (_ : r ∈ D) => hbound r)
    change ‖∫ r in D, E r‖ ≤ _ at he
    rw [measureReal_def, hDmass] at he
    convert he using 1 <;> first | rfl | ring
  have hconst : Integrable (B.indicator fun _ => c) volume := by
    exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const hBfin)
  have hIntegral : (∫ r : ℝ, E r) = (∫ r : ℝ, F r) - (2 * R : ℝ) • c := by
    rw [integral_sub hF hconst, integral_indicator measurableSet_Icc, integral_const]
    rw [measureReal_def, Measure.restrict_apply_univ]
    rw [hBmass]
  rwa [hIntegral] at hnorm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketFubini
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integrability of the packet reconstruction kernel

An integrable weight in the packet variables and a translated `L²`
square give an integrable three-variable majorant. This justifies the
Fubini interchange in the finite packet reconstruction without assuming
bounded representatives of the Hilbert-space vectors.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem integrable_weighted_translate
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ) (hw : Integrable w μ)
    (k : X → ℝ) (hk : Measurable k)
    (g : ℝ → ℝ) (hg : Integrable g volume) (hgm : StronglyMeasurable g) :
    Integrable (fun p : X × ℝ => w p.1 * g (p.2 + k p.1))
      (μ.prod (volume : Measure ℝ)) := by
  have hm : AEStronglyMeasurable
      (fun p : X × ℝ => w p.1 * g (p.2 + k p.1))
      (μ.prod (volume : Measure ℝ)) :=
    hw.aestronglyMeasurable.comp_fst.mul
      (hgm.comp_measurable (measurable_snd.add (hk.comp measurable_fst))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [Function.comp_def] using
      ((measurePreserving_add_right (volume : Measure ℝ) (k x)).integrable_comp_of_integrable hg).const_mul (w x)
  · have he (x : X) :
        (∫ r : ℝ, ‖w x * g (r + k x)‖) = ‖w x‖ * ∫ r : ℝ, ‖g r‖ := by
      simp only [norm_mul]
      rw [integral_const_mul]
      congr 1
      exact integral_add_right_eq_self (fun r : ℝ => ‖g r‖) (k x)
    simp_rw [he]
    exact hw.norm.mul_const _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem inner_integrals (F G : ℝ → H)
    (hF : Integrable F volume) (hG : Integrable G volume) (A : H →L[ℂ] H) :
    inner ℂ (∫ q : ℝ, F q) (A (∫ u : ℝ, G u)) =
      ∫ q : ℝ, ∫ u : ℝ, inner ℂ (F q) (A (G u)) := by
  have hleft (y : H) :
      (∫ q : ℝ, inner ℂ (F q) y) = inner ℂ (∫ q : ℝ, F q) y := by
    have h := congrArg (fun z : ℂ => star z) (integral_inner hF y)
    change (starRingEnd ℂ) (∫ q : ℝ, inner ℂ y (F q)) =
      (starRingEnd ℂ) (inner ℂ y (∫ q : ℝ, F q)) at h
    rw [← integral_conj] at h
    simpa only [inner_conj_symm] using h
  rw [← hleft]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← A.integral_comp_comm hG, integral_inner (A.integrable_comp hG)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizedPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def regularSandwichLinear
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) : (F →L[ℂ] F) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun T := V.adjoint.comp (T.comp V)
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro x
    change V.adjoint (T (V x) + S (V x)) = V.adjoint (T (V x)) + V.adjoint (S (V x))
    exact map_add V.adjoint _ _
  map_smul' c T := by
    apply ContinuousLinearMap.ext
    intro x
    change V.adjoint (c • T (V x)) = c • V.adjoint (T (V x))
    exact map_smul V.adjoint c _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularWeakApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending bounded weak limits from cutoff vectors

Uniform operator bounds make matrix coefficients equicontinuous in each
test vector. Strongly convergent cutoff vectors therefore suffice for
identifying a weak operator limit.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem weak_tendsto_of_strong_cutoff_tests
    (A : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (P : ℕ → H →L[ℂ] H) (hP : ∀ x, Tendsto (fun k => P k x) atTop (𝓝 x))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C)
    (ht : ∀ k l x y, Tendsto (fun n => inner ℂ (P l y) (A n (P k x)))
      atTop (𝓝 (inner ℂ (P l y) (T (P k x)))))
    (x y : H) :
    Tendsto (fun n => inner ℂ y (A n x)) atTop (𝓝 (inner ℂ y (T x))) := by
  have hnorm (n : ℕ) (v : H) : ‖A n v‖ ≤ C * ‖v‖ :=
    ((A n).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg v))
  have heqY (v : H) : Equicontinuous (fun n : ℕ => fun w : H => inner ℂ w (A n v)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (NNReal.mk (C * ‖v‖) (mul_nonneg hC (norm_nonneg _)))
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, ← inner_sub_left, dist_eq_norm]
    change ‖inner ℂ (z - w) (A n v)‖ ≤ C * ‖v‖ * ‖z - w‖
    calc
      _ ≤ ‖z - w‖ * ‖A n v‖ := norm_inner_le_norm _ _
      _ ≤ ‖z - w‖ * (C * ‖v‖) := mul_le_mul_of_nonneg_left (hnorm n v) (norm_nonneg _)
      _ = _ := by ring
  have hy (k : ℕ) (w : H) :
      Tendsto (fun n => inner ℂ w (A n (P k x))) atTop
        (𝓝 (inner ℂ w (T (P k x)))) := by
    have hc := (heqY (P k x)).isClosed_setOfPred_tendsto (l := atTop)
      (show Continuous (fun w : H => inner ℂ w (T (P k x))) by fun_prop)
    exact hc.mem_of_tendsto (hP w) (Eventually.of_forall fun l => ht k l x w)
  have heqX : Equicontinuous (fun n : ℕ => fun v : H => inner ℂ y (A n v)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (NNReal.mk (C * ‖y‖) (mul_nonneg hC (norm_nonneg _)))
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm, ← inner_sub_right, ← map_sub, dist_eq_norm]
    change ‖inner ℂ y (A n (v - w))‖ ≤ C * ‖y‖ * ‖v - w‖
    calc
      _ ≤ ‖y‖ * ‖A n (v - w)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖v - w‖) := mul_le_mul_of_nonneg_left (hnorm n _) (norm_nonneg _)
      _ = _ := by ring
  have hc := heqX.isClosed_setOfPred_tendsto (l := atTop)
    (show Continuous (fun v : H => inner ℂ y (T v)) by fun_prop)
  exact hc.mem_of_tendsto (hP x) (Eventually.of_forall fun k => hy k y)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizationReconstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem complex_normalization_identity {r : ℝ} (hr : r ≠ 0) (x y : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) * x - y = r⁻¹ • (x - r • y) := by
  have hc : ((r⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
    norm_cast
    exact inv_mul_cancel₀ hr
  simp only [RCLike.real_smul_eq_coe_mul (K := ℂ)]
  change ((r⁻¹ : ℝ) : ℂ) * x - y = ((r⁻¹ : ℝ) : ℂ) * (x - (r : ℂ) * y)
  rw [mul_sub, ← mul_assoc, hc, one_mul]

universe u

end

end KadisonKastler

end OAI
end


