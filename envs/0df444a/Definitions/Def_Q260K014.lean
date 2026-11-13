-- Prove2me | Definitions.Def_Q260K014
-- name    : Q260K014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:45:58.979206+00:00
-- url     : https://prove2.me/theorems/3003b7c6-f26d-4283-be27-f15569dba2e5
-- title:
--   Definitions bundle Q260K014 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 40 definitions, 6 instances and 98 theorems. The definitions and types are `OAI.KadisonKastler.commonRankMeasure`, `OAI.KadisonKastler.commonRankSourceMeasure`, `OAI.KadisonKastler.commutantSupportOrder`, `OAI.KadisonKastler.completeWeakAlgebraOrder`, `OAI.KadisonKastler.completelyPositive_of_pointwise_weak_limit`, `OAI.KadisonKastler.compressedCoordinateMeasurable`, `OAI.KadisonKastler.concreteTraceLE`, `OAI.KadisonKastler.concreteTraceOrder`, `OAI.KadisonKastler.conjugatedBilinear`, `OAI.KadisonKastler.coordinateMeasurable`, `OAI.KadisonKastler.decodeStrongUnitary`, `OAI.KadisonKastler.diagonalPairAlgebra`, `OAI.KadisonKastler.diagonalPairEquiv`, `OAI.KadisonKastler.diagonalPairHom`, `OAI.KadisonKastler.encodeStrongUnitary`, `OAI.KadisonKastler.finiteL2Basis`, `OAI.KadisonKastler.finiteL2BasisVector`, `OAI.KadisonKastler.finiteLocalAmplification`, `OAI.KadisonKastler.finiteLocalAmplificationValue`, `OAI.KadisonKastler.pointedLocalVacuumProjection`, `OAI.KadisonKastler.pointedPowerAlgebra`, `OAI.KadisonKastler.pointedPowerFibreEquiv`, `OAI.KadisonKastler.pointedPowerInsertLinear`, `OAI.KadisonKastler.pointedPowerOperator`, `OAI.KadisonKastler.pointedPowerSite`, `OAI.KadisonKastler.pointedPowerSplit`, `OAI.KadisonKastler.pointedPowerSplitBasis`, `OAI.KadisonKastler.pointedRawLeftUnits`, `OAI.KadisonKastler.pointedRawRightUnits`, `OAI.KadisonKastler.polarTestOrder`, `OAI.KadisonKastler.projectionStratumAnalysis`, `OAI.KadisonKastler.rankFiberLift`, `OAI.KadisonKastler.regularTensorAlgebra`, `OAI.KadisonKastler.regularVectorMeasure`, `OAI.KadisonKastler.resolventCyclicIsometry`, `OAI.KadisonKastler.selfAdjointVectorImage`, `OAI.KadisonKastler.selfAdjointVectorInSpace`, `OAI.KadisonKastler.selfAdjointVectorMap`, `OAI.KadisonKastler.selfAdjointVectorSpace`, `OAI.KadisonKastler.wotSelfAdjointBall`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CharacterContinuity`, `KadisonKastler_CommonRankAlgebraFields`, `KadisonKastler_CommonRankCoordinates`, `KadisonKastler_CommonRankSourceModel`, `KadisonKastler_CommutantPolarSupport`, `KadisonKastler_CompleteWeakLimits`, `KadisonKastler_ConcreteTraceTransfer`, `KadisonKastler_DiagonalLocality`, `KadisonKastler_DiagonalPairAlgebra`, `KadisonKastler_FourierSwapIdentity`, `KadisonKastler_GeometricCorrectionScale`, `KadisonKastler_GraphCutScalarBounds`, `KadisonKastler_GraphLowCutScalars`, `KadisonKastler_GraphScaleFunctionalCalculus`, `KadisonKastler_HardyCauchyBoundary`, `KadisonKastler_L2FourierIntertwining`, `KadisonKastler_L2FourierNaturality`, `KadisonKastler_L2Intertwining`, `KadisonKastler_L2MeasurableExtension`, `KadisonKastler_L2ProjectionAnalysis`, `KadisonKastler_L2ProjectionSynthesis`, `KadisonKastler_LiftedRankStrata`, `KadisonKastler_ModularSpectralCuts`, `KadisonKastler_ModularStateCoefficients`, `KadisonKastler_MultiplicationNewtonStep`, `KadisonKastler_PointedLocalMatrix`, `KadisonKastler_PointedPowerConfigurations`, `KadisonKastler_PointedPowerCyclicity`, `KadisonKastler_PointedPowerMoments`, `KadisonKastler_PointedPowerOperators`, `KadisonKastler_ProductBoundaryCocycle`, `KadisonKastler_ProjectionStrataPartition`, `KadisonKastler_ProjectionStratumFields`, `KadisonKastler_RealLaplaceUniqueness`, `KadisonKastler_RegularCoreAlgebra`, `KadisonKastler_RegularCoreCharacters`, `KadisonKastler_RegularCoreCommutant`, `KadisonKastler_RegularPacketFubini`, `KadisonKastler_RegularPacketIntegrals`, `KadisonKastler_RepresentedCorner`, `KadisonKastler_ResolventContinuousCalculus`, `KadisonKastler_ResolventCyclicModel`, `KadisonKastler_ResolventMultiplierLimit`, `KadisonKastler_ResolventVectorMeasure`, `KadisonKastler_SelfAdjointPolarTest`, `KadisonKastler_SelfAdjointVectorCompactness`, `KadisonKastler_SelfAdjointVectorSpace`, `KadisonKastler_SpatialSeparability`, `KadisonKastler_SpectralVectorMeasure`, `KadisonKastler_StripAverageMembership`, `KadisonKastler_StripAverageUniqueness`, `KadisonKastler_StrongContractionLimits`, `KadisonKastler_StrongUnitaryEvaluation`, `KadisonKastler_TwoRatioParameters`, `KadisonKastler_WeakCPLimits`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K001`, `Q260K002`, `Q260K003`, `Q260K004`, `Q260K005`, `Q260K006` and `Q260K007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K019` and `Q260K020`; the statements `OAI.KadisonKastler.Conjugates.regularTensor`, `OAI.KadisonKastler.MatrixNearInclusion.regularTensor_gap`, `OAI_KadisonKastler_WeakOperatorField_exists_unitary_lift`, `OAI_KadisonKastler_centralPairDecomposition_of_rankModel`, `OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit`, `OAI.KadisonKastler.first_leg_field_of_product_centralizer` and `OAI.KadisonKastler.kkDistance_regularTensor_conjugate_le`; the proofs of `OAI.KadisonKastler.Conjugates.regularTensor`, `OAI.KadisonKastler.FullMatrixCorner.exists_injective_algebra_containing_entries`, `OAI.KadisonKastler.FullMatrixCorner.representedCorner_isII1`, `OAI.KadisonKastler.FullMatrixCorner.scalarMatrixAlgebra_isInjective`, `OAI.KadisonKastler.StandardTracialPosition.exists_ae_diagonal_unitary_comparison`, `OAI_KadisonKastler_commonRank_algebra_decompose`, `OAI_KadisonKastler_commonRank_commutant_decompose`, `OAI.KadisonKastler.cyclicOrbitAlgebra_commutant`, `OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit`, `OAI.KadisonKastler.exists_continuous_unital_transfer_of_traceDense`, `OAI.KadisonKastler.kkDistance_regularTensor_conjugate_le`, `OAI.KadisonKastler.multiplication_correction_of_quadratic_cochains`, `OAI.KadisonKastler.traceHull_mem_ball` and `OAI.KadisonKastler.unitary_transfer_bound_of_traceDense`.
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
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
import Definitions.Def_Q260K001
import Definitions.Def_Q260K002
import Definitions.Def_Q260K003
import Definitions.Def_Q260K004
import Definitions.Def_Q260K005
import Definitions.Def_Q260K006
import Definitions.Def_Q260K007

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong trace transfer in a concrete finite representation

A finite vector-functional formula for the trace is enough: weak
compactness of the positive operator ball and faithfulness prove the
uniform two-norm-to-strong implication. No transfer theorem is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance concreteTraceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance concreteTracePreorder_r69d4ad_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance concreteTraceLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [CompleteSpace H] [l.NeBot] [DecidableEq n] in
/-- Entrywise weak convergence gives weak convergence of each finite
operator-matrix amplification. -/
theorem hilbertMatrix_weak_limit (T : ι → CStarMatrix n n (H →L[ℂ] H))
    (S : CStarMatrix n n (H →L[ℂ] H))
    (ht : ∀ j k x y, Tendsto (fun i => inner ℂ y (T i j k x)) l
      (𝓝 (inner ℂ y (S j k x))))
    (x y : Generator.FiniteHilbert n H) :
    Tendsto (fun i => inner ℂ y (hilbertMatrix (T i) x)) l
      (𝓝 (inner ℂ y (hilbertMatrix S x))) := by
  have h := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_finsetSum Finset.univ (fun k _ => ht j k (x k) (y j)))
  simpa only [PiLp.inner_apply, hilbertMatrix_apply, inner_sum] using h

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A pointwise weak limit, once bundled linearly, is completely positive. -/
def completelyPositive_of_pointwise_weak_limit
    (F : ι → A →CP (H →L[ℂ] H)) (S : A →ₗ[ℂ] (H →L[ℂ] H))
    (ht : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
      (𝓝 (inner ℂ y (S a x)))) : A →CP (H →L[ℂ] H) where
  toLinearMap := S
  map_cstarMatrix_nonneg' k X hX := by
    let T (i : ι) := hilbertMatrix (X.map (F i))
    let R := hilbertMatrix (X.map S)
    have hT (i : ι) : (T i).IsPositive := by
      have hp := map_nonneg (hilbertMatrixHom (H := H) (n := Fin k))
        ((F i).map_cstarMatrix_nonneg X hX)
      change (T i - 0).IsPositive at hp
      simpa only [sub_zero] using hp
    have hconv (x y : Generator.FiniteHilbert (Fin k) H) :=
      hilbertMatrix_weak_limit (fun i => X.map (F i)) (X.map S)
        (fun j k x y => ht (X j k) x y) x y
    have hp := isPositive_of_weak_limit T R hT hconv
    have hp' : 0 ≤ R := by
      change (R - 0).IsPositive
      simpa only [sub_zero] using hp
    apply (NonUnitalStarAlgHom.map_le_map_iff
      (hilbertMatrixHom (H := H) (n := Fin k)) hilbertMatrixHom_injective).mp
    rw [map_zero]
    change (hilbertMatrix (X.map S) - 0).IsPositive
    simpa only [sub_zero] using hp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two-sided product boundary cocycle

Standard tracial conjugation turns the second copy into a commuting right
action. The resulting product cocycle is close to the product representation
with the explicit error `2 * δ + 2 * κ`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem conjugationOperator_sub (J : H ≃ₗᵢ⋆[ℂ] H) (a b : H →L[ℂ] H) :
    conjugationOperator J (a - b) = conjugationOperator J a - conjugationOperator J b := by
  ext ξ
  exact map_sub J _ _

omit [CompleteSpace H] in
theorem norm_conjugationOperator_sub (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (a b : H →L[ℂ] H) :
    ‖conjugationOperator J a - conjugationOperator J b‖ = ‖a - b‖ := by
  rw [← conjugationOperator_sub, norm_conjugationOperator J hJ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongContractionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- No convergence is assumed away from the fixed dense sequence. -/
theorem exists_strong_limit_of_dense_contractions (ξ : ℕ → H) (hξ : DenseRange ξ)
    (A : ℕ → H →L[ℂ] H) (hA : ∀ n, ‖A n‖ ≤ 1)
    (h : ∀ j, CauchySeq (fun n => A n (ξ j))) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ 1 ∧
      ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)) := by
  have hc (x : H) := cauchySeq_apply_of_dense_contractions ξ hξ A hA h x
  choose f hf using fun x => cauchy_map_iff_exists_tendsto.mp (hc x)
  have hb (x : H) : ‖f x‖ ≤ ‖x‖ := by
    apply le_of_tendsto (hf x).norm
    exact Eventually.of_forall fun n => ((A n).le_opNorm x).trans
      (by simpa using mul_le_mul_of_nonneg_right (hA n) (norm_nonneg x))
  let L : H →ₗ[ℂ] H :=
    { toFun := f
      map_add' := fun x y => by
        have ht := (hf x).add (hf y)
        simp only [← map_add] at ht
        exact tendsto_nhds_unique (hf (x + y)) ht
      map_smul' := fun c x => by
        have ht := (hf x).const_smul c
        simp only [← map_smul] at ht
        exact tendsto_nhds_unique (hf (c • x)) ht }
  have hL (x : H) : ‖L x‖ ≤ 1 * ‖x‖ := by
    change ‖f x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using hb x
  let T := L.mkContinuous 1 hL
  refine ⟨T, T.opNorm_le_bound zero_le_one (fun x => ?_), hf⟩
  change ‖f x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using hb x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongUnitaryEvaluation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.strongUnitarySpaceMeasurable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Evaluation on the strong-star Polish unitary model -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def encodeStrongUnitary (ξ : ℕ → H) (u : unitary (H →L[ℂ] H)) : StrongUnitarySpace ξ :=
  ⟨unitaryCoordinates ξ u, ⟨u, rfl⟩⟩

def decodeStrongUnitary (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    unitary (H →L[ℂ] H) := Classical.choose p.property

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCharacters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Character multiplication in the regular core representation

The operators `Q_a` are actual multiplication unitaries on `L²(ℝ,H)`.
Their covariance with translations and their commutation with `π(B(H))`
are proved on representatives. These are the generator identities in
the dual-character argument of Section 8.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacterScalar_add_right (a t s : ℝ) :
    regularCharacterScalar a (t + s) =
      regularCharacterScalar a t * regularCharacterScalar a s := by
  simp only [regularCharacterScalar, mul_add, Circle.exp_add, Circle.coe_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CharacterContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem modularSpectralPhase_eq_character (s t : ℝ) :
    modularSpectralPhase t s = regularCharacterScalar (resolventLogFrequency s) t := by
  change Complex.exp (Complex.I * ((t : ℂ) * (resolventLogFrequency s : ℂ))) =
    Complex.exp (((resolventLogFrequency s * t : ℝ) : ℂ) * Complex.I)
  rw [Complex.ofReal_mul]
  congr 1
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2MeasurableExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

variable [NormedSpace ℂ H]

include hs in
theorem l2ExtensionFunction_smul_ae (c : ℂ)
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2ExtensionFunction μ s (c • f) =ᵐ[μ]
      fun x => c • l2ExtensionFunction μ s f x := by
  apply ae_of_subtype_of_outside μ s hs
  · filter_upwards [Lp.coeFn_smul c f] with x hx
    simpa only [l2ExtensionFunction_coe, Pi.smul_apply] using hx
  · intro x hx
    simp [l2ExtensionFunction, hx]

theorem l2Extend_smul (c : ℂ) (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Extend μ s hs (c • f) = c • l2Extend μ s hs f := by
  apply Lp.ext
  filter_upwards [l2Extend_apply_ae μ s hs (c • f), l2Extend_apply_ae μ s hs f,
    Lp.coeFn_smul c (l2Extend μ s hs f),
    l2ExtensionFunction_smul_ae μ s hs c f] with x hcf hf ha he
  simp only [Pi.smul_apply] at ha
  rw [hcf, ha, hf]
  exact he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2ProjectionSynthesis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def projectionStratumAnalysis (n : ℕ) (x : projectionRankStratum P b n) :
    H →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ) :=
  (projectionStratumCoordinates P hP b hb n x).toLinearIsometry.toContinuousLinearMap.comp
    (P x.val).rangeRestrict

theorem projectionStratumAnalysis_apply_norm_le (n : ℕ)
    (x : projectionRankStratum P b n) (v : H) :
    ‖projectionStratumAnalysis P hP b hb n x v‖ ≤ ‖P x.val‖ * ‖v‖ := by
  change ‖projectionStratumCoordinates P hP b hb n x ((P x.val).rangeRestrict v)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (P x.val).le_opNorm v

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2ProjectionAnalysis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance coordinateMeasurable (n : ℕ) : MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  borel _
local instance coordinateBorel (n : ℕ) : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩

omit [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H] in
include hPn in
theorem projectionStratumAnalysis_norm_le (n : ℕ) (x : projectionRankStratum P b n) :
    ‖projectionStratumAnalysis P hP b hb n x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  exact (projectionStratumAnalysis_apply_norm_le P hP b hb n x v).trans
    (mul_le_mul_of_nonneg_right (hPn x.val) (norm_nonneg v))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStrataPartition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The measurable partition by projection rank -/

namespace KadisonKastler

noncomputable section

variable {X : Type*}

theorem frameDimensionStratum_unique (p : X → ℕ → Prop) {x : X} {i j : ℕ}
    (hi : x ∈ frameDimensionStratum p i) (hj : x ∈ frameDimensionStratum p j) : i = j := by
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ n => exact (hj.2 (hi n)).elim
  | succ n =>
    cases j with
    | zero => exact (hi.2 (hj n)).elim
    | succ m =>
      congr 1
      by_contra hnm
      rcases lt_or_gt_of_ne hnm with hlt | hgt
      · exact hi.2 (hj.1 n hlt)
      · exact hj.2 (hi.1 m hgt)

theorem frameDimensionStratum_pairwise (p : X → ℕ → Prop) :
    Pairwise fun i j => Disjoint (frameDimensionStratum p i) (frameDimensionStratum p j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (frameDimensionStratum_unique p hi hj)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (P : X → H →L[ℂ] H) (b : ℕ → H)

theorem projectionRankStratum_pairwise :
    Pairwise fun i j => Disjoint (projectionRankStratum P b i) (projectionRankStratum P b j) :=
  frameDimensionStratum_pairwise _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStratumFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance compressedCoordinateMeasurable (n : ℕ) : MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  borel _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankCoordinates
attribute [-instance] _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

attribute [local instance] OAI.KadisonKastler.rankModelCoordinateMeasurable
local instance rankModelCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankSourceModel
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

abbrev commonRankSourceMeasure := projectionStratumMeasure
  (H := ScalarHilbertCoordinates D.generators) (cyclicCommonBaseMeasure π D)
  (commonModelProjection M) (commonRankBasis π D)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RepresentedCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete compression to a common closed subspace

The corner acts on the subspace itself. Its operators are characterized by
membership of their extension by zero in the original von Neumann algebra.
This constructs the actual corner and proves that a common compression does
not increase Kadison--Kastler distance.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem cornerExtension_compression (T : H →L[ℂ] H) :
    cornerExtension E (cornerCompression E T) = E.starProjection * T * E.starProjection := by
  ext x
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem graphScaleScalar_pos {c s : ℝ} (hc : c ≠ 0) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < graphScaleScalar c s := by
  unfold graphScaleScalar
  by_cases hz : s = 0
  · simpa only [hz, sub_zero, mul_one, zero_add] using sq_pos_of_ne_zero hc
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hs (Ne.symm hz))
      (mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hs1))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphCutScalarBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem graphHighInverseScalar_nonneg {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) : 0 ≤ graphHighInverseScalar c r s := by
  have hm : 0 ≤ min s r := le_min hs hr
  have hm1 : min s r < 1 := (min_le_right s r).trans_lt hr1
  exact div_nonneg (graphScaleScalar_pos hc hm hm1.le).le
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hm1.le))

theorem graphHighInverseScalar_cut_identity {c r s : ℝ} (hc : c ≠ 0)
    (hr1 : r < 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (((1 - s / graphScaleScalar c s) * graphHighInverseScalar c r s) - 1) *
      max (r - s) 0 = 0 := by
  by_cases hsr : s < r
  · have hq := (graphScaleScalar_pos hc hs hs1).ne'
    have hd : c ^ 2 * (1 - s) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hc) (ne_of_gt (sub_pos.mpr (hsr.trans hr1)))
    rw [graphHighInverseScalar, min_eq_left hsr.le]
    have he : (1 - s / graphScaleScalar c s) *
        (graphScaleScalar c s / (c ^ 2 * (1 - s))) = 1 := by
      field_simp [hq, pow_ne_zero _ hc, (sub_pos.mpr (hsr.trans hr1)).ne']
      unfold graphScaleScalar
      ring
    rw [he, sub_self, zero_mul]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hsr)), mul_zero]

theorem graphHighInverse_bound_exp (a : ℝ) :
    graphScaleScalar (Real.exp (-a / 2)) ((1 + Real.exp (a + 1 / 2))⁻¹) /
      (Real.exp (-a / 2) ^ 2 * (1 - (1 + Real.exp (a + 1 / 2))⁻¹)) =
      1 + Real.exp (-(1 / 2 : ℝ)) := by
  have he : Real.exp (-a) * Real.exp (a + 1 / 2) = Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhalf : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hp : 1 + Real.exp (a + 1 / 2) ≠ 0 := by positivity
  have hd : Real.exp (-a) * (1 - (1 + Real.exp (a + 1 / 2))⁻¹) ≠ 0 := by
    apply mul_ne_zero (Real.exp_ne_zero _)
    exact ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith [Real.exp_pos (a + 1 / 2)])))
  unfold graphScaleScalar
  rw [graphScale_exp_square]
  apply (div_eq_iff hd).mpr
  field_simp
  have harg : (a * 2 + 1) / 2 = a + 1 / 2 := by ring
  have hprod : Real.exp (-a) * Real.exp ((a * 2 + 1) / 2) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
    rw [harg, he, mul_comm, hhalf]
  nlinarith [hprod]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSpectralCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem mul_resolventLowerCut_eq_zero (R A : H →L[ℂ] H) (r : ℝ)
    (h : A * resolventCutGenerator R r = 0) : A * resolventLowerCut R r = 0 := by
  have hs : (resolventCutGenerator R r).range.topologicalClosure ≤ A.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact congrArg (fun T : H →L[ℂ] H => T x) h
    · exact A.isClosed_ker
  ext x
  exact hs ((resolventCutGenerator R r).range.topologicalClosure.starProjection_apply_mem x)

theorem modularCutThreshold_pos (a : ℝ) : 0 < modularCutThreshold a := by
  unfold modularCutThreshold
  positivity

theorem modularCutThreshold_lt_one (a : ℝ) : modularCutThreshold a < 1 := by
  unfold modularCutThreshold
  exact inv_lt_one_of_one_lt₀ (by linarith [Real.exp_pos a])

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphLowCutScalars
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem graphComplementScalar_nonneg {c s : ℝ} (hc : c ≠ 0) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ graphComplementScalar c s := by
  apply sub_nonneg.mpr
  apply (div_le_one (graphScaleScalar_pos hc hs hs1)).mpr
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs1))

theorem graphComplementScalar_difference {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    graphComplementScalar c s - graphComplementScalar c r =
      graphLowFactorScalar c r s * (r - s) := by
  have hs0 := (graphScaleScalar_pos hc hs hs1).ne'
  have hr0 := (graphScaleScalar_pos hc hr hr1).ne'
  unfold graphComplementScalar graphLowFactorScalar
  field_simp
  unfold graphScaleScalar
  ring

theorem graphComplementScalar_clipping {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    graphComplementScalar c s - min (graphComplementScalar c s) (graphComplementScalar c r) =
      graphLowFactorScalar c r s * max (r - s) 0 := by
  have hd := graphComplementScalar_difference hc hr hr1 hs hs1
  have hf : 0 ≤ graphLowFactorScalar c r s := div_nonneg (sq_nonneg _)
    (mul_nonneg (graphScaleScalar_pos hc hs hs1).le (graphScaleScalar_pos hc hr hr1).le)
  rcases le_total s r with hsr | hrs
  · have hg : graphComplementScalar c r ≤ graphComplementScalar c s := by
      apply sub_nonneg.mp
      rw [hd]
      exact mul_nonneg hf (sub_nonneg.mpr hsr)
    rw [min_eq_right hg, max_eq_left (sub_nonneg.mpr hsr), hd]
  · have hg : graphComplementScalar c s ≤ graphComplementScalar c r := by
      apply sub_nonpos.mp
      rw [hd]
      exact mul_nonpos_of_nonneg_of_nonpos hf (sub_nonpos.mpr hrs)
    rw [min_eq_left hg, sub_self, max_eq_right (sub_nonpos.mpr hrs), mul_zero]

theorem graphComplementScalar_logistic {c b : ℝ} (hc : c ≠ 0) :
    graphComplementScalar c ((1 + Real.exp b)⁻¹) =
      c ^ 2 * Real.exp b / (1 + c ^ 2 * Real.exp b) := by
  have hp : 0 < (1 + Real.exp b)⁻¹ := by positivity
  have hp1 : (1 + Real.exp b)⁻¹ ≤ 1 :=
    (inv_lt_one_of_one_lt₀ (by linarith [Real.exp_pos b])).le
  have hq := (graphScaleScalar_pos hc hp.le hp1).ne'
  have hne : 1 + c ^ 2 * Real.exp b ≠ 0 := by positivity
  have hsum : 1 + Real.exp b ≠ 0 := by positivity
  unfold graphComplementScalar
  apply (eq_div_iff hne).mpr
  field_simp
  unfold graphScaleScalar
  field_simp [hne, hsum]
  ring

theorem graphComplementScalar_exp (a : ℝ) :
    graphComplementScalar (Real.exp (-a / 2)) ((1 + Real.exp (a - 1 / 2))⁻¹) =
      Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ))) := by
  rw [graphComplementScalar_logistic (Real.exp_ne_zero _), graphScale_exp_square]
  have he : Real.exp (-a) * Real.exp (a - 1 / 2) = Real.exp (-(1 / 2 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventVectorMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar vector measures of the bounded Tomita resolvent

The real continuous functional calculus, tested on one Hilbert vector,
is a positive functional. Riesz representation supplies the finite measure
needed to compare the modular phases and their spectral cuts.
-/

namespace KadisonKastler

open MeasureTheory
open scoped CompactlySupported

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance resolventVectorMeasure_finite (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    IsFiniteMeasure (resolventVectorMeasure R hR x) := by
  unfold resolventVectorMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem resolventVectorMeasure_integral (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℝ)) :
    (∫ s, f s ∂resolventVectorMeasure R hR x) =
      (inner ℂ x ((cfcHom hR f) x)).re := by
  exact RealRMK.integral_rieszMeasure (resolventVectorFunctional R hR x)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventContinuousCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem resolventContinuousVector_norm_sq (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℂ)) :
    ‖resolventContinuousVector R hR x f‖ ^ 2 =
      ∫ s, ‖f s‖ ^ 2 ∂resolventVectorMeasure R hR x := by
  let g : C(spectrum ℝ R, ℝ) := ⟨fun s => ‖f s‖ ^ 2, f.continuous.norm.pow 2⟩
  have hg : (⟨fun s => (g s : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ :
      C(spectrum ℝ R, ℂ)) = star f * f := by
    ext s
    change ((‖f s‖ ^ 2 : ℝ) : ℂ) = star (f s) * f s
    have hn := RCLike.conj_mul (f s)
    change star (f s) * f s = (‖f s‖ : ℂ) ^ 2 at hn
    rw [Complex.ofReal_pow]
    exact hn.symm
  have hop := resolventContinuousCalculus_ofReal R hR g
  rw [hg, map_mul, map_star] at hop
  have hi := resolventVectorMeasure_integral R hR x g
  rw [← hop] at hi
  change (∫ s, ‖f s‖ ^ 2 ∂resolventVectorMeasure R hR x) =
    RCLike.re (inner ℂ x ((star (resolventContinuousCalculus R hR f) *
      resolventContinuousCalculus R hR f) x)) at hi
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq] at hi
  exact hi.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCyclicModel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A cyclic spectral isometry for the bounded resolvent

Continuous spectral functions are dense in the scalar L2 space. Their
functional-calculus vectors have exactly the same norm, so the map
extends to an isometry into the original Hilbert space.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventContinuousVector_norm_L2 (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℂ)) :
    ‖resolventContinuousVector R hR x f‖ =
      ‖ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f‖ := by
  let μ := resolventVectorMeasure R hR x
  let v : ResolventCyclicL2 R hR x := ContinuousMap.toLp 2 μ ℂ f
  have hi := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) v v)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)] at hi
  simp only [inner_self_eq_norm_sq] at hi
  have he : (∫ s, ‖v s‖ ^ 2 ∂μ) = ∫ s, ‖f s‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f] with s hs
    rw [show v s = f s from hs]
  rw [he] at hi
  have hn := resolventContinuousVector_norm_sq R hR x f
  change ‖resolventContinuousVector R hR x f‖ = ‖v‖
  nlinarith [norm_nonneg (resolventContinuousVector R hR x f), norm_nonneg v]

def resolventCyclicIsometry (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    ResolventCyclicL2 R hR x →ₗᵢ[ℂ] H :=
  (resolventContinuousVector R hR x).extendOfIsometry
    (e := (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ).toLinearMap)
    (ContinuousMap.toLp_denseRange ℂ (p := 2) (resolventVectorMeasure R hR x) ℂ (by norm_num))
    (resolventContinuousVector_norm_L2 R hR x)

theorem resolventCyclicIsometry_continuous (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℂ)) :
    resolventCyclicIsometry R hR x (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f) =
      resolventContinuousCalculus R hR f x :=
  LinearMap.extendOfIsometry_eq _ _ _ f

theorem resolventCyclicIsometry_one (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    resolventCyclicIsometry R hR x
      (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ (1 : C(spectrum ℝ R, ℂ))) = x := by
  rw [resolventCyclicIsometry_continuous, map_one, one_apply_eq_self]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventMultiplierLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem resolventCyclic_integral_norm_sq (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    (∫ s, ‖v s‖ ^ 2 ∂resolventVectorMeasure R hR x) = ‖v‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) v v)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)] at h
  simpa only [inner_self_eq_norm_sq] using h.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2FourierNaturality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem l2ScalarSwap_fourier {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ)) :
    l2ScalarSwap volume μ (𝓕 F) =
      (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (l2ScalarSwap volume μ F) := by
  let L := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  refine (l2TensorEmbedding_dense volume).induction_on
    (p := fun F => l2ScalarSwap volume μ (𝓕 F) = L.compLp (l2ScalarSwap volume μ F)) F ?_ ?_
  · exact isClosed_eq ((l2ScalarSwap volume μ).continuous.comp
      (Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ)).continuous)
      ((L.compLpL 2 μ).continuous.comp (l2ScalarSwap volume μ).continuous)
  · intro z
    induction z using OAI.tensorInductionOn with
    | tmul f x =>
        change l2ScalarSwap volume μ (𝓕 (scalarLpTensor volume f x)) =
          L.compLp (l2ScalarSwap volume μ (scalarLpTensor volume f x))
        rw [fourier_scalarLpTensor, l2ScalarSwap_tensor, l2ScalarSwap_tensor,
          compLp_scalarLpTensor]
        rfl
    | add z w hz hw =>
        change l2ScalarSwap volume μ ((Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ))
          (l2TensorEmbedding volume z)) = _ at hz
        change l2ScalarSwap volume μ ((Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ))
          (l2TensorEmbedding volume w)) = _ at hw
        have hadd (a b : Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 μ) :
            L.compLp (a + b) = L.compLp a + L.compLp b := (L.compLpL 2 μ).map_add a b
        change l2ScalarSwap volume μ ((Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ))
          (l2TensorEmbedding volume (z + w))) = _
        simpa only [map_add, hadd] using congrArg₂ (· + ·) hz hw

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2Intertwining
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem compLp_fourierInv (L : H →L[ℂ] K) (f : RegularCoreHilbert H) :
    L.compLp ((Lp.fourierTransformₗᵢ ℝ H).symm f) =
      (Lp.fourierTransformₗᵢ ℝ K).symm (L.compLp f) := by
  apply (Lp.fourierTransformₗᵢ ℝ K).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := fourier_compLp L ((Lp.fourierTransformₗᵢ ℝ H).symm f)
  change (Lp.fourierTransformₗᵢ ℝ K) (L.compLp ((Lp.fourierTransformₗᵢ ℝ H).symm f)) =
    L.compLp ((Lp.fourierTransformₗᵢ ℝ H) ((Lp.fourierTransformₗᵢ ℝ H).symm f)) at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The concrete tensor algebra, specified by its constant commutant. -/
def regularTensorAlgebra (P : VonNeumannAlgebra H) :
    VonNeumannAlgebra (RegularCoreHilbert H) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (regularConstantHom volume '' (P.commutant : Set (H →L[ℂ] H)))
  centralizer_centralizer' := by
    let S : Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
      regularConstantHom volume '' (P.commutant : Set (H →L[ℂ] H))
    change (S ∪ star S).centralizer.centralizer.centralizer =
      (S ∪ star S).centralizer
    exact Set.centralizer_centralizer_centralizer _

theorem mem_regularTensorAlgebra_iff (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    T ∈ regularTensorAlgebra P ↔ ∀ z ∈ P.commutant,
      regularConstantHom volume z * T = T * regularConstantHom volume z := by
  change T ∈ StarSubalgebra.centralizer ℂ
    (regularConstantHom volume '' (P.commutant : Set (H →L[ℂ] H))) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h z hz
    exact (h _ ⟨z, hz, rfl⟩).1
  · rintro h g ⟨z, hz, hzg⟩
    subst g
    refine ⟨h z hz, ?_⟩
    have hs : regularConstantHom (volume : Measure ℝ) (star z) =
        star (regularConstantHom (volume : Measure ℝ) z) :=
      StarHomClass.map_star (regularConstantHom (H := H) (volume : Measure ℝ)) z
    simpa only [hs] using h (star z) (star_mem hz)

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem generatedAlgebra_le_of_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : StarSubalgebra ℂ (K →L[ℂ] K)) (B : VonNeumannAlgebra K)
    (h : (A : Set (K →L[ℂ] K)) ⊆ B) : generatedVonNeumannAlgebra A ≤ B := by
  intro T hT
  rw [← SetLike.mem_coe, generatedVonNeumannAlgebra_coe] at hT
  have hc := Set.centralizer_subset (Set.centralizer_subset h)
  have hmem := hc hT
  change T ∈ (B : Set (K →L[ℂ] K))
  simpa only [VonNeumannAlgebra.centralizer_centralizer] using hmem

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierSwapIdentity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem fourier_swap_identity (μ : Measure X)
    (A C : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ) →L[ℂ] Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ))
    (B D : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ)
    (hA : ∀ F, l2ScalarSwap volume μ (A F) = B (l2ScalarSwap volume μ F))
    (hC : ∀ F, l2ScalarSwap volume μ (C F) = D (l2ScalarSwap volume μ F))
    (hBD : ∀ F, (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp (B F) =
      D ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp F))
    (F : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ)) :
    𝓕 (A F) = C (𝓕 F) := by
  apply (l2ScalarSwap volume μ).injective
  rw [l2ScalarSwap_fourier, hA, hBD, ← l2ScalarSwap_fourier, hC]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2FourierIntertwining
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting Fourier conjugacy through a bounded intertwiner -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem fourier_intertwines_of_transport (L : H →L[ℂ] K)
    (A B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (C D : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
    (hA : ∀ F, L.compLp (A F) = C (L.compLp F))
    (hB : ∀ F, L.compLp (B F) = D (L.compLp F))
    (hAB : ∀ F, (𝓕 (A F) : RegularCoreHilbert H) = B (𝓕 F)) (F : RegularCoreHilbert H) :
    (𝓕 (C (L.compLp F)) : RegularCoreHilbert K) = D (𝓕 (L.compLp F)) := by
  calc
    _ = 𝓕 (L.compLp (A F)) := congrArg (fun W : RegularCoreHilbert K => 𝓕 W) (hA F).symm
    _ = L.compLp (𝓕 (A F)) := fourier_compLp L (A F)
    _ = L.compLp (B (𝓕 F)) := congrArg L.compLp (hAB F)
    _ = D (L.compLp (𝓕 F)) := hB (𝓕 F)
    _ = _ := congrArg D (fourier_compLp L F).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStateCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem productVectorState_conjugate_left (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) (x y : H →L[ℂ] H) :
    productVectorState Ω (unitaryConj u x * y) =
      inner ℂ (star x Ω) (star (u : H →L[ℂ] H) (y Ω)) := by
  change inner ℂ Ω ((u : H →L[ℂ] H) (x (star (u : H →L[ℂ] H) (y Ω)))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (u : H →L[ℂ] H) Ω) (x (star (u : H →L[ℂ] H) (y Ω))) = _
  rw [star_unitary_fixes Ω u hfix]
  exact (ContinuousLinearMap.adjoint_inner_left x _ Ω).symm

theorem productVectorState_conjugate_right (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) (x y : H →L[ℂ] H) :
    productVectorState Ω (y * unitaryConj u x) =
      inner ℂ (star y Ω) ((u : H →L[ℂ] H) (x Ω)) := by
  change inner ℂ Ω (y ((u : H →L[ℂ] H) (x (star (u : H →L[ℂ] H) Ω)))) = _
  rw [star_unitary_fixes Ω u hfix]
  exact (ContinuousLinearMap.adjoint_inner_left y _ Ω).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointVectorSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

attribute [local instance] OAI.KadisonKastler.selfAdjointSpaceReal
def selfAdjointVectorMap (M : VonNeumannAlgebra H) (Ω : H) :
    selfAdjoint (Algebra M) →ₗ[ℝ] H where
  toFun a := a.val.val Ω
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def selfAdjointVectorSpace (M : VonNeumannAlgebra H) (Ω : H) : Submodule ℝ H :=
  (selfAdjointVectorMap M Ω).range.topologicalClosure

instance selfAdjointVectorSpace_complete (M : VonNeumannAlgebra H) (Ω : H) :
    CompleteSpace (selfAdjointVectorSpace M Ω) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def selfAdjointVectorInSpace (M : VonNeumannAlgebra H) (Ω : H)
    (a : selfAdjoint (Algebra M)) : selfAdjointVectorSpace M Ω :=
  ⟨selfAdjointVectorMap M Ω a, Submodule.le_topologicalClosure _ ⟨a, rfl⟩⟩

theorem selfAdjointVectorInSpace_dense (M : VonNeumannAlgebra H) (Ω : H) :
    DenseRange (selfAdjointVectorInSpace M Ω) := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  have hx := x.property
  change x.val ∈ closure (Set.range (selfAdjointVectorMap M Ω)) at hx
  obtain ⟨v, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hx ε hε
  exact ⟨a, ha⟩

theorem inner_selfAdjointVector_projection (M : VonNeumannAlgebra H) (Ω : H)
    (a : selfAdjoint (Algebra M)) (v : H) :
    inner ℝ (selfAdjointVectorMap M Ω a) ((selfAdjointVectorSpace M Ω).starProjection v) =
      inner ℝ (selfAdjointVectorMap M Ω a) v := by
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (selfAdjointVectorInSpace M Ω a) v

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointPolarTest
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The polar support test for self-adjoint vectors

The positive spectral support gives a self-adjoint unitary whose pairing
with a self-adjoint operator is the sum of its positive and negative parts.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance polarTestOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance polarTestPreorder_r69d4ad_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance polarTestLE_r69d4ad_1 : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance polarTestStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem selfAdjoint_polar_test (x : Algebra M) (hx : IsSelfAdjoint x) :
    ∃ u : Algebra M, IsSelfAdjoint u ∧ ‖u‖ ≤ 1 ∧
      u * x = x⁺ + x⁻ ∧ x * u = x⁺ + x⁻ := by
  let p := positiveSupport x
  let u := p.val - (1 - p.val)
  have hu : IsSelfAdjoint u := p.property.isSelfAdjoint.sub
    ((show IsSelfAdjoint (1 : Algebra M) from star_one _).sub p.property.isSelfAdjoint)
  have hs : u * u = 1 := by
    dsimp [u]
    simp only [sub_mul, mul_sub, mul_one, one_mul, p.property.isIdempotentElem.eq]
    abel
  let U : unitary (Algebra M) := ⟨u, by rw [hu.star_eq]; exact hs, by rw [hu.star_eq]; exact hs⟩
  have hn : ‖u‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Algebra M) with h | h
    · let := h
      rw [Subsingleton.elim u 0, norm_zero]
      exact zero_le_one
    · let := h
      exact (CStarRing.norm_coe_unitary U).le
  have hl : u * x = x⁺ + x⁻ := by
    rw [sub_mul, positiveSupport_mul x hx, positiveSupport_complement_mul x hx, sub_neg_eq_add]
  have hr : x * u = x⁺ + x⁻ := by
    have h := congrArg star hl
    simpa only [star_mul, hu.star_eq, hx.star_eq, star_add,
      (CFC.posPart_nonneg x).isSelfAdjoint.star_eq,
      (CFC.negPart_nonneg x).isSelfAdjoint.star_eq] using h
  exact ⟨u, hu, hn, hl, hr⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommutantPolarSupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A support inequality for positive commutant contractions

This is the operator-order part of the bounded modular Radon--Nikodym
argument. The sign of a self-adjoint test operator dominates its pairing
with a positive contraction from the commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance commutantSupportOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance commutantSupportPreorder_r69d4ad_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance commutantSupportLE_r69d4ad_1 : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance commutantSupportStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem commutant_positive_polar_support (Ω : H) (x : Algebra M)
    (hx : IsSelfAdjoint x) (b : H →L[ℂ] H) (hb : b ∈ M.commutant)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ u : Algebra M, IsSelfAdjoint u ∧ ‖u‖ ≤ 1 ∧
      (inner ℂ (x.val Ω) (b Ω)).re ≤ (inner ℂ (x.val Ω) (u.val Ω)).re ∧
      (inner ℂ (x.val Ω) (u.val Ω)).im = 0 := by
  obtain ⟨u, hu, hun, _, hxu⟩ := selfAdjoint_polar_test x hx
  let P : H →L[ℂ] H := (x⁺).val
  let N : H →L[ℂ] H := (x⁻).val
  have hP : 0 ≤ P := by
    have h := map_rel M.toStarSubalgebra.subtype (CFC.posPart_nonneg x)
    change M.toStarSubalgebra.subtype 0 ≤ P at h
    simpa only [map_zero] using h
  have hN : 0 ≤ N := by
    have h := map_rel M.toStarSubalgebra.subtype (CFC.negPart_nonneg x)
    change M.toStarSubalgebra.subtype 0 ≤ N at h
    simpa only [map_zero] using h
  have hPb : Commute P b := hb _ (Set.mem_union_left _ (x⁺).property)
  have hNb : Commute N b := hb _ (Set.mem_union_left _ (x⁻).property)
  have hp : 0 ≤ P * (1 - b) :=
    Commute.mul_nonneg hP (sub_nonneg.mpr hb1) ((Commute.one_right P).sub_right hPb)
  have hn : 0 ≤ N * (1 + b) :=
    Commute.mul_nonneg hN (add_nonneg zero_le_one hb0) ((Commute.one_right N).add_right hNb)
  have hparts : x.val = P - N :=
    congrArg Subtype.val (CFC.posPart_sub_negPart x hx).symm
  have he : P + N - x.val * b = P * (1 - b) + N * (1 + b) := by
    rw [hparts]
    noncomm_ring
  have hpos : 0 ≤ P + N - x.val * b := by rw [he]; exact add_nonneg hp hn
  have hxu' : x.val * u.val = P + N := congrArg Subtype.val hxu
  have hsa : x.val.adjoint = x.val :=
    (show IsSelfAdjoint x.val from congrArg Subtype.val hx.star_eq).star_eq
  have hi (A : H →L[ℂ] H) : inner ℂ (x.val Ω) (A Ω) = inner ℂ Ω ((x.val * A) Ω) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsa]
    rfl
  refine ⟨u, hu, hun, ?_, ?_⟩
  · have h := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos).re_inner_nonneg_right Ω
    change 0 ≤ (inner ℂ Ω ((P + N - x.val * b) Ω)).re at h
    simp only [sub_apply, inner_sub_right, Complex.sub_re] at h
    rw [hi b, hi u.val, hxu']
    linarith
  · rw [hi u.val, hxu']
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (add_nonneg hP hN)).toLinearMap.isSymmetric.im_inner_self_apply Ω

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointVectorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- Self-adjoint contractions of the given algebra, with the weak operator topology. -/
def wotSelfAdjointBall (M : VonNeumannAlgebra H) : Set (H →WOT[ℂ] H) :=
  Generator.Tracial.weakOperatorBall M 1 ∩ {T | IsSelfAdjoint T.toCLM}

attribute [local instance] OAI.KadisonKastler.selfAdjointCompactReal
theorem wotSelfAdjointBall_convex (M : VonNeumannAlgebra H) :
    Convex ℝ (wotSelfAdjointBall M) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨⟨M.toStarSubalgebra.add_mem
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hX.1.1 a)
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hY.1.1 b), ?_⟩, ?_⟩
  · have h := (convex_closedBall (0 : H →L[ℂ] H) 1)
      (show X.toCLM ∈ Metric.closedBall 0 1 by simpa using hX.1.2)
      (show Y.toCLM ∈ Metric.closedBall 0 1 by simpa using hY.1.2)
      ha hb hab
    simpa using h
  · change star (a • X.toCLM + b • Y.toCLM) = a • X.toCLM + b • Y.toCLM
    simp only [star_add, star_smul, star_trivial, hX.2.star_eq, hY.2.star_eq]

/-- A fixed real-linear transform of the vector ball. -/
def selfAdjointVectorImage (M : VonNeumannAlgebra H) (Ω : H) (P : H →L[ℝ] H) : Set H :=
  (fun T : H →WOT[ℂ] H => P (T Ω)) '' wotSelfAdjointBall M

theorem selfAdjointVectorImage_convex (M : VonNeumannAlgebra H) (Ω : H) (P : H →L[ℝ] H) :
    Convex ℝ (selfAdjointVectorImage M Ω P) := by
  let F : (H →WOT[ℂ] H) →ₗ[ℝ] H :=
    { toFun := fun T => P (T Ω)
      map_add' := fun _ _ => P.map_add _ _
      map_smul' := fun _ _ => P.map_smul _ _ }
  exact (wotSelfAdjointBall_convex M).linear_image F

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealLaplaceUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local Laplace uniqueness for the signed averaging coefficient -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

/-- For continuous coefficients, the conclusion holds at every real parameter. -/
theorem zero_of_local_laplace (f : ℝ → ℝ) (hf : Continuous f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => Real.exp (s * t) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, Real.exp (s * t) * f t) = 0) :
    f = 0 :=
  (Continuous.ae_eq_iff_eq volume hf continuous_const).mp
    (ae_zero_of_local_laplace f hf.measurable ha hi hz)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripAverageUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular averaging kernels separate bounded continuous functions -/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem stripAverageKernel_tilt (a s t : ℝ) :
    (Real.exp (s * t) : ℂ) * stripAverageKernel a 0 t =
      stripAverageKernel a (-s : ℂ) t := by
  unfold stripAverageKernel
  rw [zero_mul, neg_zero, Complex.exp_zero, Complex.ofReal_exp]
  push_cast
  simp only [neg_mul, neg_neg, div_eq_mul_inv, one_mul]

theorem stripAverageKernel_ne_zero (a t : ℝ) : stripAverageKernel a 0 t ≠ 0 := by
  unfold stripAverageKernel
  apply div_ne_zero (Complex.exp_ne_zero _)
  exact_mod_cast (add_pos (Real.exp_pos (a * t)) (Real.exp_pos (-a * t))).ne'

/-- A bounded continuous coefficient is determined by all the real exponential
tilts of the strip averaging kernel. -/
theorem zero_of_strip_averages {a : ℝ} (ha : 0 < a) (g : ℝ → ℂ)
    (hg : Continuous g) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B)
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, stripAverageKernel a (s : ℂ) t * g t) = 0) :
    g = 0 := by
  let f : ℝ → ℂ := fun t => stripAverageKernel a 0 t * g t
  have hfc : Continuous f := (stripAverageKernel_continuous a 0).mul hg
  have hint (s : ℝ) (hs : s ∈ Ioo (-a) a) :
      Integrable (fun t => (Real.exp (s * t) : ℂ) * f t) := by
    have hh : |(-s : ℂ).re| < a := by
      simp only [Complex.neg_re, Complex.ofReal_re, abs_neg]
      exact abs_lt.mpr hs
    have hi := (stripAverageKernel_integrable hh).mul_bdd hg.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    change (Real.exp (s * t) : ℂ) * (stripAverageKernel a 0 t * g t) = _
    rw [← mul_assoc, stripAverageKernel_tilt]
  have hzero (s : ℝ) (hs : s ∈ Ioo (-a) a) :
      (∫ t, (Real.exp (s * t) : ℂ) * f t) = 0 := by
    have he : (fun t => (Real.exp (s * t) : ℂ) * f t) =
        (fun t => stripAverageKernel a (-s : ℂ) t * g t) := by
      funext t
      change (Real.exp (s * t) : ℂ) * (stripAverageKernel a 0 t * g t) = _
      rw [← mul_assoc, stripAverageKernel_tilt]
    rw [he]
    simpa only [Complex.ofReal_neg] using
      hz (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hre : (fun t => (f t).re) = 0 := zero_of_local_laplace _
    (Complex.continuous_re.comp hfc) ha
    (fun s hs => by
      simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using (hint s hs).re)
    (fun s hs => by
      have h := integral_re (hint s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).re) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).re at h
      rw [hzero s hs] at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.zero_re] using h)
  have him : (fun t => (f t).im) = 0 := zero_of_local_laplace _
    (Complex.continuous_im.comp hfc) ha
    (fun s hs => by
      simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        using (hint s hs).im)
    (fun s hs => by
      have h := integral_im (hint s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).im) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).im at h
      rw [hzero s hs] at h
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.zero_im] using h)
  funext t
  have hf0 : f t = 0 := Complex.ext (congrFun hre t) (congrFun him t)
  exact (mul_eq_zero.mp hf0).resolve_left (stripAverageKernel_ne_zero a t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripAverageMembership
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering algebra membership from all strip averages

Once the bounded modular equation identifies these averages with algebra
elements, this lemma gives membership of every operator on the orbit.
-/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exponential strip averages determine membership in a von Neumann algebra. -/
theorem mem_of_strip_averages (M : VonNeumannAlgebra H) {a : ℝ} (ha : 0 < a)
    (F : ℝ → H →L[ℂ] H) (hc : ∀ x, Continuous (fun t => F t x))
    (B : ℝ) (hb : ∀ t, ‖F t‖ ≤ B)
    (hm : ∀ s (hs : |s| < a),
      weightedOperatorIntegral volume (stripAverageKernel a (s : ℂ))
        (stripAverageKernel_integrable (by simpa using hs)) F
        (fun x => (hc x).aestronglyMeasurable) B (Filter.Eventually.of_forall hb) ∈ M) :
    ∀ t, F t ∈ M := by
  intro t
  change F t ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro A hA
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  let g : ℝ → ℂ := fun u => inner ℂ y (F u (A x) - A (F u x))
  have hgc : Continuous g := continuous_const.inner
    ((hc (A x)).sub (A.continuous.comp (hc x)))
  have hgb : ∀ u, ‖g u‖ ≤ ‖y‖ * (B * ‖A x‖ + ‖A‖ * (B * ‖x‖)) := by
    intro u
    apply (norm_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg y)
    apply (norm_sub_le _ _).trans
    exact add_le_add
      (((F u).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)))
      ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (((F u).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)))
        (norm_nonneg A)))
  have hgz : ∀ s ∈ Ioo (-a) a, (∫ u, stripAverageKernel a (s : ℂ) u * g u) = 0 := by
    intro s hs
    have hs' : |s| < a := abs_lt.mpr hs
    let w := stripAverageKernel a (s : ℂ)
    have hw : Integrable w := stripAverageKernel_integrable (by simpa using hs')
    let V := weightedOperatorIntegral volume w hw F
      (fun z => (hc z).aestronglyMeasurable) B (Filter.Eventually.of_forall hb)
    have hV : V ∈ M := hm s hs'
    have hcomm : V * A = A * V := hA V hV
    have hi (z : H) : Integrable (fun u => w u • F u z) :=
      integrable_weighted_operator_vector volume w hw F
        (fun z => (hc z).aestronglyMeasurable) B (Filter.Eventually.of_forall hb) z
    have hdi : (∫ u, w u • (F u (A x) - A (F u x))) = 0 := by
      have hAs (u : ℝ) : w u • A (F u x) = A (w u • F u x) :=
        (map_smul A (w u) (F u x)).symm
      simp_rw [smul_sub, hAs]
      rw [integral_sub (hi (A x)) (A.integrable_comp (hi x)),
        A.integral_comp_comm (hi x)]
      exact sub_eq_zero.mpr (congrArg (fun T : H →L[ℂ] H => T x) hcomm)
    have hdiI : Integrable (fun u => w u • (F u (A x) - A (F u x))) := by
      convert! (hi (A x)).sub (A.integrable_comp (hi x)) using 1
      all_goals try with_reducible_and_instances rfl
      funext u
      simp only [Pi.sub_apply, smul_sub, map_smul]
    have he := (innerSL ℂ y).integral_comp_comm hdiI
    change (∫ u, inner ℂ y (w u • (F u (A x) - A (F u x)))) =
      inner ℂ y (∫ u, w u • (F u (A x) - A (F u x))) at he
    rw [hdi, inner_zero_right] at he
    simpa only [inner_smul_right, smul_eq_mul] using he
  have hg0 := zero_of_strip_averages ha g hgc hgb hgz
  have he := congrFun hg0 t
  change inner ℂ y (F t (A x) - A (F t x)) = 0 at he
  rw [inner_sub_right] at he
  exact (sub_eq_zero.mp he).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiagonalPairAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The diagonal algebra on two Hilbert copies

Weak compactness shows that duplicating a represented von Neumann algebra
already has weakly closed range. This is the ambient algebra for two vector
states of the same represented algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def diagonalPairHom (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :=
  hilbertPairRepresentation M.toStarSubalgebra.subtype M.toStarSubalgebra.subtype

theorem diagonalPairHom_injective (M : VonNeumannAlgebra H) :
    Function.Injective (diagonalPairHom M) := by
  intro a b hab
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) =>
    (T (WithLp.toLp 2 (x, 0))).fst) hab

theorem diagonalPairHom_norm (M : VonNeumannAlgebra H) (a : Algebra M) :
    ‖diagonalPairHom M a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (diagonalPairHom M) (diagonalPairHom_injective M) a

theorem diagonalPairHom_tendsto_weak (M : VonNeumannAlgebra H)
    {I : Type*} {l : Filter I} (a : I → Algebra M) (b : Algebra M)
    (h : ∀ x y, Tendsto (fun i => inner ℂ y ((a i).val x)) l (𝓝 (inner ℂ y (b.val x))))
    (x y : WithLp 2 (H × H)) :
    Tendsto (fun i => inner ℂ y (diagonalPairHom M (a i) x)) l
      (𝓝 (inner ℂ y (diagonalPairHom M b x))) := by
  change Tendsto (fun i => inner ℂ y.fst ((a i).val x.fst) +
    inner ℂ y.snd ((a i).val x.snd)) l
    (𝓝 (inner ℂ y.fst (b.val x.fst) + inner ℂ y.snd (b.val x.snd)))
  exact (h x.fst y.fst).add (h x.snd y.snd)

def diagonalPairAlgebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra (WithLp 2 (H × H)) :=
  generatedVonNeumannAlgebra (diagonalPairHom M).range

theorem diagonalPairHom_surjective_unitBall (M : VonNeumannAlgebra H)
    (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (hT : T ∈ diagonalPairAlgebra M) (hnT : ‖T‖ ≤ 1) :
    ∃ a : Algebra M, ‖a‖ ≤ 1 ∧ diagonalPairHom M a = T := by
  classical
  let K := WithLp 2 (H × H)
  let ρ := diagonalPairHom M
  let A := ρ.range
  have hcomm : T ∈ Set.centralizer (Set.centralizer (A : Set (K →L[ℂ] K))) := by
    change T ∈ (generatedVonNeumannAlgebra A : Set _) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨d, hd, hlim⟩ := publishedKaplanskyDensity.exists_weak_contraction_net A T hcomm hnT
  choose a ha using fun i => (d i).property
  have ha' (i : Finset K × ℕ) : ρ (a i) = (d i).val := ha i
  have hn (i : Finset K × ℕ) : ‖a i‖ ≤ 1 := by
    rw [← diagonalPairHom_norm M]
    change ‖ρ (a i)‖ ≤ 1
    rw [ha' i]
    exact hd i
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, hb, hweak⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val) 1 zero_le_one hn
  let b₀ : Algebra M := ⟨b, weak_operator_limit_mem M a b hweak⟩
  refine ⟨b₀, hb, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₁ := diagonalPairHom_tendsto_weak M a b₀ hweak x y
  have h₂ : Tendsto (fun i => inner ℂ y (ρ (a i) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (T x))) := by
    simpa only [ha'] using (hlim x y).mono_left (Ultrafilter.of_le atTop)
  exact tendsto_nhds_unique h₁ h₂

theorem diagonalPairHom_surjective (M : VonNeumannAlgebra H)
    (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (hT : T ∈ diagonalPairAlgebra M) : ∃ a : Algebra M, diagonalPairHom M a = T := by
  by_cases hzero : T = 0
  · exact ⟨0, by rw [map_zero, hzero]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, _, ha⟩ := diagonalPairHom_surjective_unitBall M ((‖T‖ : ℂ)⁻¹ • T)
    ((diagonalPairAlgebra M).smul_mem hT _) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  rw [map_smul, ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

def diagonalPairEquiv (M : VonNeumannAlgebra H) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (diagonalPairAlgebra M) := by
  let ρ := (diagonalPairHom M).codRestrict (diagonalPairAlgebra M).toStarSubalgebra
    (fun a => subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩)
  apply StarAlgEquiv.ofBijective ρ
  constructor
  · intro a b hab
    exact diagonalPairHom_injective M (congrArg Subtype.val hab)
  · intro T
    obtain ⟨a, ha⟩ := diagonalPairHom_surjective M T.val T.property
    exact ⟨a, Subtype.ext ha⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiagonalLocality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
theorem regular_integral_norm_sq (f : RegularCoreHilbert H) :
    (∫ t : ℝ, ‖f t‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simpa only [inner_self_eq_norm_sq] using h.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem generated_le_vonNeumann
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (S : Set (K →L[ℂ] K)) (B : VonNeumannAlgebra K)
    (hS : S ⊆ B) :
    generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ S) ≤ B := by
  have hA : (StarAlgebra.adjoin ℂ S : Set (K →L[ℂ] K)) ⊆ B := by
    apply StarAlgebra.adjoin_le
    exact hS
  intro T hT
  have hT' : T ∈ (generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ S) :
      Set (K →L[ℂ] K)) := hT
  rw [generatedVonNeumannAlgebra_coe] at hT'
  have h := Set.centralizer_subset (Set.centralizer_subset hA) hT'
  change T ∈ (B : Set (K →L[ℂ] K))
  simpa only [VonNeumannAlgebra.centralizer_centralizer] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralVectorMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def regularVectorMeasure (f : RegularCoreHilbert H) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (‖f t‖ ^ 2))

instance regularVectorMeasure_finite (f : RegularCoreHilbert H) :
    IsFiniteMeasure (regularVectorMeasure f) := by
  have hi := (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  exact isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Eventually.of_forall fun t => sq_nonneg ‖f t‖)).mpr hi)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularVectorMeasure_integral (f : RegularCoreHilbert H) (φ : ℝ → ℂ) :
    (∫ t, φ t ∂regularVectorMeasure f) = ∫ t, (‖f t‖ ^ 2 : ℝ) • φ t := by
  have hi := (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  rw [regularVectorMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankAlgebraFields
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Field decomposition for an algebra and a commuting generating source -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {A B C E H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B] [CStarAlgebra C] [CStarAlgebra E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

abbrev commonRankMeasure := projectionStratumMeasure (cyclicCommonBaseMeasure π D)
  (commonModelProjection M) (commonRankBasis π D)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteWeakLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

attribute [local instance] OAI.KadisonKastler.completeWeakOperatorOrder
local instance completeWeakOperatorStarOrder_r69d4ad_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance completeWeakAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance completeWeakAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeometricCorrectionScale
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The summable error scale for multiplication correction -/

namespace KadisonKastler

open Filter Topology

noncomputable section

@[simp] theorem correctionScale_zero (q : ℝ) : correctionScale q 0 = q := by
  simp [correctionScale]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyCauchyBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary formula for the Hardy reproducing kernel -/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

theorem hardyCauchyFunction_norm_sq {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    ‖hardyCauchyFunction z s‖ ^ 2 =
      realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s /
        (2 * z.re) := by
  unfold hardyCauchyFunction
  rw [norm_inv, inv_pow, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
  unfold realPoissonKernel
  field_simp
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_LiftedRankStrata
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

def rankFiberLift (n : ℕ) :
    ℓ²(projectionDimensionIndex n, ℂ) ≃ₗᵢ[ℂ] ULift.{u} ℓ²(projectionDimensionIndex n, ℂ) :=
  (LinearIsometryEquiv.ulift ℂ ℓ²(projectionDimensionIndex n, ℂ)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationNewtonStep
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # One quadratic step in correction of multiplication

These are the concrete matrix identities used in the perturbation iteration.
The choice of a correcting cochain is a separate construction.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Transport an arbitrary bilinear multiplication by a linear equivalence. -/
def conjugatedBilinear (L : A ≃ₗ[ℂ] A) (m : A →ₗ[ℂ] A →ₗ[ℂ] A) :
    A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x := L.toLinearMap.comp ((m (L.symm x)).comp L.symm.toLinearMap)
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

@[simp] theorem conjugatedBilinear_apply (L : A ≃ₗ[ℂ] A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    conjugatedBilinear L m x y = L (m (L.symm x) (L.symm y)) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioParameters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two fixed product-state parameters

The manuscript uses `exp (-1)` and `exp (-sqrt 2)`. Their logarithms
generate an incommensurable pair of modular frequencies. No parameter
depends on an algebra, representation, or requested perturbation bound.
-/

namespace KadisonKastler

noncomputable section

theorem fixedProductLambda_lt_one : fixedProductLambda < 1 := by
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem fixedProductMu_lt_one : fixedProductMu < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by norm_num))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedLocalMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem pointedRawLeft_star (i j : Fin 2) : star (pointedRawLeft i j) = pointedRawLeft j i := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pointedRawLeft_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem pointedRawRight_star (i j : Fin 2) : star (pointedRawRight i j) = pointedRawRight j i := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pointedRawRight_apply]
  fin_cases i <;> fin_cases j <;> simp

def pointedRawLeftUnits : Generator.MatrixUnitSystem (Fin 2)
    (PointedRawHilbert →L[ℂ] PointedRawHilbert) where
  entry := pointedRawLeft
  star_entry := pointedRawLeft_star
  mul_entry i j k l := by
    ext x p
    simp only [mul_apply_eq_comp, pointedRawLeft_apply]
    split_ifs <;> simp_all
  total := by
    ext x p
    simp only [Fin.sum_univ_two, add_apply,
      one_apply_eq_self]
    rcases p with ⟨p, q⟩
    fin_cases p <;> simp

def pointedRawRightUnits : Generator.MatrixUnitSystem (Fin 2)
    (PointedRawHilbert →L[ℂ] PointedRawHilbert) where
  entry := pointedRawRight
  star_entry := pointedRawRight_star
  mul_entry i j k l := by
    ext x p
    simp only [mul_apply_eq_comp, pointedRawRight_apply]
    split_ifs <;> simp_all
  total := by
    ext x p
    simp only [Fin.sum_univ_two, add_apply,
      one_apply_eq_self]
    rcases p with ⟨p, q⟩
    fin_cases q <;> simp

theorem pointedRawUnits_commute (i j k l : Fin 2) :
    Commute (pointedRawLeft i j) (pointedRawRight k l) := by
  ext x p
  simp only [mul_apply_eq_comp, pointedRawLeft_apply, pointedRawRight_apply]
  split_ifs <;> rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerConfigurations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.norm_hilbertExtendLeft _root_.OAI.KadisonKastler.norm_hilbertExtendRight _root_.OAI.KadisonKastler.norm_tupleSingle _root_.OAI.KadisonKastler.rectangularHilbertMatrix_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Configuration coordinates for a pointed countable Hilbert product

A configuration records the finitely many sites outside the reference
vector. Splitting off one site gives a finite Hilbert sum of identical
tail spaces, with an explicit action on every orthonormal basis vector.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators lp

noncomputable section

instance instNontrivialSubtypePreLpPointedPowerConfigurationComplexMemAddSubgroupPointedPowerHilbert : Nontrivial PointedPowerHilbert := by
  have h : pointedPowerVacuum ≠ 0 := by
    intro hz
    have hn := norm_pointedPowerVacuum
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  exact ⟨⟨pointedPowerVacuum, 0, h⟩⟩

instance instSeparableSpaceSubtypePreLpPointedPowerConfigurationComplexMemAddSubgroupPointedPowerHilbert : TopologicalSpace.SeparableSpace PointedPowerHilbert := by
  have hs0 : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range pointedPowerBasis) : Set PointedPowerHilbert) :=
    (Set.countable_range pointedPowerBasis).isSeparable.span
  have hs := hs0.closure
  change TopologicalSpace.IsSeparable
    ((Submodule.span ℂ (Set.range pointedPowerBasis)).topologicalClosure : Set PointedPowerHilbert) at hs
  have hd := pointedPowerHilbertBasis.dense_span
  rw [show (pointedPowerHilbertBasis : PointedPowerConfiguration → PointedPowerHilbert) =
    pointedPowerBasis from funext pointedPowerHilbertBasis_apply] at hd
  rw [hd] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

/-- A configuration is its label at one site and the vacuum-filled tail. -/
def pointedPowerSplit (i : ℕ) :
    PointedPowerConfiguration ≃ Fin 4 × PointedPowerTail i where
  toFun f := (f i, ⟨f.erase i, Finsupp.erase_same⟩)
  invFun p := p.2.val.update i p.1
  left_inv f := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp
  right_inv p := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      ext j
      by_cases h : j = i
      · subst j
        simp [p.2.property]
      · simp [h]

@[simp] theorem pointedPowerSplit_fst (i : ℕ) (f : PointedPowerConfiguration) :
    (pointedPowerSplit i f).1 = f i := rfl

@[simp] theorem pointedPowerSplit_symm (i : ℕ) (a : Fin 4) (f : PointedPowerTail i) :
    (pointedPowerSplit i).symm (a, f) = f.val.update i a := rfl

section FiniteFibres

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

def finiteL2BasisVector (p : ι × κ) : FiniteHilbert ι ℓ²(κ, ℂ) :=
  tupleSingle p.1 (lp.single 2 p.2 1)

theorem finiteL2BasisVector_orthonormal :
    Orthonormal ℂ (finiteL2BasisVector (ι := ι) (κ := κ)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : i = k
  · subst k
    simp [finiteL2BasisVector, PiLp.inner_apply, tupleSingle_apply, Pi.single_apply, apply_ite,
      lp.inner_single_left, lp.single_apply, Prod.mk.injEq]
  · simp [finiteL2BasisVector, PiLp.inner_apply, tupleSingle_apply, Pi.single_apply, apply_ite,
      hik, Ne.symm hik, Prod.mk.injEq]

theorem finiteL2BasisVector_total :
    ⊤ ≤ (Submodule.span ℂ (Set.range
      (finiteL2BasisVector (ι := ι) (κ := κ)))).topologicalClosure := by
  apply le_of_eq
  symm
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply bot_unique
  intro x hx
  change x = 0
  apply PiLp.ext
  intro i
  apply lp.ext
  funext j
  have h := hx (finiteL2BasisVector (i, j)) (Submodule.subset_span ⟨(i, j), rfl⟩)
  have he : inner ℂ (finiteL2BasisVector (i, j)) x = x i j := by
    simp only [finiteL2BasisVector, PiLp.inner_apply, tupleSingle_apply]
    rw [Finset.sum_eq_single i]
    · simp [lp.inner_single_left]
    · intro k _hk hki
      simp [hki]
    · simp
  rwa [he] at h

/-- The usual basis of the finite sum of scalar `l²` spaces. -/
def finiteL2Basis : HilbertBasis (ι × κ) ℂ (FiniteHilbert ι ℓ²(κ, ℂ)) :=
  HilbertBasis.mk finiteL2BasisVector_orthonormal finiteL2BasisVector_total

@[simp] theorem finiteL2Basis_apply (i : ι) (j : κ) :
    finiteL2Basis (i, j) = tupleSingle i (lp.single 2 j 1) := by
  simp only [finiteL2Basis, HilbertBasis.coe_mk, finiteL2BasisVector]

end FiniteFibres

def pointedPowerSplitBasis (i : ℕ) :
    HilbertBasis (Fin 4 × PointedPowerTail i) ℂ PointedPowerHilbert := by
  let b := pointedPowerHilbertBasis
  have ho := b.orthonormal.comp (pointedPowerSplit i).symm
    (pointedPowerSplit i).symm.injective
  refine HilbertBasis.mk ho ?_
  have hr : Set.range (b ∘ (pointedPowerSplit i).symm) = Set.range b := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨pointedPowerSplit i f, by simp⟩
  rw [hr, b.dense_span]

theorem pointedPowerSplitBasis_apply (i : ℕ) (p : Fin 4 × PointedPowerTail i) :
    pointedPowerSplitBasis i p = pointedPowerBasis ((pointedPowerSplit i).symm p) := by
  simp only [pointedPowerSplitBasis, HilbertBasis.coe_mk, Function.comp_apply,
    pointedPowerHilbertBasis_apply]

/-- Splitting off one site is a genuine Hilbert-space equivalence. -/
def pointedPowerFibreEquiv (i : ℕ) :
    PointedPowerHilbert ≃ₗᵢ[ℂ] FiniteHilbert (Fin 4) (PointedPowerTailHilbert i) :=
  (pointedPowerSplitBasis i).repr.trans finiteL2Basis.repr.symm

@[simp] theorem pointedPowerFibreEquiv_basis (i : ℕ) (f : PointedPowerConfiguration) :
    pointedPowerFibreEquiv i (pointedPowerBasis f) =
      tupleSingle (f i) (lp.single 2 ⟨f.erase i, Finsupp.erase_same⟩ 1) := by
  have hb := pointedPowerSplitBasis_apply i (pointedPowerSplit i f)
  simp only [Equiv.symm_apply_apply] at hb
  rw [← hb]
  change finiteL2Basis.repr.symm
    ((pointedPowerSplitBasis i).repr (pointedPowerSplitBasis i (pointedPowerSplit i f))) = _
  rw [HilbertBasis.repr_self, HilbertBasis.repr_symm_single]
  exact finiteL2Basis_apply _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.norm_hilbertExtendLeft _root_.OAI.KadisonKastler.norm_hilbertExtendRight _root_.OAI.KadisonKastler.norm_tupleSingle _root_.OAI.KadisonKastler.rectangularHilbertMatrix_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem finiteLocalCoefficient_mul
    (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (i j : ι) :
    finiteLocalCoefficient (A * B) i j =
      ∑ k, finiteLocalCoefficient A i k * finiteLocalCoefficient B k j := by
  have h := tuple_eq_sum_single (B (EuclideanSpace.single j 1))
  change A (B (EuclideanSpace.single j 1)) i = _
  rw [h, map_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have he : tupleSingle k (B (EuclideanSpace.single j 1) k) =
      (B (EuclideanSpace.single j 1) k) • EuclideanSpace.single k 1 := by
    ext l
    simp [tupleSingle_apply, Pi.single_apply]
  rw [he, map_smul]
  simp only [finiteLocalCoefficient, PiLp.smul_apply, smul_eq_mul, mul_comm]

def finiteLocalAmplificationValue
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    FiniteHilbert ι E →L[ℂ] FiniteHilbert ι E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j, (finiteLocalCoefficient A i j) • PiLp.proj 2 (fun _ : ι => E) j)

omit [CompleteSpace E] in
@[simp] theorem finiteLocalAmplificationValue_apply
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (x : FiniteHilbert ι E) (i : ι) :
    finiteLocalAmplificationValue A x i = ∑ j, finiteLocalCoefficient A i j • x j := by
  simp [finiteLocalAmplificationValue]

/-- Amplification of a finite-dimensional operator by an identity. -/
def finiteLocalAmplification :
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →⋆ₐ[ℂ]
      (FiniteHilbert ι E →L[ℂ] FiniteHilbert ι E) where
  toFun := finiteLocalAmplificationValue
  map_zero' := by
    ext x i
    simp [finiteLocalCoefficient]
  map_one' := by
    ext x i
    simp [finiteLocalCoefficient]
  map_add' A B := by
    ext x i
    simp [finiteLocalCoefficient, add_smul, Finset.sum_add_distrib]
  map_mul' A B := by
    ext x i
    simp only [finiteLocalAmplificationValue_apply, finiteLocalCoefficient_mul,
      mul_apply_eq_comp, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
  commutes' z := by
    ext x i
    simp [finiteLocalCoefficient]
  map_star' A := by
    change finiteLocalAmplificationValue (star A) = star (finiteLocalAmplificationValue A)
    rw [ContinuousLinearMap.star_eq_adjoint (finiteLocalAmplificationValue (E := E) A)]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [PiLp.inner_apply, finiteLocalAmplificationValue_apply,
      inner_sum, sum_inner, inner_smul_left, inner_smul_right,
      finiteLocalCoefficient_star, starRingEnd_apply, star_star]
    rw [Finset.sum_comm]

@[simp] theorem finiteLocalAmplification_apply
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (x : FiniteHilbert ι E) (i : ι) :
    finiteLocalAmplification (ι := ι) (E := E) A x i = ∑ j, finiteLocalCoefficient A i j • x j :=
  finiteLocalAmplificationValue_apply A x i

end FiniteAmplification

/-- Apply a four-dimensional operator at one site of the Hilbert product. -/
def pointedPowerOperator (i : ℕ) :
    (EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)) →⋆ₐ[ℂ]
      (PointedPowerHilbert →L[ℂ] PointedPowerHilbert) :=
  (pointedPowerFibreEquiv i).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (finiteLocalAmplification (E := PointedPowerTailHilbert i))

theorem pointedPowerOperator_basis (i : ℕ)
    (A : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))
    (f : PointedPowerConfiguration) :
    pointedPowerOperator i A (pointedPowerBasis f) =
      ∑ k : Fin 4, finiteLocalCoefficient A k (f i) •
        pointedPowerBasis (f.update i k) := by
  apply (pointedPowerFibreEquiv i).injective
  change (pointedPowerFibreEquiv i)
      ((pointedPowerFibreEquiv i).symm
        (finiteLocalAmplification (ι := Fin 4) (E := PointedPowerTailHilbert i) A
          ((pointedPowerFibreEquiv i) (pointedPowerBasis f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rw [pointedPowerFibreEquiv_basis, map_sum]
  simp only [map_smul, pointedPowerFibreEquiv_basis,
    Finsupp.update_apply, ite_eq_left, Finsupp.erase_update_eq_erase]
  apply PiLp.ext
  intro k
  simp [finiteLocalAmplification_apply, tupleSingle_apply, Pi.single_apply,
    apply_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- Operators on different sites commute, with no condition on their matrices. -/
theorem pointedPowerOperator_commute {i j : ℕ} (hij : i ≠ j)
    (A B : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)) :
    Commute (pointedPowerOperator i A) (pointedPowerOperator j B) := by
  change pointedPowerOperator i A * pointedPowerOperator j B =
    pointedPowerOperator j B * pointedPowerOperator i A
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro f
  apply ContinuousLinearMap.ext
  intro c
  change (pointedPowerOperator i A) ((pointedPowerOperator j B) (lp.single 2 f c)) =
    (pointedPowerOperator j B) ((pointedPowerOperator i A) (lp.single 2 f c))
  have hsingle : (lp.single 2 f c : PointedPowerHilbert) = c • pointedPowerBasis f := by
    simp only [pointedPowerBasis, ← lp.single_smul, smul_eq_mul, mul_one]
  rw [hsingle]
  simp only [map_smul, pointedPowerOperator_basis,
    map_sum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finsupp.update_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  rw [Finsupp.update_comm f hij k l]
  congr 1
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerCyclicity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Cyclic and separating configuration vacua

Local cyclicity generates every finitely excited basis vector. Applying
the same argument to the commuting right actions proves separation.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

def pointedPowerInsertLinear (i : ℕ) (f : PointedPowerConfiguration) :
    PointedLocalHilbert →ₗ[ℂ] PointedPowerHilbert where
  toFun x := ∑ k : Fin 4, x k • pointedPowerBasis (f.update i k)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem pointedPowerInsertLinear_single (i : ℕ)
    (f : PointedPowerConfiguration) (k : Fin 4) :
    pointedPowerInsertLinear i f (EuclideanSpace.single k 1) =
      pointedPowerBasis (f.update i k) := by
  simp [pointedPowerInsertLinear]

theorem pointedPowerInsertLinear_operator (i : ℕ) (f : PointedPowerConfiguration)
    (hf : f i = 0) (A : PointedLocalHilbert →L[ℂ] PointedLocalHilbert) :
    pointedPowerInsertLinear i f (A pointedLocalVacuum) =
      pointedPowerOperator i A (pointedPowerBasis f) := by
  rw [pointedPowerOperator_basis]
  simp only [pointedPowerInsertLinear, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLocalCoefficient, hf, pointedLocalVacuum]

def pointedPowerSite
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (i : ℕ) : MatrixUnitSystem (Fin 2) (PointedPowerHilbert →L[ℂ] PointedPowerHilbert) :=
  E.map (pointedPowerOperator i)

def pointedPowerAlgebra
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert)) :
    VonNeumannAlgebra PointedPowerHilbert :=
  generatedVonNeumannAlgebra (⨆ i : ℕ, (pointedPowerSite E i).algebra)

theorem pointedPowerSite_mem
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (i : ℕ) (a b : Fin 2) : pointedPowerOperator i (E.entry a b) ∈ pointedPowerAlgebra E := by
  apply subset_generatedVonNeumannAlgebra
  exact (le_iSup (fun j : ℕ => (pointedPowerSite E j).algebra) i)
    ((pointedPowerSite E i).entry_mem a b)

theorem pointedPowerAlgebra_commutant
    (E F : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (hEF : ∀ a b c d, Commute (E.entry a b) (F.entry c d)) :
    pointedPowerAlgebra F ≤ (pointedPowerAlgebra E).commutant := by
  have hentry (i j : ℕ) (a b c d : Fin 2) :
      Commute (pointedPowerOperator i (E.entry a b))
        (pointedPowerOperator j (F.entry c d)) := by
    by_cases hij : i = j
    · subst j
      change pointedPowerOperator i (E.entry a b) * pointedPowerOperator i (F.entry c d) = _
      rw [← map_mul, ← map_mul, (hEF a b c d).eq]
    · exact pointedPowerOperator_commute hij _ _
  apply generatedVonNeumannAlgebra_le_of_le
  apply iSup_le
  intro j
  apply ((pointedPowerSite F j).algebra_le_iff _).mpr
  intro c d
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  let b := pointedPowerOperator j (F.entry c d)
  have hstar : star b = pointedPowerOperator j (F.entry d c) := by
    dsimp only [b]
    rw [← map_star, F.star_entry]
  let S : StarSubalgebra ℂ (PointedPowerHilbert →L[ℂ] PointedPowerHilbert) :=
    ⨆ i : ℕ, (pointedPowerSite E i).algebra
  have hs : S ≤ StarSubalgebra.centralizer ℂ {b} := by
    apply iSup_le
    intro i
    apply ((pointedPowerSite E i).algebra_le_iff _).mpr
    intro r s
    rw [StarSubalgebra.mem_centralizer_iff]
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    constructor
    · exact (hentry i j r s c d).eq.symm
    · rw [hstar]
      exact (hentry i j r s d c).eq.symm
  have hb : b ∈ Set.centralizer
      (S : Set (PointedPowerHilbert →L[ℂ] PointedPowerHilbert)) := by
    intro x hx
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hs hx) b
      (Set.mem_singleton b)).1.symm
  change a ∈ (pointedPowerAlgebra E : Set (PointedPowerHilbert →L[ℂ] PointedPowerHilbert)) at ha
  rw [pointedPowerAlgebra, generatedVonNeumannAlgebra_coe] at ha
  exact (ha b hb).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedPowerMoments
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

def pointedLocalVacuumProjection : PointedLocalHilbert →L[ℂ] PointedLocalHilbert :=
  InnerProductSpace.rankOne ℂ pointedLocalVacuum pointedLocalVacuum

theorem pointedLocalVacuumProjection_apply :
    pointedLocalVacuumProjection pointedLocalVacuum = pointedLocalVacuum := by
  simp [pointedLocalVacuumProjection, pointedLocalVacuum]

theorem pointedLocalVacuumProjection_star :
    star pointedLocalVacuumProjection = pointedLocalVacuumProjection := by
  simp only [pointedLocalVacuumProjection, ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne]

theorem pointedLocalVacuumProjection_corner
    (A : PointedLocalHilbert →L[ℂ] PointedLocalHilbert) :
    pointedLocalVacuumProjection * A * pointedLocalVacuumProjection =
      (inner ℂ pointedLocalVacuum (A pointedLocalVacuum)) • pointedLocalVacuumProjection := by
  ext x
  simp [pointedLocalVacuumProjection, mul_apply_eq_comp, map_smul,
    smul_smul, mul_comm]

theorem pointedPowerVacuumProjection_fixes (i : ℕ) :
    pointedPowerOperator i pointedLocalVacuumProjection pointedPowerVacuum =
      pointedPowerVacuum := by
  rw [pointedPowerVacuum, ← pointedPowerInsertLinear_operator i 0 (by simp),
    pointedLocalVacuumProjection_apply, pointedLocalVacuum,
    pointedPowerInsertLinear_single]
  congr 1
  ext j
  simp

theorem pointedPowerVacuumProjection_star (i : ℕ) :
    star (pointedPowerOperator i pointedLocalVacuumProjection) =
      pointedPowerOperator i pointedLocalVacuumProjection := by
  rw [← map_star, pointedLocalVacuumProjection_star]

theorem vacuum_moment_split
    (i : ℕ) (A : PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
    (B : PointedPowerHilbert →L[ℂ] PointedPowerHilbert)
    (hB : Commute (pointedPowerOperator i pointedLocalVacuumProjection) B) :
    inner ℂ pointedPowerVacuum (pointedPowerOperator i A (B pointedPowerVacuum)) =
      inner ℂ pointedLocalVacuum (A pointedLocalVacuum) *
        inner ℂ pointedPowerVacuum (B pointedPowerVacuum) := by
  let Q := pointedPowerOperator i pointedLocalVacuumProjection
  have hQ : Q pointedPowerVacuum = pointedPowerVacuum := pointedPowerVacuumProjection_fixes i
  have hQs : star Q = Q := pointedPowerVacuumProjection_star i
  have hQB : Q (B pointedPowerVacuum) = B pointedPowerVacuum := by
    rw [← mul_apply_eq_comp, hB.eq, mul_apply_eq_comp, hQ]
  have hinner (x : PointedPowerHilbert) :
      inner ℂ pointedPowerVacuum (Q x) = inner ℂ pointedPowerVacuum x := by
    have h := ContinuousLinearMap.adjoint_inner_right Q pointedPowerVacuum x
    rw [← ContinuousLinearMap.star_eq_adjoint, hQs, hQ] at h
    exact h
  have hcorner : Q * pointedPowerOperator i A * Q =
      (inner ℂ pointedLocalVacuum (A pointedLocalVacuum)) • Q := by
    dsimp only [Q]
    rw [← map_mul, ← map_mul, pointedLocalVacuumProjection_corner, map_smul]
  calc
    _ = inner ℂ pointedPowerVacuum (Q (pointedPowerOperator i A (Q (B pointedPowerVacuum)))) := by
      rw [hQB, hinner]
    _ = inner ℂ pointedPowerVacuum ((Q * pointedPowerOperator i A * Q) (B pointedPowerVacuum)) := rfl
    _ = _ := by
      rw [hcorner]
      simp only [smul_apply, inner_smul_right, hQB]

/-- The vacuum factors on every finite family of distinct sites. -/
theorem pointedPower_product_moment
    (A : ℕ → PointedLocalHilbert →L[ℂ] PointedLocalHilbert)
    (l : List ℕ) (hl : l.Nodup) :
    inner ℂ pointedPowerVacuum
      (((l.map fun i => pointedPowerOperator i (A i)).prod) pointedPowerVacuum) =
      (l.map fun i => inner ℂ pointedLocalVacuum (A i pointedLocalVacuum)).prod := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, norm_pointedPowerVacuum]
    norm_num
  | cons i l ih =>
    have hnot : i ∉ l := (List.nodup_cons.mp hl).1
    have htail : l.Nodup := (List.nodup_cons.mp hl).2
    have hcomm : Commute (pointedPowerOperator i pointedLocalVacuumProjection)
        ((l.map fun j => pointedPowerOperator j (A j)).prod) := by
      apply Commute.list_prod_right
      intro T hT
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hT
      exact pointedPowerOperator_commute (i := i) (j := j)
        (by intro h; subst j; exact hnot hj) _ _
    simpa only [List.map_cons, List.prod_cons, mul_apply_eq_comp, ih htail] using
      vacuum_moment_split i (A i) ((l.map fun j => pointedPowerOperator j (A j)).prod) hcomm

theorem pointedPowerSite_commuting
    (E : MatrixUnitSystem (Fin 2) (PointedLocalHilbert →L[ℂ] PointedLocalHilbert))
    (i j : ℕ) (hij : i ≠ j) (a b c d : Fin 2) :
    Commute ((pointedPowerSite E i).entry a b) ((pointedPowerSite E j).entry c d) :=
  pointedPowerOperator_commute hij _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketIntegrals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

omit [CompleteSpace H] in
theorem integrable_scalarPacket_pair
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    Integrable (fun t => star (φ t) • f t) volume := by
  have hi := (Lp.memLp φ).norm.integrable_mul (Lp.memLp f).norm
  apply hi.mono' ((Lp.aestronglyMeasurable φ).star.smul (Lp.aestronglyMeasurable f))
  filter_upwards [] with t
  change ‖star (φ t) • f t‖ ≤ ‖φ t‖ * ‖f t‖
  rw [norm_smul, norm_star]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketFubini
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
/-- The complete scalar kernel is integrable over the two packet
variables and the translation variable. -/
theorem integrable_regularPacket_kernel
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    Integrable (fun p : (ℝ × ℝ) × ℝ =>
      (φ p.1.1 * star (ψ p.1.2)) *
        inner ℂ ((U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1)))
          (A ((U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2)))))
      (((volume : Measure ℝ).prod volume).prod volume) := by
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  let w : ℝ × ℝ → ℂ := fun q => φ q.1 * star (ψ q.2)
  have hψs : Integrable (fun t => star (ψ t)) volume := by
    apply hψ.norm.mono' hψ.aestronglyMeasurable.star
    filter_upwards [] with t
    change ‖star (ψ t)‖ ≤ ‖ψ t‖
    exact (norm_star (ψ t)).le
  have hw : Integrable w μ := hφ.mul_prod hψs
  have hfm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      (U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1))) (μ.prod volume) := by
    apply aestronglyMeasurable_field_apply
    · intro ξ
      exact ((hU ξ).comp (continuous_fst.comp continuous_fst)).aestronglyMeasurable
    · exact ((Lp.stronglyMeasurable f).comp_measurable
        (measurable_snd.add (measurable_fst.comp measurable_fst))).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      (U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))) (μ.prod volume) := by
    apply aestronglyMeasurable_field_apply
    · intro ξ
      exact ((hU ξ).comp (continuous_snd.comp continuous_fst)).aestronglyMeasurable
    · exact ((Lp.stronglyMeasurable g).comp_measurable
        (measurable_snd.add (measurable_snd.comp measurable_fst))).aestronglyMeasurable
  have hf2 : Integrable (fun t : ℝ => ‖f t‖ ^ 2) volume :=
    (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hg2 : Integrable (fun t : ℝ => ‖g t‖ ^ 2) volume :=
    (Lp.memLp g).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hb₁ := integrable_weighted_translate μ (fun q => ‖w q‖ * ‖A‖)
    (hw.norm.mul_const ‖A‖) Prod.fst measurable_fst
    (fun t => ‖f t‖ ^ 2) hf2 ((Lp.stronglyMeasurable f).norm.pow 2)
  have hb₂ := integrable_weighted_translate μ (fun q => ‖w q‖ * ‖A‖)
    (hw.norm.mul_const ‖A‖) Prod.snd measurable_snd
    (fun t => ‖g t‖ ^ 2) hg2 ((Lp.stronglyMeasurable g).norm.pow 2)
  apply (hb₁.add hb₂).mono'
    (hw.aestronglyMeasurable.comp_fst.mul
      (hfm.inner (A.continuous.comp_aestronglyMeasurable hgm)))
  filter_upwards [] with p
  change ‖w p.1 * inner ℂ _ _‖ ≤
    ‖w p.1‖ * ‖A‖ * ‖f (p.2 + p.1.1)‖ ^ 2 +
      ‖w p.1‖ * ‖A‖ * ‖g (p.2 + p.1.2)‖ ^ 2
  rw [norm_mul]
  have hinner : ‖inner ℂ
      ((U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1)))
      (A ((U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))))‖ ≤
      ‖A‖ * (‖f (p.2 + p.1.1)‖ * ‖g (p.2 + p.1.2)‖) := by
    apply (norm_inner_le_norm _ _).trans
    calc
      _ ≤ ‖(U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1))‖ *
          (‖A‖ * ‖(U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))‖) :=
        mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = _ := by rw [Unitary.norm_map, Unitary.norm_map]; ring
  have hquad : ‖f (p.2 + p.1.1)‖ * ‖g (p.2 + p.1.2)‖ ≤
      ‖f (p.2 + p.1.1)‖ ^ 2 + ‖g (p.2 + p.1.2)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f (p.2 + p.1.1)‖ - ‖g (p.2 + p.1.2)‖)]
  calc
    _ ≤ ‖w p.1‖ * (‖A‖ * (‖f (p.2 + p.1.1)‖ * ‖g (p.2 + p.1.2)‖)) :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ ≤ ‖w p.1‖ * (‖A‖ * (‖f (p.2 + p.1.1)‖ ^ 2 + ‖g (p.2 + p.1.2)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hquad (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialSeparability
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- A pair of nonzero vectors witnesses nontriviality after completion. -/
instance spatialHilbert_nontrivial [Nontrivial H] [Nontrivial K] :
    Nontrivial (SpatialHilbert H K) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨y, hy⟩ := exists_ne (0 : K)
  refine ⟨⟨tensorVector y x, 0, ?_⟩⟩
  intro he
  have hn := congrArg norm he
  rw [norm_tensorVector_apply, norm_zero] at hn
  exact (mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)) hn

end

end KadisonKastler

end OAI
end


