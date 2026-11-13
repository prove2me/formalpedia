-- Prove2me | Definitions.Def_Q260K024
-- name    : Q260K024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:17:20.770051+00:00
-- url     : https://prove2.me/theorems/e4751d8a-0a3d-48b6-be92-af2e5e2bc605
-- title:
--   Definitions bundle Q260K024 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 90 declarations of OpenAI's Lean: 11 definitions, 1 instance and 78 theorems. The definitions and types are `OAI.KadisonKastler.compatibleMatrixFrames`, `OAI.KadisonKastler.regularActionIntegral`, `OAI.KadisonKastler.regularGaugedCoordinates`, `OAI.KadisonKastler.regularLocalFrame`, `OAI.KadisonKastler.regularLocalFrameValue`, `OAI.KadisonKastler.regularLocalizationAverage`, `OAI.KadisonKastler.regularLocalizationAverageLinear`, `OAI.KadisonKastler.regularNormalizedIntervalAverage`, `OAI.KadisonKastler.regularPacketConvolution`, `OAI.KadisonKastler.regularPacketProjection`, `OAI.KadisonKastler.twoRatioScalingSites`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CanonicalAmplification`, `KadisonKastler_CharacterPacketTotality`, `KadisonKastler_CompatibleMatrixFrames`, `KadisonKastler_CountableAmplificationNormal`, `KadisonKastler_CountableOperatorEntries`, `KadisonKastler_FourierShiftedFields`, `KadisonKastler_L2FourierIntertwining`, `KadisonKastler_L2GaugeStarTransport`, `KadisonKastler_L2Intertwining`, `KadisonKastler_NormUltraproduct`, `KadisonKastler_ProductBoundaryLifts`, `KadisonKastler_ProductInvariantL2`, `KadisonKastler_RegularCommutantFourier`, `KadisonKastler_RegularCommutantPackets`, `KadisonKastler_RegularConvolutionCoefficients`, `KadisonKastler_RegularConvolutionOperators`, `KadisonKastler_RegularCoreActions`, `KadisonKastler_RegularCoreAlgebra`, `KadisonKastler_RegularCoreCharacters`, `KadisonKastler_RegularCoreCommutant`, `KadisonKastler_RegularCoreRepresentation`, `KadisonKastler_RegularFourierTransport`, `KadisonKastler_RegularIntervalAverages`, `KadisonKastler_RegularLocalizationAverage`, `KadisonKastler_RegularLocalizationNormal`, `KadisonKastler_RegularLocalizationReconstruction`, `KadisonKastler_RegularLocalizedPackets`, `KadisonKastler_RegularPacketAveraging`, `KadisonKastler_RegularPacketCompression`, `KadisonKastler_RegularPacketIntegrals`, `KadisonKastler_TwoRatioScalingWords`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K017`, `Q260K018` and `Q260K019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K028` and `Q260K030`; the statement `OAI_KadisonKastler_constructed_exists_common_action_of_comparison_normalizers`; the proofs of `OAI.KadisonKastler.regularCoreEmbedding_symmetry_of_balance`, `OAI.KadisonKastler.regularCore_central_fourier_field`, `OAI.KadisonKastler.regularCore_constant_central_scalar` and `OAI.KadisonKastler.scalarCenter_regularCore_of_two_site_frequencies`.
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
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
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
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
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
import Definitions.Def_Q260K017
import Definitions.Def_Q260K018
import Definitions.Def_Q260K019

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport and the canonical infinite amplification

Transport into the initial coordinate preserves the unit balls and their
Hausdorff distance. The abstract diagonal action obtained from the matrix
units is exactly the coordinatewise action on the Hilbert direct sum.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (H)

theorem l2DiagonalHom_injective : Function.Injective (l2DiagonalHom (E := H)) := by
  intro T S h
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun R : CountableHilbertSum H →L[ℂ] CountableHilbertSum H =>
    R (lp.single 2 0 x) 0) h
  change l2Diagonal T (lp.single 2 0 x) 0 = l2Diagonal S (lp.single 2 0 x) 0 at he
  simpa only [l2Diagonal_apply, lp.single_apply, Pi.single_eq_same] using he

theorem norm_l2Diagonal (T : H →L[ℂ] H) : ‖l2Diagonal T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map (l2DiagonalHom (E := H)) (l2DiagonalHom_injective H) T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem regularGauge_apply_ae (f : RegularCoreHilbert H) :
    (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t) :=
  regularUnitaryField_apply_ae volume _ _ _ f

theorem regularGauge_star_apply_ae (f : RegularCoreHilbert H) :
    (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (f t) := by
  let b := regularUnitaryFieldApply volume (fun t => star (U (Multiplicative.ofAdd t)))
    (regularGroup_star_measurable U hU) f
  have hb : b =ᵐ[volume] fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (f t) :=
    regularUnitaryFieldApply_ae volume _ _ f
  have hback : (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) b = f := by
    apply Lp.ext
    filter_upwards [regularGauge_apply_ae U hU b, hb] with t hG hb
    rw [hG, hb]
    exact congrArg (fun T : H →L[ℂ] H => T (f t))
      (Unitary.mul_star_self_of_mem (U (Multiplicative.ofAdd t)).property)
  have heq : (star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f = b := by
    apply (Unitary.linearIsometryEquiv (regularGauge U hU)).injective
    change (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) b
    rw [hback]
    exact congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => T f)
      (Unitary.mul_star_self_of_mem (regularGauge U hU).property)
  rw [heq]
  exact hb

theorem regularCoreEmbedding_apply_ae (T : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    regularCoreEmbedding U hU T f =ᵐ[volume] fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H)
        (T ((U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t))) := by
  change (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU)))
    (regularConstantHom volume T) f =ᵐ[volume] _
  rw [Unitary.conjStarAlgAut_star_apply]
  change (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularConstantHom volume T
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) =ᵐ[volume] _
  filter_upwards [regularGauge_star_apply_ae U hU
      (regularConstantHom volume T
        ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    regularConstantHom_apply_ae volume T
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_apply_ae U hU f] with t hs hc hg
  rw [hs, hc, hg]

/-- The gauge turns the common regular action into ordinary translation. -/
theorem regularGauge_intertwines_action (s : Multiplicative ℝ) :
    (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularCoreAction U s =
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularGauge U hU := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularGauge_apply_ae U hU
      ((regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCoreAction_apply_ae U s f,
    regularRightTranslation_apply_ae s
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularGauge_apply_ae U hU f)] with t hG hA hR hGs
  simp only [Function.comp_def] at hGs
  change (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t =
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hG, hA, hR, hGs]
  have hmul : U (Multiplicative.ofAdd (t + s.toAdd)) =
      U (Multiplicative.ofAdd t) * U s := map_mul U _ _
  rw [hmul, Submonoid.coe_mul, mul_apply_eq_comp]

theorem regularCoreAction_eq_gauged_translation (s : Multiplicative ℝ) :
    (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU))
        (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [Unitary.conjStarAlgAut_star_apply]
  have h := congrArg
    (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * T)
    (regularGauge_intertwines_action U hU s)
  simpa only [← mul_assoc, Unitary.coe_star,
    Unitary.star_mul_self_of_mem (regularGauge U hU).property, one_mul] using h

/-- Every embedded operator is fixed by the common regular action. -/
theorem regularCoreEmbedding_fixed (s : Multiplicative ℝ) (T : H →L[ℂ] H) :
    unitaryConj (regularCoreAction U s) (regularCoreEmbedding U hU T) =
      regularCoreEmbedding U hU T := by
  apply (commute_unitary_iff_star_right_conjugate (regularCoreAction U s).property).mp
  have h := (regularConstant_commute_translation T s).symm.map
    (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU)))
  rw [← regularCoreAction_eq_gauged_translation U hU s] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCharacters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Translation/character covariance, proved directly on `L²` classes. -/
theorem regularTranslation_character_covariance (a : ℝ) (s : Multiplicative ℝ) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularCharacterUnitary (H := H) a =
      regularCharacterScalar a s.toAdd •
        ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
          regularRightTranslation (H := H) s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularRightTranslation_apply_ae s
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularCharacterUnitary_apply_ae a f),
    regularCharacterUnitary_apply_ae a
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f,
    Lp.coeFn_smul (regularCharacterScalar a s.toAdd)
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))]
    with t hρQ hQshift hQρ hρ hsmul
  simp only [Function.comp_def] at hQshift
  change (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t =
    (regularCharacterScalar a s.toAdd •
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))) t
  rw [hρQ, hQshift, hsmul]
  simp only [Pi.smul_apply]
  rw [hQρ, hρ, regularCharacterScalar_add_right, smul_smul, mul_comm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CharacterPacketTotality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-! # Totality of character translates of a nonvanishing scalar packet

Fourier uniqueness proves totality on the actual vector-valued `L²` space.
No countability or pointwise choice of vector representatives is needed.
-/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every vector orthogonal to all character translates of the packet is zero. -/
theorem eq_zero_of_inner_character_packets
    (φ : RegularCoreHilbert ℂ) (hφ : ∀ᵐ t : ℝ, φ t ≠ 0)
    (g : RegularCoreHilbert H)
    (hg : ∀ s : ℝ, ∀ x : H,
      inner ℂ ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularTensorVector φ x)) g = 0) :
    g = 0 := by
  let f : ℝ → H := fun t => star (φ t) • g t
  have hi : Integrable f :=
    memLp_one_iff_integrable.mp ((Lp.memLp g).smul (Lp.memLp φ).star)
  have hf (s : ℝ) : 𝓕 f s = 0 := by
    apply ext_inner_left ℂ
    intro x
    rw [inner_zero_right, Real.fourier_eq]
    have hconv := (Real.fourierIntegral_convergent_iff s).mpr hi
    change (innerSL ℂ x) (∫ t : ℝ, (Real.fourierChar (-inner ℝ t s) : ℂ) • f t) = 0
    have hconv' : Integrable (fun t : ℝ =>
        (Real.fourierChar (-inner ℝ t s) : ℂ) • f t) := by
      simpa only [Circle.smul_def] using hconv
    rw [← (innerSL ℂ x).integral_comp_comm hconv']
    calc
      _ = inner ℂ ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularTensorVector φ x)) g := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [regularCharacterUnitary_apply_ae (2 * Real.pi * s)
          (regularTensorVector φ x), regularTensorVector_apply_ae φ x] with t ht hx
        rw [ht, hx]
        change inner ℂ x ((Real.fourierChar (-inner ℝ t s) : ℂ) • (star (φ t) • g t)) = _
        simp only [inner_smul_left, inner_smul_right]
        rw [show inner ℝ t s = t * s by simp [RCLike.inner_apply, mul_comm],
          fourierChar_eq_star_character]
        simp only [starRingEnd_apply]
      _ = 0 := hg s x
  have hzero := ae_zero_of_integrable_fourier_zero hi hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero, hφ] with t ht hne
  change star (φ t) • g t = 0 at ht
  exact (smul_eq_zero.mp ht).resolve_left (star_ne_zero.mpr hne)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompatibleMatrixFrames
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compatible finite groups for an increasing matrix chain

The finite index set is retained as data, so tensor refinements do not
require changing the represented operators or reindexing to a fixed type.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] {A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)}

/-- Choose compatible frames without changing any algebra in the chain. -/
def compatibleMatrixFrames (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A) :
    ∀ n, FullMatrixFrame (A n)
  | 0 => F 0
  | n + 1 => Classical.choose
      (FullMatrixFrame.exists_refinement (compatibleMatrixFrames F hA n) (F (n + 1))
        (hA (Nat.le_succ n)))

theorem compatibleMatrixFrames_group_monotone
    (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A) :
    Monotone (fun n => (compatibleMatrixFrames F hA n).group) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Classical.choose_spec
    (FullMatrixFrame.exists_refinement (compatibleMatrixFrames F hA n) (F (n + 1))
      (hA (Nat.le_succ n)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableAmplificationNormal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.countableOperatorEntry_apply _root_.OAI.KadisonKastler.countableOperatorEntry_diagonal_mul _root_.OAI.KadisonKastler.countableOperatorEntry_mul_diagonal _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

instance countableHilbertSum_separable [SeparableSpace H] :
    SeparableSpace (CountableHilbertSum H) := by
  let s : Set (CountableHilbertSum H) :=
    ⋃ n : ℕ, Set.range (lp.single (E := fun _ : ℕ => H) 2 n)
  have hs : IsSeparable s := .iUnion fun n => isSeparable_range
    ((lp.isometry_single (E := fun _ : ℕ => H) (p := 2) n).continuous)
  have hd : Dense (Submodule.span ℂ s : Set (CountableHilbertSum H)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) x)
    apply Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro n _
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨n, ⟨x n, rfl⟩⟩)
  apply isSeparable_univ_iff.mp
  rw [← hd.closure_eq]
  exact hs.span.closure

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableOperatorEntries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Entries of operators on a countable Hilbert sum

Entrywise identities detect equality and diagonal commutation. Under the
countable tensor unitary, tensoring an operator on the sum tensors each
of its entries. No summability of the operator's matrix is assumed.
-/

namespace KadisonKastler

open UnitalTomsWinter Filter
open scoped TensorProduct Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem countableOperator_ext
    {S T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H}
    (h : ∀ i j, countableOperatorEntry S i j = countableOperatorEntry T i j) : S = T := by
  have hs (j : ℕ) (x : H) : S (lp.single 2 j x) = T (lp.single 2 j x) := by
    ext i
    exact DFunLike.congr_fun (h i j) x
  apply ContinuousLinearMap.ext
  intro x
  have h₁ := S.continuous.continuousAt.tendsto.comp (lp.hasSum_single (by norm_num) x)
  have h₂ := T.continuous.continuousAt.tendsto.comp (lp.hasSum_single (by norm_num) x)
  change Tendsto (fun s : Finset ℕ => S (∑ i ∈ s, lp.single 2 i (x i)))
    atTop (𝓝 (S x)) at h₁
  change Tendsto (fun s : Finset ℕ => T (∑ i ∈ s, lp.single 2 i (x i)))
    atTop (𝓝 (T x)) at h₂
  have he : (fun s : Finset ℕ => S (∑ i ∈ s, lp.single 2 i (x i))) =
      (fun s : Finset ℕ => T (∑ i ∈ s, lp.single 2 i (x i))) := by
    funext s
    simp only [map_sum, hs]
  rw [he] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem countableOperator_commutes_diagonal_iff
    (a : H →L[ℂ] H) (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) :
    l2Diagonal a * S = S * l2Diagonal a ↔
      ∀ i j, a * countableOperatorEntry S i j = countableOperatorEntry S i j * a := by
  constructor
  · intro h i j
    simpa only [countableOperatorEntry_diagonal_mul, countableOperatorEntry_mul_diagonal]
      using congrArg (fun T => countableOperatorEntry T i j) h
  · intro h
    apply countableOperator_ext
    intro i j
    simpa only [countableOperatorEntry_diagonal_mul, countableOperatorEntry_mul_diagonal]
      using h i j

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace H] [CompleteSpace K]

theorem countableOperatorEntry_spatialLeft
    (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) :
    countableOperatorEntry
      ((countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv (spatialLeft S)) i j =
      spatialLeft (K := K) (countableOperatorEntry S i j) := by
  apply spatialTensorOp_ext
  intro x y
  simp only [countableOperatorEntry_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    countableTensorEquiv_symm_single]
  change countableTensorEquiv
      (spatialTensorOp S 1 ((lp.single 2 j x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K)) i = _
  simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self,
    countableTensorEquiv_tmul, countableTensorVector_apply]
  change _ = spatialTensorOp (countableOperatorEntry S i j) 1 _
  simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self,
    countableOperatorEntry_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularFourierTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem fourier_translate_schwartz_p1 (s : ℝ) (f : SchwartzMap ℝ H) :
    (𝓕 (regularTranslateApply s (f.toLp 2)) : RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (𝓕 (f.toLp 2)) := by
  rw [← translate_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (SchwartzMap.compSubConstCLM ℂ (-s) f)).coeFn_toLp 2,
    (𝓕 f).coeFn_toLp 2, regularCharacterUnitary_apply_ae (2 * Real.pi * s) ((𝓕 f).toLp 2)]
    with t h₁ h₂ h₃
  rw [h₁, h₃, h₂, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have he : (SchwartzMap.compSubConstCLM ℂ (-s) f : ℝ → H) =
      (f : ℝ → H) ∘ (fun t => t + s) := by
    funext t
    simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, Function.comp_apply]
  rw [he]
  simp only [Real.fourier_real_eq]
  change Fourier.fourierIntegral Real.fourierChar volume ((f : ℝ → H) ∘ (fun t => t + s)) t = _
  rw [Fourier.fourierIntegral_comp_add_right]
  simp only [Fourier.fourierIntegral, VectorFourier.fourierIntegral, Circle.smul_def,
    Real.fourierChar_apply', regularCharacterScalar, mul_assoc]
  rfl

/-- Right translation becomes multiplication by the positive Fourier character. -/
theorem fourier_regularTranslateApply (s : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularTranslateApply s f) : RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  let R : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularTranslationEquiv (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  have he : F.comp R = C.comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer (F.comp R).continuous (C.comp F).continuous
    funext g
    exact fourier_translate_schwartz_p1 s g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

/-- Translation generators become the complete scalar-character family. -/
theorem fourierConj_regularTranslation (s : ℝ) :
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (𝓕 (regularTranslateApply s ((Lp.fourierTransformₗᵢ ℝ H).symm f)) :
    RegularCoreHilbert H) = _
  rw [fourier_regularTranslateApply]
  exact congrArg
    (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    ((Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply f)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2Intertwining
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem compLp_regularGauge (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (f : RegularCoreHilbert H) :
    L.compLp ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (regularGauge V hV : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_apply_ae U hU f, regularGauge_apply_ae V hV (L.compLp f),
    L.coeFn_compLp f] with t hl hu hv hf
  rw [hl, hu, hv, hf, hL]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

/-- The field formula for the regular embedding preserves the concrete
tensor algebra whenever the original group normalizes `P`. -/
theorem regularCoreEmbedding_mem_tensorAlgebra (P : VonNeumannAlgebra H)
    (hP : ∀ s T, T ∈ P → unitaryConj (U s) T ∈ P)
    {T : H →L[ℂ] H} (hT : T ∈ P) :
    regularCoreEmbedding U hU T ∈ regularTensorAlgebra P := by
  apply (mem_regularTensorAlgebra_iff P _).mpr
  intro z hz
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularConstantHom_apply_ae volume z (regularCoreEmbedding U hU T f),
    regularCoreEmbedding_apply_ae U hU T f,
    regularCoreEmbedding_apply_ae U hU T (regularConstantHom volume z f),
    regularConstantHom_apply_ae volume z f] with t hleft hπ hright hzv
  change regularConstantHom volume z (regularCoreEmbedding U hU T f) t =
    regularCoreEmbedding U hU T (regularConstantHom volume z f) t
  rw [hleft, hπ, hright, hzv]
  have ht : unitaryConj (star (U (Multiplicative.ofAdd t))) T ∈ P := by
    rw [regularGroup_star_eq U t]
    exact hP _ T hT
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hz _ ht).symm
  have he := congrArg (fun A : H →L[ℂ] H => A (f t)) hc
  simpa only [unitaryConj, Unitary.coe_star, star_star,
    mul_apply_eq_comp] using he

/-- The generator calculation proves the first core fixed-point inclusion. -/
theorem regularCoreAlgebra_le_fixed (P : VonNeumannAlgebra H)
    (hP : ∀ s T, T ∈ P → unitaryConj (U s) T ∈ P) :
    regularCoreAlgebra U hU P ≤
      fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P) := by
  apply generatedAlgebra_le_of_le
  apply StarAlgebra.adjoin_le
  rintro T (⟨x, hx, rfl⟩ | ⟨s, rfl⟩)
  · exact (mem_fixedPointAlgebra_iff _ _ _).mpr
      ⟨regularCoreEmbedding_mem_tensorAlgebra U hU P hP hx,
        fun s => regularCoreEmbedding_fixed U hU s x⟩
  · exact (mem_fixedPointAlgebra_iff _ _ _).mpr
      ⟨regularTranslation_mem_tensorAlgebra P s, fun t => regularTranslation_fixed U t s⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierShiftedFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem scalarFourierCut_apply_ae (a : ℝ) (f : RegularCoreHilbert ℂ) :
    scalarFourierCut a f =ᵐ[volume] (Set.Ioi (a / (2 * Real.pi))).indicator f := by
  have h := regularFrequencyProjection_apply_fourier a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
    (regularFrequencyProjection a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)) =ᵐ[volume]
    (Set.Ioi (a / (2 * Real.pi))).indicator
      ((Lp.fourierTransformₗᵢ ℝ ℂ) ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)) at h
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
    (regularFrequencyProjection a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)) =ᵐ[volume] _
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2GaugeStarTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Intertwining the adjoint regular gauge -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem compLp_regularGauge_star (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (f : RegularCoreHilbert H) :
    L.compLp ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_star_apply_ae U hU f,
    regularGauge_star_apply_ae V hV (L.compLp f), L.coeFn_compLp f]
    with t hl hu hv hf
  rw [hl, hu, hv, hf]
  have hu' := regularGroup_star_eq U t
  have hv' := regularGroup_star_eq V t
  change L ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (f t)) =
    (star (V (Multiplicative.ofAdd t)) : K →L[ℂ] K) (L (f t))
  have huC : star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) :=
    congrArg (fun w : unitary (H →L[ℂ] H) => (w : H →L[ℂ] H)) hu'
  have hvC : star (V (Multiplicative.ofAdd t) : K →L[ℂ] K) =
      (V (Multiplicative.ofAdd (-t)) : K →L[ℂ] K) :=
    congrArg (fun w : unitary (K →L[ℂ] K) => (w : K →L[ℂ] K)) hv'
  rw [huC, hvC]
  exact hL (Multiplicative.ofAdd (-t)) (f t)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2FourierIntertwining
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem compLp_regularGaugeFrequency (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (a : ℝ) (F : RegularCoreHilbert H) :
    L.compLp ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a ((regularGauge U hU :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) F))) =
    (star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
      (regularFrequencyProjection a ((regularGauge V hV :
        RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp F))) := by
  rw [compLp_regularGauge_star L U V hU hV hL, compLp_regularFrequencyProjection,
    compLp_regularGauge L U V hU hV hL]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence
local instance instStarOrderedRingSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence : StarOrderedRing (VaryingBoundedSequence B) := CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductInvariantL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

section Bounded

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem scalarInfinity_mem_firstInvariantSigma_of_fixed
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity (μ.prod ν))
    (hf : scalarInfinityPullback (firstCoordinateShift S)
      (firstCoordinateShift_quasi hS) f = f) :
    f ∈ lpMeas ℂ ℂ (firstInvariantSigma μ S) ⊤ (μ.prod ν) := by
  have hfix : ∀ᵐ z ∂μ.prod ν,
      scalarInfinityToL2 f (S z.1, z.2) = scalarInfinityToL2 f z := by
    have ha := scalarInfinityPullback_ae (firstCoordinateShift S)
      (firstCoordinateShift_quasi hS) f
    rw [hf] at ha
    filter_upwards [ha, scalarInfinityToL2_ae f,
      (firstCoordinateShift_quasi (ν := ν) hS).ae (scalarInfinityToL2_ae f)]
      with z ha hz hs
    exact hs.trans (ha.symm.trans hz.symm)
  have hm := L2_mem_firstInvariantSigma_of_fixed hS (scalarInfinityToL2 f) hfix
  exact mem_lpMeas_iff_aestronglyMeasurable.mpr
    ((mem_lpMeas_iff_aestronglyMeasurable.mp hm).congr (scalarInfinityToL2_ae f))

end Bounded

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductBoundaryLifts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem exists_firstBoundaryLift_of_measurable (f : ScalarLInfinity (μ.prod ν))
    (hf : f ∈ lpMeas ℂ ℂ (firstInvariantSigma μ S) ⊤ (μ.prod ν)) :
    ∃ g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν), firstBoundaryLiftL μ S g = f := by
  let g₀ := lpMeasToLpTrim ℂ ℂ ⊤ (μ.prod ν) firstInvariantSigma_le ⟨f, hf⟩
  have hg₀ : MemLp (fun z : ShiftBoundarySpace μ S × Y => g₀ z) ⊤
      ((shiftBoundaryMeasure μ S).prod ν) := by
    rw [← firstBoundaryMeasure_eq_trim μ S]
    exact Lp.memLp g₀
  let g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν) := hg₀.toLp (fun z => g₀ z)
  refine ⟨g, Lp.ext ?_⟩
  have hg : g =ᵐ[(shiftBoundaryMeasure μ S).prod ν] fun z => g₀ z := hg₀.coeFn_toLp
  have hp : (fun z => g (firstBoundaryMap μ S z)) =ᵐ[μ.prod ν]
      (fun z => g₀ (firstBoundaryMap μ S z)) :=
    (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae hg
  have h₀ : g₀ =ᵐ[μ.prod ν] f := lpMeasToLpTrim_ae_eq firstInvariantSigma_le ⟨f, hf⟩
  exact (firstBoundaryLiftL_ae μ S g).trans (hp.trans h₀)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Constant operators commute with the actual scalar character multipliers. -/
theorem regularCharacter_commute_constant (a : ℝ) (T : H →L[ℂ] H) :
    Commute (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularConstantHom volume T) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae a (regularConstantHom volume T f),
    regularConstantHom_apply_ae volume T f,
    regularConstantHom_apply_ae volume T
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae a f] with t hQC hC hCQ hQ
  change (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularConstantHom volume T f) t =
    regularConstantHom volume T
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hQC, hC, hCQ, hQ, map_smul]

/-- Scalar characters preserve the tensor algebra. -/
theorem regularCharacter_normalizes_tensor (P : VonNeumannAlgebra H)
    (a : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularCharacterRepresentation (H := H) a) T ∈ regularTensorAlgebra P :=
  tensor_mem_conjugate_of_constant_commute P _
    (regularCharacter_commute_constant a.toAdd) hT

/-- The regular and character actions commute as inner automorphisms. -/
theorem regularCore_character_actions_commute
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (s a : Multiplicative ℝ)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    unitaryConj (regularCoreAction U s)
        (unitaryConj (regularCharacterRepresentation (H := H) a) T) =
      unitaryConj (regularCharacterRepresentation (H := H) a)
        (unitaryConj (regularCoreAction U s) T) := by
  let c : ℂ := regularCharacterScalar a.toAdd s.toAdd
  have hc : c * star c = 1 := by
    rw [mul_comm]
    change star (regularCharacterScalar a.toAdd s.toAdd) *
      regularCharacterScalar a.toAdd s.toAdd = 1
    rw [Complex.star_def, Complex.conj_mul']
    simp only [regularCharacterScalar, Circle.norm_coe, one_pow, Complex.ofReal_one]
  apply conjugations_commute_of_scalar_product _ _ c hc
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularConstantHom volume (U s : H →L[ℂ] H)
  let R : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  let Q : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (regularCharacterUnitary (H := H) a.toAdd :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  change (C * R) * Q = c • (Q * (C * R))
  have hRQ : R * Q = c • (Q * R) := regularTranslation_character_covariance a.toAdd s
  have hCQ : C * Q = Q * C :=
    (regularCharacter_commute_constant (H := H) a.toAdd (U s : H →L[ℂ] H)).eq.symm
  calc
    (C * R) * Q = C * (R * Q) := mul_assoc _ _ _
    _ = C * (c • (Q * R)) := congrArg (fun X => C * X) hRQ
    _ = c • (C * (Q * R)) := mul_smul_comm _ _ _
    _ = c • ((C * Q) * R) := by rw [mul_assoc]
    _ = c • ((Q * C) * R) := by rw [hCQ]
    _ = c • (Q * (C * R)) := by rw [mul_assoc]

/-- The dual character action preserves the actual core fixed algebra. -/
theorem regularCharacter_normalizes_coreFixed
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (a : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)) :
    unitaryConj (regularCharacterRepresentation (H := H) a) T ∈
      fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P) := by
  exact normalizes_fixedPointAlgebra_of_commuting_actions
    (regularCoreAction U) regularCharacterRepresentation (regularTensorAlgebra P)
    (fun b S hS => regularCharacter_normalizes_tensor P b hS)
    (regularCore_character_actions_commute U) a T hT

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The reverse core inclusion follows by applying the published
commutant formula and then taking one more commutant. -/
theorem regularCoreAlgebra_eq_fixed_of_published
    [TopologicalSpace.SeparableSpace H]
    (hComm : PublishedRegularCommutant.{u})
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (P : VonNeumannAlgebra H)
    (hP : ∀ s T, T ∈ P → unitaryConj (U s) T ∈ P) :
    regularCoreAlgebra U hU P =
      fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P) := by
  apply le_antisymm (regularCoreAlgebra_le_fixed U hU P hP)
  intro T hT
  have he := hComm H U hU P hP
  have hle : (regularCoreAlgebra U hU P).commutant ≤
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra P)).commutant := by
    rw [he]
    exact regularCommutantAlgebra_le_fixed_commutant U P
  have hm : T ∈ (regularCoreAlgebra U hU P).commutant.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro S hS
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hle hS) T hT).symm
  simpa only [VonNeumannAlgebra.commutant_commutant] using hm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCommutantFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete Fourier reductions for the regular commutant theorem

Translation commutation gives an actual bounded measurable Fourier field.
Adjoining the character multipliers to the regular core generates the
whole constant-commutant tensor algebra. These conclusions use the proved
spectral and diagonal decomposition theorems, not a crossed-product
commutant assumption.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Fourier transformation sends translation commutation to character commutation. -/
theorem fourier_commute_characters_of_translations
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s : Multiplicative ℝ, Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) (a : ℝ) :
    Commute ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  let s : ℝ := a / (2 * Real.pi)
  have hs : 2 * Real.pi * s = a := by dsimp [s]; field_simp
  have he := congrArg (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
    (hT (Multiplicative.ofAdd s)).eq
  change _ * _ = _ * _
  simpa only [map_mul, fourierConj_regularTranslation, hs] using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCommutantPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem regularGaugedPacket_apply_ae (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularGaugedPacket U hU φ ξ =ᵐ[volume] fun t =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (φ t • ξ) := by
  filter_upwards [regularGauge_star_apply_ae U hU (regularTensorVector φ ξ),
    regularTensorVector_apply_ae φ ξ] with t hg hφ
  exact hg.trans (congrArg (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) hφ)

/-- The packet inclusion intertwines the original and regular actions. -/
theorem regularGaugedPacket_intertwines
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    (regularCoreEmbedding U hU A).comp (regularGaugedPacket U hU φ) =
      (regularGaugedPacket U hU φ).comp A := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU A (regularGaugedPacket U hU φ ξ),
    regularGaugedPacket_apply_ae U hU φ ξ,
    regularGaugedPacket_apply_ae U hU φ (A ξ)] with t hπ hφ hA
  change regularCoreEmbedding U hU A (regularGaugedPacket U hU φ ξ) t =
    regularGaugedPacket U hU φ (A ξ) t
  rw [hπ, hφ, hA]
  have hc : (U (Multiplicative.ofAdd t) : H →L[ℂ] H)
      ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (φ t • ξ)) = φ t • ξ := by
    exact congrArg (fun B : H →L[ℂ] H => B (φ t • ξ))
      (Unitary.mul_star_self_of_mem (U (Multiplicative.ofAdd t)).property)
  rw [hc, map_smul]

/-- The adjoint packet intertwines in the reverse direction. -/
theorem regularGaugedPacket_adjoint_intertwines
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    (regularGaugedPacket U hU φ).adjoint.comp (regularCoreEmbedding U hU A) =
      A.comp (regularGaugedPacket U hU φ).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint
    (regularGaugedPacket_intertwines U hU φ (star A))
  have he : (regularCoreEmbedding U hU (star A)).adjoint = regularCoreEmbedding U hU A := by
    rw [StarHomClass.map_star, ← ContinuousLinearMap.star_eq_adjoint, star_star]
  have ha : (star A).adjoint = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_star]
  simpa only [ContinuousLinearMap.adjoint_comp, he, ha] using h

/-- Core commutation forces every packet coefficient into the original commutant. -/
theorem regularPacketCoefficient_mem_commutant (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ A ∈ P, Commute T (regularCoreEmbedding U hU A))
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    regularPacketCoefficient U hU T φ ψ ∈ P.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro A hA
  apply ContinuousLinearMap.ext
  intro ξ
  change A ((regularGaugedPacket U hU φ).adjoint (T (regularGaugedPacket U hU ψ ξ))) =
    (regularGaugedPacket U hU φ).adjoint (T (regularGaugedPacket U hU ψ (A ξ)))
  have hleft := congrArg (fun B : RegularCoreHilbert H →L[ℂ] H =>
    B (T (regularGaugedPacket U hU ψ ξ)))
    (regularGaugedPacket_adjoint_intertwines U hU φ A)
  have hright := congrArg (fun B : H →L[ℂ] RegularCoreHilbert H => B ξ)
    (regularGaugedPacket_intertwines U hU ψ A)
  have hcomm := congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    B (regularGaugedPacket U hU ψ ξ)) (hT A hA).eq
  change (regularGaugedPacket U hU φ).adjoint
    (regularCoreEmbedding U hU A (T (regularGaugedPacket U hU ψ ξ))) =
    A ((regularGaugedPacket U hU φ).adjoint (T (regularGaugedPacket U hU ψ ξ))) at hleft
  change regularCoreEmbedding U hU A (regularGaugedPacket U hU ψ ξ) =
    regularGaugedPacket U hU ψ (A ξ) at hright
  change T (regularCoreEmbedding U hU A (regularGaugedPacket U hU ψ ξ)) =
    regularCoreEmbedding U hU A (T (regularGaugedPacket U hU ψ ξ)) at hcomm
  rw [← hleft, ← hcomm, hright]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularConvolutionOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

include hU in
/-- The common regular action inherits strong continuity from translations. -/
theorem continuous_regularCoreAction (f : RegularCoreHilbert H) :
    Continuous (fun t : ℝ => (regularCoreAction U (Multiplicative.ofAdd t) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
  have he (t : ℝ) :
      (regularCoreAction U (Multiplicative.ofAdd t) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularTranslateApply t
          ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) := by
    rw [regularCoreAction_eq_gauged_translation U hU]
    rw [Unitary.conjStarAlgAut_star_apply]
    rfl
  simp_rw [he]
  exact (star (regularGauge U hU) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).continuous.comp
      (continuous_regularTranslateApply _)

/-- The convolution convention uses the action at `-t`. -/
def regularActionIntegral (w : ℝ → ℂ) (hw : Integrable w volume) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  weightedOperatorIntegral volume w hw
    (fun t => (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (fun f => ((continuous_regularCoreAction U hU f).comp continuous_neg).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall fun t => regularCoreAction_norm_le_one U (-t))

/-- No normalizer hypothesis is needed for these explicit generators. -/
theorem regularActionIntegral_mem (P : VonNeumannAlgebra H)
    (w : ℝ → ℂ) (hw : Integrable w volume) :
    regularActionIntegral U hU w hw ∈ regularCommutantAlgebra U P := by
  apply weightedOperatorIntegral_mem
  apply Filter.Eventually.of_forall
  intro t
  exact subset_generatedVonNeumannAlgebra _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨Multiplicative.ofAdd (-t), rfl⟩))

/-- The finite packet average has a factored, algebra-valued realization. -/
def regularPacketConvolution
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularActionIntegral U hU φ hφ * regularConstantHom (volume : Measure ℝ) A *
    star (regularActionIntegral U hU ψ hψ)

theorem regularPacketConvolution_mem (P : VonNeumannAlgebra H)
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    {A : H →L[ℂ] H} (hA : A ∈ P.commutant) :
    regularPacketConvolution U hU φ ψ hφ hψ A ∈ regularCommutantAlgebra U P := by
  apply (regularCommutantAlgebra U P).mul_mem
  · apply (regularCommutantAlgebra U P).mul_mem
    · exact regularActionIntegral_mem U hU P φ hφ
    · exact subset_generatedVonNeumannAlgebra _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨A, hA, rfl⟩))
  · exact (regularCommutantAlgebra U P).star_mem'
      (regularActionIntegral_mem U hU P ψ hψ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularConvolutionCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

include hU in
theorem integrable_action_vector
    (w : ℝ → ℂ) (hw : Integrable w volume) (f : RegularCoreHilbert H) :
    Integrable (fun t : ℝ => w t •
      (regularCoreAction U (Multiplicative.ofAdd t) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) volume := by
  apply (hw.norm.mul_const ‖f‖).mono'
    (hw.aestronglyMeasurable.smul (continuous_regularCoreAction U hU f).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖w t • (regularCoreAction U (Multiplicative.ofAdd t) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f‖ ≤ ‖w t‖ * ‖f‖
  rw [norm_smul, Unitary.norm_map]

/-- A coefficient of the action integral, with its adjoint moved to the
test vector. -/
theorem inner_regularActionIntegral
    (w : ℝ → ℂ) (hw : Integrable w volume) (f g : RegularCoreHilbert H) :
    inner ℂ f (regularActionIntegral U hU w hw g) =
      ∫ t : ℝ, w t * inner ℂ
        ((regularCoreAction U (Multiplicative.ofAdd t) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) g := by
  change inner ℂ f (∫ t : ℝ, w t •
    (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) = _
  have hi : Integrable (fun t : ℝ => w t •
      (regularCoreAction U (Multiplicative.ofAdd (-t)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) volume := by
    apply (hw.norm.mul_const ‖g‖).mono'
      (hw.aestronglyMeasurable.smul
        ((continuous_regularCoreAction U hU g).comp continuous_neg).aestronglyMeasurable)
    filter_upwards [] with t
    change ‖w t • (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g‖ ≤ ‖w t‖ * ‖g‖
    rw [norm_smul, Unitary.norm_map]
  rw [← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [inner_smul_right, ← regularAction_adjoint U t,
    ContinuousLinearMap.adjoint_inner_right]

/-- The adjoint action integral has the positive-translation formula. -/
theorem regularActionIntegral_star_apply
    (w : ℝ → ℂ) (hw : Integrable w volume) (g : RegularCoreHilbert H) :
    star (regularActionIntegral U hU w hw) g =
      ∫ t : ℝ, star (w t) •
        (regularCoreAction U (Multiplicative.ofAdd t) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g := by
  have hi := integrable_action_vector U hU (fun t => star (w t))
    (integrable_star_weight w hw) g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (∫ t : ℝ, w t •
    (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) g = _
  have hi' : Integrable (fun t : ℝ => w t •
      (regularCoreAction U (Multiplicative.ofAdd (-t)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) volume := by
    apply (hw.norm.mul_const ‖f‖).mono'
      (hw.aestronglyMeasurable.smul
        ((continuous_regularCoreAction U hU f).comp continuous_neg).aestronglyMeasurable)
    filter_upwards [] with t
    change ‖w t • (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f‖ ≤ ‖w t‖ * ‖f‖
    rw [norm_smul, Unitary.norm_map]
  calc
    _ = ∫ t : ℝ, inner ℂ (w t •
        (regularCoreAction U (Multiplicative.ofAdd (-t)) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) g :=
      (integral_inner_left hi' g).symm
    _ = _ := ?_
  rw [← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [inner_smul_left, inner_smul_right, ← regularAction_adjoint U t,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- The two scalar weights and the constant operator are the exact
double-integral kernel of the factored packet convolution. -/
theorem inner_regularPacketConvolution
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    inner ℂ f (regularPacketConvolution U hU φ ψ hφ hψ A g) =
      ∫ q : ℝ, φ q * (∫ u : ℝ, star (ψ u) *
        inner ℂ ((regularCoreAction U (Multiplicative.ofAdd q) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
          (regularConstantHom (volume : Measure ℝ) A
            ((regularCoreAction U (Multiplicative.ofAdd u) :
              RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g))) := by
  change inner ℂ f (regularActionIntegral U hU φ hφ
    (regularConstantHom (volume : Measure ℝ) A
      (star (regularActionIntegral U hU ψ hψ) g))) = _
  rw [inner_regularActionIntegral]
  apply integral_congr_ae
  filter_upwards [] with q
  congr 1
  rw [regularActionIntegral_star_apply]
  have hi := integrable_action_vector U hU (fun u => star (ψ u))
    (integrable_star_weight ψ hψ) g
  rw [← (regularConstantHom (volume : Measure ℝ) A).integral_comp_comm hi]
  rw [← integral_inner ((regularConstantHom (volume : Measure ℝ) A).integrable_comp hi)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [map_smul, inner_smul_right]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizationAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

include hfinite in
theorem localFrame_memLp (f : RegularCoreHilbert H) :
    MemLp (fun r : ℝ => regularIndicatorProjection s hs (regularTranslateApply r f))
      2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    ((regularIndicatorProjection s hs).continuous.comp
      (continuous_regularTranslateApply f)).aestronglyMeasurable).mpr
  exact integrable_norm_local_translation_sq s hs hfinite f

/-- The continuous analysis map of the translated scalar cutoff. -/
def regularLocalFrameValue (f : RegularCoreHilbert H) :
    Lp (RegularCoreHilbert H) 2 (volume : Measure ℝ) :=
  (localFrame_memLp s hs hfinite f).toLp _

theorem regularLocalFrameValue_apply_ae (f : RegularCoreHilbert H) :
    regularLocalFrameValue s hs hfinite f =ᵐ[volume]
      fun r => regularIndicatorProjection s hs (regularTranslateApply r f) :=
  (localFrame_memLp s hs hfinite f).coeFn_toLp

theorem norm_regularLocalFrameValue_sq (f : RegularCoreHilbert H) :
    ‖regularLocalFrameValue s hs hfinite f‖ ^ 2 =
      (volume s).toReal * ‖f‖ ^ 2 := by
  rw [← regular_integral_norm_sq]
  calc
    (∫ r : ℝ, ‖regularLocalFrameValue s hs hfinite f r‖ ^ 2) =
        ∫ r : ℝ, ‖regularIndicatorProjection s hs (regularTranslateApply r f)‖ ^ 2 := by
      apply integral_congr_ae
      exact (regularLocalFrameValue_apply_ae s hs hfinite f).fun_comp
        (fun x => ‖x‖ ^ 2)
    _ = _ := integral_norm_local_translation_sq s hs hfinite f

theorem norm_regularLocalFrameValue (f : RegularCoreHilbert H) :
    ‖regularLocalFrameValue s hs hfinite f‖ = Real.sqrt (volume s).toReal * ‖f‖ := by
  have hsq := norm_regularLocalFrameValue_sq s hs hfinite f
  have hsqrt : (Real.sqrt (volume s).toReal * ‖f‖) ^ 2 =
      (volume s).toReal * ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (ENNReal.toReal_nonneg)]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    (hsq.trans hsqrt.symm)

/-- The translated-cutoff analysis map is bounded with its exact frame constant. -/
def regularLocalFrame : RegularCoreHilbert H →L[ℂ]
    Lp (RegularCoreHilbert H) 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := regularLocalFrameValue s hs hfinite
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite (f + g),
          regularLocalFrameValue_apply_ae s hs hfinite f,
          regularLocalFrameValue_apply_ae s hs hfinite g,
          Lp.coeFn_add (regularLocalFrameValue s hs hfinite f)
            (regularLocalFrameValue s hs hfinite g)] with r hfg hf hg hsum
        rw [hfg, hsum]
        simp only [Pi.add_apply, hf, hg]
        change regularIndicatorProjection s hs
          ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (f + g)) = _
        rw [map_add, map_add]
        rfl
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite (c • f),
          regularLocalFrameValue_apply_ae s hs hfinite f,
          Lp.coeFn_smul c (regularLocalFrameValue s hs hfinite f)] with r hcf hf hsmul
        simp only [RingHom.id_apply]
        rw [hcf, hsmul]
        simp only [Pi.smul_apply, hf]
        change regularIndicatorProjection s hs
          ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (c • f)) =
          c • regularIndicatorProjection s hs (regularTranslateApply r f)
        rw [map_smul, map_smul]
        rfl }
    (Real.sqrt (volume s).toReal)
    (fun f => (norm_regularLocalFrameValue s hs hfinite f).le)

theorem norm_regularLocalFrame_le :
    ‖regularLocalFrame (H := H) s hs hfinite‖ ≤ Real.sqrt (volume s).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  exact (norm_regularLocalFrameValue s hs hfinite f).le

/-- The unnormalized Haar average of localized copies of an operator. -/
def regularLocalizationAverage
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (regularLocalFrame s hs hfinite).adjoint.comp
    ((T.compLpL 2 (volume : Measure ℝ)).comp (regularLocalFrame s hs hfinite))

theorem norm_regularLocalizationAverage_le
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    ‖regularLocalizationAverage s hs hfinite T‖ ≤ (volume s).toReal * ‖T‖ := by
  have he := norm_frame_sandwich_le (regularLocalFrame (H := H) s hs hfinite)
    (T.compLpL 2 (volume : Measure ℝ)) (Real.sqrt (volume s).toReal) ‖T‖
    (Real.sqrt_nonneg _) (norm_regularLocalFrame_le s hs hfinite)
    (T.norm_compLpL_le (p := 2) (μ := (volume : Measure ℝ)))
  rw [Real.sq_sqrt (ENNReal.toReal_nonneg)] at he
  exact he

/-- Matrix coefficients of the Haar average are the actual scalar integrals. -/
theorem inner_regularLocalizationAverage
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (f g : RegularCoreHilbert H) :
    inner ℂ f (regularLocalizationAverage s hs hfinite T g) =
      ∫ r : ℝ, inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
        (T (regularIndicatorProjection s hs (regularTranslateApply r g))) := by
  change inner ℂ f ((regularLocalFrame s hs hfinite).adjoint
    (T.compLpL 2 volume (regularLocalFrame s hs hfinite g))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite f,
    regularLocalFrameValue_apply_ae s hs hfinite g,
    T.coeFn_compLpL (p := 2) (μ := (volume : Measure ℝ))
      (regularLocalFrame s hs hfinite g)] with r hf hg hT
  change inner ℂ (regularLocalFrameValue s hs hfinite f r)
    ((T.compLpL 2 volume (regularLocalFrame s hs hfinite g)) r) = _
  rw [hf, hT]
  change inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
    (T (regularLocalFrameValue s hs hfinite g r)) = _
  rw [hg]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketIntegrals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
theorem integrable_gaugedPacket_pair
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    Integrable (fun t => star (φ t) •
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t)) volume := by
  apply (integrable_scalarPacket_pair φ
    ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)).congr
  filter_upwards [regularGauge_apply_ae U hU f] with t ht
  exact congrArg (fun x : H => star (φ t) • x) ht

/-- The adjoint of a gauged packet integrates the untwisted vector field. -/
theorem regularGaugedPacket_adjoint_apply
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    (regularGaugedPacket U hU φ).adjoint f =
      ∫ t : ℝ, star (φ t) • (U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t) := by
  have he : (regularGaugedPacket U hU φ).adjoint f =
      (regularTensorVector φ).adjoint
        ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
    change (((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).comp
        (regularTensorVector φ)).adjoint) f = _
    simp only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
      ← Unitary.coe_star, star_star, ContinuousLinearMap.comp_apply]
  rw [he, regularTensorVector_adjoint_apply]
  apply integral_congr_ae
  filter_upwards [regularGauge_apply_ae U hU f] with t ht
  exact congrArg (fun x : H => star (φ t) • x) ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

include hU in
theorem integrable_packet_translate
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) (r : ℝ) :
    Integrable (fun q : ℝ => star (φ q) •
      (U (Multiplicative.ofAdd q) : H →L[ℂ] H) (f (r + q))) volume := by
  apply (integrable_gaugedPacket_pair U hU φ (regularTranslateApply r f)).congr
  filter_upwards [regularTranslateApply_ae r f] with q hq
  rw [hq, add_comm q r]

theorem packet_adjoint_translate
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) (r : ℝ) :
    (regularGaugedPacket U hU φ).adjoint (regularTranslateApply r f) =
      ∫ q : ℝ, star (φ q) •
        (U (Multiplicative.ofAdd q) : H →L[ℂ] H) (f (r + q)) := by
  rw [regularGaugedPacket_adjoint_apply]
  apply integral_congr_ae
  filter_upwards [regularTranslateApply_ae r f] with q hq
  rw [hq, add_comm q r]

/-- Haar averaging a packet operator is exactly the constructed
convolution with the same commutant coefficient. -/
theorem integral_packet_orbit_inner_eq
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ))
    (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    (∫ r : ℝ, inner ℂ
      ((regularGaugedPacket U hU φ).adjoint (regularTranslateApply r f))
      (A ((regularGaugedPacket U hU ψ).adjoint (regularTranslateApply r g)))) =
      inner ℂ f (regularPacketConvolution U hU φ ψ hφ hψ A g) := by
  let K : (ℝ × ℝ) × ℝ → ℂ := fun p =>
    (φ p.1.1 * star (ψ p.1.2)) *
      inner ℂ ((U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1)))
        (A ((U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))))
  have hK : Integrable K (((volume : Measure ℝ).prod volume).prod volume) :=
    integrable_regularPacket_kernel U hU φ ψ hφ hψ A f g
  have havg : (∫ r : ℝ, inner ℂ
      ((regularGaugedPacket U hU φ).adjoint (regularTranslateApply r f))
      (A ((regularGaugedPacket U hU ψ).adjoint (regularTranslateApply r g)))) =
      ∫ r : ℝ, ∫ p : ℝ × ℝ, K (p, r) ∂((volume : Measure ℝ).prod volume) := by
    apply integral_congr_ae
    filter_upwards [hK.prod_left_ae] with r hr
    rw [packet_adjoint_translate, packet_adjoint_translate,
      inner_integrals _ _ (integrable_packet_translate U hU φ f r)
        (integrable_packet_translate U hU ψ g r) A,
      integral_prod _ hr]
    apply integral_congr_ae
    filter_upwards [] with q
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [K]
    simp only [inner_smul_left, map_smul, inner_smul_right, starRingEnd_apply, star_star]
    ring
  rw [havg, ← integral_integral_swap hK]
  rw [integral_prod _ hK.integral_prod_left, inner_regularPacketConvolution]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [action_coefficient_integral, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  dsimp only [K]
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizationNormal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded weak continuity of localization averages

The constant representation is a countable diagonal amplification in
scalar Hilbert coordinates. Its bounded weak continuity therefore gives
bounded weak continuity of the translated-cutoff sandwich. This permits
finite packet compressions to be averaged before taking their limit.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Bounded weak operator limits pass through the constant representation. -/
theorem regularConstantHom_tendsto_weak {ι : Type*} {l : Filter ι}
    (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hT : ∀ x y : H, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (S x))))
    (f g : RegularCoreHilbert H) :
    Tendsto (fun i => inner ℂ g (regularConstantHom (volume : Measure ℝ) (T i) f)) l
      (𝓝 (inner ℂ g (regularConstantHom (volume : Measure ℝ) S f))) := by
  let e : RegularCoreHilbert H ≃ₗᵢ[ℂ] CountableHilbertSum H :=
    regularHilbertCoordinates regularScalarBasis
  have he (A : H →L[ℂ] H) :
      inner ℂ (e g) (l2Diagonal A (e f)) =
        inner ℂ g (regularConstantHom (volume : Measure ℝ) A f) := by
    rw [← regularHilbertCoordinates_constant regularScalarBasis A]
    change inner ℂ (e g)
      (e (regularConstantHom (volume : Measure ℝ) A (e.symm (e f)))) = _
    rw [e.symm_apply_apply, e.inner_map_map]
  simpa only [he] using l2Diagonal_tendsto_weak T S C hC hT (e f) (e g)

/-- A localized Haar average preserves every bounded weak operator limit. -/
theorem regularLocalizationAverage_tendsto_weak {ι : Type*} {l : Filter ι}
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (T : ι → RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (C : ℝ)
    (hC : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hT : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (S x))))
    (f g : RegularCoreHilbert H) :
    Tendsto (fun i => inner ℂ g (regularLocalizationAverage s hs hfinite (T i) f)) l
      (𝓝 (inner ℂ g (regularLocalizationAverage s hs hfinite S f))) := by
  have h := regularConstantHom_tendsto_weak T S C hC hT
    (regularLocalFrame s hs hfinite f) (regularLocalFrame s hs hfinite g)
  have he (A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
      inner ℂ g (regularLocalizationAverage s hs hfinite A f) =
        inner ℂ (regularLocalFrame s hs hfinite g)
          (regularConstantHom (volume : Measure ℝ) A
            (regularLocalFrame s hs hfinite f)) := by
    change inner ℂ g ((regularLocalFrame s hs hfinite).adjoint
      (A.compLpL 2 (volume : Measure ℝ) (regularLocalFrame s hs hfinite f))) = _
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
  simpa only [he] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularPacketCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.countableOperatorEntry_apply _root_.OAI.KadisonKastler.countableOperatorEntry_diagonal_mul _root_.OAI.KadisonKastler.countableOperatorEntry_mul_diagonal _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite scalar-packet compressions

Scalar Hilbert coordinates give finite orthogonal projections on the
regular Hilbert space. Their compressions converge boundedly in the
weak operator topology and have the expected finite packet expansion.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- Scalar coordinates after undoing the gauge in the packet inclusions. -/
def regularGaugedCoordinates : RegularCoreHilbert H ≃ₗᵢ[ℂ] CountableHilbertSum H :=
  (Unitary.linearIsometryEquiv (regularGauge U hU)).trans
    (regularHilbertCoordinates regularScalarBasis)

theorem regularGaugedCoordinates_symm_single (i : ℕ) (x : H) :
    (regularGaugedCoordinates U hU).symm (lp.single 2 i x) =
      regularGaugedPacket U hU (regularScalarBasis i) x := by
  change (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    ((regularHilbertCoordinates regularScalarBasis).symm (lp.single 2 i x)) = _
  have hs : (regularHilbertCoordinates (H := H) regularScalarBasis).symm
      (lp.single 2 i x) = regularTensorVector (regularScalarBasis i) x :=
    (regularHilbertSum regularScalarBasis).linearIsometryEquiv_symm_apply_single x
  rw [hs]
  rfl

theorem regularGaugedCoordinates_apply (f : RegularCoreHilbert H) (i : ℕ) :
    regularGaugedCoordinates U hU f i =
      (regularGaugedPacket U hU (regularScalarBasis i)).adjoint f := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h := (regularGaugedCoordinates U hU).inner_map_map
    ((regularGaugedCoordinates U hU).symm (lp.single 2 i x)) f
  rw [LinearIsometryEquiv.apply_symm_apply,
    regularGaugedCoordinates_symm_single, lp.inner_single_left] at h
  exact h

/-- Projection onto finitely many whole vector-valued scalar packets. -/
def regularPacketProjection (s : Finset ℕ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (regularGaugedCoordinates U hU).symm.conjStarAlgEquiv
    ((canonicalMatrixCorner H).partialDiagonal s)

theorem canonical_partialDiagonal_apply (s : Finset ℕ)
    (f : CountableHilbertSum H) (i : ℕ) :
    (canonicalMatrixCorner H).partialDiagonal s f i = if i ∈ s then f i else 0 := by
  classical
  simp only [FullMatrixCorner.partialDiagonal, sum_apply,
    canonicalMatrixCorner_entry, canonicalMatrixUnit_apply, lp.coeFn_sum,
    Finset.sum_apply, lp.single_apply]
  simp

theorem canonical_partialDiagonal_projection (s : Finset ℕ) :
    IsStarProjection ((canonicalMatrixCorner H).partialDiagonal s) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    change (canonicalMatrixCorner H).partialDiagonal s
      ((canonicalMatrixCorner H).partialDiagonal s f) i = _
    simp only [canonical_partialDiagonal_apply]
    split_ifs <;> rfl
  · exact (canonicalMatrixCorner H).partialDiagonal_star s

theorem regularPacketProjection_isStarProjection (s : Finset ℕ) :
    IsStarProjection (regularPacketProjection U hU s) :=
  (canonical_partialDiagonal_projection (H := H) s).map
    (regularGaugedCoordinates U hU).symm.conjStarAlgEquiv

theorem norm_regularPacketProjection_le (s : Finset ℕ) :
    ‖regularPacketProjection U hU s‖ ≤ 1 :=
  IsStarProjection.norm_le _ (regularPacketProjection_isStarProjection U hU s)

theorem regularPacketProjection_apply (s : Finset ℕ) (f : RegularCoreHilbert H) :
    regularPacketProjection U hU s f =
      ∑ i ∈ s, regularGaugedPacket U hU (regularScalarBasis i)
        ((regularGaugedPacket U hU (regularScalarBasis i)).adjoint f) := by
  change (regularGaugedCoordinates U hU).symm
    ((canonicalMatrixCorner H).partialDiagonal s (regularGaugedCoordinates U hU f)) = _
  simp only [FullMatrixCorner.partialDiagonal, sum_apply,
    canonicalMatrixCorner_entry, canonicalMatrixUnit_apply, map_sum,
    regularGaugedCoordinates_symm_single, regularGaugedCoordinates_apply]

theorem regularPacketProjection_tendsto (f : RegularCoreHilbert H) :
    Tendsto (fun s : Finset ℕ => regularPacketProjection U hU s f) atTop (𝓝 f) := by
  have h := (regularGaugedCoordinates U hU).symm.continuous.continuousAt.tendsto.comp
    ((canonicalMatrixCorner H).partialDiagonal_tendsto (regularGaugedCoordinates U hU f))
  change Tendsto (fun s : Finset ℕ => (regularGaugedCoordinates U hU).symm
    ((canonicalMatrixCorner H).partialDiagonal s (regularGaugedCoordinates U hU f)))
      atTop (𝓝 f)
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using h

theorem regularPacketCompression_norm_le
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (s : Finset ℕ) :
    ‖regularPacketProjection U hU s * T * regularPacketProjection U hU s‖ ≤ ‖T‖ := by
  calc
    _ ≤ (‖regularPacketProjection U hU s‖ * ‖T‖) *
        ‖regularPacketProjection U hU s‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := by
      gcongr <;> exact norm_regularPacketProjection_le U hU s
    _ = _ := by ring

/-- The finite packet compressions converge weakly, with their original bound. -/
theorem regularPacketCompression_tendsto_weak
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (f g : RegularCoreHilbert H) :
    Tendsto (fun s : Finset ℕ => inner ℂ g
      ((regularPacketProjection U hU s * T * regularPacketProjection U hU s) f))
      atTop (𝓝 (inner ℂ g (T f))) := by
  have h := (regularPacketProjection_tendsto U hU g).inner (𝕜 := ℂ)
    (T.continuous.continuousAt.tendsto.comp (regularPacketProjection_tendsto U hU f))
  have he (s : Finset ℕ) :
      inner ℂ (regularPacketProjection U hU s g)
        (T (regularPacketProjection U hU s f)) =
      inner ℂ g ((regularPacketProjection U hU s * T *
        regularPacketProjection U hU s) f) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left (regularPacketProjection U hU s)
      (T (regularPacketProjection U hU s f)) g]
    rw [← ContinuousLinearMap.star_eq_adjoint,
      (regularPacketProjection_isStarProjection U hU s).isSelfAdjoint.star_eq]
  exact h.congr he

/-- A finite compression is the finite matrix of its packet coefficients. -/
theorem regularPacketCompression_apply
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (s : Finset ℕ) (f : RegularCoreHilbert H) :
    (regularPacketProjection U hU s * T * regularPacketProjection U hU s) f =
      ∑ i ∈ s, ∑ j ∈ s, regularGaugedPacket U hU (regularScalarBasis i)
        (regularPacketCoefficient U hU T (regularScalarBasis i) (regularScalarBasis j)
          ((regularGaugedPacket U hU (regularScalarBasis j)).adjoint f)) := by
  simp only [mul_apply_eq_comp, regularPacketProjection_apply, map_sum,
    regularPacketCoefficient, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_comm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizedPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Linearity in the operator being localized and averaged. -/
def regularLocalizationAverageLinear
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤) :
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) →ₗ[ℂ]
      (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  (regularSandwichLinear (regularLocalFrame (H := H) s hs hfinite)).comp
    (regularConstantHom (H := RegularCoreHilbert H) (volume : Measure ℝ)).toAlgHom.toLinearMap

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

theorem regularIndicatorProjection_gaugedPacket
    (s : Set ℝ) (hs : MeasurableSet s)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularIndicatorProjection s hs (regularGaugedPacket U hU φ x) =
      regularGaugedPacket U hU (regularIndicatorProjection s hs φ) x := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae s hs (regularGaugedPacket U hU φ x),
    regularGaugedPacket_apply_ae U hU φ x,
    regularGaugedPacket_apply_ae U hU (regularIndicatorProjection s hs φ) x,
    regularIndicatorProjection_apply_ae s hs φ] with t hcut hφ hpacket hscalar
  rw [hcut, hpacket, hscalar]
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hφ]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_smul, map_zero]

theorem regularGaugedPacket_adjoint_indicator
    (s : Set ℝ) (hs : MeasurableSet s)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    (regularGaugedPacket U hU φ).adjoint (regularIndicatorProjection s hs f) =
      (regularGaugedPacket U hU (regularIndicatorProjection s hs φ)).adjoint f := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← regularIndicatorProjection_gaugedPacket]
  have hQ := (regularIndicatorProjection_isStarProjection (H := H) s hs).isSelfAdjoint
  have he : (regularIndicatorProjection (H := H) s hs).adjoint =
      regularIndicatorProjection s hs := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hQ.star_eq]
  simpa only [he] using (ContinuousLinearMap.adjoint_inner_right
    (regularIndicatorProjection (H := H) s hs) (regularGaugedPacket U hU φ x) f)

theorem regularLocalizationAverage_packetOperator
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    regularLocalizationAverage s hs hfinite (regularPacketOperator U hU φ ψ A) =
      regularPacketConvolution U hU
        (regularIndicatorProjection s hs φ) (regularIndicatorProjection s hs ψ)
        (integrable_regularIndicatorPacket s hs hfinite φ)
        (integrable_regularIndicatorPacket s hs hfinite ψ) A := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [inner_regularLocalizationAverage,
    ← integral_packet_orbit_inner_eq]
  apply integral_congr_ae
  filter_upwards [] with r
  change inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
    (regularGaugedPacket U hU φ (A ((regularGaugedPacket U hU ψ).adjoint
      (regularIndicatorProjection s hs (regularTranslateApply r g))))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left,
    regularGaugedPacket_adjoint_indicator, regularGaugedPacket_adjoint_indicator]

theorem regularLocalizationAverage_packetOperator_mem
    (P : VonNeumannAlgebra H)
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) (hA : A ∈ P.commutant) :
    regularLocalizationAverage s hs hfinite (regularPacketOperator U hU φ ψ A) ∈
      regularCommutantAlgebra U P := by
  rw [regularLocalizationAverage_packetOperator]
  exact regularPacketConvolution_mem U hU P _ _ _ _ hA

/-- Every finite compression has its localized average in the candidate commutant. -/
theorem regularLocalizationAverage_compression_mem
    (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ A ∈ P, Commute T (regularCoreEmbedding U hU A))
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (d : Finset ℕ) :
    regularLocalizationAverage s hs hfinite
      (regularPacketProjection U hU d * T * regularPacketProjection U hU d) ∈
      regularCommutantAlgebra U P := by
  have he : regularPacketProjection U hU d * T * regularPacketProjection U hU d =
      ∑ i ∈ d, ∑ j ∈ d, regularPacketOperator U hU (regularScalarBasis i)
        (regularScalarBasis j)
        (regularPacketCoefficient U hU T (regularScalarBasis i) (regularScalarBasis j)) := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [sum_apply, regularPacketOperator, ContinuousLinearMap.comp_apply] using
      regularPacketCompression_apply U hU T d f
  rw [he]
  change regularLocalizationAverageLinear s hs hfinite _ ∈ _
  rw [map_sum]
  apply (regularCommutantAlgebra U P).sum_mem
  intro i hi
  rw [map_sum]
  apply (regularCommutantAlgebra U P).sum_mem
  intro j hj
  exact regularLocalizationAverage_packetOperator_mem U hU P s hs hfinite _ _ _
    (regularPacketCoefficient_mem_commutant U hU P T hT _ _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularIntervalAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem integrable_localized_coefficient
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (f g : RegularCoreHilbert H) :
    Integrable (fun r : ℝ =>
      inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
        (T (regularIndicatorProjection s hs (regularTranslateApply r g)))) volume := by
  have h := L2.integrable_inner (𝕜 := ℂ) (regularLocalFrame s hs hfinite f)
    (T.compLpL 2 volume (regularLocalFrame s hs hfinite g))
  apply h.congr
  filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite f,
    regularLocalFrameValue_apply_ae s hs hfinite g,
    T.coeFn_compLpL (p := 2) (μ := (volume : Measure ℝ))
      (regularLocalFrame s hs hfinite g)] with r hf hg hT
  change inner ℂ (regularLocalFrameValue s hs hfinite f r)
    (T.compLpL 2 volume (regularLocalFrame s hs hfinite g) r) = _
  rw [hf, hT]
  change inner ℂ _ (T (regularLocalFrameValue s hs hfinite g r)) = _
  rw [hg]

/-- The unnormalized error is confined to a fixed-width boundary strip. -/
theorem regularIntervalAverage_error_le
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ r : ℝ, Commute T (regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    {A R : ℝ} (hA : 0 ≤ A) (hR : A ≤ R) (f g : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f)
    (hg : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc g = g) :
    ‖inner ℂ f (regularLocalizationAverage (Set.Icc (-R) R) measurableSet_Icc
      (by simp [Real.volume_Icc]) T g) - (2 * R : ℝ) • inner ℂ f (T g)‖ ≤
      8 * A * (‖T‖ * (‖f‖ * ‖g‖)) := by
  rw [inner_regularLocalizationAverage]
  apply regular_interval_boundary_estimate hA hR (by positivity)
  · exact integrable_localized_coefficient _ measurableSet_Icc (by simp [Real.volume_Icc]) T f g
  · calc
      ‖inner ℂ f (T g)‖ ≤ ‖f‖ * ‖T g‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖T‖ * ‖g‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  · intro r
    calc
      _ ≤ ‖regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc (regularTranslateApply r f)‖ *
          ‖T (regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc (regularTranslateApply r g))‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖T‖ * ‖g‖) :=
        mul_le_mul (norm_regularCut_translate_le _ measurableSet_Icc r f)
          ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (norm_regularCut_translate_le _ measurableSet_Icc r g) (norm_nonneg T)))
          (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  · intro r hr
    rw [regularInterval_translate_eq hr f hf, regularInterval_translate_eq hr g hg]
    have hc := congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => B g) (hT r).eq
    change T (regularTranslateApply r g) = regularTranslateApply r (T g) at hc
    rw [hc]
    exact Unitary.inner_map_map (regularRightTranslation (H := H) (Multiplicative.ofAdd r)) f (T g)
  · intro r hr
    rw [regularInterval_translate_zero hr f hf, inner_zero_left]

/-- The interval-length-normalized localization is a contraction on operators. -/
def regularNormalizedIntervalAverage (n : ℕ)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (((2 * ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) • regularLocalizationAverage
    (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc
    (by simp [Real.volume_Icc]) T

theorem norm_regularNormalizedIntervalAverage_le (n : ℕ)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    ‖regularNormalizedIntervalAverage n T‖ ≤ ‖T‖ := by
  have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hm : (volume (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))).toReal =
      2 * ((n : ℝ) + 1) := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Nat.cast_nonneg (α := ℝ) n])]
    ring
  rw [regularNormalizedIntervalAverage, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (2 * ((n : ℝ) + 1))⁻¹ *
        ((volume (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))).toReal * ‖T‖) :=
      mul_le_mul_of_nonneg_left (norm_regularLocalizationAverage_le _ measurableSet_Icc
        (by simp [Real.volume_Icc]) T) (inv_nonneg.mpr hp.le)
    _ = _ := by rw [hm, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularLocalizationReconstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem regularNormalizedIntervalAverage_tendsto_supported
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ r : ℝ, Commute T (regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    {A : ℝ} (hA : 0 ≤ A) (f g : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f)
    (hg : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc g = g) :
    Tendsto (fun n => inner ℂ f (regularNormalizedIntervalAverage n T g)) atTop
      (𝓝 (inner ℂ f (T g))) := by
  let b : ℝ := 8 * A * (‖T‖ * (‖f‖ * ‖g‖))
  have hscale : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_mono (fun n => by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1))⁻¹ * b) atTop (𝓝 0) := by
    simpa only [zero_mul] using hscale.mul_const b
  have hlarge : ∀ᶠ n : ℕ in atTop, A ≤ (n : ℝ) + 1 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop A)] with n hn
    linarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hlarge.mono fun n hn => ?_) hb
  have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have he : inner ℂ f (regularNormalizedIntervalAverage n T g) - inner ℂ f (T g) =
      (2 * ((n : ℝ) + 1))⁻¹ •
        (inner ℂ f (regularLocalizationAverage
          (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc
          (by simp [Real.volume_Icc]) T g) -
          (2 * ((n : ℝ) + 1) : ℝ) • inner ℂ f (T g)) := by
    change inner ℂ f (((((2 * ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) •
      (regularLocalizationAverage
        (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc
        (by simp [Real.volume_Icc]) T g))) - _ = _
    rw [inner_smul_right]
    exact complex_normalization_identity hp.ne' _ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  exact mul_le_mul_of_nonneg_left (regularIntervalAverage_error_le T hT hA hn f g hf hg)
    (inv_nonneg.mpr hp.le)

/-- Normalized interval localization converges weakly on all regular vectors. -/
theorem regularNormalizedIntervalAverage_tendsto_weak
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ r : ℝ, Commute T (regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (f g : RegularCoreHilbert H) :
    Tendsto (fun n => inner ℂ f (regularNormalizedIntervalAverage n T g)) atTop
      (𝓝 (inner ℂ f (T g))) := by
  apply weak_tendsto_of_strong_cutoff_tests (fun n => regularNormalizedIntervalAverage n T) T
    (fun k => regularIndicatorProjection (Set.Icc (-(k : ℝ)) (k : ℝ)) measurableSet_Icc)
    regularIntervalProjection_tendsto ‖T‖ (norm_nonneg T)
    (fun n => norm_regularNormalizedIntervalAverage_le n T) ?_ g f
  intro k l x y
  let A : ℝ := max (k : ℝ) (l : ℝ)
  have hk : Set.Icc (-(k : ℝ)) (k : ℝ) ⊆ Set.Icc (-A) A := by
    intro r hr
    have hh : (k : ℝ) ≤ A := le_max_left _ _
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hl : Set.Icc (-(l : ℝ)) (l : ℝ) ⊆ Set.Icc (-A) A := by
    intro r hr
    have hh : (l : ℝ) ≤ A := le_max_right _ _
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  exact regularNormalizedIntervalAverage_tendsto_supported T hT
    (le_trans (Nat.cast_nonneg k) (le_max_left _ _)) _ _
    (regularIndicatorProjection_larger _ _ measurableSet_Icc measurableSet_Icc hl y)
    (regularIndicatorProjection_larger _ _ measurableSet_Icc measurableSet_Icc hk x)

universe u

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioScalingWords
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integer powers of the two fixed state-scaling ratios

Distinct finite sites realize each ratio `lambda^k * mu^l` exactly.
-/

namespace KadisonKastler

noncomputable section

def twoRatioScalingSites (k l : ℤ) : List TwoRatioSite :=
  (List.range k.natAbs).map Sum.inl ++ (List.range l.natAbs).map Sum.inr

open Generator

end

end KadisonKastler

end OAI
end


