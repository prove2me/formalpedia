-- Prove2me | Definitions.Def_Q260K023
-- name    : Q260K023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:07:12.871942+00:00
-- url     : https://prove2.me/theorems/723f386c-c8cd-4ad1-8467-02e2c3c9950e
-- title:
--   Definitions bundle Q260K023 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 13 definitions and 24 theorems. The definitions and types are `OAI.KadisonKastler.boundedBoundaryTransport`, `OAI.KadisonKastler.canonicalAmplifiedAlgebra`, `OAI.KadisonKastler.canonicalCornerAlgebra`, `OAI.KadisonKastler.characterField`, `OAI.KadisonKastler.commonRankCoordinates`, `OAI.KadisonKastler.l2Extension`, `OAI.KadisonKastler.l2StrataCoordinates`, `OAI.KadisonKastler.normUltraproductMap`, `OAI.KadisonKastler.projectionPartitionCoordinates`, `OAI.KadisonKastler.projectionStrataCoordinates`, `OAI.KadisonKastler.projectionStrataSynthesis`, `OAI.KadisonKastler.shiftedFrequencyField`, `OAI.KadisonKastler.twoRatioScalingColumn`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_BoundaryBoundedTransport`, `KadisonKastler_CanonicalAmplification`, `KadisonKastler_CommonRankCoordinates`, `KadisonKastler_CyclicGaugeKernel`, `KadisonKastler_DirectIntegralUnitary`, `KadisonKastler_FrequencyCovariance`, `KadisonKastler_L2MeasurableExtension`, `KadisonKastler_L2PartitionCoordinates`, `KadisonKastler_L2StrataSum`, `KadisonKastler_NormUltraproduct`, `KadisonKastler_PointedMatrixSum`, `KadisonKastler_ProjectionStrataCoordinates`, `KadisonKastler_ProjectionStrataSynthesis`, `KadisonKastler_ScalarFrequencySwap`, `KadisonKastler_ScalarPositiveLimit`, `KadisonKastler_ShiftedFrequencyFields`, `KadisonKastler_SpatialAssociatorAlgebra`, `KadisonKastler_SpectralCommutant`, `KadisonKastler_SpectralVectorMeasure`, `KadisonKastler_TwoRatioScalingWords`.
--
--   **Imports.** It imports the bundles `Q260K017`, `Q260K018` and `Q260K019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K028` and `Q260K030`; the statements `OAI_KadisonKastler_commonRankCoordinates_action`, `OAI.KadisonKastler.commonRank_algebra_decomposition`, `OAI.KadisonKastler.projectionStrataCoordinates_operator_action`, `OAI.KadisonKastler.scalarGaugeWindowBalance` and `OAI_KadisonKastler_uniform_separable_typeI_strong_stability`; the proofs of `OAI.KadisonKastler.MatrixNearInclusion.regularTensor_gap`, `OAI_KadisonKastler_commonRankCoordinates_action`, `OAI_KadisonKastler_commonRankSpace_separable`, `OAI.KadisonKastler.commonRank_algebra_decomposition`, `OAI.KadisonKastler.commonRank_field_mem_of_closure`, `OAI.KadisonKastler.constructed_exists_normalizing_representation`, `OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean`, `OAI.KadisonKastler.exists_bounded_conjugacy_from_centralPair`, `OAI.KadisonKastler.projectionStrataCoordinates_operator_action` and `OAI.KadisonKastler.scalarGaugeWindowBalance`.
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
import Definitions.Def_Q260K017
import Definitions.Def_Q260K018
import Definitions.Def_Q260K019

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

local instance boundaryBoundedComplete_r0f1897_1 : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
attribute [local instance] OAI.KadisonKastler.boundaryBoundedStarOrder
/-- The exact transport field, bundled as a bounded unitary family. -/
def boundedBoundaryTransport (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g : G) : unitary (G →ᵇ B) :=
  boundedUnitaryFamily (fun t =>
    ⟨boundaryTransport α (unitaryFamilyEval V) g t,
      boundaryTransport_mem_unitary α (unitaryFamilyEval V) g t⟩)

@[simp]
theorem boundedBoundaryTransport_apply (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g t : G) :
    (boundedBoundaryTransport α V g).val t =
      V.val t * α g (star (V.val (g⁻¹ * t))) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The original algebra in the first coordinate of its countable sum. -/
def canonicalCornerAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (canonicalInitialSpace H) :=
  spatialTransportAlgebra (canonicalInitialEquiv H) M

/-- The countable amplification formed from the actual coordinate matrix units. -/
def canonicalAmplifiedAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (CountableHilbertSum H) :=
  (canonicalMatrixCorner H).amplifiedAlgebra (canonicalCornerAlgebra H M)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2MeasurableExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Extension by zero is an isometric linear inclusion of each stratum. -/
def l2Extension : Lp H 2 (Measure.comap ((↑) : s → X) μ) →ₗᵢ[ℂ] Lp H 2 μ where
  toFun := l2Extend μ s hs
  map_add' := l2Extend_add μ s hs
  map_smul' := l2Extend_smul μ s hs
  norm_map' := l2Extend_norm μ s hs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2StrataSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem l2Extension_inner (s : Set X) (hs : MeasurableSet s)
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) (g : Lp H 2 μ) :
    ⟪l2Extension μ s hs f, g⟫_ℂ = ⟪f, l2Restrict μ s hs g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, s.indicator (fun x => ⟪l2ExtensionFunction μ s f x, g x⟫_ℂ) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [l2Extend_apply_ae μ s hs f] with x hx
      change ⟪l2Extend μ s hs f x, g x⟫_ℂ = _
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [l2ExtensionFunction, hxs]
    _ = ∫ x in s, ⟪l2ExtensionFunction μ s f x, g x⟫_ℂ ∂μ :=
      integral_indicator hs
    _ = ∫ x : s, ⟪l2ExtensionFunction μ s f x.val, g x.val⟫_ℂ
        ∂Measure.comap ((↑) : s → X) μ := (integral_subtype_comap hs _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [l2Restrict_apply_ae μ s hs g] with x hx
      rw [l2ExtensionFunction_coe, hx]

theorem l2Restrict_extension_disjoint (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t)
    (f : Lp H 2 (Measure.comap ((↑) : t → X) μ)) :
    l2Restrict μ s hs (l2Extension μ t ht f) = 0 := by
  apply Lp.ext
  have he := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (l2Extend_apply_ae μ t ht f))
  filter_upwards [l2Restrict_apply_ae μ s hs (l2Extension μ t ht f), he,
    Lp.coeFn_zero (E := H) (p := 2) (Measure.comap ((↑) : s → X) μ)] with x hr he hz
  rw [hr, hz]
  change l2Extend μ t ht f x.val = 0
  rw [he]
  have hxt : x.val ∉ t := fun hx => Set.disjoint_left.mp hst x.property hx
  simp [l2ExtensionFunction, hxt]

variable {ι : Type*} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))

theorem l2Strata_orthogonal (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    OrthogonalFamily ℂ (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ))
      (fun i => l2Extension μ (s i) (hs i)) := by
  intro i j hij f g
  rw [l2Extension_inner, l2Restrict_extension_disjoint μ (s i) (s j)
    (hs i) (hs j) (hd hij), inner_zero_right]

theorem l2Strata_isHilbertSum [CompleteSpace H] [Countable ι]
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : ⋃ i, s i = Set.univ) :
    IsHilbertSum ℂ (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ))
      (fun i => l2Extension μ (s i) (hs i)) := by
  apply IsHilbertSum.mk (l2Strata_orthogonal μ s hs hd)
  let M := (⨆ i, LinearMap.range (l2Extension (H := H) μ (s i) (hs i)).toLinearMap).closure
  suffices hM : M.toSubmodule = ⊤ by
    rw [show (⨆ i, LinearMap.range (l2Extension (H := H) μ (s i) (hs i)).toLinearMap).topologicalClosure =
      M.toSubmodule from rfl, hM]
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  change g = 0
  apply l2_eq_zero_of_restrictions μ s hs hcover
  intro i
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← l2Extension_inner]
  apply hg
  exact Submodule.le_topologicalClosure _
    (Submodule.mem_iSup_of_mem i ⟨l2Restrict μ (s i) (hs i) g, rfl⟩)

/-- The actual Hilbert-space coordinates associated with a measurable partition. -/
def l2StrataCoordinates [CompleteSpace H] [Countable ι]
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : ⋃ i, s i = Set.univ) :
    Lp H 2 μ ≃ₗᵢ[ℂ] lp (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ)) 2 :=
  (l2Strata_isHilbertSum μ s hs hd hcover).linearIsometryEquiv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2PartitionCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Evaluation of the coordinates associated with a measurable partition -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X)

theorem l2Restrict_extension_same (s : Set X) (hs : MeasurableSet s)
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Restrict μ s hs (l2Extension μ s hs f) = f := by
  apply Lp.ext
  have he := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (l2Extend_apply_ae μ s hs f))
  filter_upwards [l2Restrict_apply_ae μ s hs (l2Extension μ s hs f), he] with x hr he
  rw [hr]
  change l2Extend μ s hs f x.val = f x
  rw [he, l2ExtensionFunction_coe]

variable [CompleteSpace H] (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
  (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : ⋃ n, s n = Set.univ)

theorem l2StrataCoordinates_apply (f : Lp H 2 μ) (n : ℕ) :
    l2StrataCoordinates μ s hs hd hcover f n = l2Restrict μ (s n) (hs n) f := by
  let e := l2StrataCoordinates (H := H) μ s hs hd hcover
  have he : (l2Restriction μ (s n) (hs n)).comp e.symm.toLinearIsometry.toContinuousLinearMap =
      lp.evalCLM ℂ (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ)) 2 n := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro i
    apply ContinuousLinearMap.ext
    intro v
    change l2Restrict μ (s n) (hs n) (e.symm (lp.single 2 i v)) =
      lp.single (E := fun j => Lp H 2 (Measure.comap ((↑) : s j → X) μ)) 2 i v n
    rw [show e.symm (lp.single 2 i v) = l2Extension μ (s i) (hs i) v from
      (l2Strata_isHilbertSum μ s hs hd hcover).linearIsometryEquiv_symm_apply_single v]
    by_cases hi : i = n
    · subst i
      rw [l2Restrict_extension_same]
      simp [lp.single_apply]
    · rw [l2Restrict_extension_disjoint μ (s n) (s i) (hs n) (hs i) (hd (Ne.symm hi))]
      simp [lp.single_apply, hi]
  have h := congrArg (fun T => T (e f)) he
  change l2Restrict μ (s n) (hs n) (e.symm (e f)) = e f n at h
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStrataSynthesis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def projectionPartitionCoordinates :
    Lp H 2 μ ≃ₗᵢ[ℂ] lp (fun n => Lp H 2 (projectionStratumMeasure μ P b n)) 2 :=
  l2StrataCoordinates μ (projectionRankStratum P b)
    (measurableSet_projectionRankStratum P b hPm)
    (projectionRankStratum_pairwise P b) (iUnion_projectionRankStratum P b)

def projectionStrataSynthesis : ProjectionStrataSpace μ P b →ₗᵢ[ℂ] Lp H 2 μ :=
  (projectionPartitionCoordinates μ P b hPm).symm.toLinearIsometry.comp
    (hilbertSumIsometryMap fun n =>
      l2ProjectionStratumSynthesis P hP b hb hPm n (projectionStratumMeasure μ P b n))

theorem projectionStrataSynthesis_range_components (f : Lp H 2 μ) :
    f ∈ LinearMap.range (projectionStrataSynthesis μ P hP b hb hPm).toLinearMap ↔
      ∀ n, (projectionPartitionCoordinates μ P b hPm f) n ∈
        LinearMap.range (l2ProjectionStratumSynthesis P hP b hb hPm n
          (projectionStratumMeasure μ P b n)).toLinearMap := by
  let e := projectionPartitionCoordinates μ P b hPm
  let S := fun n => l2ProjectionStratumSynthesis P hP b hb hPm n
    (projectionStratumMeasure μ P b n)
  rw [← hilbertSumIsometryMap_range S (e f)]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    change hilbertSumIsometryMap S g = e (e.symm (hilbertSumIsometryMap S g))
    rw [LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply e.injective
    change e (e.symm (hilbertSumIsometryMap S g)) = e f
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hg

theorem projectionStrataSynthesis_range (hPn : ∀ x, ‖P x‖ ≤ 1) (f : Lp H 2 μ) :
    f ∈ LinearMap.range (projectionStrataSynthesis μ P hP b hb hPm).toLinearMap ↔
      ∀ᵐ x ∂μ, P x (f x) = f x := by
  rw [projectionStrataSynthesis_range_components]
  have hc (n : ℕ) : (projectionPartitionCoordinates μ P b hPm f) n =
      l2Restrict μ (projectionRankStratum P b n)
        (measurableSet_projectionRankStratum P b hPm n) f :=
    l2StrataCoordinates_apply μ _ _ _ _ f n
  simp_rw [hc, l2ProjectionStratumSynthesis_range P hP b hb hPm hPn]
  rw [ae_iff_forall_partition μ (projectionRankStratum P b)
    (measurableSet_projectionRankStratum P b hPm) (iUnion_projectionRankStratum P b)]
  constructor <;> intro h n
  · filter_upwards [h n, l2Restrict_apply_ae μ (projectionRankStratum P b n)
      (measurableSet_projectionRankStratum P b hPm n) f] with x hx hr
    rwa [hr] at hx
  · filter_upwards [h n, l2Restrict_apply_ae μ (projectionRankStratum P b n)
      (measurableSet_projectionRankStratum P b hPm n) f] with x hx hr
    rwa [hr]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStrataCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary coordinates for the original spectral subspace

The original isometric embedding and the assembled measurable rank strata
have the same range. Their comparison is the required genuine unitary.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {X H E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
  (hPm : ∀ v, Measurable fun x => P x v)

variable (hPn : ∀ x, ‖P x‖ ≤ 1) (J : E →ₗᵢ[ℂ] Lp H 2 μ)
  (hJ : ∀ f : Lp H 2 μ, isometricExtension J 1 f =ᵐ[μ] fun x => P x (f x))

def projectionStrataCoordinates : E ≃ₗᵢ[ℂ] ProjectionStrataSpace μ P b :=
  isometryRangeCoordinates J (projectionStrataSynthesis μ P hP b hb hPm) (by
    ext f
    rw [isometry_range_iff_field_fixed μ J P hJ,
      projectionStrataSynthesis_range μ P hP b hb hPm hPn])

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankCoordinates
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

attribute [local instance] OAI.KadisonKastler.rankModelCoordinateBorel
variable {π D} {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] OAI.KadisonKastler.rankModelCoordinateMeasurable
def commonRankCoordinates : H ≃ₗᵢ[ℂ]
    ProjectionStrataSpace (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D) :=
  projectionStrataCoordinates (cyclicCommonBaseMeasure π D) (commonModelProjection M)
    (commonModelProjection_idempotent M) (commonRankBasis π D) (commonRankBasis_total π D)
    (commonModelProjection_measurable M) (commonModelProjection_norm_le M)
    (cyclicCommonEmbedding π D) (commonModelProjection_action M)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounds and adjoints for assembled measurable unitaries

The assembly is the actual multiplication operator on `L²(X,H)`.
An almost-everywhere fiber bound gives the same operator-norm bound.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularUnitaryField_star_apply_ae (μ : Measure X)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (f : Lp H 2 μ) :
    (star (regularUnitaryField μ U hU hUs) : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (star (U t) : H →L[ℂ] H) (f t) := by
  let u := regularUnitaryField μ U hU hUs
  let b := regularUnitaryFieldApply μ (fun t => star (U t)) hUs f
  have hb : (u : Lp H 2 μ →L[ℂ] Lp H 2 μ) b = f := by
    apply Lp.ext
    filter_upwards [regularUnitaryField_apply_ae μ U hU hUs b,
      regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs f] with t hu hv
    rw [hu, hv]
    exact congrArg (fun T : H →L[ℂ] H => T (f t)) (U t).property.2
  have heq : (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f = b := by
    calc
      _ = (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) ((u : Lp H 2 μ →L[ℂ] Lp H 2 μ) b) :=
        congrArg (fun g => (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) g) hb.symm
      _ = b := congrArg (fun T : Lp H 2 μ →L[ℂ] Lp H 2 μ => T b) u.property.1
  rw [show (star (regularUnitaryField μ U hU hUs) : Lp H 2 μ →L[ℂ] Lp H 2 μ) f = b from heq]
  exact regularUnitaryFieldApply_ae μ (fun t => star (U t)) hUs f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGaugeKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cyclic gauge as a field of scalar characters

Interchanging the time and spectral variables turns the cyclic modular
gauge into ordinary character multiplication in each spectral fiber.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

section CharacterField

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

include hl

def characterField : unitary (Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) :=
  regularUnitaryField μ (fun s => regularCharacterUnitary (H := ℂ) (l s))
    (characterField_measurable μ l hl) (characterField_star_measurable μ l hl)

theorem characterField_apply_ae (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    (characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F =ᵐ[μ]
      fun s => (regularCharacterUnitary (H := ℂ) (l s) : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (F s) :=
  regularUnitaryField_apply_ae μ _ _ _ F

end CharacterField

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencyCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Characters permute the concrete frequency nest -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sign and the `2*pi` normalization in the frequency shift. -/
theorem regularFrequencyProjection_character_intertwine (a s : ℝ) :
    regularFrequencyProjection (H := H) a *
        (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
          regularFrequencyProjection (a - 2 * Real.pi * s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularFrequencyProjection a
    ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) : RegularCoreHilbert H) =
    𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyProjection (a - 2 * Real.pi * s) f))
  rw [fourier_regularCharacterUnitary]
  apply Lp.ext
  have hp := regularFrequencyProjection_apply_fourier a
    ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
  rw [fourier_regularCharacterUnitary] at hp
  filter_upwards [hp,
    regularTranslateApply_ae (-s) (𝓕 f : RegularCoreHilbert H),
    regularTranslateApply_ae (-s)
      (𝓕 (regularFrequencyProjection (a - 2 * Real.pi * s) f) : RegularCoreHilbert H),
    (measurePreserving_add_right volume (-s)).quasiMeasurePreserving.ae_eq_comp
      (regularFrequencyProjection_apply_fourier (a - 2 * Real.pi * s) f)]
    with t h₁ h₂ h₃ h₄
  simp only [Function.comp_def] at h₄
  rw [h₁, h₃, h₄]
  have hcut : a / (2 * Real.pi) < t ↔
      (a - 2 * Real.pi * s) / (2 * Real.pi) < t + -s := by
    have hpos : 0 < 2 * Real.pi := by positivity
    rw [div_lt_iff₀ hpos, div_lt_iff₀ hpos]
    constructor <;> intro h <;> nlinarith
  by_cases ht : a / (2 * Real.pi) < t
  · simpa only [Set.indicator_apply, Set.mem_Ioi, ht, hcut.mp ht, ite_true, if_true] using h₂
  · have ht' := mt hcut.mpr ht
    simp only [Set.indicator_apply, Set.mem_Ioi, ht, ht', ite_false, if_false]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
local instance instStarOrderedRingSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence_r0f1897_1 : StarOrderedRing (VaryingBoundedSequence B) := CStarAlgebra.spectralOrderedRing _
def normUltraproductMap (ω : Ultrafilter ℕ) :
    VaryingBoundedSequence B →⋆ₐ[ℂ] NormUltraproduct B ω :=
  (normNullClosedIdeal B ω).quotientStarHom

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShiftedFrequencyFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable fields of shifted Fourier cuts -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem character_frequency_cut (a b : ℝ) :
    (star (regularCharacterUnitary (H := H) b) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      regularFrequencyProjection a *
      (regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
    regularFrequencyProjection (a - b) := by
  have hb : 2 * Real.pi * (b / (2 * Real.pi)) = b := by field_simp
  have h := regularFrequencyProjection_character_intertwine (H := H) a (b / (2 * Real.pi))
  rw [hb] at h
  rw [mul_assoc, h, ← mul_assoc,
    Unitary.star_mul_self_of_mem (regularCharacterUnitary (H := H) b).property, one_mul]

theorem continuous_shiftedFrequencyProjection (a : ℝ) (f : RegularCoreHilbert H) :
    Continuous (fun b : ℝ => regularFrequencyProjection (a - b) f) := by
  have hs (g : RegularCoreHilbert H) : Continuous (fun b : ℝ =>
      (star (regularCharacterUnitary (H := H) b) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) := by
    have he : (fun b : ℝ => (star (regularCharacterUnitary (H := H) b) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) =
        (fun b => (regularCharacterUnitary (H := H) (-b) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) := by
      funext b
      exact congrArg (fun u : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =>
        (u : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) (star_regularCharacterUnitary b)
    rw [he]
    exact (continuous_regularCharacterUnitary g).comp continuous_neg
  have hc := continuous_unitary_field_apply
    (fun b : ℝ => star (regularCharacterUnitary (H := H) b)) hs
    (fun b => regularFrequencyProjection a
      ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))
    ((regularFrequencyProjection a).continuous.comp (continuous_regularCharacterUnitary f))
  have he (b : ℝ) : (star (regularCharacterUnitary (H := H) b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) =
      regularFrequencyProjection (a - b) f :=
    congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => T f) (character_frequency_cut a b)
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext b
  exact (he b).symm

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

include hl in
theorem shiftedFrequencyField_measurable (a : ℝ) (f : RegularCoreHilbert H) :
    AEStronglyMeasurable (fun s => regularFrequencyProjection (a - l s) f) μ :=
  ((continuous_shiftedFrequencyProjection a f).stronglyMeasurable.comp_measurable hl).aestronglyMeasurable

def shiftedFrequencyField (a : ℝ) : Lp (RegularCoreHilbert H) 2 μ →L[ℂ] Lp (RegularCoreHilbert H) 2 μ :=
  regularFieldOperator μ (fun s => regularFrequencyProjection (a - l s))
    (shiftedFrequencyField_measurable μ l hl a) 1
    (Eventually.of_forall fun _ => (regularFrequencyProjection_isStarProjection _).norm_le _)

theorem shiftedFrequencyField_apply_ae (a : ℝ) (F : Lp (RegularCoreHilbert H) 2 μ) :
    shiftedFrequencyField μ l hl a F =ᵐ[μ] fun s => regularFrequencyProjection (a - l s) (F s) :=
  regularFieldOperator_represents μ _ _ _ _ F

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarFrequencySwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem characterField_frequency_conjugate (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (a : ℝ) (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    (star (characterField μ l hl) : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ)
      ((regularFrequencyProjection (H := ℂ) a).compLp
        ((characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F)) =
      shiftedFrequencyField μ l hl a F := by
  let C := characterField μ l hl
  let P := regularFrequencyProjection (H := ℂ) a
  have hs := regularUnitaryField_star_apply_ae μ (fun s => regularCharacterUnitary (H := ℂ) (l s))
    (characterField_measurable μ l hl) (characterField_star_measurable μ l hl)
    (P.compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F))
  change (star C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ)
    (P.compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F)) =ᵐ[μ] _ at hs
  apply Lp.ext
  filter_upwards [hs, P.coeFn_compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
      Lp (RegularCoreHilbert ℂ) 2 μ) F), characterField_apply_ae μ l hl F,
    shiftedFrequencyField_apply_ae μ l hl a F] with s hs hp hc ht
  calc
    _ = (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        ((P.compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F)) s) := hs
    _ = (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (P ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F s)) :=
      congrArg (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) hp
    _ = (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (P ((regularCharacterUnitary (H := ℂ) (l s) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (F s))) :=
      congrArg (fun w => (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (P w)) hc
    _ = regularFrequencyProjection (a - l s) (F s) :=
      congrArg (fun T : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ => T (F s))
        (character_frequency_cut a (l s))
    _ = _ := ht.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralVectorMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem regularVectorMeasure_charFun (f : RegularCoreHilbert H) (a : ℝ) :
    charFun (regularVectorMeasure f) a =
      inner ℂ f ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
  rw [charFun_apply_real, regularVectorMeasure_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularCharacterUnitary_apply_ae a f] with t ht
  rw [ht, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.real_smul]
  simp only [regularCharacterScalar, Circle.coe_exp, Complex.ofReal_mul, Complex.ofReal_pow]
  exact mul_comm _ _

theorem regularVectorMeasure_unitary_eq
    (U : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hU : ∀ a : ℝ, Commute (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (f : RegularCoreHilbert H) :
    regularVectorMeasure ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      regularVectorMeasure f := by
  apply Measure.ext_of_charFun
  funext a
  rw [regularVectorMeasure_charFun, regularVectorMeasure_charFun]
  have he := congrArg (fun S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => S f)
    (hU a).eq.symm
  change (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
    (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) at he
  rw [he]
  exact Unitary.inner_map_map U _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem regularCharacterUnitary_neg (a : ℝ) :
    regularCharacterUnitary (H := H) (-a) = star (regularCharacterUnitary a) := by
  simpa only [regularCharacterRepresentation, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_inv, toAdd_ofAdd, Unitary.star_eq_inv] using
    map_inv (regularCharacterRepresentation (H := H)) (Multiplicative.ofAdd a)

theorem mem_characterCommutant
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ a : ℝ, Commute T (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) :
    T ∈ characterCommutant := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨a, rfl⟩
  refine ⟨(hT a).eq.symm, ?_⟩
  simpa only [regularCharacterUnitary_neg, Unitary.coe_star] using (hT (-a)).eq.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialAssociatorAlgebra
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Associativity of represented spatial von Neumann products

The canonical Hilbert tensor associator transports the actual spatial
product algebras. The passage from algebraic generators to their von
Neumann algebras uses the existing bounded Kaplansky approximation input.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped TensorProduct Topology

noncomputable section

universe u

section LeftContinuity

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Bounded strong convergence is preserved by the first tensor leg. -/
theorem spatialLeft_tendsto_strong
    {ι : Type*} {l : Filter ι} (T : ι → H →L[ℂ] H) (a : H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C)
    (ha : ∀ x, Tendsto (fun i => T i x) l (𝓝 (a x)))
    (z : SpatialHilbert H K) :
    Tendsto (fun i => spatialLeft (K := K) (T i) z) l
      (𝓝 (spatialLeft (K := K) a z)) := by
  have hequi : Equicontinuous
      (fun i : ι => (spatialLeft (K := K) (T i) : SpatialHilbert H K → SpatialHilbert H K)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C * t)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0))))
    intro x y i
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    have hn : ‖spatialLeft (K := K) (T i)‖ ≤ C := by
      calc
        _ ≤ ‖T i‖ * ‖(1 : K →L[ℂ] K)‖ := spatialTensorOp_norm_le _ _
        _ ≤ ‖T i‖ * 1 := mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le : ‖(1 : K →L[ℂ] K)‖ ≤ 1) (norm_nonneg _)
        _ ≤ C := by simpa only [mul_one] using hT i
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hequi.isClosed_setOfPred_tendsto (spatialLeft (K := K) a).continuous
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul x y =>
      let L : H →L[ℂ] SpatialHilbert H K :=
        UniformSpace.Completion.toComplL.comp ((TensorProduct.mkL ℂ H K).flip y)
      have h := L.continuous.continuousAt.tendsto.comp (ha x)
      change Tendsto (fun i => (((T i x) ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K))
        l (𝓝 (((a x) ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)) at h
      change Tendsto (fun i => spatialTensorOp (T i) (1 : K →L[ℂ] K) _) l
        (𝓝 (spatialTensorOp a (1 : K →L[ℂ] K) _))
      simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self] using h
    | add x y hx hy =>
      simpa only [map_add, UniformSpace.Completion.coe_add] using hx.add hy

end LeftContinuity

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PointedMatrixSum
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tensorVectorSliceCP_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tensor products of pointed matrix-site systems

The two site families act in the two tensor legs. Finite words split into
their two subwords, and their vector moments multiply. Cyclicity follows
from the dense tensor-product orbit; separation follows by the same
argument for the commutants. No modular or infinite-product input is used.
-/

namespace KadisonKastler

open Generator UnitalTomsWinter
open scoped TensorProduct

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem sumList_operator_prod {I J : Type*}
    (a : I → H →L[ℂ] H) (b : J → K →L[ℂ] K) (l : List (I ⊕ J)) :
    (l.map (Sum.elim (fun i => spatialLeft (K := K) (a i))
      (fun j => spatialRight (H := H) (b j)))).prod =
      spatialTensorOp (((sumLeftList l).map a).prod) (((sumRightList l).map b).prod) := by
  induction l with
  | nil => simpa [sumLeftList, sumRightList] using Pureness.spatialTensorOp_one.symm
  | cons x l ih =>
    cases x with
    | inl i =>
      simp only [List.map_cons, List.prod_cons, Sum.elim_inl]
      rw [ih]
      change spatialTensorOp (a i) 1 * spatialTensorOp _ _ = spatialTensorOp _ _
      rw [← spatialTensorOp_mul]
      simp [sumLeftList, sumRightList]
    | inr j =>
      simp only [List.map_cons, List.prod_cons, Sum.elim_inr]
      rw [ih]
      change spatialTensorOp 1 (b j) * spatialTensorOp _ _ = spatialTensorOp _ _
      rw [← spatialTensorOp_mul]
      simp [sumLeftList, sumRightList]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPositiveLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem scalarNonnegative_pullback (T : X → X)
    (hT : Measure.QuasiMeasurePreserving T μ μ) {f : ScalarLInfinity μ}
    (hf : ScalarNonnegative f) : ScalarNonnegative (scalarInfinityPullback T hT f) := by
  filter_upwards [scalarInfinityPullback_ae T hT f, hT.ae hf] with x hx hp
  rwa [hx]

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

def twoRatioScalingColumn (k l : ℤ) : TwoRatioSite → Fin 2 :=
  Sum.elim (fun _ => signedSiteColumn k) (fun _ => signedSiteColumn l)

open Generator

end

end KadisonKastler

end OAI
end


