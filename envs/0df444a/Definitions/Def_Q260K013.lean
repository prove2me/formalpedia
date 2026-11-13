-- Prove2me | Definitions.Def_Q260K013
-- name    : Q260K013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:42:45.747353+00:00
-- url     : https://prove2.me/theorems/cfe71c4b-d538-4c69-a4d4-405a0bce0564
-- title:
--   Definitions bundle Q260K013 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 150 declarations of OpenAI's Lean: 46 definitions, 2 instances and 102 theorems. The definitions and types are `OAI.KadisonKastler.PublishedBlockCommutantApproximation`, `OAI.KadisonKastler.QuadraticCochainSolver`, `OAI.KadisonKastler.TraceStrongContinuous`, `OAI.KadisonKastler.TwoStateMatrixHilbert`, `OAI.KadisonKastler.WeakOperatorRepresentative.densityFieldOrder`, `OAI.KadisonKastler.WeakOperatorRepresentative.evalHom`, `OAI.KadisonKastler.WeakOperatorRepresentative.kernelAverage`, `OAI.KadisonKastler.WeakOperatorRepresentative.kernelProjection`, `OAI.KadisonKastler.WeakOperatorRepresentative.kernelSourceOrder`, `OAI.KadisonKastler.WeakOperatorRepresentative.positiveKernelProjection`, `OAI.KadisonKastler.WeakOperatorRepresentative.positiveSupport`, `OAI.KadisonKastler.WeakOperatorRepresentative.supportFieldOrder`, `OAI.KadisonKastler.WeakOperatorRepresentative.topElement`, `OAI.KadisonKastler.WeakOperatorRepresentative.unitaryEval`, `OAI.KadisonKastler.WeakUnitBallDense`, `OAI.KadisonKastler.abelianBoxAverage`, `OAI.KadisonKastler.abelianBoxFunctional`, `OAI.KadisonKastler.abelianMeanValue`, `OAI.KadisonKastler.algebraInclusion`, `OAI.KadisonKastler.asymptoticRowAlgebraOrder`, `OAI.KadisonKastler.bilateralBlockA`, `OAI.KadisonKastler.bilateralBlockB`, `OAI.KadisonKastler.bilateralFuture`, `OAI.KadisonKastler.bilateralIncrementProduct`, `OAI.KadisonKastler.bilateralLeftWord`, `OAI.KadisonKastler.bilateralMiddleWord`, `OAI.KadisonKastler.bilateralNegativeApprox`, `OAI.KadisonKastler.bilateralPast`, `OAI.KadisonKastler.bilateralPositiveApprox`, `OAI.KadisonKastler.bilateralRawHalves`, `OAI.KadisonKastler.bilateralReflectedPast`, `OAI.KadisonKastler.bilateralRightWord`, `OAI.KadisonKastler.bilateralTranslate`, `OAI.KadisonKastler.bilateralTranslateL2`, `OAI.KadisonKastler.bilateralWalkLaw`, `OAI.KadisonKastler.borelCommonModel`, `OAI.KadisonKastler.cesaroTranslation`, `OAI.KadisonKastler.cochainSymmetrize`, `OAI.KadisonKastler.finiteRowOrbit`, `OAI.KadisonKastler.l2IsometryField` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_AbelianCesaro`, `KadisonKastler_AbelianInvariantMean`, `KadisonKastler_AsymptoticRowCochain`, `KadisonKastler_Basic`, `KadisonKastler_BilateralBlockApproximations`, `KadisonKastler_BilateralBlockFunctions`, `KadisonKastler_BilateralBlockWords`, `KadisonKastler_BilateralBoundaryPair`, `KadisonKastler_BilateralBoundaryTransport`, `KadisonKastler_BilateralCocycle`, `KadisonKastler_BilateralL2Transport`, `KadisonKastler_BilateralRandomWalk`, `KadisonKastler_BoundaryDiagonal`, `KadisonKastler_BoundedSequence`, `KadisonKastler_CommonRankCoordinates`, `KadisonKastler_CommonSpectralMeasurable`, `KadisonKastler_ConcreteUCP`, `KadisonKastler_DenseUnitBallGap`, `KadisonKastler_FiniteRowOrbit`, `KadisonKastler_FourierModulation`, `KadisonKastler_HardyCauchyKernel`, `KadisonKastler_InvariantOperatorMean`, `KadisonKastler_L2LinearFields`, `KadisonKastler_L2MeasurableExtension`, `KadisonKastler_L2ProjectionSynthesis`, `KadisonKastler_MeasurableFiberRepresentations`, `KadisonKastler_MeasurableNatEnumeration`, `KadisonKastler_MeasurableProjectionFrame`, `KadisonKastler_MultiplicationCorrectionSequence`, `KadisonKastler_OperatorCochainStar`, `KadisonKastler_PairedRepresentations`, `KadisonKastler_PoissonKernelContinuity`, `KadisonKastler_ProjectionDimensionStrata`, `KadisonKastler_ProjectionRangeFrame`, `KadisonKastler_ProjectionStrataPartition`, `KadisonKastler_RegularCoreCharacters`, `KadisonKastler_SeparableAlgebraPair`, `KadisonKastler_StripContourAverage`, `KadisonKastler_StripContourBoundary`, `KadisonKastler_StripContourBounds`, `KadisonKastler_StripContourLimit`, `KadisonKastler_StripContourRectangle`, `KadisonKastler_StripSineQuotient`, `KadisonKastler_SubalgebraInvariantMean`, `KadisonKastler_TwoStateMatrixRepresentation`, `KadisonKastler_WeakFieldKernel`, `KadisonKastler_WeakFieldProjectionDensity`, `KadisonKastler_WeakFieldSpectralSupport`, `KadisonKastler_WeakFieldUnitary`, `KadisonSimilarity_Representation_CommonFiberRepresentations`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K000`, `Q260K002`, `Q260K003`, `Q260K004`, `Q260K005` and `Q260K006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K017`, `Q260K018`, `Q260K019` and `Q260K020`; the statements `OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveSupport`, `OAI.KadisonKastler.cochainSymmetrize_bound`, `OAI.KadisonKastler.cochainSymmetrize_residual_bound`, `OAI.KadisonKastler.cochainSymmetrize_star`, `OAI.KadisonKastler.concrete_ucp_starEquiv_of_published`, `OAI.KadisonKastler.concrete_ucp_unitary_of_published`, `OAI.KadisonKastler.multiplication_correction_of_quadratic_cochains`, `OAI.KadisonKastler.publishedBlockCommutantApproximation` and `OAI.KadisonKastler.quadraticCochainSolver_of_modular_rows`; the proofs of `OAI.KadisonKastler.FrequencySmoothing.continuous_smooth`, `OAI.KadisonKastler.WeakOperatorRepresentative.eval_posPart`, `OAI.KadisonKastler.WeakOperatorRepresentative.ext_eval`, `OAI.KadisonKastler.cochainSymmetrize_bound`, `OAI.KadisonKastler.cochainSymmetrize_star`, `OAI.KadisonKastler.concrete_ucp_unitary_of_published`, `OAI.KadisonKastler.exists_block_field_decomposition`, `OAI.KadisonKastler.kkDistance_generated_restriction_le`, `OAI.KadisonKastler.multiplication_correction_of_quadratic_cochains`, `OAI.KadisonKastler.publishedBlockCommutantApproximation`, `OAI_KadisonKastler_rankClosureCoordinateSeparable` and `OAI.KadisonKastler.traceHull_mem_ball`.
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
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
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
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Cylinders
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
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
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
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
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
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.RingTheory.Congruence.Basic
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
import Definitions.Def_Q260K000
import Definitions.Def_Q260K002
import Definitions.Def_Q260K003
import Definitions.Def_Q260K004
import Definitions.Def_Q260K005
import Definitions.Def_Q260K006

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitBall_nonempty (M : VonNeumannAlgebra H) : (unitBall M).Nonempty :=
  ⟨0, zero_mem_unitBall M⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operator averaging from an actual scalar invariant mean

The scalar mean is data on bounded scalar functions. Riesz representation
constructs the operator average from its coefficients. No operator-valued
mean, fixed-point projection, or amenability conclusion is assumed.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction BigOperators Topology CStarAlgebra

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G)

theorem fixed (c : ℂ) : m.toCLM (BoundedContinuousFunction.const G c) = c := by
  have he : BoundedContinuousFunction.const G c =
      c • BoundedContinuousFunction.const G (1 : ℂ) := by
    ext g
    simp
  rw [he, map_smul, m.map_const_one, smul_eq_mul, mul_one]

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianCesaro
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite Cesaro averages in an abelian group

Iterating the one-generator averages over a finite list gives positive
contractions. A translation by any generator in the list changes the
average by at most twice the reciprocal averaging length.
-/

namespace KadisonKastler

open scoped BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

def scalarTranslation (g : G) : (G →ᵇ ℂ) →L[ℂ] (G →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := scalarMeanTranslate g
      map_add' f h := by ext t; rfl
      map_smul' c f := by ext t; rfl }
    1 (fun f => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
        (fun t => f.norm_coe_le_norm _))

@[simp] theorem scalarTranslation_apply (g : G) (f : G →ᵇ ℂ) (t : G) :
    scalarTranslation g f t = f (g⁻¹ * t) := rfl

theorem scalarTranslation_norm_le (g : G) (f : G →ᵇ ℂ) :
    ‖scalarTranslation g f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun t => f.norm_coe_le_norm (g⁻¹ * t))

@[simp] theorem scalarTranslation_one (f : G →ᵇ ℂ) : scalarTranslation (1 : G) f = f := by
  ext t
  simp only [scalarTranslation_apply, inv_one, one_mul]

theorem scalarTranslation_mul (g h : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (scalarTranslation h f) = scalarTranslation (g * h) f := by
  ext t
  simp only [scalarTranslation_apply, mul_inv_rev, mul_assoc]

theorem scalarTranslation_comm (g h : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (scalarTranslation h f) = scalarTranslation h (scalarTranslation g f) := by
  rw [scalarTranslation_mul, scalarTranslation_mul, mul_comm g h]

@[simp] theorem scalarTranslation_const (g : G) (c : ℂ) :
    scalarTranslation g (BoundedContinuousFunction.const G c) =
      BoundedContinuousFunction.const G c := by ext t; rfl

def cesaroTranslation (n : ℕ) (g : G) : (G →ᵇ ℂ) →L[ℂ] (G →ᵇ ℂ) :=
  (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
    ∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i)

theorem cesaroTranslation_apply (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    cesaroTranslation n g f = (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
      ∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f := by
  simp only [cesaroTranslation, smul_apply, sum_apply]

theorem cesaroTranslation_norm_le (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    ‖cesaroTranslation n g f‖ ≤ ‖f‖ := by
  have hp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [cesaroTranslation_apply, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hp.le]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), ‖scalarTranslation (g ^ i) f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hp.le)
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _i ∈ Finset.range (n + 1), ‖f‖ := by
      gcongr with i hi
      exact scalarTranslation_norm_le _ _
    _ = ‖f‖ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

@[simp] theorem cesaroTranslation_const (n : ℕ) (g : G) (c : ℂ) :
    cesaroTranslation n g (BoundedContinuousFunction.const G c) =
      BoundedContinuousFunction.const G c := by
  rw [cesaroTranslation_apply]
  simp only [scalarTranslation_const, Finset.sum_const, Finset.card_range]
  have hp : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  change (((n + 1 : ℕ) : ℂ)⁻¹ * ((n + 1 : ℕ) : ℂ)) • _ = _
  rw [inv_mul_cancel₀ hp, one_smul]

theorem scalarTranslation_cesaro (n : ℕ) (g h : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (cesaroTranslation n h f) =
      cesaroTranslation n h (scalarTranslation g f) := by
  simp only [cesaroTranslation_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact scalarTranslation_comm _ _ _

theorem cesaroTranslation_difference (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (cesaroTranslation n g f) - cesaroTranslation n g f =
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) • (scalarTranslation (g ^ (n + 1)) f - f) := by
  simp only [cesaroTranslation_apply, map_smul, map_sum, ← smul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  have hsum : (∑ i ∈ Finset.range (n + 1),
      (scalarTranslation g (scalarTranslation (g ^ i) f) - scalarTranslation (g ^ i) f)) =
      ∑ i ∈ Finset.range (n + 1),
        (scalarTranslation (g ^ (i + 1)) f - scalarTranslation (g ^ i) f) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarTranslation_mul, ← pow_succ']
  rw [hsum]
  simpa only [pow_zero, scalarTranslation_one] using
    (Finset.sum_range_sub (fun i : ℕ => scalarTranslation (g ^ i) f) (n + 1))

theorem cesaroTranslation_difference_norm_le (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    ‖scalarTranslation g (cesaroTranslation n g f) - cesaroTranslation n g f‖ ≤
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) * ‖f‖ := by
  rw [cesaroTranslation_difference]
  exact norm_inv_nat_smul_sub_le n (scalarTranslation (g ^ (n + 1)) f) f
    (scalarTranslation_norm_le (g ^ (n + 1)) f)

def abelianBoxAverage (n : ℕ) : List G → (G →ᵇ ℂ) →L[ℂ] (G →ᵇ ℂ)
  | [] => 1
  | g :: s => (cesaroTranslation n g).comp (abelianBoxAverage n s)

@[simp] theorem abelianBoxAverage_nil (n : ℕ) (f : G →ᵇ ℂ) :
    abelianBoxAverage n [] f = f := rfl

@[simp] theorem abelianBoxAverage_cons (n : ℕ) (g : G) (s : List G) (f : G →ᵇ ℂ) :
    abelianBoxAverage n (g :: s) f = cesaroTranslation n g (abelianBoxAverage n s f) := rfl

theorem abelianBoxAverage_norm_le (n : ℕ) (s : List G) (f : G →ᵇ ℂ) :
    ‖abelianBoxAverage n s f‖ ≤ ‖f‖ := by
  induction s with
  | nil => exact le_rfl
  | cons g s ih => exact (cesaroTranslation_norm_le n g _).trans ih

@[simp] theorem abelianBoxAverage_const (n : ℕ) (s : List G) (c : ℂ) :
    abelianBoxAverage n s (BoundedContinuousFunction.const G c) =
      BoundedContinuousFunction.const G c := by
  induction s with
  | nil => rfl
  | cons g s ih => rw [abelianBoxAverage_cons, ih, cesaroTranslation_const]

theorem scalarTranslation_box (n : ℕ) (s : List G) (g : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (abelianBoxAverage n s f) =
      abelianBoxAverage n s (scalarTranslation g f) := by
  induction s with
  | nil => rfl
  | cons h s ih => rw [abelianBoxAverage_cons, scalarTranslation_cesaro, ih,
      abelianBoxAverage_cons]

theorem abelianBoxAverage_difference_norm_le (n : ℕ) (s : List G) (g : G)
    (hg : g ∈ s) (f : G →ᵇ ℂ) :
    ‖scalarTranslation g (abelianBoxAverage n s f) - abelianBoxAverage n s f‖ ≤
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) * ‖f‖ := by
  induction s with
  | nil => simp only [List.not_mem_nil] at hg
  | cons h s ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (cesaroTranslation_difference_norm_le n g _).trans
        (mul_le_mul_of_nonneg_left (abelianBoxAverage_norm_le n s f) (by positivity))
    · rw [abelianBoxAverage_cons, scalarTranslation_cesaro, ← map_sub]
      exact (cesaroTranslation_norm_le n h _).trans (ih hg)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianInvariantMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A scalar invariant mean for every discrete abelian group

Finite iterated Cesaro averages give a positive, unital, contractive
family of scalar functionals. An ultrafilter extending the directed
finite-set/length filter gives a simultaneous scalar limit. The explicit
telescoping bound proves invariance. This constructs the mean used for
the real modular and character groups without an amenability premise.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

theorem cesaroTranslation_positive (n : ℕ) (g : G) (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) (t : G) :
    (cesaroTranslation n g f t).im = 0 ∧ 0 ≤ (cesaroTranslation n g f t).re := by
  have hsumim : (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t).im = 0 := by
    change Complex.imLm (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ => (hf _).1)
  have hsumre : 0 ≤ (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t).re := by
    change 0 ≤ Complex.reLm (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t)
    rw [map_sum]
    exact Finset.sum_nonneg (fun i _ => (hf _).2)
  let c : ℂ := (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
  have hci : c.im = 0 := by
    change (((n + 1 : ℕ) : ℂ)⁻¹).im = 0
    rw [Complex.inv_im]
    simp only [Complex.natCast_im, neg_zero, zero_div]
  have hcr : 0 ≤ c.re := by
    change 0 ≤ (((n + 1 : ℕ) : ℂ)⁻¹).re
    rw [Complex.inv_re, Complex.natCast_re]
    exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  rw [cesaroTranslation_apply]
  simp only [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sum_apply,
    smul_eq_mul]
  change (c * _).im = 0 ∧ 0 ≤ (c * _).re
  rw [Complex.mul_im, Complex.mul_re, hci, hsumim]
  simpa only [zero_mul, mul_zero, add_zero, zero_add, sub_zero] using
    (show (0 : ℝ) = 0 ∧ 0 ≤ c.re *
      (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t).re from
      ⟨rfl, mul_nonneg hcr hsumre⟩)

theorem abelianBoxAverage_positive (n : ℕ) (s : List G) (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) :
    ∀ t, (abelianBoxAverage n s f t).im = 0 ∧ 0 ≤ (abelianBoxAverage n s f t).re := by
  induction s with
  | nil => exact hf
  | cons g s ih => exact cesaroTranslation_positive n g _ ih

def abelianBoxFunctional (d : Finset G × ℕ) : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ (1 : G)).comp
    (abelianBoxAverage d.2 d.1.toList)

theorem abelianBoxFunctional_apply (d : Finset G × ℕ) (f : G →ᵇ ℂ) :
    abelianBoxFunctional d f = abelianBoxAverage d.2 d.1.toList f 1 := rfl

theorem abelianBoxFunctional_norm_le (d : Finset G × ℕ) (f : G →ᵇ ℂ) :
    ‖abelianBoxFunctional d f‖ ≤ ‖f‖ :=
  ((abelianBoxAverage d.2 d.1.toList f).norm_coe_le_norm 1).trans
    (abelianBoxAverage_norm_le d.2 d.1.toList f)

@[simp] theorem abelianBoxFunctional_const (d : Finset G × ℕ) (c : ℂ) :
    abelianBoxFunctional d (BoundedContinuousFunction.const G c) = c := by
  rw [abelianBoxFunctional_apply, abelianBoxAverage_const]
  rfl

theorem abelianBoxFunctional_positive (d : Finset G × ℕ) (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) :
    (abelianBoxFunctional d f).im = 0 ∧ 0 ≤ (abelianBoxFunctional d f).re :=
  abelianBoxAverage_positive d.2 d.1.toList f hf 1

theorem abelianBoxFunctional_translation_bound (d : Finset G × ℕ) (g : G)
    (hg : g ∈ d.1) (f : G →ᵇ ℂ) :
    ‖abelianBoxFunctional d (scalarTranslation g f) - abelianBoxFunctional d f‖ ≤
      2 * (((d.2 + 1 : ℕ) : ℝ)⁻¹) * ‖f‖ := by
  have hmem : g ∈ d.1.toList := by simpa using hg
  have hb := abelianBoxAverage_difference_norm_le d.2 d.1.toList g hmem f
  rw [scalarTranslation_box] at hb
  calc
    _ = ‖(abelianBoxAverage d.2 d.1.toList (scalarTranslation g f) -
        abelianBoxAverage d.2 d.1.toList f) 1‖ := rfl
    _ ≤ ‖abelianBoxAverage d.2 d.1.toList (scalarTranslation g f) -
        abelianBoxAverage d.2 d.1.toList f‖ :=
      (BoundedContinuousFunction.norm_coe_le_norm _ _)
    _ ≤ _ := hb

theorem exists_abelianMeanValue (f : G →ᵇ ℂ) :
    ∃ z : ℂ, ‖z‖ ≤ ‖f‖ ∧
      Tendsto (fun d => abelianBoxFunctional d f) (abelianMeanFilter G : Filter _) (𝓝 z) := by
  obtain ⟨z, hz, ht⟩ := (isCompact_closedBall (0 : ℂ) ‖f‖).ultrafilter_le_nhds
    ((abelianMeanFilter G).map (fun d => abelianBoxFunctional d f)) (by
      apply le_principal_iff.mpr
      change ∀ᶠ d in (abelianMeanFilter G : Filter (Finset G × ℕ)),
        abelianBoxFunctional d f ∈ Metric.closedBall (0 : ℂ) ‖f‖
      exact Eventually.of_forall (fun d => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using abelianBoxFunctional_norm_le d f))
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ht⟩

def abelianMeanValue (f : G →ᵇ ℂ) : ℂ :=
  Classical.choose (exists_abelianMeanValue f)

theorem norm_abelianMeanValue (f : G →ᵇ ℂ) : ‖abelianMeanValue f‖ ≤ ‖f‖ :=
  (Classical.choose_spec (exists_abelianMeanValue f)).1

theorem tendsto_abelianMeanValue (f : G →ᵇ ℂ) :
    Tendsto (fun d => abelianBoxFunctional d f) (abelianMeanFilter G : Filter _)
      (𝓝 (abelianMeanValue f)) :=
  (Classical.choose_spec (exists_abelianMeanValue f)).2

theorem abelianMeanValue_add (f h : G →ᵇ ℂ) :
    abelianMeanValue (f + h) = abelianMeanValue f + abelianMeanValue h := by
  apply tendsto_nhds_unique (tendsto_abelianMeanValue (f + h))
  simpa only [map_add] using (tendsto_abelianMeanValue f).add (tendsto_abelianMeanValue h)

theorem abelianMeanValue_smul (c : ℂ) (f : G →ᵇ ℂ) :
    abelianMeanValue (c • f) = c • abelianMeanValue f := by
  apply tendsto_nhds_unique (tendsto_abelianMeanValue (c • f))
  simpa only [map_smul] using (tendsto_abelianMeanValue f).const_smul c

theorem abelianMeanValue_const (c : ℂ) :
    abelianMeanValue (BoundedContinuousFunction.const G c) = c := by
  apply tendsto_nhds_unique (tendsto_abelianMeanValue _)
  simpa only [abelianBoxFunctional_const] using
    (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
      (abelianMeanFilter G : Filter _) (𝓝 c))

theorem abelianMeanValue_positive (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) :
    (abelianMeanValue f).im = 0 ∧ 0 ≤ (abelianMeanValue f).re := by
  constructor
  · apply tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp (tendsto_abelianMeanValue f))
    have h : (fun d : Finset G × ℕ => (abelianBoxFunctional d f).im) = fun _ => 0 :=
      funext (fun d => (abelianBoxFunctional_positive d f hf).1)
    change Tendsto (fun d => (abelianBoxFunctional d f).im)
      (abelianMeanFilter G : Filter (Finset G × ℕ)) (𝓝 0)
    rw [h]
    exact tendsto_const_nhds
  · exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (tendsto_abelianMeanValue f))
      (Eventually.of_forall (fun d => (abelianBoxFunctional_positive d f hf).2))

theorem abelianBoxFunctional_translation_tendsto_zero (g : G) (f : G →ᵇ ℂ) :
    Tendsto (fun d => abelianBoxFunctional d (scalarTranslation g f) - abelianBoxFunctional d f)
      (atTop : Filter (Finset G × ℕ)) (𝓝 0) := by
  classical
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsnd : Tendsto (fun d : Finset G × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hrate : Tendsto (fun d : Finset G × ℕ =>
      2 * (((d.2 + 1 : ℕ) : ℝ)⁻¹) * ‖f‖) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd).const_mul 2).mul_const ‖f‖
    simpa only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one, mul_zero, zero_mul] using h
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hrate
  filter_upwards [eventually_ge_atTop (({g} : Finset G), 0)] with d hd
  exact abelianBoxFunctional_translation_bound d g (hd.1 (Finset.mem_singleton_self g)) f

theorem abelianMeanValue_invariant (g : G) (f : G →ᵇ ℂ) :
    abelianMeanValue (scalarMeanTranslate g f) = abelianMeanValue f := by
  have hz := (abelianBoxFunctional_translation_tendsto_zero g f).mono_left
    (abelianMeanFilter_le (G := G))
  have hd := (tendsto_abelianMeanValue (scalarTranslation g f)).sub (tendsto_abelianMeanValue f)
  have he := tendsto_nhds_unique hd hz
  exact sub_eq_zero.mp he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorCochainStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Involution symmetrization of operator-valued cochains -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def cochainSymmetrize (D : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  (1/2 : ℂ) • (D + cochainSharp D)


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AsymptoticRowCochain
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Passage from asymptotically modular row averages to a quadratic cochain.
The asymptotic modularity hypothesis is explicit; its general construction is
not asserted by this adapter. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance asymptoticRowAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance asymptoticRowAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralRandomWalk
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independent forward and reflected backward random walks -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralWalkLaw : Measure (BilateralWalkPath G) :=
  Measure.infinitePi (fun _ : ℤ => symmetricRandomWalkLaw G)

instance instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw : IsProbabilityMeasure (bilateralWalkLaw G) := by
  unfold bilateralWalkLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def bilateralFuture (ω : BilateralWalkPath G) (n : ℕ) : G := ω (n : ℤ)

def bilateralPast (ω : BilateralWalkPath G) (n : ℕ) : G := ω (-(n : ℤ) - 1)

def bilateralReflectedPast (ω : BilateralWalkPath G) (n : ℕ) : G := (bilateralPast G ω n)⁻¹

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBoundaryPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two boundary endpoints of a bilateral random walk

The forward and reflected backward halves have the exact boundary product
law. Every integer shift preserves the bilateral path probability.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralTranslate (k : ℤ) (ω : BilateralWalkPath G) (j : ℤ) : G := ω (j + k)

theorem bilateralTranslate_measurePreserving (k : ℤ) :
    MeasurePreserving (bilateralTranslate G k) (bilateralWalkLaw G) (bilateralWalkLaw G) := by
  refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (j + k)), ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => add_right_cancel h)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBoundaryTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The boundary pair transforms by the inverse increment under a bilateral shift.

The boundary uses an invariant sigma algebra, not a point quotient. Its endpoint
identities are therefore proved on measurable Hilbert-valued functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralRawHalves (ω : BilateralWalkPath G) : (ℕ → G) × (ℕ → G) :=
  (bilateralFuture G ω, bilateralReflectedPast G ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite random-walk cocycles and the iterated coefficient transport. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralIncrementProduct : ℕ → BilateralWalkPath G → G
  | 0, _ => 1
  | n + 1, ω => (ω (n : ℤ))⁻¹ * bilateralIncrementProduct n ω

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
@[simp] theorem bilateralIncrementProduct_zero (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G 0 ω = 1 := rfl

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
@[simp] theorem bilateralIncrementProduct_succ (n : ℕ) (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G (n + 1) ω = (ω (n : ℤ))⁻¹ * bilateralIncrementProduct G n ω := rfl

omit [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
@[simp] theorem bilateralTranslate_add (a b : ℤ) (ω : BilateralWalkPath G) :
    bilateralTranslate G a (bilateralTranslate G b ω) = bilateralTranslate G (a + b) ω := by
  funext j
  simp [bilateralTranslate, add_assoc]

theorem bilateralIncrementProduct_measurable (n : ℕ) : Measurable (bilateralIncrementProduct G n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : G × G => p.1⁻¹ * p.2)).comp
      ((measurable_pi_apply (n : ℤ)).prodMk ih)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Three separated increment blocks in the double-ergodicity proof. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralLeftWord (m : ℕ) := bilateralIncrementProduct G (m + 1)
def bilateralMiddleWord (m : ℕ) (ω : BilateralWalkPath G) := (ω ((m + 1 : ℕ) : ℤ))⁻¹
def bilateralRightWord (m : ℕ) (ω : BilateralWalkPath G) :=
  bilateralIncrementProduct G m (bilateralTranslate G (m + 2) ω)

theorem bilateralLeftWord_measurable (m : ℕ) : Measurable (bilateralLeftWord G m) :=
  bilateralIncrementProduct_measurable G _

theorem bilateralMiddleWord_measurable (m : ℕ) : Measurable (bilateralMiddleWord G m) :=
  (measurable_of_countable (Inv.inv : G → G)).comp (measurable_pi_apply _)

theorem bilateralRightWord_measurable (m : ℕ) : Measurable (bilateralRightWord G m) :=
  (bilateralIncrementProduct_measurable G _).comp (bilateralTranslate_measurePreserving G _).measurable

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralL2Transport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The bilateral cocycle acts isometrically on L2. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

def bilateralTranslateL2 (k : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  Lp.compMeasurePreserving (bilateralTranslate G k) (bilateralTranslate_measurePreserving G k) f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockFunctions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Measurability and independence of the two transported finite blocks. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

def bilateralBlockA (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  countableUnitaryL2 σ (bilateralLeftWord_measurable G m) g

def bilateralBlockB (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  countableUnitaryL2 (fun h => (σ h)⁻¹) (bilateralRightWord_measurable G m)
    (bilateralTranslateL2 (2 * m + 2) g)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockApproximations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Positive- and negative-coordinate approximations to invariant coefficients. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

def bilateralPositiveApprox (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  countableUnitaryL2 (fun h => (σ h)⁻¹) (bilateralLeftWord_measurable G m)
    (hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockA σ m g ω ∂bilateralWalkLaw G))

def bilateralNegativeApprox (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  bilateralTranslateL2 (-((2 * m + 2 : ℕ) : ℤ))
    (countableUnitaryL2 σ (bilateralRightWord_measurable G m)
      (hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {R : Type*}
  [Ring R]
  [_root_.Algebra ℂ R]

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

variable (A) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonKastler.instPartialOrderContinuousLinearMapComplexId_solutions
attribute [local instance] OAI.KadisonKastler.instStarOrderedRingContinuousLinearMapComplexId_solutions
/-- The precise strict-approximation consequence of the published
commutant-distance formula, restricted to two-by-two operator matrices. -/
def PublishedBlockCommutantApproximation : Prop :=
  ∀ (π : A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K))
    (T : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K)) (e : ℝ), 0 ≤ e →
    CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e →
    ∀ r : ℝ, e / 2 < r →
      ∃ D : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K),
        (∀ x, D * π x = π x * D) ∧ ‖D - T‖ < r

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundedSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Bounded sequences, spectral clipping and trace-to-strong transfer

The sequence algebra is the ordinary C*-algebra of bounded functions on
the discrete natural numbers. Evaluation commutes with the spectral
cutoff. A trace quotient therefore kills the discarded part as soon as
the quotient norm satisfies the desired cutoff bound.
-/

namespace KadisonKastler

open Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

/-- Continuity from the tracial two-norm to the strong topology on each
norm-bounded ball. This is the exact normal-representation property used
by the clipping argument; no existence assertion is made here. -/
def TraceStrongContinuous {B H : Type*} [CStarAlgebra B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : FaithfulTracialState B) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ z : H, ∀ C : ℝ, 0 ≤ C → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∀ x : B, ‖x‖ ≤ C → traceTwoNorm τ x < η → ‖ρ x z‖ < ε

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise diagonal comparison in a finite algebra

The least-norm argument is carried out in a supplied faithful tracial
Hilbert realization. Bounded completeness of the concrete finite algebra
keeps Hilbert limits in the operator algebra. No measurable selection or
existence of a boundary space is asserted here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

section Concrete

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable (J : Algebra M →ₗ[ℂ] E)
variable (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)

include hJ in
/-- Faithfulness makes a tracial Hilbert realization injective. -/
theorem traceHilbert_injective : Function.Injective J := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (traceTwoNorm_eq_zero_iff τ _).mp
  rw [← hJ, map_sub, hxy, sub_self, norm_zero]

end Concrete


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableNatEnumeration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem measurable_indexCount (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (n : ℕ) :
    Measurable fun x => measurableIndexCount p x n := by
  classical
  induction n with
  | zero => simpa only [measurableIndexCount, Nat.count_zero] using
      (measurable_const : Measurable fun _ : X => (0 : ℕ))
  | succ n ih =>
    simp only [measurableIndexCount, Nat.count_succ] at ih ⊢
    exact ih.add (Measurable.ite (hp n) measurable_const measurable_const)

theorem nth_eq_nonzero_iff (p : ℕ → Prop) (k m : ℕ) (hm : m ≠ 0) :
    Nat.nth p k = m ↔ p m ∧ measurableIndexCount (fun _ : Unit => p) () m = k := by
  classical
  change Nat.nth p k = m ↔ p m ∧ Nat.count p m = k
  constructor
  · intro h
    have hn : Nat.nth p k ≠ 0 := h.trans_ne hm
    refine ⟨h ▸ Nat.nth_mem_of_ne_zero hn, ?_⟩
    rw [← h]
    exact Nat.count_nth fun hf => Nat.lt_card_toFinset_of_nth_ne_zero hn hf
  · rintro ⟨hpm, hc⟩
    rw [← hc]
    exact Nat.nth_count hpm

theorem measurable_natNth (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (k : ℕ) :
    Measurable fun x => Nat.nth (p x) k := by
  classical
  have hm (m : ℕ) (hm0 : m ≠ 0) : MeasurableSet {x | Nat.nth (p x) k = m} := by
    have he : {x | Nat.nth (p x) k = m} =
        {x | p x m} ∩ {x | measurableIndexCount p x m = k} := by
      ext x
      exact nth_eq_nonzero_iff (p x) k m hm0
    rw [he]
    exact (hp m).inter (measurableSet_eq_fun (measurable_indexCount p hp m) measurable_const)
  apply measurable_to_countable'
  intro m
  by_cases hm0 : m = 0
  · subst m
    have he : {x | Nat.nth (p x) k = 0} =
        (⋃ n : ℕ, {x | Nat.nth (p x) k = n + 1})ᶜ := by
      ext x
      cases h : Nat.nth (p x) k with
      | zero => simp [h]
      | succ n => simp [h]
    change MeasurableSet {x | Nat.nth (p x) k = 0}
    rw [he]
    exact (MeasurableSet.iUnion fun n => hm (n + 1) (by omega)).compl
  · exact hm m hm0

omit [MeasurableSpace X] in
theorem exists_frameDimensionStratum (p : X → ℕ → Prop) (x : X) :
    ∃ n, x ∈ frameDimensionStratum p n := by
  classical
  by_cases h : ∀ k, frameIndexAvailable (p x) k
  · exact ⟨0, h⟩
  · obtain ⟨k, hk⟩ := not_forall.mp h
    let hn : ∃ k, ¬frameIndexAvailable (p x) k := ⟨k, hk⟩
    exact ⟨Nat.find hn + 1, fun k hk => of_not_not (Nat.find_min hn hk), Nat.find_spec hn⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableProjectionFrame
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem measurableProjectionFrame_measurable (P : X → H →L[ℂ] H) (b : ℕ → H)
    (hP : ∀ v : H, Measurable fun x => P x v) (n : ℕ) :
    Measurable fun x => measurableProjectionFrame P b x n :=
  measurable_gramSchmidtNormed_sequence _ (fun i => hP (b i)) n

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionRangeFrame
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {X : Type*} [MeasurableSpace X]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem measurable_enumeratedSequence (v : X → ℕ → H)
    (hv : ∀ n, Measurable fun x => v x n) (k : ℕ) :
    Measurable fun x => v x (Nat.nth (fun n => v x n ≠ 0) k) := by
  have hp (n : ℕ) : MeasurableSet {x | v x n ≠ 0} :=
    (measurableSet_eq_fun (hv n) (measurable_const : Measurable fun _ : X => (0 : H))).compl
  have hn : Measurable fun x => Nat.nth (fun n => v x n ≠ 0) k :=
    measurable_natNth (fun x n => v x n ≠ 0) hp k
  have he : Measurable fun q : X × ℕ => v q.1 q.2 :=
    measurable_from_prod_countable_left hv
  exact he.comp (measurable_id.prodMk hn)

omit [CompleteSpace H] in
theorem enumeratedProjectionFrame_measurable (P : X → H →L[ℂ] H) (b : ℕ → H)
    (hP : ∀ v : H, Measurable fun x => P x v) (k : ℕ) :
    Measurable fun x => enumeratedProjectionFrame P b x k :=
  measurable_enumeratedSequence (measurableProjectionFrame P b)
    (measurableProjectionFrame_measurable P b hP) k

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonFiberRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.strongUnitarySpaceMeasurable _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! Genuine representations of a norm-separable algebra on the fibers of
the common spectral model. The old unit supplies the projection onto the
fibers of the original Hilbert space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- Every commuting norm-separable algebra has genuine unital fiber
representations after adjoining the ambient identity. -/
theorem exists_conull_common_representations
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) :
    ∃ s : Set (WeakDual.characterSpace ℂ A), MeasurableSet s ∧
      (cyclicCommonBaseMeasure π D) sᶜ = 0 ∧
      ∃ ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ]
          (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators),
        ∀ (b : B) (f : CommonCyclicHilbert π D),
          ∀ᵐ (x : s) ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
              (cyclicCommonBaseMeasure π D),
            isometricExtension (cyclicCommonEmbedding π D) (σ b) f x =
              ρ x (Unitization.inr b) (f x) := by
  let : TopologicalSpace.SeparableSpace (Unitization ℂ B) := separable_unitization
  obtain ⟨s, hsm, hsnull, ρ, haction, _⟩ :=
    exists_conull_diagonal_star_representations (cyclicCommonBaseMeasure π D)
      (unitalizedExtension (cyclicCommonEmbedding π D) σ) (by
        intro b r hr
        apply unitalizedExtension_commutes
        intro c
        exact commonExtension_commutes_localizations π D (σ c) (hσ c) r hr)
  refine ⟨s, hsm, hsnull, ρ, ?_⟩
  intro b f
  simpa only [unitalizedExtension_inr] using haction (Unitization.inr b) f

/-- Extending the conull representation by zero gives genuine nonunital
representations at every point, retaining the action of the original algebra. -/
theorem exists_common_nonunital_representations
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) :
    ∃ ρ : WeakDual.characterSpace ℂ A → B →⋆ₙₐ[ℂ]
        (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators),
      ∀ (b : B) (f : CommonCyclicHilbert π D),
        ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
          isometricExtension (cyclicCommonEmbedding π D) (σ b) f x = ρ x b (f x) := by
  obtain ⟨s, hsm, hsnull, ρ, haction⟩ := exists_conull_common_representations π D σ hσ
  refine ⟨zeroExtendNonunitalRepresentation s ρ, ?_⟩
  intro b f
  have h := zeroExtendOperatorField_action (cyclicCommonBaseMeasure π D) s hsm hsnull
    (isometricExtension (cyclicCommonEmbedding π D) (σ b))
    (fun y => ρ y (Unitization.inr b)) (haction b) f
  simpa only [zeroExtendNonunitalRepresentation_apply] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonSpectralMeasurable
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.strongUnitarySpaceMeasurable _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Borel representations in the common spectral model

The common spectral construction gives representations and their L²
action. A common-conull modification supplies Borel vector evaluations
for every source element while retaining that action.
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

attribute [local instance] OAI.KadisonKastler.commonCoordinateMeasurable
attribute [local instance] OAI.KadisonKastler.commonCoordinateBorel
theorem exists_measurable_common_representations
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) :
    ∃ ρ : WeakDual.characterSpace ℂ A → B →⋆ₙₐ[ℂ]
        (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators),
      (∀ b v, Measurable fun x => ρ x b v) ∧
      ∀ (b : B) (f : CommonCyclicHilbert π D),
        ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
          isometricExtension (cyclicCommonEmbedding π D) (σ b) f x = ρ x b (f x) := by
  obtain ⟨ρ, hρ⟩ := exists_common_nonunital_representations π D σ hσ
  have hm (b : B) (v : ScalarHilbertCoordinates D.generators) :
      AEStronglyMeasurable (fun x => ρ x b v) (cyclicCommonBaseMeasure π D) := by
    let f : CommonCyclicHilbert π D := Lp.const 2 (cyclicCommonBaseMeasure π D) v
    have he : ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
        isometricExtension (cyclicCommonEmbedding π D) (σ b) f x = ρ x b v := by
      filter_upwards [hρ b f, Lp.coeFn_const (cyclicCommonBaseMeasure π D) v (p := 2)]
        with x hx hf
      simpa only [f, hf, Function.const_apply] using hx
    exact (Lp.aestronglyMeasurable _).congr he
  obtain ⟨τ, hτm, hτ⟩ := exists_measurable_nonunitalRepresentation_version
    (cyclicCommonBaseMeasure π D) ρ hm
  refine ⟨τ, hτm, ?_⟩
  intro b f
  filter_upwards [hρ b f, hτ b] with x hx he
  rw [he]
  exact hx

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionDimensionStrata
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.projectionStratumOperator_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

instance projectionDimensionIndex_countable (n : ℕ) : Countable (projectionDimensionIndex n) := by
  cases n <;> dsimp [projectionDimensionIndex] <;> infer_instance

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem projectionStratumBasis_measurable (hPm : ∀ v, Measurable fun x => P x v)
    (n : ℕ) (i : projectionDimensionIndex n) :
    Measurable fun x : projectionRankStratum P b n =>
      (projectionStratumBasis P hP b hb n x i : H) := by
  simp_rw [projectionStratumBasis_coe]
  exact (enumeratedProjectionFrame_measurable P b hPm (projectionDimensionIndexNat i)).comp
    measurable_subtype_coe

theorem projectionStratumCoordinates_symm_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (v : projectionRankStratum P b n → ℓ²(projectionDimensionIndex n, ℂ))
    (hv : ∀ i, Measurable fun x => v x i) :
    Measurable fun x => ((projectionStratumCoordinates P hP b hb n x).symm (v x) : H) :=
  measurable_rangeHilbertSynthesis (fun x : projectionRankStratum P b n => P x.val)
    (projectionStratumBasis P hP b hb n) (projectionStratumBasis_measurable P hP b hb hPm n) v hv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurableFiberRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem representationUnitProjection_idempotent (x : X) :
    IsIdempotentElem (representationUnitProjection ρ x) :=
  (nonunitalUnitProjection_isStarProjection (ρ x)).isIdempotentElem

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2MeasurableExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

include hs in
theorem l2ExtensionFunction_add_ae
    (f g : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2ExtensionFunction μ s (f + g) =ᵐ[μ]
      fun x => l2ExtensionFunction μ s f x + l2ExtensionFunction μ s g x := by
  apply ae_of_subtype_of_outside μ s hs
  · filter_upwards [Lp.coeFn_add f g] with x hx
    simpa only [l2ExtensionFunction_coe, Pi.add_apply] using hx
  · intro x hx
    simp [l2ExtensionFunction, hx]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2LinearFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem l2LinearFieldMemLp (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    MemLp (fun x => T x (f x)) 2 μ := by
  apply ((Lp.memLp f).norm.const_mul C).mono'
    (aestronglyMeasurable_linearField_apply μ T hT f (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with x hx
  exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def l2LinearFieldApply (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) : Lp F 2 μ :=
  (l2LinearFieldMemLp μ T hT C hC f).toLp _

theorem l2LinearFieldApply_ae (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    l2LinearFieldApply μ T hT C hC f =ᵐ[μ] fun x => T x (f x) :=
  MemLp.coeFn_toLp _

def l2LinearFieldMap (T : X → E →L[ℂ] F)
    (hT : ∀ v, AEStronglyMeasurable (fun x => T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) : Lp E 2 μ →L[ℂ] Lp F 2 μ :=
  LinearMap.mkContinuous
    { toFun := l2LinearFieldApply μ T hT C hC
      map_add' f g := by
        apply Lp.ext
        filter_upwards [l2LinearFieldApply_ae μ T hT C hC (f + g),
          l2LinearFieldApply_ae μ T hT C hC f, l2LinearFieldApply_ae μ T hT C hC g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (l2LinearFieldApply μ T hT C hC f)
            (l2LinearFieldApply μ T hT C hC g)] with x hfg hf hg ha hb
        rw [hfg, hb, ha]
        simp only [Pi.add_apply]
        rw [hf, hg, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [l2LinearFieldApply_ae μ T hT C hC (c • f),
          l2LinearFieldApply_ae μ T hT C hC f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (l2LinearFieldApply μ T hT C hC f)] with x hc hf ha hb
        rw [hc, hb, ha]
        simp only [Pi.smul_apply]
        rw [hf, map_smul] }
    C (by
      intro f
      change ‖l2LinearFieldApply μ T hT C hC f‖ ≤ C * ‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [l2LinearFieldApply_ae μ T hT C hC f, hC] with x hx hn
      rw [hx]
      exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _)))

/-- Pointwise isometries give a genuine isometric inclusion of L² spaces. -/
def l2IsometryField (U : X → E →ₗᵢ[ℂ] F)
    (hU : ∀ v, AEStronglyMeasurable (fun x => U x v) μ) :
    Lp E 2 μ →ₗᵢ[ℂ] Lp F 2 μ where
  toLinearMap := (l2LinearFieldMap μ (fun x => (U x).toContinuousLinearMap) hU 1
    (isometryField_norm_bound μ U)).toLinearMap
  norm_map' f := by
    change ‖l2LinearFieldApply μ (fun x => (U x).toContinuousLinearMap) hU 1
      (isometryField_norm_bound μ U) f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (l2LinearFieldApply_ae μ _ hU 1 (isometryField_norm_bound μ U) f)]
    congr 1
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => (U x).norm_map (f x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_L2ProjectionSynthesis
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def projectionStratumSynthesis (n : ℕ) (x : projectionRankStratum P b n) :
    ℓ²(projectionDimensionIndex n, ℂ) →ₗᵢ[ℂ] H :=
  (P x.val).range.subtypeₗᵢ.comp
    (projectionStratumCoordinates P hP b hb n x).symm.toLinearIsometry

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem projectionStratumSynthesis_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    Measurable fun x => projectionStratumSynthesis P hP b hb n x v :=
  projectionStratumCoordinates_symm_measurable P hP b hb hPm n
    (fun _ => v) (fun _ => measurable_const)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionStrataPartition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem iUnion_frameDimensionStratum (p : X → ℕ → Prop) :
    (⋃ n, frameDimensionStratum p n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_frameDimensionStratum p x
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (P : X → H →L[ℂ] H) (b : ℕ → H)

theorem iUnion_projectionRankStratum : (⋃ n, projectionRankStratum P b n) = Set.univ :=
  iUnion_frameDimensionStratum _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRankCoordinates
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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
local instance rankModelCoordinateBorel_r82b5ee_1 :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩
def borelCommonModel (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) : BorelCommonModel π D σ := by
  let h := exists_measurable_common_representations π D σ hσ
  exact ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

omit [TopologicalSpace.SeparableSpace A] in
theorem commonRankBasis_total :
    (Submodule.span ℂ (Set.range (commonRankBasis π D))).topologicalClosure = ⊤ := by
  apply SetLike.coe_injective
  change closure (Submodule.span ℂ (Set.range (commonRankBasis π D)) :
    Set (ScalarHilbertCoordinates D.generators)) = Set.univ
  apply Set.eq_univ_of_forall
  intro v
  exact closure_mono Submodule.subset_span (TopologicalSpace.denseRange_denseSeq _ v)

variable {π D} {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_idempotent (x : WeakDual.characterSpace ℂ A) :
    IsIdempotentElem (commonModelProjection M x) :=
  representationUnitProjection_idempotent M.field x

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_norm_le (x : WeakDual.characterSpace ℂ A) :
    ‖commonModelProjection M x‖ ≤ 1 :=
  (nonunitalUnitProjection_isStarProjection (M.field x)).norm_le

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_measurable (v : ScalarHilbertCoordinates D.generators) :
    Measurable fun x => commonModelProjection M x v := M.measurable 1 v

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_action (f : CommonCyclicHilbert π D) :
    isometricExtension (cyclicCommonEmbedding π D) 1 f =ᵐ[cyclicCommonBaseMeasure π D]
      fun x => commonModelProjection M x (f x) := by
  simpa only [map_one, commonModelProjection, representationUnitProjection,
    nonunitalUnitProjection] using M.action (1 : B) f

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteUCP
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The UCP criterion for concrete von Neumann algebras

The ordinary Kadison--Kastler gap supplies precisely the reverse unit-ball
approximation used in the UCP range argument.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instPartialOrderContinuousLinearMapComplexId_solutions_1_r82b5ee_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingContinuousLinearMapComplexId_solutions_1_r82b5ee_1 : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2_r82b5ee_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2_r82b5ee_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
/-- The faithful inclusion of a concrete von Neumann algebra into its
ambient bounded operators. -/
abbrev algebraInclusion (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DenseUnitBallGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Passing unit-ball approximation through weakly dense tests

A bounded target family has a weak operator ultralimit. The same
uniform approximation bound survives this limit, allowing bounds on
weakly dense unit-ball tests to control the full Kadison--Kastler gap.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A family of contractions whose coefficientwise limits cover the
whole unit ball. No metrizability or choice of a sequence is required. -/
def WeakUnitBallDense {ι : Type*} (T : ι → H →L[ℂ] H) (M : VonNeumannAlgebra H) : Prop :=
  (∀ i, T i ∈ unitBall M) ∧
    ∀ a ∈ unitBall M, ∃ l : Filter ι, l.NeBot ∧
      ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (a x)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteRowOrbit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The normalized finite-row orbit is convex and invariant under row averaging. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def finiteRowOrbit (F : A →ₗ[ℂ] A) : Set (A →ₗ[ℂ] A) :=
  {G | ∃ (n : ℕ) (r : Fin n → A), (∑ i, r i * star (r i) = 1) ∧
    G = finiteRightAverage r F}

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreCharacters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem regularCharacterScalar_add_left (a b t : ℝ) :
    regularCharacterScalar (a + b) t =
      regularCharacterScalar a t * regularCharacterScalar b t := by
  simp only [regularCharacterScalar, add_mul, Circle.exp_add, Circle.coe_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierModulation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem character_eq_fourierChar (s t : ℝ) :
    regularCharacterScalar (2 * Real.pi * s) t = (Real.fourierChar (s * t) : ℂ) := by
  simp only [regularCharacterScalar, Real.fourierChar_apply', mul_assoc]

attribute [local instance] OAI.KadisonKastler.instNormedSpaceRealComplex_solutions
theorem character_temperate (s : ℝ) :
    (regularCharacterScalar (2 * Real.pi * s)).HasTemperateGrowth := by
  change (fun t : ℝ => Complex.exp ((↑((2 * Real.pi * s) * t) : ℂ) * Complex.I)).HasTemperateGrowth
  exact Function.HasTemperateGrowth.comp (g := fun t : ℝ => Complex.exp (t * Complex.I)) OAI.hasTemperateGrowth_exp_mul_I
    (f := fun t : ℝ => (2 * Real.pi * s) * t) (by fun_prop)

def modulatedSchwartz (s : ℝ) (f : SchwartzMap ℝ H) : SchwartzMap ℝ H :=
  SchwartzMap.smulLeftCLM H (regularCharacterScalar (2 * Real.pi * s)) f

omit [CompleteSpace H] in
theorem modulatedSchwartz_apply (s t : ℝ) (f : SchwartzMap ℝ H) :
    modulatedSchwartz s f t = regularCharacterScalar (2 * Real.pi * s) t • f t :=
  SchwartzMap.smulLeftCLM_apply_apply (character_temperate s) f t

omit [CompleteSpace H] in
theorem fourier_modulate_function (s : ℝ) (f : ℝ → H) (x : ℝ) :
    𝓕 (fun t => regularCharacterScalar (2 * Real.pi * s) t • f t) x = 𝓕 f (x - s) := by
  simp only [Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [character_eq_fourierChar]
  simp only [Circle.smul_def, smul_smul]
  have he : -(t * x) + s * t = -(t * (x - s)) := by ring
  have hp := congrArg (fun z : Circle => (z : ℂ))
    (Real.fourierChar.map_add_eq_mul (-(t * x)) (s * t))
  rw [he] at hp
  simp only [Circle.coe_mul] at hp
  exact congrArg (fun z : ℂ => z • f t) hp.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonKernelContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative translation continuity of the Poisson kernel -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

theorem realPoissonKernel_eq_cauchyPDFReal (t s : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    realPoissonKernel t r s = cauchyPDFReal t (NNReal.mk r hr) s := by
  change r / (Real.pi * ((t - s) ^ 2 + r ^ 2)) =
    Real.pi⁻¹ * r * ((s - t) ^ 2 + r ^ 2)⁻¹
  have hs : (t - s) ^ 2 = (s - t) ^ 2 := by ring
  rw [hs, div_eq_mul_inv, mul_inv]
  ring

theorem integrable_realPoissonKernel (t : ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (realPoissonKernel t r) := by
  have he : realPoissonKernel t r = cauchyPDFReal t (NNReal.mk r hr.le) :=
    funext fun s => realPoissonKernel_eq_cauchyPDFReal t s hr.le
  rw [he]
  exact integrable_cauchyPDFReal t

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyCauchyKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The one-sided exponential and its Cauchy transform

These are the concrete kernels for evaluating a positive-frequency multiplier.
All transforms here are computed from the half-line exponential integral.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The squared norm of the Cauchy kernel is a multiple of a probability
Poisson kernel. This also supplies its square integrability. -/
theorem cauchyResolvent_norm_sq {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    ‖(z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹‖ ^ 2 =
      realPoissonKernel (-z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s /
        (2 * z.re) := by
  rw [norm_inv, inv_pow, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
  unfold realPoissonKernel
  field_simp
  ring

theorem cauchyResolvent_memLp {z : ℂ} (hz : 0 < z.re) :
    MemLp (fun s : ℝ => (z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹) 2 := by
  have hn (s : ℝ) : z + (2 * Real.pi * s : ℝ) * Complex.I ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at h'
    exact hz.ne' h'
  have hc : Continuous (fun s : ℝ => (z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · exact hn
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact ((integrable_realPoissonKernel (-z.im / (2 * Real.pi))
    (div_pos hz (by positivity))).div_const (2 * z.re)).congr
      (Filter.Eventually.of_forall fun s => (cauchyResolvent_norm_sq hz s).symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationCorrectionSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Iterating the quadratic cochain correction

A cochain with unit complete bound and quadratic coboundary remainder
produces successive associative multiplications whose defects halve.
-/

namespace KadisonKastler

noncomputable section

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The precise local cochain estimate used by the quadratic iteration. -/
def QuadraticCochainSolver : Prop :=
  ∀ q : ℝ, 0 ≤ q → q ≤ 1/11 → ∀ m : SmallAssociativeProduct A q,
    ∃ D : A →ₗ[ℂ] A, CompletelyBoundedBy D q ∧
      (∀ x, D (star x) = star (D x)) ∧
      HaagerupBound (m.mul - LinearMap.mul ℂ A - linearCoboundary D) (2 * q ^ 2)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableAlgebraPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nearby separable test algebras

Countably many generators are enlarged alternately by nearby contractions.
The increasing norm closures give the two separable C*-algebras in §9.
All choices and closure estimates are constructed here; there is no
separable-reduction hypothesis.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cstarHull_le {s : Set (H →L[ℂ] H)} (M : VonNeumannAlgebra H)
    (hs : s ⊆ M) : cstarHull s ≤ M.toStarSubalgebra :=
  StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hs) (isClosed_algebra M)

theorem isSeparable_cstarHull {s : Set (H →L[ℂ] H)} (hs : s.Countable) :
    IsSeparable (cstarHull s : Set (H →L[ℂ] H)) :=
  (Generator.separable_countable_star_adjoin hs).closure

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripSineQuotient
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the pole in the modular strip contour

The scalar contour step in Rieffel--Van Daele, Lemma 4.6, uses
`(exp (i φ z) f z - f 0) / sin (π z)`. Divided differences remove its
singularity at zero without assuming a residue theorem.
-/

namespace KadisonKastler

open Set Filter
open scoped Topology

noncomputable section

theorem stripSineQuotient_differentiableOn (φ : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2}) :
    DifferentiableOn ℂ (stripSineQuotient φ f) {z : ℂ | |z.re| < 1 / 2} := by
  have h0 : {z : ℂ | |z.re| < 1 / 2} ∈ 𝓝 (0 : ℂ) := by
    apply (isOpen_lt (Complex.continuous_re.abs) continuous_const).mem_nhds
    norm_num
  apply DifferentiableOn.div _ stripSineSlope_differentiable.differentiableOn
    (fun z hz => stripSineSlope_ne_zero (lt_trans hz (by norm_num)))
  apply (Complex.differentiableOn_dslope h0).mpr
  exact (by fun_prop : Differentiable ℂ (fun w : ℂ => Complex.exp (Complex.I * φ * w))).differentiableOn.mul hf

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripContourBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary values of the regularized strip contour -/

namespace KadisonKastler

noncomputable section

theorem stripSineQuotient_right (φ : ℝ) (f : ℂ → ℂ) (t : ℝ) :
    stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I) =
      2 * stripAverageKernel Real.pi (φ : ℂ) t *
        (Complex.exp (Complex.I * φ / 2) * f ((1 / 2 : ℂ) + t * Complex.I)) -
      2 * stripAverageKernel Real.pi 0 t * f 0 := by
  have hz : (1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  rw [stripSineQuotient_eq hz, sine_strip_right]
  have he : Complex.I * φ * ((1 / 2 : ℂ) + t * Complex.I) =
      Complex.I * φ / 2 + -((φ : ℂ) * t) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [he, Complex.exp_add]
  unfold stripAverageKernel
  simp only [zero_mul, neg_zero, Complex.exp_zero]
  ring

theorem stripSineQuotient_left (φ : ℝ) (f : ℂ → ℂ) (t : ℝ) :
    stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I) =
      -(2 * stripAverageKernel Real.pi (φ : ℂ) t *
        (Complex.exp (-(Complex.I * φ / 2)) * f ((-1 / 2 : ℂ) + t * Complex.I))) +
      2 * stripAverageKernel Real.pi 0 t * f 0 := by
  have hz : (-1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  rw [stripSineQuotient_eq hz, sine_strip_left]
  have he : Complex.I * φ * ((-1 / 2 : ℂ) + t * Complex.I) =
      -(Complex.I * φ / 2) + -((φ : ℂ) * t) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [he, Complex.exp_add]
  unfold stripAverageKernel
  simp only [zero_mul, neg_zero, Complex.exp_zero]
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripContourBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem stripSineQuotient_decay (φ : ℝ) (f : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B)
    (x t : ℝ) (hx : |x| ≤ 1 / 2) (ht : 1 ≤ Real.pi * |t|) :
    ‖stripSineQuotient φ f ((x : ℂ) + t * Complex.I)‖ ≤
      8 * B * Real.exp (-(Real.pi - |φ|) * |t|) := by
  have ht0 : t ≠ 0 := by intro h; norm_num [h] at ht
  have hz0 : (x : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] at hi
    exact ht0 hi
  have hf : ‖f ((x : ℂ) + t * Complex.I)‖ ≤ B := hb _ (by simpa using hx)
  have hf0 : ‖f 0‖ ≤ B := hb _ (by norm_num)
  have he : ‖Complex.exp (Complex.I * φ * ((x : ℂ) + t * Complex.I))‖ ≤
      Real.exp (|φ| * |t|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : (Complex.I * φ * ((x : ℂ) + t * Complex.I)).re = -φ * t := by simp
    rw [hr]
    calc
      -φ * t ≤ |-φ * t| := le_abs_self _
      _ = |φ| * |t| := by rw [abs_mul, abs_neg]
  have hE : 1 ≤ Real.exp (|φ| * |t|) := Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hnum : ‖Complex.exp (Complex.I * φ * ((x : ℂ) + t * Complex.I)) *
        f ((x : ℂ) + t * Complex.I) - f 0‖ ≤ 2 * B * Real.exp (|φ| * |t|) := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    calc
      _ ≤ Real.exp (|φ| * |t|) * B + B :=
        add_le_add (mul_le_mul he hf (norm_nonneg _) (Real.exp_pos _).le) hf0
      _ ≤ _ := by nlinarith
  have hden := strip_sine_exponential_lower x t ht
  have hdpos : 0 < ‖Complex.sin (Real.pi * ((x : ℂ) + t * Complex.I))‖ :=
    (div_pos (Real.exp_pos _) (by norm_num)).trans_le hden
  rw [stripSineQuotient_eq hz0, norm_div]
  apply (div_le_iff₀ hdpos).mpr
  calc
    _ ≤ 2 * B * Real.exp (|φ| * |t|) := hnum
    _ = (8 * B * Real.exp (-(Real.pi - |φ|) * |t|)) *
        (Real.exp (Real.pi * |t|) / 4) := by
      rw [div_eq_mul_inv]
      have heq : Real.exp (-(Real.pi - |φ|) * |t|) * Real.exp (Real.pi * |t|) =
          Real.exp (|φ| * |t|) := by rw [← Real.exp_add]; congr 1; ring
      nlinarith [heq]
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripContourRectangle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The finite modular strip contour identity -/

namespace KadisonKastler

open Set

noncomputable section

theorem stripSineQuotient_rectangle (φ : ℝ) (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2})
    (T : ℝ) :
    (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + (-T : ℝ) * Complex.I)) -
    (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + T * Complex.I)) +
    Complex.I * (∫ t : ℝ in -T..T,
      stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) -
    Complex.I * (∫ t : ℝ in -T..T,
      stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I)) = 0 := by
  have h0 : {z : ℂ | |z.re| < 1 / 2} ∈ nhds (0 : ℂ) := by
    apply (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds
    norm_num
  have hc' := stripSineQuotient_continuousOn φ f hc (hd.differentiableAt h0)
  have hd' := stripSineQuotient_differentiableOn φ f hd
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (stripSineQuotient φ f) ((-1 / 2 : ℂ) + (-T : ℝ) * Complex.I)
    ((1 / 2 : ℂ) + T * Complex.I) ?_ ?_
  · simpa using h
  · apply hc'.mono
    intro z hz
    change z.re ∈ Set.uIcc _ _ ∧ z.im ∈ Set.uIcc _ _ at hz
    have hz' := hz.1
    norm_num at hz'
    exact abs_le.mpr hz'

  · apply hd'.mono
    intro z hz
    change z.re ∈ Ioo _ _ ∧ z.im ∈ Ioo _ _ at hz
    have hz' := hz.1
    norm_num at hz'
    exact abs_lt.mpr hz'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripContourLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Letting the horizontal strip edges tend to infinity -/

namespace KadisonKastler

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

theorem stripSineQuotient_horizontal_tendsto (φ : ℝ) (hφ : |φ| < Real.pi)
    (f : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B)
    (σ : ℝ) (hσ : |σ| = 1) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + (σ * n : ℝ) * Complex.I)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.exp (-(Real.pi - |φ|) * (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr (sub_pos.mpr hφ))
        tendsto_natCast_atTop_atTop)
  have hl := ht.const_mul (8 * B)
  rw [mul_zero] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have habs : |σ * (n : ℝ)| = n := by rw [abs_mul, hσ, one_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  have hlarge : 1 ≤ Real.pi * |σ * (n : ℝ)| := by
    rw [habs]
    nlinarith [Real.two_le_pi]
  have h : ‖∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + (σ * n : ℝ) * Complex.I)‖ ≤
      (8 * B * Real.exp (-(Real.pi - |φ|) * (n : ℝ))) * |(1 / 2 : ℝ) - (-1 / 2)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : |x| ≤ 1 / 2 := by
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    simpa only [habs] using stripSineQuotient_decay φ f B hB hb x (σ * n) hx' hlarge
  norm_num only [show (1 / 2 : ℝ) - (-1 / 2) = 1 by norm_num, abs_one, mul_one] at h
  simpa only [neg_div] using h

theorem stripSineQuotient_integral_edges_eq (φ : ℝ) (hφ : |φ| < Real.pi)
    (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2})
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B)
    (hr : Integrable (fun t : ℝ => stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)))
    (hl : Integrable (fun t : ℝ => stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I))) :
    (∫ t : ℝ, stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I) := by
  have htop := stripSineQuotient_horizontal_tendsto φ hφ f B hB hb 1 (by norm_num)
  have hbottom := stripSineQuotient_horizontal_tendsto φ hφ f B hB hb (-1) (by norm_num)
  have hright := intervalIntegral_tendsto_integral hr
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have hleft := intervalIntegral_tendsto_integral hl
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have he := ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub (hleft.const_mul Complex.I)
  have hzero : Tendsto (fun n : ℕ =>
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (-1 * n : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (1 * n : ℝ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I))) atTop (𝓝 0) := by
    have hf : (fun n : ℕ =>
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (-1 * n : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (1 * n : ℝ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I))) = fun _ => 0 := by
      funext n
      simpa using stripSineQuotient_rectangle φ f hc hd (n : ℝ)
    rw [hf]
    exact tendsto_const_nhds
  have h := tendsto_nhds_unique he hzero
  simp only [sub_self, zero_add, sub_eq_zero, mul_eq_mul_left_iff, Complex.I_ne_zero,
    or_false] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripContourAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar modular strip averaging formula

This is the contour identity of Rieffel--Van Daele, Lemma 4.6, for the
centered strip. The pole is removed before applying rectangle integration.
-/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem centered_strip_average (φ : ℝ) (hφ : |φ| < Real.pi) (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2})
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B) :
    (∫ t : ℝ, stripAverageKernel Real.pi (φ : ℂ) t *
      (Complex.exp (Complex.I * φ / 2) * f ((1 / 2 : ℂ) + t * Complex.I) +
        Complex.exp (-(Complex.I * φ / 2)) * f ((-1 / 2 : ℂ) + t * Complex.I))) = f 0 := by
  let kp := stripAverageKernel Real.pi (φ : ℂ)
  let k0 := stripAverageKernel Real.pi 0
  have hk : Integrable kp := stripAverageKernel_integrable (by simpa using hφ)
  have hk0 : Integrable k0 := stripAverageKernel_integrable (by simpa using Real.pi_pos)
  have hi (x : ℝ) (hx : |x| ≤ 1 / 2) :
      Integrable (fun t : ℝ => kp t * f ((x : ℂ) + t * Complex.I)) := by
    have hc' : Continuous (fun t : ℝ => f ((x : ℂ) + t * Complex.I)) :=
      hc.comp_continuous (by fun_prop) (fun t => by simpa using hx)
    exact hk.mul_bdd hc'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => hb _ (by simpa using hx)))
  let p : ℝ → ℂ := fun t => kp t *
    (Complex.exp (Complex.I * φ / 2) * f ((1 / 2 : ℂ) + t * Complex.I))
  let m : ℝ → ℂ := fun t => kp t *
    (Complex.exp (-(Complex.I * φ / 2)) * f ((-1 / 2 : ℂ) + t * Complex.I))
  have hp : Integrable p := by
    convert! (hi (1 / 2) (by norm_num)).const_mul (Complex.exp (Complex.I * φ / 2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    dsimp [p]
    push_cast
    ring
  have hm : Integrable m := by
    convert! (hi (-1 / 2) (by norm_num)).const_mul (Complex.exp (-(Complex.I * φ / 2))) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    dsimp [m]
    push_cast
    ring
  have hrfun : (fun t : ℝ => stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) =
      fun t => 2 * p t - (2 * f 0) * k0 t := by
    funext t
    rw [stripSineQuotient_right]
    dsimp [p, kp, k0]
    ring
  have hlfun : (fun t : ℝ => stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I)) =
      fun t => (-2) * m t + (2 * f 0) * k0 t := by
    funext t
    rw [stripSineQuotient_left]
    dsimp [m, kp, k0]
    ring
  have hr : Integrable (fun t : ℝ => stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) := by
    rw [hrfun]
    exact (hp.const_mul 2).sub (hk0.const_mul (2 * f 0))
  have hl : Integrable (fun t : ℝ => stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I)) := by
    rw [hlfun]
    exact (hm.const_mul (-2)).add (hk0.const_mul (2 * f 0))
  have he := stripSineQuotient_integral_edges_eq φ hφ f hc hd B hB hb hr hl
  rw [hrfun, hlfun, integral_sub (hp.const_mul 2) (hk0.const_mul (2 * f 0)),
    integral_add (hm.const_mul (-2)) (hk0.const_mul (2 * f 0))] at he
  simp only [integral_const_mul] at he
  change 2 * (∫ t, p t) - 2 * f 0 * (∫ t, stripAverageKernel Real.pi 0 t) =
    (-2) * (∫ t, m t) + 2 * f 0 * (∫ t, stripAverageKernel Real.pi 0 t) at he
  rw [integral_stripAverageKernel_zero] at he
  have hsum : (∫ t, p t) + (∫ t, m t) = f 0 := by linear_combination (1 / 2 : ℂ) * he
  rw [← integral_add hp hm] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext t
  dsimp [p, m, kp]
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SubalgebraInvariantMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting an invariant operator mean to a von Neumann algebra

The coefficient construction preserves every von Neumann algebra. Restricting
its domain and codomain therefore gives the exact mean for internal unitary
correction, without a normality or injectivity assumption on the target.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance subalgebraFamilyCStar (N : VonNeumannAlgebra H) :
    CStarAlgebra (G →ᵇ Algebra N) where

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateMatrixRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

abbrev TwoStateMatrixHilbert (H K : Type*)
    [NormedAddCommGroup H] [NormedAddCommGroup K] :=
  WithLp 2 (FiniteHilbert (Fin 2) H × FiniteHilbert (Fin 2) K)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `normSubLeMaxCompat` (port compat, absent from our Mathlib). -/
theorem normSubLeMaxCompat_p1 {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have hsa : IsSelfAdjoint (a - b) :=
    (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have h := IsSelfAdjoint.norm_le_max_of_le_of_le (a := -b) (b := a) (x := a - b)
    (by rw [le_sub_iff_add_le]; simpa using ha) (sub_le_self a hb) hsa
  rwa [norm_neg, max_comm] at h

/-! # Kernel projections of measurable operator fields

Cesàro averages of a positive contraction converge strongly to its kernel
projection. Applied pointwise, this proves measurability of the projection
without using a measurable selection or Borel functional calculus input.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

/-- Evaluation is a star algebra homomorphism. -/
def evalHom (x : D) : WeakOperatorRepresentative (H := H) μ →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun F := eval F x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem evalHom_apply (x : D) (F : WeakOperatorRepresentative (H := H) μ) :
    evalHom x F = eval F x := rfl


local instance kernelSourceOrder : PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _
local instance kernelSourceStarOrder : StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _

attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.kernelTargetStarOrder
def kernelAverage (F : WeakOperatorRepresentative (H := H) μ) (n : ℕ) :
    WeakOperatorRepresentative (H := H) μ :=
  (n : ℂ)⁻¹ • ∑ i ∈ Finset.range n, (1 - F) ^ i

attribute [local instance] OAI.KadisonKastler.WeakOperatorRepresentative.kernelTargetOrder
theorem norm_positive_complement_le (T : H →L[ℂ] H)
    (hT : 0 ≤ T) (hn : ‖T‖ ≤ 1) : ‖1 - T‖ ≤ 1 :=
  (normSubLeMaxCompat_p1
    (show (0 : H →L[ℂ] H) ≤ 1 from zero_le_one) hT).trans
    (max_le (IsStarProjection.norm_le _ (IsStarProjection.one _)) hn)

theorem operator_kernel_averages_tendsto (T : H →L[ℂ] H)
    (hT : 0 ≤ T) (hn : ‖T‖ ≤ 1) (ξ : H) :
    Tendsto (fun n => birkhoffAverage ℂ ((1 : H →L[ℂ] H) - T) id n ξ) atTop
      (𝓝 (T.ker.starProjection ξ)) := by
  have heq : (1 - T).eqLocus (1 : H →L[ℂ] H) = T.ker := by
    ext η
    change η - T η = η ↔ T η = 0
    simp only [sub_eq_self]
  have ht := (1 - T).tendsto_birkhoffAverage_orthogonalProjection
    (norm_positive_complement_le T hT hn) ξ
  change Tendsto (fun n => birkhoffAverage ℂ ((1 : H →L[ℂ] H) - T) id n ξ) atTop
    (𝓝 (((1 - T).eqLocus (1 : H →L[ℂ] H)).starProjection ξ)) at ht
  rw [starProjection_congr _ _ heq] at ht
  exact ht

theorem kernelAverage_eval (F : WeakOperatorRepresentative (H := H) μ)
    (x : D) (ξ : H) (n : ℕ) : eval (kernelAverage F n) x ξ =
      birkhoffAverage ℂ ((1 : H →L[ℂ] H) - eval F x) id n ξ := by
  change (evalHom (H := H) (μ := μ) x ((n : ℂ)⁻¹ • ∑ i ∈ Finset.range n, (1 - F) ^ i)) ξ = _
  simp only [birkhoffAverage, birkhoffSum, map_smul, map_sum,
    map_pow, map_sub, map_one, evalHom_apply]
  simp only [smul_apply, sum_apply, FunLike.coe_pow_eq_iterate, id_eq]

theorem kernelAverage_tendsto (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) (x : D) (ξ : H) :
    Tendsto (fun n => eval (kernelAverage F n) x ξ) atTop
      (𝓝 ((eval F x).ker.starProjection ξ)) := by
  have ht := operator_kernel_averages_tendsto (eval F x)
    (map_nonneg (evalHom (H := H) (μ := μ) x) hF) ((eval_norm_le F x).trans hn) ξ
  simpa only [kernelAverage_eval] using ht

/-- Kernel projections of positive contraction fields are measurable. -/
theorem kernel_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) (ξ : H) :
    AEStronglyMeasurable (fun x => (eval F x).ker.starProjection ξ) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (kernelAverage F n).eval_aestronglyMeasurable ξ)
  exact Eventually.of_forall fun x => kernelAverage_tendsto F hF hn x ξ

/-- The kernel projection is an actual measurable representative. -/
def kernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) : WeakOperatorRepresentative (H := H) μ :=
  mk (fun x => (eval F x).ker.starProjection) 1
    (fun x => IsStarProjection.norm_le _ (isStarProjection_starProjection (U := (eval F x).ker)))
    (kernel_aestronglyMeasurable F hF hn)
    (fun ξ => by
      have he (x : D) : star ((eval F x).ker.starProjection) = (eval F x).ker.starProjection :=
        (isStarProjection_starProjection (U := (eval F x).ker)).isSelfAdjoint.star_eq
      simpa only [he] using kernel_aestronglyMeasurable F hF hn ξ)

@[simp] theorem eval_kernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) (x : D) :
    eval (kernelProjection F hF hn) x = (eval F x).ker.starProjection := rfl

/-- Remove the contraction restriction by a positive scalar rescaling. -/
theorem positive_kernel_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (ξ : H) :
    AEStronglyMeasurable (fun x => (eval F x).ker.starProjection ξ) μ := by
  let c : ℝ := ‖F‖ + 1
  have hc : 0 < c := by dsimp [c] <;> positivity
  let G : WeakOperatorRepresentative (H := H) μ := c⁻¹ • F
  have hG : 0 ≤ G := smul_nonneg (inv_nonneg.mpr hc.le) hF
  have hGn : ‖G‖ ≤ 1 := by
    dsimp [G]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    apply (inv_mul_le_iff₀ hc).mpr
    dsimp [c]
    linarith
  have he (x : D) : (eval G x).ker = (eval F x).ker := by
    ext η
    change c⁻¹ • eval F x η = 0 ↔ eval F x η = 0
    simp only [smul_eq_zero, inv_ne_zero hc.ne', false_or]
  simpa only [he] using kernel_aestronglyMeasurable G hG hGn ξ

/-- Kernel projection of a positive measurable field, with no norm restriction. -/
def positiveKernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) : WeakOperatorRepresentative (H := H) μ :=
  mk (fun x => (eval F x).ker.starProjection) 1
    (fun x => IsStarProjection.norm_le _ (isStarProjection_starProjection (U := (eval F x).ker)))
    (positive_kernel_aestronglyMeasurable F hF)
    (fun ξ => by
      have he (x : D) : star ((eval F x).ker.starProjection) = (eval F x).ker.starProjection :=
        (isStarProjection_starProjection (U := (eval F x).ker)).isSelfAdjoint.star_eq
      simpa only [he] using positive_kernel_aestronglyMeasurable F hF ξ)

@[simp] theorem eval_positiveKernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (x : D) :
    eval (positiveKernelProjection F hF) x = (eval F x).ker.starProjection := rfl

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldSpectralSupport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral support inside measurable fields

The pointwise support of a continuous positive part is a measurable field.
This connects the constructed kernel projection with the concrete spectral
splittings already used in finite-factor arguments.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

local instance supportFieldOrder : PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _
local instance supportFieldStarOrder : StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _

local instance supportOperatorOrder_r82b5ee_1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance supportOperatorStarOrder_r82b5ee_1 : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
local instance supportTopOrder_r82b5ee_1 : PartialOrder (fullOperatorAlgebra (H := H)).toStarSubalgebra :=
  CStarAlgebra.spectralOrder _
local instance supportTopStarOrder_r82b5ee_1 : StarOrderedRing (fullOperatorAlgebra (H := H)).toStarSubalgebra :=
  CStarAlgebra.spectralOrderedRing _
/-- The value of a field, viewed inside the full operator algebra. -/
def topElement (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    (fullOperatorAlgebra (H := H)).toStarSubalgebra := ⟨eval F x, by trivial⟩

@[simp] theorem topElement_val (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    (topElement F x).val = eval F x := rfl

/-- Support of the positive part, as an actual measurable field. -/
def positiveSupport (F : WeakOperatorRepresentative (H := H) μ) :
    WeakOperatorRepresentative (H := H) μ :=
  1 - positiveKernelProjection (F⁺) (CFC.posPart_nonneg F)

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldProjectionDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.PopaCorner.algebra_closed _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral step approximation of measurable fields

A common dyadic mesh is used for every point of the measure space.
Measurability of its finitely many projection fields follows inductively
from the constructed spectral support. The existing concrete spectral
interval estimate gives a uniform operator-norm error.
-/

namespace KadisonKastler

open MeasureTheory Generator.Tracial
open scoped Topology CStarAlgebra BigOperators

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

local instance densityFieldOrder : PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakFieldUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary representatives of measurable operator classes

The AE-zero ideal has a useful lifting property: every unitary quotient
class has an everywhere unitary, weakly measurable representative. Only a
null set is changed, so no selection theorem is needed.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

/-- Pointwise evaluation of a unitary representative is an actual unitary. -/
def unitaryEval (V : unitary (WeakOperatorRepresentative (H := H) μ)) (x : D) :
    unitary (H →L[ℂ] H) :=
  ⟨eval (V : WeakOperatorRepresentative (H := H) μ) x, by
    constructor
    · exact congrArg (fun F : WeakOperatorRepresentative (H := H) μ => eval F x)
        (Unitary.star_mul_self_of_mem V.property)
    · exact congrArg (fun F : WeakOperatorRepresentative (H := H) μ => eval F x)
        (Unitary.mul_star_self_of_mem V.property)⟩

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end


