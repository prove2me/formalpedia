-- Prove2me | Definitions.Def_Q260K022
-- name    : Q260K022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:26:18.546193+00:00
-- url     : https://prove2.me/theorems/1a47b16b-06df-4886-ba8b-b999a369533c
-- title:
--   Definitions bundle Q260K022 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 9 definitions and 13 theorems. The definitions and types are `OAI.KadisonKastler.NonsingularAction.operatorAction`, `OAI.KadisonKastler.NonsingularAction.operatorEquiv`, `OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction`, `OAI.KadisonKastler.NonsingularAction.restrictedOperatorEquiv`, `OAI.KadisonKastler.ScalarBoundaryMean.operatorMean`, `OAI.KadisonKastler.ScalarBoundaryMean.operatorMeanValue`, `OAI.KadisonKastler.operatorFieldAlgebra`, `OAI.KadisonKastler.operatorFieldDiagonal`, `OAI.KadisonKastler.twoRatioScalingRow`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_HardyCauchyBoundary`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/HardyCauchyBoundary.lean), [`KadisonKastler_KernelReconstruction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/KernelReconstruction.lean), [`KadisonKastler_OperatorCoefficientMean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/OperatorCoefficientMean.lean), [`KadisonKastler_OperatorFieldValues`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/OperatorFieldValues.lean), [`KadisonKastler_OperatorMeanEquivariance`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/OperatorMeanEquivariance.lean), [`KadisonKastler_PublishedFieldTomiyama`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/PublishedFieldTomiyama.lean), [`KadisonKastler_RestrictedOperatorMean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/RestrictedOperatorMean.lean), [`KadisonKastler_ScalarBoundaryMean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ScalarBoundaryMean.lean), [`KadisonKastler_TwoRatioScalingWords`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TwoRatioScalingWords.lean).
--
--   **Imports.** It imports the bundles `Q260K015`, `Q260K016`, `Q260K017` and `Q260K018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K026`, `Q260K028` and `Q260K061`; the statements `OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_equivariant` and `OAI.KadisonKastler.exists_measurable_operator_cocycle_with_lift`; the proofs of `OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_equivariant`, `OAI.KadisonKastler.exists_measurable_operator_cocycle_with_lift` and `OAI.KadisonKastler.weakOperatorField_closed_projection_span_eq_top`.
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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
import Definitions.Def_Q260K015
import Definitions.Def_Q260K016
import Definitions.Def_Q260K017
import Definitions.Def_Q260K018

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyCauchyBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem hardyReproducingKernel_apply_ae {z : ℂ} (hz : 0 < z.re) :
    hardyReproducingKernel z hz =ᵐ[volume] hardyCauchyFunction z := by
  have he : 𝓕⁻ (positiveLaplaceKernel z) = hardyCauchyFunction z :=
    funext (fourierInv_positiveLaplaceKernel hz)
  have hF : MemLp (𝓕⁻ (positiveLaplaceKernel z)) 2 := by
    rw [he]
    exact hardyCauchyFunction_memLp hz
  have h := fourierInv_toLp_of_integrable (integrable_positiveLaplaceKernel hz)
    (positiveLaplaceKernel_memLp hz) hF
  change 𝓕⁻ ((positiveLaplaceKernel_memLp hz).toLp _) = _ at h
  change (𝓕⁻ ((positiveLaplaceKernel_memLp hz).toLp _) : RegularCoreHilbert ℂ) =ᵐ[volume] _
  rw [h]
  exact hF.coeFn_toLp.trans (Filter.Eventually.of_forall fun s => congrFun he s)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarBoundaryMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar boundary mean on actual L-infinity classes

The source is the bounded family of L-infinity sections indexed by the
countable discrete group. Multiplication and nonsingular pullback are
defined on the actual almost-everywhere classes. The scalar
conditional-expectation property includes the module and action identities.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D : Type*} [MeasurableSpace D] {μ : Measure D}

theorem scalarInfinityMul_const_one (f : ScalarLInfinity μ) :
    scalarInfinityMul (scalarInfinityConst μ 1) f = f := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae (scalarInfinityConst μ 1) f,
    scalarInfinityConst_ae (μ := μ) 1] with x hm h1
  rw [hm, h1, one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_KernelReconstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reconstructing measurable operator fields from scalar kernels

The coherent countable-core representatives give pointwise bounded
operators. Dense scalar tests prove measurability; continuity of the
L-infinity kernel then identifies all coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ScalarOperatorKernel

variable (K : ScalarOperatorKernel H μ) (C : RationalComplexCore H)

variable [SeparableSpace H]

variable [IsFiniteMeasure μ]

/-- Bounded scalar sesquilinear kernels have actual measurable operator
representatives, with no additional existence premise. -/
theorem exists_representative : ∃ F : WeakOperatorRepresentative (H := H) μ,
    ‖F‖ ≤ K.bound ∧ ∀ ξ η : H, WeakOperatorRepresentative.coefficient F ξ η = K.coeff ξ η := by
  let C : RationalComplexCore H := Classical.choice (exists_rationalComplexCore H)
  exact ⟨K.reconstructedRepresentative C, K.reconstructedRepresentative_norm_le C,
    K.reconstructedRepresentative_coefficient C⟩

end ScalarOperatorKernel

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorCoefficientMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_pullback _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorRepresentative.pullback_id _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.randomWalkPathAction_apply _root_.OAI.KadisonKastler.shiftBoundaryAction_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive operator-field averaging from the scalar boundary mean

All objects here are the actual measurable fields modulo almost-everywhere
equality. The construction uses norm-minimizing representatives only to
produce an operator; its scalar coefficients characterize it intrinsically.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable {α : NonsingularAction G D μ}

namespace ScalarBoundaryMean

variable (m : ScalarBoundaryMean α)

/-- Reconstruct the operator-valued mean from the averaged scalar kernel. -/
def operatorMeanValue (F : G →ᵇ WeakOperatorField (H := H) μ) : WeakOperatorField (H := H) μ :=
  operatorFieldQuotient μ
    (Classical.choose ((WeakOperatorField.uniformFamily F).meanKernel m).exists_representative)

theorem operatorMeanValue_coefficient (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    WeakOperatorField.coefficient (m.operatorMeanValue F) ξ η =
      m.toCLM (WeakOperatorField.coefficientFamily F ξ η) := by
  rw [operatorMeanValue, WeakOperatorField.coefficient_quotient]
  exact (Classical.choose_spec
    ((WeakOperatorField.uniformFamily F).meanKernel m).exists_representative).2 ξ η

theorem norm_operatorMeanValue_le (F : G →ᵇ WeakOperatorField (H := H) μ) :
    ‖m.operatorMeanValue F‖ ≤ ‖F‖ :=
  (operatorFieldQuotient_norm_le μ _).trans (Classical.choose_spec
    ((WeakOperatorField.uniformFamily F).meanKernel m).exists_representative).1

theorem operatorMeanValue_add (F E : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMeanValue (F + E) = m.operatorMeanValue F + m.operatorMeanValue E := by
  apply WeakOperatorField.ext_coeff
  intro ξ η
  rw [WeakOperatorField.coefficient_add, m.operatorMeanValue_coefficient,
    m.operatorMeanValue_coefficient, m.operatorMeanValue_coefficient,
    WeakOperatorField.coefficientFamily_add, map_add]

theorem operatorMeanValue_smul (c : ℂ) (F : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMeanValue (c • F) = c • m.operatorMeanValue F := by
  apply WeakOperatorField.ext_coeff
  intro ξ η
  rw [WeakOperatorField.coefficient_smul, m.operatorMeanValue_coefficient,
    m.operatorMeanValue_coefficient, WeakOperatorField.coefficientFamily_smul, map_smul]

/-- The scalar boundary mean induces a contractive complex-linear map
on actual essentially bounded measurable operator fields. -/
def operatorMean : (G →ᵇ WeakOperatorField (H := H) μ) →L[ℂ] WeakOperatorField (H := H) μ :=
  LinearMap.mkContinuous
    { toFun := m.operatorMeanValue
      map_add' := m.operatorMeanValue_add
      map_smul' := m.operatorMeanValue_smul }
    1 (fun F => by simpa using m.norm_operatorMeanValue_le F)

@[simp]
theorem operatorMean_apply (F : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMean F = m.operatorMeanValue F := rfl

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedFieldTomiyama
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace OAI

/-! # The precise Tomiyama input for the operator-field mean

Tomiyama, *On the projection of norm one in W*-algebras*, Proceedings of
 the Japan Academy 33 (1957), 608–612, Theorem 1(2), pp. 608–609,
 DOI 10.3792/pja/1195524885.

Only the bimodule conclusion for the constant-field inclusion is retained.
The contractive retraction and its adjoint preservation are constructed in
`OperatorCoefficientMean` and `OperatorMeanStar`, not assumed here.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : MeasureTheory.Measure D} [MeasureTheory.IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Constant fields form the target C-star subalgebra of the expectation. -/
abbrev operatorFieldDiagonal : WeakOperatorField (H := H) μ →⋆ₐ[ℂ]
    (G →ᵇ WeakOperatorField (H := H) μ) := boundaryConstant

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorFieldValues
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Von Neumann algebra values of measurable operator fields

Commuting with constant operators in the commutant is a norm-closed
condition. Countably many strong-operator tests identify this condition
with pointwise membership outside one null set.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Pointwise BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed field algebra commuting with the constant commutant. -/
def operatorFieldAlgebra (M : VonNeumannAlgebra H) :
    StarSubalgebra ℂ (WeakOperatorField (H := H) μ) :=
  StarSubalgebra.centralizer ℂ (operatorFieldConst μ '' (M.commutant : Set (H →L[ℂ] H)))

theorem mem_operatorFieldAlgebra_iff (M : VonNeumannAlgebra H)
    (q : WeakOperatorField (H := H) μ) :
    q ∈ operatorFieldAlgebra (μ := μ) M ↔
      ∀ T ∈ M.commutant, operatorFieldConst μ T * q = q * operatorFieldConst μ T := by
  rw [operatorFieldAlgebra, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h T hT
    exact (h _ ⟨T, hT, rfl⟩).1
  · intro h b hb
    obtain ⟨T, hT, rfl⟩ := hb
    exact ⟨h T hT, by simpa only [map_star] using h (star T) (star_mem hT)⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorMeanEquivariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.randomWalkPathAction_apply _root_.OAI.KadisonKastler.shiftBoundaryAction_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The nonsingular action and equivariant operator mean -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace NonsingularAction

variable (α : NonsingularAction G D μ)

/-- Inverse pullback gives the boundary action on actual operator classes. -/
def operatorEquiv (g : G) :
    WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ] WeakOperatorField (H := H) μ where
  toFun := WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹)
  invFun := WeakOperatorField.pullback (α.toPerm g) (α.quasi g)
  left_inv q := by
    rw [WeakOperatorField.pullback_comp]
    have h : (α.toPerm g⁻¹ : D → D) ∘ α.toPerm g = id := by
      funext x
      simp only [Function.comp_apply, ← α.mul_apply, inv_mul_cancel, α.one_apply, id_eq]
    simpa only [h] using WeakOperatorField.pullback_id q
  right_inv q := by
    rw [WeakOperatorField.pullback_comp]
    have h : (α.toPerm g : D → D) ∘ α.toPerm g⁻¹ = id := by
      funext x
      simp only [Function.comp_apply, ← α.mul_apply, mul_inv_cancel, α.one_apply, id_eq]
    simpa only [h] using WeakOperatorField.pullback_id q
  map_mul' := (WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹)).map_mul
  map_add' := (WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹)).map_add
  map_smul' c q := map_smul (WeakOperatorField.pullback (H := H) (α.toPerm g⁻¹) (α.quasi g⁻¹)) c q
  map_star' q := map_star (WeakOperatorField.pullback (H := H) (α.toPerm g⁻¹) (α.quasi g⁻¹)) q

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem operatorEquiv_apply (g : G) (q : WeakOperatorField (H := H) μ) :
    α.operatorEquiv (H := H) g q = WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹) q := rfl

/-- The inverse pullbacks form a group action. -/
def operatorAction : G →* (WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ] WeakOperatorField (H := H) μ) where
  toFun := α.operatorEquiv (H := H)
  map_one' := by
    apply StarAlgEquiv.ext
    intro q
    change WeakOperatorField.pullback (α.toPerm (1 : G)⁻¹) (α.quasi (1 : G)⁻¹) q = q
    have h : (α.toPerm (1 : G)⁻¹ : D → D) = id := by funext x; simp
    simpa only [h] using WeakOperatorField.pullback_id q
  map_mul' g h := by
    apply StarAlgEquiv.ext
    intro q
    change WeakOperatorField.pullback (α.toPerm (g * h)⁻¹) _ q =
      WeakOperatorField.pullback (α.toPerm g⁻¹) _ (WeakOperatorField.pullback (α.toPerm h⁻¹) _ q)
    rw [WeakOperatorField.pullback_comp]
    have he : (α.toPerm (g * h)⁻¹ : D → D) = α.toPerm h⁻¹ ∘ α.toPerm g⁻¹ := by
      funext x
      simp only [mul_inv_rev, α.mul_apply, Function.comp_apply]
    simp only [he]

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem operatorAction_constant (g : G) (T : H →L[ℂ] H) :
    α.operatorAction (H := H) g (operatorFieldConst μ T) = operatorFieldConst μ T :=
  WeakOperatorField.pullback_constant _ _ _

end NonsingularAction

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.evalHom_apply _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_kernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.eval_positiveKernelProjection _root_.OAI.KadisonKastler.WeakOperatorRepresentative.topElement_val _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.randomWalkPathAction_apply _root_.OAI.KadisonKastler.shiftBoundaryAction_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equivariant averaging within a von Neumann algebra

The constant-commutant description of the field algebra is invariant under
boundary pullback. Restricting the constructed mean therefore keeps both
the cocycle and its correction in the prescribed von Neumann algebra.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace NonsingularAction

variable (α : NonsingularAction G D μ) (M : VonNeumannAlgebra H)

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
/-- Boundary pullback preserves the algebra of fields with values in M. -/
theorem operatorAction_mem (g : G) (q : WeakOperatorField (H := H) μ)
    (hq : q ∈ operatorFieldAlgebra (μ := μ) M) :
    α.operatorAction (H := H) g q ∈ operatorFieldAlgebra (μ := μ) M := by
  apply (mem_operatorFieldAlgebra_iff M _).mpr
  intro T hT
  have he := congrArg (α.operatorAction (H := H) g)
    ((mem_operatorFieldAlgebra_iff M q).mp hq T hT)
  simpa only [map_mul, α.operatorAction_constant] using he

/-- The boundary automorphism restricted to the M-valued field algebra. -/
def restrictedOperatorEquiv (g : G) :
    operatorFieldAlgebra (μ := μ) M ≃⋆ₐ[ℂ] operatorFieldAlgebra (μ := μ) M where
  toFun q := ⟨α.operatorAction (H := H) g q.val, α.operatorAction_mem M g q.val q.property⟩
  invFun q := ⟨α.operatorAction (H := H) g⁻¹ q.val,
    α.operatorAction_mem M g⁻¹ q.val q.property⟩
  left_inv q := by
    apply Subtype.ext
    change (α.operatorAction (H := H) g⁻¹) ((α.operatorAction (H := H) g) q.val) = q.val
    rw [← StarAlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, StarAlgEquiv.one_apply]
  right_inv q := by
    apply Subtype.ext
    change (α.operatorAction (H := H) g) ((α.operatorAction (H := H) g⁻¹) q.val) = q.val
    rw [← StarAlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, StarAlgEquiv.one_apply]
  map_mul' q r := Subtype.ext ((α.operatorAction (H := H) g).map_mul q.val r.val)
  map_add' q r := Subtype.ext ((α.operatorAction (H := H) g).map_add q.val r.val)
  map_smul' c q := Subtype.ext (map_smul (α.operatorAction (H := H) g) c q.val)
  map_star' q := Subtype.ext (map_star (α.operatorAction (H := H) g) q.val)

/-- The restricted automorphisms form a group action. -/
def restrictedOperatorAction :
    G →* (operatorFieldAlgebra (μ := μ) M ≃⋆ₐ[ℂ] operatorFieldAlgebra (μ := μ) M) where
  toFun := α.restrictedOperatorEquiv M
  map_one' := by
    apply StarAlgEquiv.ext
    intro q
    apply Subtype.ext
    exact congrArg (fun e : WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ]
      WeakOperatorField (H := H) μ => e q.val) (α.operatorAction (H := H)).map_one
  map_mul' g h := by
    apply StarAlgEquiv.ext
    intro q
    apply Subtype.ext
    exact congrArg (fun e : WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ]
      WeakOperatorField (H := H) μ => e q.val) ((α.operatorAction (H := H)).map_mul g h)

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem restrictedOperatorAction_coe (g : G) (q : operatorFieldAlgebra (μ := μ) M) :
    (α.restrictedOperatorAction M g q : WeakOperatorField (H := H) μ) =
      α.operatorAction (H := H) g (q : WeakOperatorField (H := H) μ) := rfl

end NonsingularAction

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

def twoRatioScalingRow (k l : ℤ) : TwoRatioSite → Fin 2 :=
  Sum.elim (fun _ => signedSiteRow k) (fun _ => signedSiteRow l)

open Generator

end

end KadisonKastler

end OAI
end


