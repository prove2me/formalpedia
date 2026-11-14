-- Prove2me | Definitions.Def_Q260K035
-- name    : Q260K035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T08:34:31.262102+00:00
-- url     : https://prove2.me/theorems/915940b4-d265-4a1f-aa84-71b363c6a78e
-- title:
--   Definitions bundle Q260K035 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 24 definitions, 2 instances and 32 theorems. The definitions and types are `OAI.KadisonKastler.ScalarBoundaryMean.restrictedOperatorBimoduleMean`, `OAI.KadisonKastler.graphCoordinateScale`, `OAI.KadisonKastler.graphHighCutInverse`, `OAI.KadisonKastler.graphIdentificationUnitary`, `OAI.KadisonKastler.graphIsometry`, `OAI.KadisonKastler.graphResolventCutoff`, `OAI.KadisonKastler.graphScaleDenominator`, `OAI.KadisonKastler.graphScaleInverse`, `OAI.KadisonKastler.matrixCentralResidual`, `OAI.KadisonKastler.matrixInnerAverage`, `OAI.KadisonKastler.matrixStageCentralProjection`, `OAI.KadisonKastler.modularApproximation`, `OAI.KadisonKastler.modularUpperCut`, `OAI.KadisonKastler.modularUpperCutField`, `OAI.KadisonKastler.projectionCentralSpace`, `OAI.KadisonKastler.regularizedModularGroup`, `OAI.KadisonKastler.regularizedModularLog`, `OAI.KadisonKastler.rescaledGraphAction`, `OAI.KadisonKastler.stateGraphUnitary`, `OAI.KadisonKastler.subgroupAlgebraRepresentation`, `OAI.KadisonKastler.tomitaClosedLinearOperator`, `OAI.KadisonKastler.tomitaProductCoordinates`, `OAI.KadisonKastler.tomitaProductGraph`, `OAI.KadisonKastler.twoStateFirstColumnVector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CentralVectorMatrixLimit`, `KadisonKastler_FaithfulCyclicConstruction`, `KadisonKastler_GraphCompressionVectors`, `KadisonKastler_GraphHighCutInverse`, `KadisonKastler_GraphIdentificationIndependence`, `KadisonKastler_GraphIsometryTransport`, `KadisonKastler_GraphScaleFunctionalCalculus`, `KadisonKastler_GraphScaleResolvent`, `KadisonKastler_MatrixCentralRefinement`, `KadisonKastler_MatrixCentralResidual`, `KadisonKastler_MatrixChainEmbedding`, `KadisonKastler_ModularGaugeTransport`, `KadisonKastler_ModularPairingComplexification`, `KadisonKastler_ModularPairingProducts`, `KadisonKastler_ModularSpectralCuts`, `KadisonKastler_ModularStrongLimit`, `KadisonKastler_ProjectionCentralSpace`, `KadisonKastler_RegularizedModularGroup`, `KadisonKastler_RescaledGraphAction`, `KadisonKastler_ResolventCutMeasurable`, `KadisonKastler_RestrictedOperatorMean`, `KadisonKastler_StateGraphTransport`, `KadisonKastler_TomitaClosedOperator`, `KadisonKastler_TomitaResolventDenseRange`, `KadisonKastler_TomitaResolventFaithful`, `KadisonKastler_TwoStateCocycleContinuity`, `KadisonKastler_TypeIIIDixmier`.
--
--   **Imports.** It imports the bundles `Q260K031`, `Q260K032`, `Q260K087` and `Q260K033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K037`, `Q260K038`, `Q260K039` and `Q260K072`; the statements `OAI.KadisonKastler.FullMatrixCorner.signedGroupUnion_generates`, `OAI.KadisonKastler.exists_algebraic_modular_test_values`, `OAI.KadisonKastler.exists_bounded_graphRow_signal_scale`, `OAI.KadisonKastler.exists_bounded_rescaledGraph_signal`, `OAI.KadisonKastler.exists_rescaledGraph_orbit_signal_and_cost`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_projection_cuts_with_gap`, `OAI.KadisonKastler.haagerupCommutatorWitnesses_of_modular_product`, `OAI.KadisonKastler.modular_localized_algebra_approximate` and `OAI.KadisonKastler.stateGraphUnitary_single_zero`; the proofs of `OAI.KadisonKastler.FullMatrixCorner.signedGroupUnion_generates`, `OAI.KadisonKastler.FullMatrixCorner.spatial_of_injective_matrix_subalgebra`, `OAI.KadisonKastler.ScalarBoundaryMean.exists_measurable_cocycle_near_representation`, `OAI.KadisonKastler.TypeIIIFactor.exists_centered_selfAdjoint_implementer`, `OAI_KadisonKastler_constructed_finiteFactor_spatial_of_matrixStages_and_boundary`, `OAI.KadisonKastler.exists_algebraic_modular_test_values`, `OAI.KadisonKastler.exists_bounded_graphRow_signal_scale`, `OAI.KadisonKastler.exists_bounded_rescaledGraph_signal`, `OAI.KadisonKastler.exists_localized_unitary_finiteStage_embedding`, `OAI.KadisonKastler.exists_localized_unitary_matrixUnits_embedding`, `OAI.KadisonKastler.exists_properInfinite_matrix_preparation_of_embedding`, `OAI.KadisonKastler.exists_rescaledGraph_orbit_signal_and_cost`, `OAI_KadisonKastler_exists_standard_finiteFactor_isomorphism`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_projection_cuts_with_gap`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_relative_bicentralizers`, `OAI.KadisonKastler.norm_graphProjectionDefect_le_of_row_approx_scale`, `OAI.KadisonKastler.stateGraphUnitary_single_zero`, `OAI.KadisonKastler.statePreservingUnitary_resolvent`, `OAI.KadisonKastler.statePreservingUnitary_resolvent_apply`, `OAI.KadisonKastler.uniformFactorStability_of_properlyInfinite` and `OAI.KadisonKastler.uniform_prepared_matrix_strong_stability`.
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
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
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
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K031
import Definitions.Def_Q260K032
import Definitions.Def_Q260K087
import Definitions.Def_Q260K033

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledGraphAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common unitary action on rescaled graphs

Left and right multiplication by common unitaries acts on graph vectors
through one unitary of the fixed two-coordinate Hilbert space. Thus each
closed graph reduces this unitary whenever the right action belongs to
the relevant commutant and has the prescribed value on the common vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The common graph action implementing `x ↦ r*x*s`. -/
def rescaledGraphAction (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (r s : unitary (H →L[ℂ] H)) :
    unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
  graphDiagonalUnitary (r * conjugationUnitary J hJ (star s))
    (conjugationUnitary J hJ ((star s) * conjugationUnitary J hJ r))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralVectorMatrixLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central vectors of an increasing matrix sequence

The decreasing central-vector projections have an actual strong limit.
When their common range is a separating line, the state and commutant
identities supply the exact expected-subfactor model.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrixCentralVectorSpace_isClosed
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) :
    IsClosed (matrixCentralVectorSpace A J : Set H) := by
  simp only [matrixCentralVectorSpace, Submodule.coe_iInf]
  exact isClosed_iInter (fun n => centralVectorSpace_isClosed _ J)

instance matrixCentralVectorSpace_complete
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) :
    CompleteSpace (matrixCentralVectorSpace A J) :=
  (matrixCentralVectorSpace_isClosed A J).completeSpace_coe

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulCyclicConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A faithful cyclic representation from a countable amplification

The weighted dense vector is separating for the diagonal action. Its
closed orbit gives a faithful cyclic restriction. Kaplansky density and
weak compactness of the original operator ball show that the restricted
image is already a von Neumann algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter TopologicalSpace
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [SeparableSpace H]

theorem norm_faithfulCyclicVector (M : VonNeumannAlgebra H) :
    ‖faithfulCyclicVector M‖ = 1 := norm_denseSeparatingUnitVector

instance faithfulCyclicSpace_nontrivial (M : VonNeumannAlgebra H) :
    Nontrivial (faithfulCyclicSpace M) :=
  nontrivial_of_ne (faithfulCyclicVector M) 0 (by
    intro h
    have hn := norm_faithfulCyclicVector M
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)

omit [Nontrivial H] in
theorem faithfulCyclicHom_cyclic (M : VonNeumannAlgebra H) :
    DenseRange (fun a : Algebra M => faithfulCyclicHom M a (faithfulCyclicVector M)) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, ⟨b, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp y.property ε hε
  obtain ⟨a, ha⟩ := b.property
  refine ⟨faithfulCyclicHom M a (faithfulCyclicVector M), ⟨a, rfl⟩, ?_⟩
  change dist y.val
    (↑(faithfulCyclicHom M a (faithfulCyclicVector M)) : CountableHilbertSum H) < ε
  rw [faithfulCyclicHom_apply]
  change dist y.val (b.val (denseSeparatingUnitVector (H := H))) < ε at hb
  change l2Diagonal a.val = b.val at ha
  rwa [ha]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphIdentificationIndependence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independence of the auxiliary graph identification

Changing the antiunitary used to identify the second graph coordinate
conjugates the graph projection by a diagonal unitary whose first entry
is the identity. Its first compression is therefore unchanged.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def graphIdentificationUnitary (J K : H ≃ₗᵢ⋆[ℂ] H) :
    unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
  graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K))

theorem graphIdentificationUnitary_vector (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (a : H →L[ℂ] H) :
    (graphIdentificationUnitary J K : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c a) = rescaledGraphVector K Ω c a := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K)) :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (rescaledGraphVector J Ω c a) 0 = _
    rw [graphDiagonalUnitary_apply_zero]
    rfl
  · change (graphDiagonalUnitary 1 (Unitary.linearIsometryEquiv.symm (J.symm.trans K)) :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (rescaledGraphVector J Ω c a) 1 = _
    rw [graphDiagonalUnitary_apply_one]
    change K (J.symm (c • J (star a Ω))) = c • K (star a Ω)
    simp only [← Complex.coe_smul]
    rw [J.symm.map_smulₛₗ, Complex.conj_ofReal, J.symm_apply_apply, K.map_smulₛₗ,
      Complex.conj_ofReal]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphIsometryTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.finiteDiagonalMap_apply _root_.OAI.KadisonKastler.finiteL2Basis_apply _root_.OAI.KadisonKastler.finiteLocalAmplificationValue_apply _root_.OAI.KadisonKastler.finiteLocalAmplification_apply _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.pointedPowerFibreEquiv_basis _root_.OAI.KadisonKastler.rescaledGraphSignalMap_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonKastler.twoStateCornerEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_fst_zero _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_one _root_.OAI.KadisonKastler.twoStateCornerEmbedding_snd_zero _root_.OAI.KadisonKastler.twoStateSourceEmbedding_adjoint _root_.OAI.KadisonKastler.twoStateTargetEmbedding_adjoint _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compression of closed Tomita graphs by a Hilbert isometry -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : H →ₗᵢ[ℂ] K) (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)

def graphIsometry : TomitaGraphHilbert H →ₗᵢ[ℂ] TomitaGraphHilbert K where
  toFun v := WithLp.toLp 2 ![V (v 0), L (V (J.symm (v 1)))]
  map_add' x y := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_add]
  map_smul' z v := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_smulₛₗ]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_two]
    change ‖V (v 0)‖ ^ 2 + ‖L (V (J.symm (v 1)))‖ ^ 2 = _
    rw [V.norm_map, L.norm_map, V.norm_map, J.symm.norm_map]

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem graphIsometry_zero (v : TomitaGraphHilbert H) :
    graphIsometry V J L v 0 = V (v 0) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem graphIsometry_one (v : TomitaGraphHilbert H) :
    graphIsometry V J L v 1 = L (V (J.symm (v 1))) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem graphIsometry_single_zero (x : H) :
    graphIsometry V J L (Generator.tupleSingle 0 x) = Generator.tupleSingle 0 (V x) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [Generator.tupleSingle_apply]

variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} (Ω : H) (ξ : K)
  (c : ℝ)

theorem graphIsometry_projection
    (hforward : ∀ a : Algebra M, graphIsometry V J L (rescaledGraphVector J Ω c a.val) ∈
      rescaledGraphSubspace N L ξ c)
    (hback : ∀ b : Algebra N,
      (graphIsometry V J L).toContinuousLinearMap.adjoint (rescaledGraphVector L ξ c b.val) ∈
        rescaledGraphSubspace M J Ω c)
    (v : TomitaGraphHilbert H) :
    rescaledGraphProjection N L ξ c (graphIsometry V J L v) =
      graphIsometry V J L (rescaledGraphProjection M J Ω c v) := by
  let W := graphIsometry V J L
  have hmap {x : TomitaGraphHilbert H} (hx : x ∈ rescaledGraphSubspace M J Ω c) :
      W x ∈ rescaledGraphSubspace N L ξ c := by
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω c)) ?_
      ((Submodule.isClosed_topologicalClosure _).preimage W.continuous) hx
    rintro _ ⟨a, rfl⟩
    exact hforward a
  have hadj {y : TomitaGraphHilbert K} (hy : y ∈ rescaledGraphSubspace N L ξ c) :
      W.toContinuousLinearMap.adjoint y ∈ rescaledGraphSubspace M J Ω c := by
    apply closure_minimal (s := Set.range (rescaledGraphMap N L ξ c)) ?_
      ((Submodule.isClosed_topologicalClosure _).preimage
        W.toContinuousLinearMap.adjoint.continuous) hy
    rintro _ ⟨b, rfl⟩
    exact hback b
  apply (rescaledGraphSubspace N L ξ c).eq_starProjection_of_mem_of_inner_eq_zero
  · exact hmap ((rescaledGraphSubspace M J Ω c).starProjection_apply_mem v)
  · intro w hw
    change inner ℂ (W v - W (rescaledGraphProjection M J Ω c v)) w = 0
    rw [← map_sub]
    change inner ℂ (W.toContinuousLinearMap _) w = 0
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact (rescaledGraphSubspace M J Ω c).starProjection_inner_eq_zero v _ (hadj hw)

theorem graphIsometry_resolvent
    (hforward : ∀ a : Algebra M, graphIsometry V J L (rescaledGraphVector J Ω c a.val) ∈
      rescaledGraphSubspace N L ξ c)
    (hback : ∀ b : Algebra N,
      (graphIsometry V J L).toContinuousLinearMap.adjoint (rescaledGraphVector L ξ c b.val) ∈
        rescaledGraphSubspace M J Ω c)
    (x : H) :
    graphResolvent N L ξ c (V x) = V (graphResolvent M J Ω c x) := by
  have h := congrArg (fun v : TomitaGraphHilbert K => v 0)
    (graphIsometry_projection V J L Ω ξ c hforward hback (Generator.tupleSingle 0 x))
  rw [graphIsometry_single_zero, graphIsometry_zero] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphCompressionVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebraic vectors under the graph isometry and its adjoint -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : H →ₗᵢ[ℂ] K) (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)
  (Ω : H) (ξ : K) (c : ℝ) (a : H →L[ℂ] H) (b : K →L[ℂ] K)

theorem graphIsometry_vector
    (h0 : V (a Ω) = b ξ) (h1 : V (star a Ω) = star b ξ) :
    graphIsometry V J L (rescaledGraphVector J Ω c a) = rescaledGraphVector L ξ c b := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · change L (V (J.symm (c • J (star a Ω)))) = c • L (star b ξ)
    simp only [← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal,
      J.symm_apply_apply, RingHom.id_apply, h1]

theorem graphIsometry_adjoint_vector
    (h0 : V.toContinuousLinearMap.adjoint (b ξ) = a Ω)
    (h1 : V.toContinuousLinearMap.adjoint (star b ξ) = star a Ω) :
    (graphIsometry V J L).toContinuousLinearMap.adjoint (rescaledGraphVector L ξ c b) =
      rescaledGraphVector J Ω c a := by
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  change inner ℂ (V (v 0)) (b ξ) +
      inner ℂ (L (V (J.symm (v 1)))) (c • L (star b ξ)) =
    inner ℂ (v 0) (a Ω) + inner ℂ (v 1) (c • J (star a Ω))
  simp only [← Complex.coe_smul, inner_smul_right]
  have hv (y : H) (z : K) : inner ℂ (V y) z =
      inner ℂ y (V.toContinuousLinearMap.adjoint z) :=
    (ContinuousLinearMap.adjoint_inner_right V.toContinuousLinearMap y z).symm
  rw [hv, h0, conjugateIsometry_inner, hv, h1]
  have hj := conjugateIsometry_inner J (J.symm (v 1)) (star a Ω)
  rw [J.apply_symm_apply] at hj
  rw [← hj]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaClosedOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The closed Tomita operator in linear coordinates

The fixed antiunitary in the second coordinate turns the Tomita operator
into a complex-linear, densely defined closed operator. Its graph is the
previously constructed closed graph, not an assumed modular object.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Changing only the finite product norm does not change the graph topology. -/
def tomitaProductCoordinates : TomitaGraphHilbert H ≃L[ℂ] H × H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => H)).trans
    (ContinuousLinearEquiv.finTwoArrow ℂ H)

/-- The closed graph in the ordinary product used by `LinearPMap`. -/
def tomitaProductGraph (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : Submodule ℂ (H × H) :=
  (rescaledGraphSubspace M J Ω c).comap tomitaProductCoordinates.symm.toLinearMap

/-- The actual closed operator, expressed using a fixed conjugate copy of H. -/
def tomitaClosedLinearOperator (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →ₗ.[ℂ] H :=
  (tomitaProductGraph M J Ω c).toLinearPMap

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaResolventFaithful
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithfulness of the bounded Tomita graph resolvent

Both endpoints of the positive contraction have zero eigenspace. This is the
bounded starting point for recovering the modular operator by spectral calculus.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem graphResolvent_norm_le_one (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    ‖graphResolvent M J Ω c‖ ≤ 1 :=
  (norm_graph_operatorEntry_le _ 0 0).trans
    (rescaledGraphSubspace M J Ω c).starProjection_norm_le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularizedModularGroup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded logarithmic approximations to the modular group

The logarithmic generator of the graph resolvent is regularized at both
endpoints. Each approximation is an actual norm-continuous unitary group.
The strong limit and its modular properties are subsequent constructions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded approximation to `log ((1-R)/R)`. -/
def regularizedModularLog (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (ε : ℝ) : selfAdjoint (H →L[ℂ] H) :=
  ⟨CFC.log (1 - graphResolvent M J Ω 1 + algebraMap ℝ (H →L[ℂ] H) ε) -
      CFC.log (graphResolvent M J Ω 1 + algebraMap ℝ (H →L[ℂ] H) ε),
    IsSelfAdjoint.log.sub IsSelfAdjoint.log⟩

/-- The regularized unitary groups used to approach the modular group. -/
def regularizedModularGroup (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (ε : ℝ) : Multiplicative ℝ →* unitary (H →L[ℂ] H) :=
  boundedSelfAdjointGroup (regularizedModularLog M J Ω ε)

theorem regularizedModularGroup_stronglyContinuous (M : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (ε : ℝ) (x : H) :
    Continuous (fun t : ℝ =>
      (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) x) :=
  boundedSelfAdjointGroup_stronglyContinuous _ x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaResolventDenseRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- This product kills both singular endpoints and still has dense range. -/
def graphResolventCutoff (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) : H →L[ℂ] H :=
  graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleResolvent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.graphIsometry_one _root_.OAI.KadisonKastler.graphIsometry_zero _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Resolvents under a change of graph scale

Scaling the second graph coordinate gives an exact algebraic relation
between every graph resolvent and the resolvent at scale one. This
relation is obtained from orthogonal projection, before using spectral
calculus or an unbounded modular operator.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def graphCoordinateScale (c : ℝ) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
  tomitaProductCoordinates.symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.id ℂ H).prodMap ((c : ℂ) • ContinuousLinearMap.id ℂ H)) ∘L
      tomitaProductCoordinates.toContinuousLinearMap

omit [CompleteSpace H] in
@[simp] theorem graphCoordinateScale_zero (c : ℝ) (v : TomitaGraphHilbert H) :
    graphCoordinateScale c v 0 = v 0 := rfl

omit [CompleteSpace H] in
@[simp] theorem graphCoordinateScale_one (c : ℝ) (v : TomitaGraphHilbert H) :
    graphCoordinateScale c v 1 = (c : ℂ) • v 1 := rfl

theorem graphCoordinateScale_vector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c d : ℝ)
    (a : H →L[ℂ] H) :
    graphCoordinateScale c (rescaledGraphVector J Ω d a) =
      rescaledGraphVector J Ω (c * d) a := by
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · change (c : ℂ) • (d • J (star a Ω)) = (c * d) • J (star a Ω)
    rw [Complex.coe_smul, smul_smul]

omit [CompleteSpace H] in
theorem scaled_residual_inner (c : ℝ) (x : H) (v w : TomitaGraphHilbert H) :
    inner ℂ (Generator.tupleSingle 0 (v 0 + (c : ℂ) ^ 2 • (x - v 0)) -
      graphCoordinateScale c v) (graphCoordinateScale c w) =
      (c : ℂ) ^ 2 * inner ℂ (Generator.tupleSingle 0 x - v) w := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two]
  change inner ℂ ((v 0 + (c : ℂ) ^ 2 • (x - v 0)) - v 0) (w 0) +
    inner ℂ (0 - (c : ℂ) • v 1) ((c : ℂ) • w 1) =
    (c : ℂ) ^ 2 * (inner ℂ (x - v 0) (w 0) + inner ℂ (0 - v 1) (w 1))
  rw [add_sub_cancel_left]
  simp only [inner_smul_left, inner_smul_right, zero_sub, inner_neg_left,
    map_pow, Complex.conj_ofReal]
  ring

/-- The positive denominator relating the rescaled graph resolvents. -/
def graphScaleDenominator (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →L[ℂ] H :=
  graphResolvent M J Ω 1 + (c : ℂ) ^ 2 • (1 - graphResolvent M J Ω 1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleFunctionalCalculus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def graphScaleInverse (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : H →L[ℂ] H :=
  cfc (fun s => (graphScaleScalar c s)⁻¹) (graphResolvent M J Ω 1)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStrongLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def modularApproximation (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (n : ℕ) (t : ℝ) : H →L[ℂ] H :=
  regularizedModularGroup M J Ω (modularRegularizationScale n) (Multiplicative.ofAdd t)

theorem modularApproximation_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (n : ℕ) (t : ℝ) :
    ‖modularApproximation M J Ω n t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [modularApproximation, Unitary.norm_map, one_mul, le_refl]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSpectralCuts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

def modularUpperCut (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (a : ℝ) : H →L[ℂ] H :=
  resolventLowerCut (graphResolvent M J Ω 1) (modularCutThreshold a)

theorem modularUpperCut_projection (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    IsStarProjection (modularUpperCut M J Ω a) := resolventLowerCut_projection _ _

theorem modularUpperCut_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ‖modularUpperCut M J Ω a‖ ≤ 1 := (modularUpperCut_projection J Ω a).norm_le _

theorem modularUpperCut_complement_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ‖1 - modularUpperCut M J Ω a‖ ≤ 1 := (modularUpperCut_projection J Ω a).one_sub.norm_le _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphHighCutInverse
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded inverse on the high logarithmic cut

The inverse is clipped outside the cut before applying continuous
functional calculus, so it remains a bounded ambient operator.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

def graphHighCutInverse (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c r : ℝ) : H →L[ℂ] H :=
  cfc (graphHighInverseScalar c r) (graphResolvent M J Ω 1) *
    resolventLowerCut (graphResolvent M J Ω 1) r

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Passing central-vector refinement estimates to finite families

Further matrix refinement preserves every previous distance-to-line
estimate. Repeated one-vector refinement therefore handles any finite
family with a prescribed total displacement budget.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def matrixStageCentralProjection (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) : H →L[ℂ] H :=
  (centralVectorSpace (matrixUnitConcreteAlgebra E.units) J).starProjection

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralResidual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The part of a matrix-central vector orthogonal to the reference line -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def matrixCentralResidual (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) : H :=
  matrixStageCentralProjection E J η -
    (Submodule.span ℂ {matrixStageCentralProjection E J ξ}).starProjection
      (matrixStageCentralProjection E J η)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixChainEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Regard an ambient unitary subgroup contained in an algebra as internal unitaries. -/
def subgroupAlgebraRepresentation (G : Subgroup (unitary (H →L[ℂ] H)))
    (M : VonNeumannAlgebra H) (hG : ∀ u : G, (u : H →L[ℂ] H) ∈ M) :
    G →* unitary (Algebra M) where
  toFun u := algebraUnitaryOfMem u.val (hG u)
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ResolventCutMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem modularUpperCut_measurable {M : VonNeumannAlgebra H}
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) (x : H) :
    AEStronglyMeasurable (fun ξ : ℝ => modularUpperCut M J Ω (a - 2 * Real.pi * ξ) x)
      volume := by
  apply resolventLowerCut_comp_aestronglyMeasurable
  exact (show Continuous (fun ξ : ℝ => modularCutThreshold (a - 2 * Real.pi * ξ)) by
    unfold modularCutThreshold
    apply Continuous.inv₀ (by fun_prop)
    intro ξ
    positivity).measurable

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularGaugeTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting the cyclic Fourier gauge identity to the original space -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

def modularUpperCutField (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularFieldOperator volume (fun ξ => modularUpperCut M J Ω (a - 2 * Real.pi * ξ))
    (modularUpperCut_measurable J Ω a) 1
    (Filter.Eventually.of_forall fun _ => modularUpperCut_contracts J Ω _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPairingComplexification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complexifying the modular Radon--Nikodym equation

The real equation on self-adjoint tests determines a complex-linear
identity on all algebra elements. This is the identity used to identify
the bounded Tomita resolvent.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem rightVectorPairing_star (Ω ξ : H) (a : Algebra M) :
    rightVectorPairing M Ω ξ (star a) = star (leftVectorPairing M Ω ξ a) := by
  change inner ℂ Ω (star a.val ξ) = star (inner ℂ ξ (a.val Ω))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    Complex.star_def, inner_conj_symm]

theorem leftVectorPairing_star (Ω ξ : H) (a : Algebra M) :
    leftVectorPairing M Ω ξ (star a) = star (rightVectorPairing M Ω ξ a) := by
  have h := congrArg star (rightVectorPairing_star Ω ξ (star a))
  simpa only [star_star] using h.symm

theorem leftVectorPairing_commutant (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b) :
    leftVectorPairing M Ω (b Ω) = rightVectorPairing M Ω (b Ω) := by
  ext a
  have hc : a.val * b = b * a.val := hb _ (Set.mem_union_left _ a.property)
  change inner ℂ (b Ω) (a.val Ω) = inner ℂ Ω (a.val (b Ω))
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hs : b.adjoint = b := hbs.star_eq
  rw [hs]
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ Ω (T Ω)) hc.symm

/-- The real pairing equation determines the full complex identity. -/
theorem modular_pairing_complex (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b)
    (z : ℂ) (x : Algebra M)
    (hpair : ∀ a : selfAdjoint (Algebra M),
      (inner ℂ (a.val.val Ω) (b Ω)).re =
        (z * inner ℂ (a.val.val Ω) (x.val Ω)).re) :
    ∀ a : Algebra M,
      2 * inner ℂ Ω (a.val (b Ω)) =
        z * inner ℂ Ω (a.val (x.val Ω)) +
          star z * inner ℂ (x.val Ω) (a.val Ω) := by
  let F := (2 : ℂ) • rightVectorPairing M Ω (b Ω)
  let G := z • rightVectorPairing M Ω (x.val Ω) +
    star z • leftVectorPairing M Ω (x.val Ω)
  have hF : ∀ a, F (star a) = star (F a) := by
    intro a
    dsimp only [F, LinearMap.smul_apply, smul_eq_mul]
    rw [rightVectorPairing_star, ← leftVectorPairing_commutant Ω b hb hbs]
    simp only [star_mul, star_ofNat]
    ring
  have hG : ∀ a, G (star a) = star (G a) := by
    intro a
    dsimp only [G, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [rightVectorPairing_star, leftVectorPairing_star]
    simp only [star_add, star_mul, star_star]
    ring
  have hFG : F = G := hermitianLinear_eq_of_selfAdjoint_real F G hF hG (by
    intro a
    have hb' := rightVectorPairing_selfAdjoint Ω (b Ω) a
    have hx' := rightVectorPairing_selfAdjoint Ω (x.val Ω) a
    have hl : leftVectorPairing M Ω (x.val Ω) a.val =
        star (rightVectorPairing M Ω (x.val Ω) a.val) := by
      have h := leftVectorPairing_star Ω (x.val Ω) a.val
      rwa [a.property.star_eq] at h
    change (2 * rightVectorPairing M Ω (b Ω) a.val).re =
      (z * rightVectorPairing M Ω (x.val Ω) a.val +
        star z * leftVectorPairing M Ω (x.val Ω) a.val).re
    rw [hl, hb', hx']
    have h := hpair a
    rw [Complex.mul_re] at h
    simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    norm_num
    linarith)
  intro a
  exact congrArg (fun L : Algebra M →ₗ[ℂ] ℂ => L a) hFG

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPairingProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular pairing identity on two algebra vectors -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modular_pairing_products (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b)
    (z : ℂ) (x : Algebra M)
    (hpair : ∀ a : selfAdjoint (Algebra M),
      (inner ℂ (a.val.val Ω) (b Ω)).re =
        (z * inner ℂ (a.val.val Ω) (x.val Ω)).re)
    (y w : Algebra M) :
    2 * inner ℂ (y.val Ω) (b (w.val Ω)) =
      z * inner ℂ (y.val Ω) (w.val (x.val Ω)) +
        star z * inner ℂ (y.val (x.val Ω)) (w.val Ω) := by
  have h := modular_pairing_complex Ω b hb hbs z x hpair (star y * w)
  have hw : w.val * b = b * w.val := hb _ (Set.mem_union_left _ w.property)
  have hwv : w.val (b Ω) = b (w.val Ω) := congrArg (fun T : H →L[ℂ] H => T Ω) hw
  change 2 * inner ℂ Ω ((star y.val * w.val) (b Ω)) =
    z * inner ℂ Ω ((star y.val * w.val) (x.val Ω)) +
      star z * inner ℂ (x.val Ω) ((star y.val * w.val) Ω) at h
  simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, hwv] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCentralSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vectors continuous for projection centrality -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def projectionCentralSpace (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) : Submodule ℂ H where
  carrier := ProjectionCentralVector (M := M) J ξ
  zero_mem' := by
    intro ε hε
    exact ⟨1,by norm_num,fun p _ => by simpa only [map_zero,norm_zero] using hε⟩
  add_mem' := by
    intro x y hx hy ε hε
    obtain ⟨δ,hδ,hd⟩ := hx (ε/2) (half_pos hε)
    obtain ⟨γ,hγ,hg⟩ := hy (ε/2) (half_pos hε)
    refine ⟨min δ γ,lt_min hδ hγ,?_⟩
    intro p hp
    rw [map_add]
    have h1 := hd p (hp.trans_le (min_le_left _ _))
    have h2 := hg p (hp.trans_le (min_le_right _ _))
    exact (norm_add_le _ _).trans_lt (by linarith only [h1,h2])
  smul_mem' := by
    intro c x hx ε hε
    have hden : 0 < ‖c‖+1 := by positivity
    obtain ⟨δ,hδ,hd⟩ := hx (ε/(‖c‖+1)) (div_pos hε hden)
    refine ⟨δ,hδ,?_⟩
    intro p hp
    rw [map_smul,norm_smul]
    have hh := (lt_div_iff₀ hden).mp (hd p hp)
    nlinarith [norm_nonneg (projectionVectorDefect J p x)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable (M : VonNeumannAlgebra H)

namespace ScalarBoundaryMean

variable {M} {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
  (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))

theorem norm_restrictedOperatorMean_le (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    ‖m.restrictedOperatorMean hTom M F‖ ≤ ‖F‖ :=
  m.norm_restrictedOperatorMeanValue_le hTom M F

theorem restrictedOperatorMean_one (M : VonNeumannAlgebra H) :
    m.restrictedOperatorMean hTom M 1 = 1 := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M 1) = 1
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M 1 = 1 := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    (m.operatorMean_fixed (H := H) 1)

theorem restrictedOperatorMean_star (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (star F) = star (m.restrictedOperatorMean hTom M F) := by
  apply Subtype.ext
  change m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (star F)) =
    star (m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F))
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (star F) =
      star (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    (m.operatorMean_star (H := H) _)

theorem restrictedOperatorMean_left (M : VonNeumannAlgebra H)
    (q : operatorFieldAlgebra (μ := μ) M) (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (boundaryConstant q * F) =
      q * m.restrictedOperatorMean hTom M F := by
  apply Subtype.ext
  change m.operatorMean (H := H)
      (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryConstant q * F)) =
    (q : WeakOperatorField (H := H) μ) *
      m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F)
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (boundaryConstant q * F) =
      boundaryConstant (G := G) (q : WeakOperatorField (H := H) μ) *
        operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    ((hTom (m.operatorMean (H := H)) (m.norm_operatorMeanValue_le (H := H))
      (m.operatorMean_fixed (H := H))).1 _ _)

theorem restrictedOperatorMean_right (M : VonNeumannAlgebra H)
    (F : G →ᵇ operatorFieldAlgebra (μ := μ) M) (q : operatorFieldAlgebra (μ := μ) M) :
    m.restrictedOperatorMean hTom M (F * boundaryConstant q) =
      m.restrictedOperatorMean hTom M F * q := by
  apply Subtype.ext
  change m.operatorMean (H := H)
      (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (F * boundaryConstant q)) =
    m.operatorMean (H := H) (operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F) *
      (q : WeakOperatorField (H := H) μ)
  have hi : operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M (F * boundaryConstant q) =
      operatorFieldFamilyInclusion (G := G) (D := D) (H := H) (μ := μ) M F *
        boundaryConstant (G := G) (q : WeakOperatorField (H := H) μ) := by ext g; rfl
  exact (congrArg (m.operatorMean (H := H)) hi).trans
    ((hTom (m.operatorMean (H := H)) (m.norm_operatorMeanValue_le (H := H))
      (m.operatorMean_fixed (H := H))).2 _ _)

/-- The restricted mean retains the two module identities. -/
def restrictedOperatorBimoduleMean (M : VonNeumannAlgebra H) :
    BimoduleMean (boundaryConstant (G := G) (B := operatorFieldAlgebra (μ := μ) M)) where
  toCLM := m.restrictedOperatorMean hTom M
  map_one := m.restrictedOperatorMean_one hTom M
  map_star := m.restrictedOperatorMean_star hTom M
  norm_le := m.norm_restrictedOperatorMean_le hTom M
  map_left := m.restrictedOperatorMean_left hTom M
  map_right := m.restrictedOperatorMean_right hTom M

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateGraphTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transporting the closed Tomita graph under a state isomorphism -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
  (hM : DenseRange (algebraVectorMap M Ω))
  (hN : DenseRange (algebraVectorMap N ξ))
  (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)

def stateGraphUnitary : TomitaGraphHilbert H ≃ₗᵢ[ℂ] TomitaGraphHilbert K :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 2 =>
    if i = 0 then statePreservingUnitary θ Ω ξ hM hN hstate
    else (J.symm.trans (statePreservingUnitary θ Ω ξ hM hN hstate)).trans L)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateCocycleContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong-star continuity of the two-state corner cocycle -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (M : VonNeumannAlgebra H)
  (Ω ξ : H)

def twoStateFirstColumnVector (j : Fin 2) (x : H) : TwoStateMatrixHilbert H H :=
  WithLp.toLp 2 (tupleSingle j x, 0)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIDixmier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed scalar averaging in type III factors -/

namespace KadisonKastler

open Generator
open scoped ComplexStarModule

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H}

/-- The finite signed matrix group, considered as inner automorphisms of M. -/
def matrixInnerAverage {n : ℕ} (E : MatrixUnitSystem (Fin n) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra) : FiniteInnerAverage M where
  Index := SignedPermutation (Fin n)
  fintype := inferInstance
  nonempty := inferInstance
  unitary g := algebraUnitaryOfMem (matrixUnitSignedRepresentation E g)
    (hE (matrixUnitSignedRepresentation_mem E g))

end

end KadisonKastler

end OAI
end


