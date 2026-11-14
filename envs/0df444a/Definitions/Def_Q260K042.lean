-- Prove2me | Definitions.Def_Q260K042
-- name    : Q260K042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T08:57:06.517522+00:00
-- url     : https://prove2.me/theorems/8f4050b8-28c2-4269-8ff1-b76d5028656a
-- title:
--   Definitions bundle Q260K042 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 4 definitions and 52 theorems. The definitions and types are `OAI.KadisonKastler.constructedCoreDualEquiv`, `OAI.KadisonKastler.constructedModularConjugationData`, `OAI.KadisonKastler.modularCyclicGroup`, `OAI.KadisonKastler.modularCyclicUnitary`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_ConstructedModularData`, `KadisonKastler_CoreWindowDualComparison`, `KadisonKastler_CyclicCutField`, `KadisonKastler_CyclicCutSwap`, `KadisonKastler_ModularBoundedEquation`, `KadisonKastler_ModularCyclicGroup`, `KadisonKastler_ModularCyclicPhase`, `KadisonKastler_ModularFixedVectors`, `KadisonKastler_ModularNormalization`, `KadisonKastler_ModularOrbitAverage`, `KadisonKastler_ModularOrbitCommutant`, `KadisonKastler_ModularPairingOperator`, `KadisonKastler_PolarCommutantEquality`, `KadisonKastler_TomitaAdjointCoordinates`, `KadisonKastler_TomitaAdjointCore`, `KadisonKastler_TomitaCentralizerConjugation`, `KadisonKastler_TomitaClosedOperator`, `KadisonKastler_TomitaCommutantCoordinates`, `KadisonKastler_TomitaComplementaryRoot`, `KadisonKastler_TomitaLinearPolarCoordinates`, `KadisonKastler_TomitaMiddleCore`, `KadisonKastler_TomitaMiddlePairing`, `KadisonKastler_TomitaMiddleRange`, `KadisonKastler_TomitaPolarCorePairing`, `KadisonKastler_TomitaRootDomain`, `KadisonKastler_WeightedStripCenter`, `KadisonKastler_WeightedStripCyclic`, `KadisonKastler_WeightedStripDense`, `KadisonKastler_WeightedStripFactorization`, `KadisonKastler_WeightedStripOperatorBoundary`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K037` and `Q260K038` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K045`; the statements `OAI.KadisonKastler.constructedCore_subhalf_not_equivalent_dual`, `OAI_KadisonKastler_exists_normalizer_of_weak_comparison`, `OAI.KadisonKastler.haagerup_witnesses_of_polar_coisometries` and `OAI.KadisonKastler.positive_reference_haagerup_witnesses`; the proofs of `OAI.KadisonKastler.PointedMatrixSites.represented_expected_matrix_subfactor`, `OAI.KadisonKastler.PointedMatrixSites.spatial_state_bicentralizer_scalar`, `OAI.KadisonKastler.PointedMatrixSites.spatial_universal_modular_coisometries`, `OAI.KadisonKastler.TypeIIIFactor.commutant_properlyInfinite`, `OAI.KadisonKastler.TypeIIIFactor.exists_positive_unit_state_representative`, `OAI.KadisonKastler.constructedCore_not_finite`, `OAI.KadisonKastler.constructedCore_not_typeI`, `OAI_KadisonKastler_exists_normalizer_of_weak_comparison`, `OAI_KadisonKastler_maximal_admissibleFamily_gap`, `OAI.KadisonKastler.modular_localized_algebra_approximate`, `OAI.KadisonKastler.positive_reference_haagerup_witnesses`, `OAI.KadisonKastler.positive_reference_noncollinear_projection_witness`, `OAI.KadisonKastler.stateHomogeneity_of_modular_coisometries`, `OAI.KadisonKastler.tomitaPolarConjugation_eq_of_quadratic_positive`, `OAI.KadisonKastler.tomitaPolarConjugation_quadratic_nonneg` and `OAI.KadisonKastler.twoStateCorner_positive_iff`.
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
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
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
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K037
import Definitions.Def_Q260K038

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaClosedOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem tomitaClosedLinearOperator_graph (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    (tomitaClosedLinearOperator M J Ω c).graph = tomitaProductGraph M J Ω c :=
  (tomitaProductGraph M J Ω c).toLinearPMap_graph_eq
    (tomitaProductGraph_no_vertical J Ω c hsep)

theorem tomitaClosedLinearOperator_algebraic_graph (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (c : ℝ) (hsep : Function.Injective (algebraVectorMap M Ω)) (a : Algebra M) :
    (a.val Ω, c • J (star a.val Ω)) ∈ (tomitaClosedLinearOperator M J Ω c).graph := by
  rw [tomitaClosedLinearOperator_graph J Ω c hsep]
  exact rescaledGraphVector_mem M J Ω c a

theorem tomitaClosedLinearOperator_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    Dense ((tomitaClosedLinearOperator M J Ω c).domain : Set H) := by
  apply hcyc.mono
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, hx, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (tomitaClosedLinearOperator_algebraic_graph J Ω c hsep a)
  change a.val Ω ∈ (tomitaClosedLinearOperator M J Ω c).domain
  change x.val = a.val Ω at hx
  rw [← hx]
  exact x.property

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaCentralizerConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.graphCoordinateScale_one _root_.OAI.KadisonKastler.graphCoordinateScale_zero _root_.OAI.KadisonKastler.graphIsometry_one _root_.OAI.KadisonKastler.graphIsometry_zero _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The exact centralizer-vector identity for the constructed conjugation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- On centralizer vectors the polar conjugation is precisely adjoint. -/
theorem tomitaPolarConjugation_centralizer (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    tomitaPolarConjugation J Ω hsep hcyc (r.val Ω) = star r.val Ω := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  let k : ℂ := Real.sqrt (1 / 2)
  have hk : k ≠ 0 := by
    change (Real.sqrt (1 / 2) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1 / 2)))
  have hks : (starRingEnd ℂ) k = k := Complex.conj_ofReal _
  have hh : (starRingEnd ℂ) (1 / 2) = (1 / 2 : ℂ) := by
    change star (1 / 2 : ℂ) = _
    simp
  apply U.injective
  rw [tomitaPolarCoordinates_conjugation]
  apply Subtype.ext
  apply smul_right_injective (M := TomitaGraphHilbert H) hk
  change k • tomitaGraphFlip J (U (r.val Ω)).val = k • (U (star r.val Ω)).val
  calc
    k • tomitaGraphFlip J (U (r.val Ω)).val =
        tomitaGraphFlip J (k • (U (r.val Ω)).val) := by
      rw [(tomitaGraphFlip J).map_smulₛₗ, hks]
    _ = tomitaGraphFlip J ((1 / 2 : ℂ) • rescaledGraphVector J Ω 1 r.val) := by
      rw [tomitaPolarCoordinates_centralizer J Ω hsep hcyc r hr]
    _ = (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 (star r.val) := by
      rw [(tomitaGraphFlip J).map_smulₛₗ, hh, tomitaGraphFlip_vector J Ω r]
    _ = k • (U (star r.val Ω)).val := by
      exact (tomitaPolarCoordinates_centralizer J Ω hsep hcyc (star r)
        (vectorState_centralizer_star Ω r hr)).symm

/-- Modular conjugation agrees with the adjoint on centralizer vectors. -/
theorem tomitaPolarConjugation_star_centralizer (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    tomitaPolarConjugation J Ω hsep hcyc (star r.val Ω) = r.val Ω := by
  have h := tomitaPolarConjugation_centralizer J Ω hsep hcyc (star r)
    (vectorState_centralizer_star Ω r hr)
  change tomitaPolarConjugation J Ω hsep hcyc (star r.val Ω) = star (star r.val) Ω at h
  simpa only [star_star] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularFixedVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed vectors of the constructed modular group

The half-eigenspace of the bounded graph resolvent is fixed by every
regularized group and by its strong limit. It contains the state vector
and the vectors obtained from elements of the vector-state centralizer.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem regularizedModularGroup_fixes_half_eigen (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : H)
    (hx : graphResolvent M J Ω 1 x = (1 / 2 : ℂ) • x) :
    (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) x = x := by
  rw [regularizedModularGroup_eq_cfc J Ω t hε,
    cfc_half_eigen _ (graphResolvent_positive J Ω 1).isSelfAdjoint x hx _
      (modularPhaseScalar_continuousOn J Ω t hε)]
  have hh : modularPhaseScalar t ε (1 / 2) = 1 := by
    have he : regularizedLogScalar ε (1 / 2) = 0 := by
      unfold regularizedLogScalar
      rw [show 1 - (1 / 2 : ℝ) + ε = 1 / 2 + ε by ring, sub_self]
    have hre : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
    unfold modularPhaseScalar
    rw [hre, he]
    simp
  rw [hh, one_smul]

variable [SeparableSpace H]

theorem modularStrongGroup_fixes_half_eigen (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (x : H)
    (hx : graphResolvent M J Ω 1 x = (1 / 2 : ℂ) • x) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x = x := by
  have ht := modularApproximation_tendsto J Ω hsep hcyc t x
  have he (n : ℕ) : modularApproximation M J Ω n t x = x :=
    regularizedModularGroup_fixes_half_eigen J Ω (modularRegularizationScale_pos n) t x hx
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem modularStrongGroup_fixes_centralizer_vector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) (r.val Ω) = r.val Ω :=
  modularStrongGroup_fixes_half_eigen J Ω hsep hcyc t _ (graphResolvent_centralizer J Ω r hr)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCyclicPhase
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular group in the cyclic spectral model

The two injective graph coordinates exclude the endpoints. Dominated
convergence then identifies the strong-limit group with the logarithmic
phase multiplier on every scalar cyclic spectral space.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable [TopologicalSpace.SeparableSpace H]

theorem modularStrongLimit_cyclic (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) (t : ℝ)
    (v : ResolventCyclicL2 (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x) :
    resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x
      (resolventScalarMultiplier _ (graphResolvent_positive J Ω 1).isSelfAdjoint x
        (fun s => modularSpectralPhase t s.val)
        ((modularSpectralPhase_measurable t).comp measurable_subtype_coe)
        1 (fun s => (modularSpectralPhase_norm t s.val).le) v) =
      modularStrongLimit J Ω hsep hcyc t
        (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x v) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let g : ℕ → C(spectrum ℝ R, ℂ) := fun n =>
    ⟨fun s => modularPhaseScalar t (modularRegularizationScale n) (s.val : ℂ),
      ((modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n)).comp
        Complex.continuous_ofReal.continuousOn (fun _ hs => spectrum.algebraMap_mem ℂ hs)).domRestrict⟩
  have hb (n : ℕ) (s : spectrum ℝ R) : ‖g n s‖ ≤ 1 :=
    (modularPhaseScalar_norm _ _ _).le
  have hpt : ∀ᵐ s ∂resolventVectorMeasure R hR x,
      Tendsto (fun n => g n s) atTop (𝓝 (modularSpectralPhase t s.val)) := by
    filter_upwards [graphResolventVectorMeasure_interior J Ω hsep hcyc x] with s hs
    exact modularPhaseScalar_tendsto t hs.1 hs.2
  have ht := resolventScalarMultiplier_tendsto R hR x (fun n => g n)
    (fun s => modularSpectralPhase t s.val) (fun n => (g n).continuous.measurable)
    ((modularSpectralPhase_measurable t).comp measurable_subtype_coe) hb
    (fun s => (modularSpectralPhase_norm t s.val).le) hpt v
  have he (n : ℕ) : resolventContinuousCalculus R hR (g n) =
      modularApproximation M J Ω n t := by
    rw [modularApproximation, regularizedModularGroup_eq_cfc J Ω t
      (modularRegularizationScale_pos n)]
    have hc : ContinuousOn (fun s : ℝ =>
        modularPhaseScalar t (modularRegularizationScale n) (s : ℂ)) (spectrum ℝ R) :=
      (modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n)).comp
        Complex.continuous_ofReal.continuousOn (fun _ hs => spectrum.algebraMap_mem ℂ hs)
    have hh := resolventContinuousCalculus_eq_cfc R hR _ hc
    calc
      _ = cfc (fun z : ℂ => modularPhaseScalar t (modularRegularizationScale n)
        (z.re : ℂ)) R := hh
      _ = _ := by
        apply cfc_congr
        intro z _
        simp only [modularPhaseScalar, Complex.ofReal_re]
  have hlim := (resolventCyclicIsometry R hR x).continuous.continuousAt.tendsto.comp ht
  apply tendsto_nhds_unique hlim
  apply (modularApproximation_tendsto J Ω hsep hcyc t
    (resolventCyclicIsometry R hR x v)).congr
  intro n
  dsimp only [Function.comp_def]
  rw [resolventCyclicIsometry_multiplier_of_bound, he]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCyclicGroup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar cyclic modular group

The phase multipliers form a strongly continuous unitary group. The
cyclic isometry intertwines this group with the constructed original
group, so its laws require no additional modular-theory input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable [TopologicalSpace.SeparableSpace H]
variable (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

include hsep hcyc

theorem modularCyclicPhaseOperator_intertwines (t : ℝ) (v : ModularCyclicSpace M J Ω x) :
    resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x
      (modularCyclicPhaseOperator M J Ω x t v) =
    modularStrongLimit J Ω hsep hcyc t
      (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x v) :=
  modularStrongLimit_cyclic J Ω hsep hcyc x t v

theorem modularCyclicPhaseOperator_norm (t : ℝ) (v : ModularCyclicSpace M J Ω x) :
    ‖modularCyclicPhaseOperator M J Ω x t v‖ = ‖v‖ := by
  rw [← (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).norm_map,
    modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularStrongLimit_norm_map, LinearIsometry.norm_map]

theorem modularCyclicPhaseOperator_zero : modularCyclicPhaseOperator M J Ω x 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).injective
  rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularStrongLimit_zero, one_apply_eq_self, one_apply_eq_self]

theorem modularCyclicPhaseOperator_add (s t : ℝ) :
    modularCyclicPhaseOperator M J Ω x (s + t) =
      modularCyclicPhaseOperator M J Ω x s * modularCyclicPhaseOperator M J Ω x t := by
  apply ContinuousLinearMap.ext
  intro v
  apply (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).injective
  rw [mul_apply_eq_comp, modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x,
    modularStrongLimit_add, mul_apply_eq_comp]

def modularCyclicUnitary (t : ℝ) : unitary
    (ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) :=
  Unitary.linearIsometryEquiv.symm
    { (modularCyclicPhaseOperator M J Ω x t).toLinearMap with
      invFun := modularCyclicPhaseOperator M J Ω x (-t)
      left_inv := fun v => by
        change (modularCyclicPhaseOperator M J Ω x (-t) * modularCyclicPhaseOperator M J Ω x t) v = v
        rw [← modularCyclicPhaseOperator_add J Ω hsep hcyc x, neg_add_cancel,
          modularCyclicPhaseOperator_zero J Ω hsep hcyc x, one_apply_eq_self]
      right_inv := fun v => by
        change (modularCyclicPhaseOperator M J Ω x t * modularCyclicPhaseOperator M J Ω x (-t)) v = v
        rw [← modularCyclicPhaseOperator_add J Ω hsep hcyc x, add_neg_cancel,
          modularCyclicPhaseOperator_zero J Ω hsep hcyc x, one_apply_eq_self]
      norm_map' := modularCyclicPhaseOperator_norm J Ω hsep hcyc x t }

def modularCyclicGroup : Multiplicative ℝ →* unitary
    (ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) where
  toFun t := modularCyclicUnitary J Ω hsep hcyc x t.toAdd
  map_one' := by
    apply Subtype.ext
    exact modularCyclicPhaseOperator_zero J Ω hsep hcyc x
  map_mul' s t := by
    apply Subtype.ext
    exact modularCyclicPhaseOperator_add J Ω hsep hcyc x s.toAdd t.toAdd

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicCutField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The explicit scalar kernel of the modular cut field -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem cyclicCutField_tensor_rows (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : ModularCyclicSpace M J Ω x) :
    ∀ᵐ ξ ∂(volume : Measure ℝ), ∀ᵐ s ∂resolventVectorMeasure (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x,
      (modularCyclicCutField M J Ω x a (scalarLpTensor volume f v)) ξ s =
      (if a < resolventLogFrequency s.val + 2 * Real.pi * ξ then (1 : ℂ) else 0) * f ξ * v s := by
  filter_upwards [modularCyclicCutField_apply_ae J Ω x a (scalarLpTensor volume f v),
    scalarLpTensor_apply_ae volume f v] with ξ hF hf
  have he := hF.trans (congrArg (modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ)) hf)
  filter_upwards [modularCyclicCut_apply_ae J Ω x (a - 2 * Real.pi * ξ) (f ξ • v),
    Lp.coeFn_smul (f ξ) v, graphResolventVectorMeasure_interior J Ω hsep hcyc x] with s hs hv hint
  have hcond : s.val < modularCutThreshold (a - 2 * Real.pi * ξ) ↔
      a < resolventLogFrequency s.val + 2 * Real.pi * ξ := by
    rw [lt_modularCutThreshold_iff hint.1 hint.2]
    constructor <;> intro h <;> linarith
  have hind : resolventCutIndicator (graphResolvent M J Ω 1)
      (modularCutThreshold (a - 2 * Real.pi * ξ)) s =
      if a < resolventLogFrequency s.val + 2 * Real.pi * ξ then (1 : ℂ) else 0 := by
    change (if s.val < modularCutThreshold (a - 2 * Real.pi * ξ) then (1 : ℂ) else 0) = _
    simp only [hcond]
  calc
    _ = (modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ) (f ξ • v)) s :=
      congrArg (fun w : ModularCyclicSpace M J Ω x => w s) he
    _ = _ := by rw [hs, hv, hind]; change _ * (f ξ * v s) = _; ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicCutSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Interchanging the variables of the modular cut field -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

include hsep hcyc

theorem cyclicCutField_swap_tensor (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : ModularCyclicSpace M J Ω x) :
    l2ScalarSwap volume
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (modularCyclicCutField M J Ω x a (scalarLpTensor volume f v)) =
    fourierShiftedField
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a (scalarLpTensor _ v f) := by
  let R := graphResolvent M J Ω 1
  let hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR x
  let l : spectrum ℝ R → ℝ := fun s => resolventLogFrequency s.val
  have hl : Measurable l := resolventLogFrequency_measurable.comp measurable_subtype_coe
  let k : ℝ × spectrum ℝ R → ℂ := fun p => if a < l p.2 + 2 * Real.pi * p.1 then 1 else 0
  apply l2ScalarSwap_of_kernel volume μ (fun ξ s => k (ξ, s) * f ξ * v s)
  · exact cyclicCutField_tensor_rows J Ω hsep hcyc x a f v
  · exact fourierShiftedField_tensor_rows μ l hl a f v
  · intro f' v'
    apply integrable_bounded_L2_kernel volume μ k _ _ f f' v v'
    · exact Measurable.ite
        (measurableSet_lt measurable_const
          ((hl.comp measurable_snd).add (measurable_const.mul measurable_fst)))
        measurable_const measurable_const
    · intro p
      dsimp [k]
      split <;> simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedModularData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling the constructed bounded modular data

The modular group and spectral cuts yield bounded modular data
when the group normalizes the algebra. Tomita conjugation gives the
conjugation data when it identifies the algebra with its commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

omit [TopologicalSpace.SeparableSpace H] in
/-- Modular conjugation data from the Tomita commutant identity. -/
def constructedModularConjugationData
    (hcomm : conjugateRightAlgebra (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaPolarConjugation_involutive J Ω hsep hcyc) M = M.commutant) :
    ModularConjugationData M Ω where
  conjugation := tomitaPolarConjugation J Ω hsep hcyc
  involutive := tomitaPolarConjugation_involutive J Ω hsep hcyc
  fixes_vector := tomitaPolarConjugation_fixes_vector J Ω hsep hcyc
  commutant := hcomm
  centralizer_vector r hr := by
    change tomitaPolarConjugation J Ω hsep hcyc
      (star r.val (tomitaPolarConjugation J Ω hsep hcyc Ω)) = r.val Ω
    rw [tomitaPolarConjugation_fixes_vector J Ω hsep hcyc]
    exact tomitaPolarConjugation_star_centralizer J Ω hsep hcyc r hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaRootDomain
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The domain of the closed Tomita operator

The polar graph coordinates parametrize the full closed graph, not only
its algebraic core. Thus the first coordinate has exactly the range of
the positive graph square root as its domain.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hsep hcyc

theorem tomitaClosedLinearOperator_root_graph (a : H) :
    (tomitaGraphRoot (M := M) J Ω a,
      J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a))) ∈
      (tomitaClosedLinearOperator M J Ω 1).graph := by
  rw [tomitaClosedLinearOperator_graph J Ω 1 hsep]
  let v := tomitaPolarCoordinates J Ω hsep hcyc a
  have he : tomitaProductCoordinates v.val =
      (tomitaGraphRoot (M := M) J Ω a,
        J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a))) := by
    apply Prod.ext
    · exact tomitaPolarCoordinates_first J Ω hsep hcyc a
    · exact tomitaPolarCoordinates_second J Ω hsep hcyc a
  rw [← he]
  change tomitaProductCoordinates.symm (tomitaProductCoordinates v.val) ∈
    rescaledGraphSubspace M J Ω 1
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact v.property

theorem tomitaClosedLinearOperator_graph_iff (x y : H) :
    (x, y) ∈ (tomitaClosedLinearOperator M J Ω 1).graph ↔
      ∃ a : H, tomitaGraphRoot (M := M) J Ω a = x ∧
        J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a)) = y := by
  constructor
  · intro hxy
    rw [tomitaClosedLinearOperator_graph J Ω 1 hsep] at hxy
    let v : rescaledGraphSubspace M J Ω 1 := ⟨tomitaProductCoordinates.symm (x, y), hxy⟩
    let a := (tomitaPolarCoordinates J Ω hsep hcyc).symm v
    have he : tomitaPolarCoordinates J Ω hsep hcyc a = v :=
      (tomitaPolarCoordinates J Ω hsep hcyc).apply_symm_apply v
    refine ⟨a, ?_, ?_⟩
    · have h := congrArg (fun w : rescaledGraphSubspace M J Ω 1 => w.val 0) he
      rw [tomitaPolarCoordinates_first] at h
      exact h
    · have h := congrArg (fun w : rescaledGraphSubspace M J Ω 1 => w.val 1) he
      rw [tomitaPolarCoordinates_second] at h
      exact h
  · rintro ⟨a, rfl, rfl⟩
    exact tomitaClosedLinearOperator_root_graph J Ω hsep hcyc a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaComplementaryRoot
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complementary graph square root

Polar conjugation interchanges both bounded positive square roots. This
expresses the full Tomita graph using its two positive coordinates.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaGraphRoot_polar_apply (a : H) :
    tomitaPolarConjugation J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω a) =
      tomitaGraphComplementRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a) := by
  have h := congrArg (fun T : H →L[ℂ] H => T (tomitaPolarConjugation J Ω hsep hcyc a))
    (tomitaGraphRoot_conjugation J Ω hsep hcyc)
  change tomitaPolarConjugation J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω
    (tomitaPolarConjugation J Ω hsep hcyc (tomitaPolarConjugation J Ω hsep hcyc a))) = _ at h
  rwa [tomitaPolarConjugation_involutive] at h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaLinearPolarCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Linear polar coordinates for the closed Tomita graph -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaGraphRoot_polar_symm (a : H) :
    tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a) =
      tomitaPolarConjugation J Ω hsep hcyc (tomitaGraphComplementRoot (M := M) J Ω a) := by
  have h := congrArg (tomitaPolarConjugation J Ω hsep hcyc)
    (tomitaGraphRoot_polar_apply J Ω hsep hcyc (tomitaPolarConjugation J Ω hsep hcyc a))
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc
    (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a)),
    tomitaPolarConjugation_involutive J Ω hsep hcyc a] at h
  exact h

theorem tomitaClosedLinearOperator_positive_graph_iff (x y : H) :
    (x, y) ∈ (tomitaClosedLinearOperator M J Ω 1).graph ↔
      ∃ a : H, tomitaGraphRoot (M := M) J Ω a = x ∧
        tomitaLinearPolarUnitary J Ω hsep hcyc (tomitaGraphComplementRoot (M := M) J Ω a) = y := by
  rw [tomitaClosedLinearOperator_graph_iff J Ω hsep hcyc]
  constructor <;> rintro ⟨a, ha, hb⟩ <;> refine ⟨a, ha, ?_⟩
  · rw [tomitaGraphRoot_polar_symm J Ω hsep hcyc] at hb
    exact hb
  · rw [tomitaGraphRoot_polar_symm J Ω hsep hcyc]
    exact hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaAdjointCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The full adjoint Tomita graph in positive coordinates

The equation between the two bounded square roots determines the whole
adjoint graph. Its solution uses their commuting squares summing to one.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

/-- Membership in the adjoint graph is an equation of bounded operators. -/
theorem tomitaAdjoint_graph_equation (y z : H) :
    (y, z) ∈ (tomitaClosedLinearOperator M J Ω 1).adjoint.graph ↔
      tomitaGraphComplementRoot (M := M) J Ω
        ((tomitaLinearPolarUnitary J Ω hsep hcyc).symm y) =
      tomitaGraphRoot (M := M) J Ω z := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (tomitaClosedLinearOperator_dense J Ω 1 hsep hcyc),
    Submodule.mem_adjoint_iff]
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro a
    have ha := h _ _ ((tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc _ _).mpr
      ⟨a, rfl, rfl⟩)
    rw [linearIsometry_inner_right,
      inner_selfAdjoint_left _ (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint,
      inner_selfAdjoint_left _ (tomitaGraphRoot_selfAdjoint J Ω)] at ha
    exact sub_eq_zero.mp ha
  · intro h x v hxv
    obtain ⟨a, rfl, rfl⟩ :=
      (tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc x v).mp hxv
    rw [linearIsometry_inner_right,
      inner_selfAdjoint_left _ (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint,
      inner_selfAdjoint_left _ (tomitaGraphRoot_selfAdjoint J Ω), h, sub_self]

/-- The adjoint graph is the complementary positive column. -/
theorem tomitaAdjoint_graph_iff (y z : H) :
    (y, z) ∈ (tomitaClosedLinearOperator M J Ω 1).adjoint.graph ↔
      ∃ a : H,
        tomitaLinearPolarUnitary J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω a) = y ∧
        tomitaGraphComplementRoot (M := M) J Ω a = z := by
  rw [tomitaAdjoint_graph_equation J Ω hsep hcyc]
  let R := tomitaGraphRoot (M := M) J Ω
  let Q := tomitaGraphComplementRoot (M := M) J Ω
  let U := tomitaLinearPolarUnitary J Ω hsep hcyc
  have hRQ (a : H) : R (Q a) = Q (R a) :=
    congrArg (fun T : H →L[ℂ] H => T a) (tomitaGraphRoots_commute J Ω).eq
  have hsum (a : H) : R (R a) + Q (Q a) = a := by
    change (R * R + Q * Q) a = a
    have he : R * R + Q * Q = 1 := by
      rw [tomitaGraphRoot_square, tomitaGraphComplementRoot_square J Ω hsep hcyc]
      abel
    rw [he, one_apply_eq_self]
  constructor
  · intro h
    let w := U.symm y
    change Q w = R z at h
    refine ⟨R w + Q z, ?_, ?_⟩
    · have he : R (R w + Q z) = w := by
        rw [map_add, hRQ, ← h]
        exact hsum w
      change U (R (R w + Q z)) = y
      rw [he]
      exact U.apply_symm_apply y
    · change Q (R w + Q z) = z
      rw [map_add, ← hRQ, h]
      exact hsum z
  · rintro ⟨a, ha, hb⟩
    change Q (U.symm y) = R z
    rw [← ha, U.symm_apply_apply, ← hb]
    exact (hRQ a).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaAdjointCore
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The commutant core lies in the adjoint Tomita domain

The closed-graph coefficient identity identifies the adjoint on the dense
commutant orbit. In particular the adjoint operator is densely defined.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem tomitaAdjoint_coefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) (b : Algebra M.commutant)
    (ξ : (tomitaClosedLinearOperator M J Ω 1).domain) :
    inner ℂ (star b.val Ω) ξ.val =
      inner ℂ (J (b.val Ω)) (tomitaClosedLinearOperator M J Ω 1 ξ) := by
  have hg := LinearPMap.mem_graph (tomitaClosedLinearOperator M J Ω 1) ξ
  rw [tomitaClosedLinearOperator_graph J Ω 1 hsep] at hg
  have hc := rescaledGraph_commutant_coefficient J Ω 1 b
    (tomitaProductCoordinates.symm (ξ.val, tomitaClosedLinearOperator M J Ω 1 ξ)) hg
  change inner ℂ (J (b.val Ω)) (tomitaClosedLinearOperator M J Ω 1 ξ) =
    (1 : ℂ) * inner ℂ (star b.val Ω) ξ.val at hc
  simpa only [one_mul] using hc.symm

theorem tomitaAdjoint_commutant_mem (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) (b : Algebra M.commutant) :
    J (b.val Ω) ∈ (tomitaClosedLinearOperator M J Ω 1).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨star b.val Ω, tomitaAdjoint_coefficient J Ω hsep b⟩

theorem tomitaAdjoint_commutant_apply (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (b : Algebra M.commutant) :
    (tomitaClosedLinearOperator M J Ω 1).adjoint
      ⟨J (b.val Ω), tomitaAdjoint_commutant_mem J Ω hsep b⟩ = star b.val Ω :=
  LinearPMap.adjoint_apply_eq (tomitaClosedLinearOperator_dense J Ω 1 hsep hcyc) _
    (tomitaAdjoint_coefficient J Ω hsep b)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaCommutantCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutant vectors in the positive Tomita coordinates

The adjoint identity on the commutant orbit and the full adjoint graph
parametrization put its polar-conjugated vectors in the original closed
Tomita graph, with simultaneous algebraic approximation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaCommutant_root_coordinates (b : Algebra M.commutant) :
    ∃ a : H,
      tomitaGraphRoot (M := M) J Ω a = tomitaPolarConjugation J Ω hsep hcyc (b.val Ω) ∧
      tomitaGraphComplementRoot (M := M) J Ω a = star b.val Ω := by
  have hg := LinearPMap.mem_graph (tomitaClosedLinearOperator M J Ω 1).adjoint
    ⟨J (b.val Ω), tomitaAdjoint_commutant_mem J Ω hsep b⟩
  rw [tomitaAdjoint_commutant_apply J Ω hsep hcyc b] at hg
  obtain ⟨a, ha, hb⟩ := (tomitaAdjoint_graph_iff J Ω hsep hcyc _ _).mp hg
  refine ⟨a, ?_, hb⟩
  have h := J.injective ha
  have h' := congrArg (tomitaPolarConjugation J Ω hsep hcyc) h
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at h'
  exact h'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaMiddleCore
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded middle operator on the algebra and commutant cores

The product of the complementary graph roots replaces the unbounded modular
square root in the operator identities used below.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaMiddleOperator_polar (v : H) :
    tomitaMiddleOperator (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc v) =
      tomitaPolarConjugation J Ω hsep hcyc (tomitaMiddleOperator (M := M) J Ω v) := by
  change tomitaGraphRoot (M := M) J Ω
      (tomitaGraphComplementRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc v)) = _
  rw [← tomitaGraphRoot_polar_apply J Ω hsep hcyc,
    tomitaGraphRoot_polar_symm J Ω hsep hcyc]
  exact congrArg (tomitaPolarConjugation J Ω hsep hcyc)
    (congrArg (fun T : H →L[ℂ] H => T v) (tomitaGraphRoots_commute J Ω).eq.symm)

theorem tomitaMiddleOperator_algebra (a : Algebra M) :
    tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω)) =
      (1 - graphResolvent M J Ω 1) (star a.val Ω) := by
  let v := tomitaCoreCoordinate J Ω hsep hcyc (star a)
  have hr : tomitaGraphRoot (M := M) J Ω v = star a.val Ω :=
    tomitaCoreCoordinate_first J Ω hsep hcyc (star a)
  have hq : tomitaGraphComplementRoot (M := M) J Ω v =
      tomitaPolarConjugation J Ω hsep hcyc (a.val Ω) := by
    have h := tomitaCoreCoordinate_adjoint J Ω hsep hcyc (star a)
    change tomitaGraphRoot (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc v) = star (star a.val) Ω at h
    rw [star_star, tomitaGraphRoot_polar_symm J Ω hsep hcyc] at h
    have h' := congrArg (tomitaPolarConjugation J Ω hsep hcyc) h
    rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at h'
    exact h'
  rw [← hq, ← hr]
  change (tomitaGraphRoot (M := M) J Ω *
      (tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω)) v = _
  rw [tomitaGraphComplementRoot_square J Ω hsep hcyc]
  have hc : Commute (tomitaGraphRoot (M := M) J Ω) (1 - graphResolvent M J Ω 1) := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    exact (tomitaGraphRoots_commute J Ω).mul_right (tomitaGraphRoots_commute J Ω)
  exact congrArg (fun T : H →L[ℂ] H => T v) hc.eq

theorem tomitaMiddleOperator_commutant (b : Algebra M.commutant) :
    tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω)) =
      graphResolvent M J Ω 1 (star b.val Ω) := by
  obtain ⟨v, hr, hq⟩ := tomitaCommutant_root_coordinates J Ω hsep hcyc b
  rw [← hr, ← hq]
  change (tomitaGraphRoot (M := M) J Ω *
      tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphRoot (M := M) J Ω) v = _
  have hc := (tomitaGraphRoots_commute (M := M) J Ω).eq
  calc
    _ = (tomitaGraphRoot (M := M) J Ω * tomitaGraphRoot (M := M) J Ω *
        tomitaGraphComplementRoot (M := M) J Ω) v := by
      rw [mul_assoc, ← hc, ← mul_assoc]
    _ = _ := by rw [tomitaGraphRoot_square]; rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaMiddlePairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Symmetric pairings for the bounded conjugate-linear middle operator -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaMiddleOperator_inner_swap (v w : H) :
    inner ℂ (tomitaMiddleOperator (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc v)) w =
    inner ℂ (tomitaMiddleOperator (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc w)) v := by
  rw [tomitaMiddleOperator_polar J Ω hsep hcyc,
    tomitaPolarConjugation_inner_swap J Ω hsep hcyc]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  have hs : (tomitaMiddleOperator (M := M) J Ω).adjoint =
      tomitaMiddleOperator (M := M) J Ω := (tomitaMiddleOperator_selfAdjoint J Ω).star_eq
  rw [hs]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaMiddleRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded algebra representatives for both adjoint commutant vectors -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem tomitaMiddle_commutant_representative (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (b : Algebra M.commutant) :
    ∃ a : Algebra M,
      a.val Ω = tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω)) ∧
      star a.val Ω = tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (star b.val Ω)) := by
  obtain ⟨a, ha, has⟩ := graphResolvent_commutant_starPair J Ω (star b)
  refine ⟨a, ?_, ?_⟩
  · rw [tomitaMiddleOperator_commutant J Ω hsep hcyc]
    exact ha
  · rw [show star b.val = (star b).val from rfl,
      tomitaMiddleOperator_commutant J Ω hsep hcyc]
    exact has

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPairingOperator
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded operator equation for modular averaging

This is the application-sized form of Rieffel--Van Daele, Lemma 4.5.
All operators and algebra representatives are constructed in the original
representation. Our graph resolvent is one half of their operator R.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modular_pairing_operator (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b)
    (z : ℂ) (x : Algebra M) (hx : IsSelfAdjoint x)
    (hpair : ∀ a : selfAdjoint (Algebra M),
      (inner ℂ (a.val.val Ω) (b Ω)).re =
        (z * inner ℂ (a.val.val Ω) (x.val Ω)).re) :
    (2 : ℂ) • (tomitaMiddleOperator (M := M) J Ω *
      conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b *
      tomitaMiddleOperator (M := M) J Ω) =
    star z • ((1 - graphResolvent M J Ω 1) * x.val * graphResolvent M J Ω 1) +
      z • (graphResolvent M J Ω 1 * x.val * (1 - graphResolvent M J Ω 1)) := by
  let R := graphResolvent M J Ω 1
  let Q : H →L[ℂ] H := 1 - R
  let T := tomitaMiddleOperator (M := M) J Ω
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hR : R.adjoint = R := (graphResolvent_positive J Ω 1).isSelfAdjoint.star_eq
  have hQ : Q.adjoint = Q := (IsSelfAdjoint.one _ |>.sub
    (graphResolvent_positive J Ω 1).isSelfAdjoint).star_eq
  have hx' : x.val.adjoint = x.val := congrArg Subtype.val hx.star_eq
  have hcore (b₁ b₂ : Algebra M.commutant) :
      inner ℂ (((2 : ℂ) • (T * conjugationOperator C b * T)) (b₂.val Ω)) (b₁.val Ω) =
      inner ℂ ((star z • (Q * x.val * R) + z • (R * x.val * Q)) (b₂.val Ω))
        (b₁.val Ω) := by
    obtain ⟨y, hy, hys⟩ := tomitaMiddle_commutant_representative J Ω hsep hcyc b₁
    obtain ⟨w, hw, hws⟩ := tomitaMiddle_commutant_representative J Ω hsep hcyc b₂
    have hys' : star y.val Ω = R (b₁.val Ω) := by
      rw [hys, show star b₁.val = (star b₁).val from rfl,
        tomitaMiddleOperator_commutant J Ω hsep hcyc]
      change R (star (star b₁.val) Ω) = R (b₁.val Ω)
      rw [star_star]
    have hws' : star w.val Ω = R (b₂.val Ω) := by
      rw [hws, show star b₂.val = (star b₂).val from rfl,
        tomitaMiddleOperator_commutant J Ω hsep hcyc]
      change R (star (star b₂.val) Ω) = R (b₂.val Ω)
      rw [star_star]
    have hl : inner ℂ (y.val Ω) (b (w.val Ω)) =
        inner ℂ ((T * conjugationOperator C b * T) (b₂.val Ω)) (b₁.val Ω) := by
      rw [hy, hw, tomitaMiddleOperator_inner_swap J Ω hsep hcyc,
        tomitaMiddleOperator_polar J Ω hsep hcyc (b₂.val Ω)]
      rfl
    have hr₁ : inner ℂ (y.val Ω) (w.val (x.val Ω)) =
        inner ℂ ((Q * x.val * R) (b₂.val Ω)) (b₁.val Ω) := by
      rw [hy, tomitaMiddleOperator_inner_swap J Ω hsep hcyc]
      change inner ℂ (T (C ((w * x).val Ω))) (b₁.val Ω) = _
      rw [tomitaMiddleOperator_algebra J Ω hsep hcyc (w * x)]
      change inner ℂ (Q (star (w.val * x.val) Ω)) (b₁.val Ω) = _
      rw [star_mul]
      rw [show star x.val = x.val from congrArg Subtype.val hx.star_eq]
      change inner ℂ (Q (x.val (star w.val Ω))) (b₁.val Ω) = _
      rw [hws']
      rfl
    have hr₂ : inner ℂ (y.val (x.val Ω)) (w.val Ω) =
        inner ℂ ((R * x.val * Q) (b₂.val Ω)) (b₁.val Ω) := by
      rw [hw]
      have he := congrArg star (tomitaMiddleOperator_inner_swap J Ω hsep hcyc
        (b₂.val Ω) ((y * x).val Ω))
      change (starRingEnd ℂ) (inner ℂ (T (C (b₂.val Ω))) ((y * x).val Ω)) =
        (starRingEnd ℂ) (inner ℂ (T (C ((y * x).val Ω))) (b₂.val Ω)) at he
      rw [inner_conj_symm, inner_conj_symm] at he
      change inner ℂ ((y * x).val Ω) (T (C (b₂.val Ω))) = _
      rw [he, tomitaMiddleOperator_algebra J Ω hsep hcyc (y * x)]
      change inner ℂ (b₂.val Ω) (Q (star (y.val * x.val) Ω)) = _
      rw [star_mul]
      rw [show star x.val = x.val from congrArg Subtype.val hx.star_eq]
      change inner ℂ (b₂.val Ω) (Q (x.val (star y.val Ω))) = _
      rw [hys', ← ContinuousLinearMap.adjoint_inner_left, hQ,
        ← ContinuousLinearMap.adjoint_inner_left, hx',
        ← ContinuousLinearMap.adjoint_inner_left, hR]
      rfl
    have hp := modular_pairing_products Ω b hb hbs z x hpair y w
    rw [hl, hr₁, hr₂] at hp
    simp only [smul_apply, add_apply, inner_smul_left, inner_add_left,
      map_ofNat, starRingEnd_apply, star_star]
    exact hp
  have hd : DenseRange (fun b : Algebra M.commutant => b.val Ω) :=
    Generator.commutant_orbit_dense M Ω (fun a ha => hsep ha)
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  exact hd.induction_on₂ (p := fun w v =>
    inner ℂ (((2 : ℂ) • (T * conjugationOperator C b * T)) v) w =
      inner ℂ ((star z • (Q * x.val * R) + z • (R * x.val * Q)) v) w)
    (isClosed_eq (by fun_prop) (by fun_prop)) hcore w v

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularBoundedEquation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed solutions to the bounded modular operator equation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modular_bounded_equation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (b : Algebra M.commutant) (hb : IsSelfAdjoint b) (z : ℂ) (hz : 0 < z.re) :
    ∃ x : Algebra M, IsSelfAdjoint x ∧ ‖x‖ ≤ (1 + ‖b‖) / z.re ∧
      tomitaMiddleOperator (M := M) J Ω *
          conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val *
          tomitaMiddleOperator (M := M) J Ω =
        star z • ((1 - graphResolvent M J Ω 1) * x.val * graphResolvent M J Ω 1) +
          z • (graphResolvent M J Ω 1 * x.val * (1 - graphResolvent M J Ω 1)) := by
  obtain ⟨x, hx, hxn, hxp⟩ := modular_radon_nikodym_selfAdjoint Ω b hb z hz
  let a : Algebra M := (1 / 2 : ℝ) • x
  have ha : IsSelfAdjoint a := by
    change star ((1 / 2 : ℝ) • x) = (1 / 2 : ℝ) • x
    rw [star_smul, star_trivial, hx.star_eq]
  refine ⟨a, ha, ?_, ?_⟩
  · change ‖(1 / 2 : ℝ) • x‖ ≤ (1 + ‖b‖) / z.re
    rw [norm_smul]
    norm_num
    have hn : ‖x‖ ≤ 2 * ((1 + ‖b‖) / z.re) := by
      convert hxn using 1
      all_goals try with_reducible_and_instances rfl
      ring
    change ‖x.val‖ ≤ 2 * ((1 + ‖b.val‖) / z.re) at hn
    linarith
  · have he := modular_pairing_operator J Ω hsep hcyc b.val b.property
      (congrArg Subtype.val hb.star_eq) z x hx hxp
    have ha' : a.val = (1 / 2 : ℂ) • x.val := by
      change (1 / 2 : ℝ) • x.val = (1 / 2 : ℂ) • x.val
      rw [← Complex.coe_smul]
      norm_num
    have hh := congrArg (fun A : H →L[ℂ] H => (1 / 2 : ℂ) • A) he
    rw [smul_smul] at hh
    norm_num at hh
    rw [ha']
    simpa only [smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm, starRingEnd_apply] using hh

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripCyclic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Identifying the weighted strip through cyclic spectral coordinates -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem weightedStripOperator_eq_group (a t : ℝ) (ha : |a| < 1)
    (g : C(spectrum ℝ (graphResolvent M J Ω 1), ℂ))
    (hg : ∀ s : spectrum ℝ (graphResolvent M J Ω 1), 0 < s.val → s.val < 1 →
      weightedStripKernel ((a : ℂ) + t * Complex.I) s.val = g s * modularSpectralPhase t s.val) :
    weightedStripOperator (M := M) J Ω ((a : ℂ) + t * Complex.I) =
      resolventContinuousCalculus (graphResolvent M J Ω 1)
        (graphResolvent_positive J Ω 1).isSelfAdjoint g *
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ (x : H) := resolventVectorMeasure R hR x
  let F := weightedStripContinuous (resolventRealCoordinate R) ((a : ℂ) + t * Complex.I)
  have hz : |(((a : ℂ) + t * Complex.I)).re| < 1 := by simpa using ha
  apply ContinuousLinearMap.ext
  intro x
  let e : ResolventCyclicL2 R hR x := ContinuousMap.toLp 2 (μ x) ℂ 1
  let w := modularCyclicPhaseOperator M J Ω x t e
  have hwe : w =ᵐ[μ x] fun s => modularSpectralPhase t s.val * e s :=
    resolventScalarMultiplier_apply_ae R hR x _ _ _ _ e
  have heq : ContinuousMap.toLp 2 (μ x) ℂ F =
      resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm w := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ x) F,
      resolventScalarMultiplier_apply_ae R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm w,
      hwe, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ x) (1 : C(spectrum ℝ R, ℂ)),
      graphResolventVectorMeasure_interior J Ω hsep hcyc x] with s hF hgm hw he hs
    rw [hF, hgm, hw, he, ContinuousMap.one_apply, mul_one]
    exact (weightedStripContinuous_apply _ hz s).trans (hg s hs.1 hs.2)
  calc
    weightedStripOperator (M := M) J Ω ((a : ℂ) + t * Complex.I) x =
        resolventCyclicIsometry R hR x (ContinuousMap.toLp 2 (μ x) ℂ F) :=
      (resolventCyclicIsometry_continuous R hR x F).symm
    _ = resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x w) := by
      rw [heq, resolventCyclicIsometry_multiplier]
    _ = _ := by
      rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x t e,
        resolventCyclicIsometry_one]
      rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripOperatorBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The weighted strip boundaries are modular orbit operators -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem weightedStripOperator_right (t : ℝ) :
    weightedStripOperator (M := M) J Ω ((1 / 2 : ℂ) + t * Complex.I) =
      graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1) ^ 3 *
        (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let r := resolventCoordinateFunction R
  let g := r * (1 - r) ^ 3
  have he := weightedStripOperator_eq_group J Ω hsep hcyc (1 / 2) t (by norm_num) g
    (fun s hs hs1 => by
      simpa only [g, r, resolventCoordinateFunction, ContinuousMap.mul_apply,
        ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.coe_mk, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
          weightedStripKernel_right hs hs1 t)
  have hg : resolventContinuousCalculus R hR g = R * (1 - R) ^ 3 := by
    dsimp [g, r]
    rw [map_mul, map_pow, map_sub, map_one, resolventContinuousCalculus_coordinate]
  change weightedStripOperator (M := M) J Ω _ = resolventContinuousCalculus R hR g * _ at he
  rw [hg] at he
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, hg] using he

theorem weightedStripOperator_left (t : ℝ) :
    weightedStripOperator (M := M) J Ω ((-1 / 2 : ℂ) + t * Complex.I) =
      graphResolvent M J Ω 1 ^ 2 * (1 - graphResolvent M J Ω 1) ^ 2 *
        (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let r := resolventCoordinateFunction R
  let g := r ^ 2 * (1 - r) ^ 2
  have he := weightedStripOperator_eq_group J Ω hsep hcyc (-1 / 2) t (by norm_num) g
    (fun s hs hs1 => by
      simpa only [g, r, resolventCoordinateFunction, ContinuousMap.mul_apply,
        ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.coe_mk, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
          weightedStripKernel_left hs hs1 t)
  have hg : resolventContinuousCalculus R hR g = R ^ 2 * (1 - R) ^ 2 := by
    dsimp [g, r]
    rw [map_mul, map_pow, map_pow, map_sub, map_one, resolventContinuousCalculus_coordinate]
  change weightedStripOperator (M := M) J Ω _ = resolventContinuousCalculus R hR g * _ at he
  rw [hg] at he
  simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_ofNat, hg] using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripCenter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The middle value of the weighted spectral strip -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hsep hcyc in
theorem weightedStripOperator_center :
    weightedStripOperator (M := M) J Ω 0 =
      graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1) ^ 2 *
        tomitaMiddleOperator (M := M) J Ω := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let r := resolventCoordinateFunction R
  let g := r * (1 - r) ^ 2 *
    (resolventSqrtFunction R * resolventComplementSqrtFunction R)
  have he := weightedStripOperator_eq_group J Ω hsep hcyc 0 0 (by norm_num) g
    (fun s hs hs1 => by
      simpa [g, r, resolventCoordinateFunction, resolventSqrtFunction,
        resolventComplementSqrtFunction, modularSpectralPhase] using
          weightedStripKernel_center hs hs1)
  have hp : 0 ≤ R := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (graphResolvent_positive J Ω 1)
  have hq : 0 ≤ 1 - R := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    have hs := (tomitaGraphComplementRoot_nonneg (M := M) J Ω).isSelfAdjoint
    simpa only [hs.star_eq] using
      (star_mul_self_nonneg (tomitaGraphComplementRoot (M := M) J Ω))
  have hg : resolventContinuousCalculus R hR g = R * (1 - R) ^ 2 *
      tomitaMiddleOperator (M := M) J Ω := by
    dsimp [g, r]
    rw [map_mul, map_mul, map_mul, map_pow, map_sub, map_one,
      resolventContinuousCalculus_coordinate,
      resolventContinuousCalculus_sqrt R hR hp,
      resolventContinuousCalculus_complement_sqrt R hR hq]
    rfl
  change weightedStripOperator (M := M) J Ω _ = resolventContinuousCalculus R hR g * _ at he
  rw [hg] at he
  simpa only [Complex.ofReal_zero, zero_mul, zero_add, show Multiplicative.ofAdd (0 : ℝ) = 1 from rfl,
    map_one, OneMemClass.coe_one, mul_one, hg] using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripDense
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The extra strip weight has dense range and is injective -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hsep hcyc in
theorem weightedStripOperator_center_injective :
    Function.Injective (weightedStripOperator (M := M) J Ω 0) := by
  have hq := one_sub_graphResolvent_injective J Ω hsep
  have hr := tomitaGraphRoot_injective J Ω hsep hcyc
  have hc : Function.Injective (tomitaGraphComplementRoot (M := M) J Ω) := by
    intro x y he
    apply hq
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    exact congrArg (tomitaGraphComplementRoot (M := M) J Ω) he
  rw [weightedStripOperator_center J Ω hsep hcyc]
  intro x y he
  apply hc
  apply hr
  apply hq
  apply hq
  apply graphResolvent_injective J Ω hsep hcyc
  simpa only [pow_two, mul_apply_eq_comp, tomitaMiddleOperator] using he

include hsep hcyc in
theorem weightedStripOperator_center_selfAdjoint :
    IsSelfAdjoint (weightedStripOperator (M := M) J Ω 0) := by
  let R := graphResolvent M J Ω 1
  let Q := 1 - R
  let T := tomitaMiddleOperator (M := M) J Ω
  have hRQ : Commute R Q := (Commute.one_right R).sub_right (Commute.refl R)
  have hTR : Commute T R := by
    change Commute (tomitaMiddleOperator (M := M) J Ω) (graphResolvent M J Ω 1)
    rw [← tomitaGraphRoot_square J Ω]
    have h : Commute (tomitaMiddleOperator (M := M) J Ω) (tomitaGraphRoot (M := M) J Ω) :=
      (Commute.refl _).mul_left (tomitaGraphRoots_commute J Ω).symm
    exact h.mul_right h
  have hTQ : Commute T Q := (Commute.one_right T).sub_right hTR
  rw [weightedStripOperator_center J Ω hsep hcyc]
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hQ : IsSelfAdjoint Q := by
    change star (1 - R) = 1 - R
    rw [star_sub, star_one, hR.star_eq]
  have hD := (hR.commute_iff (hQ.pow 2)).mp (hRQ.pow_right 2)
  exact (hD.commute_iff (tomitaMiddleOperator_selfAdjoint J Ω)).mp
    (hTR.symm.mul_left (hTQ.pow_right 2).symm)

include hsep hcyc in
theorem weightedStripOperator_center_dense :
    DenseRange (weightedStripOperator (M := M) J Ω 0) := by
  let W := weightedStripOperator (M := M) J Ω 0
  change Dense (W.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, W.orthogonal_range]
  have hs : W.adjoint = W := (weightedStripOperator_center_selfAdjoint J Ω hsep hcyc).star_eq
  rw [hs]
  exact LinearMap.ker_eq_bot.mpr (weightedStripOperator_center_injective J Ω hsep hcyc)

include hsep hcyc in
theorem weightedStripOperator_cancel_sandwich (A B : H →L[ℂ] H)
    (he : weightedStripOperator (M := M) J Ω 0 * A * weightedStripOperator (M := M) J Ω 0 =
      weightedStripOperator (M := M) J Ω 0 * B * weightedStripOperator (M := M) J Ω 0) : A = B := by
  apply DFunLike.ext'
  apply (weightedStripOperator_center_dense J Ω hsep hcyc).equalizer A.continuous B.continuous
  funext x
  apply weightedStripOperator_center_injective J Ω hsep hcyc
  exact congrArg (fun T : H →L[ℂ] H => T x) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeightedStripFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem weightedStrip_boundary_factorization (X Y : H →L[ℂ] H) (α β : ℂ)
    (heq : tomitaMiddleOperator (M := M) J Ω * Y * tomitaMiddleOperator (M := M) J Ω =
      α • (graphResolvent M J Ω 1 * X * (1 - graphResolvent M J Ω 1)) +
      β • ((1 - graphResolvent M J Ω 1) * X * graphResolvent M J Ω 1)) (t : ℝ) :
    α • (weightedStripOperator (M := M) J Ω (-((1 / 2 : ℂ) + t * Complex.I)) * X *
        weightedStripOperator (M := M) J Ω ((1 / 2 : ℂ) + t * Complex.I)) +
      β • (weightedStripOperator (M := M) J Ω (-((-1 / 2 : ℂ) + t * Complex.I)) * X *
        weightedStripOperator (M := M) J Ω ((-1 / 2 : ℂ) + t * Complex.I)) =
      weightedStripOperator (M := M) J Ω 0 *
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) * Y *
          (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)) *
        weightedStripOperator (M := M) J Ω 0 := by
  let R := graphResolvent M J Ω 1
  let Q := 1 - R
  let D := R * Q ^ 2
  let T := tomitaMiddleOperator (M := M) J Ω
  let U := (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
  let V := (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
  have hRQ : Commute R Q := (Commute.one_right R).sub_right (Commute.refl R)
  have hDR : Commute D R := (Commute.refl R).mul_left (hRQ.pow_right 2).symm
  have hDQ : Commute D Q := hRQ.mul_left (Commute.pow_self Q 2)
  have hUR : Commute U R := modularStrongGroup_commute_resolvent J Ω hsep hcyc t
  have hVR : Commute V R := modularStrongGroup_commute_resolvent J Ω hsep hcyc (-t)
  have hUQ : Commute U Q := (Commute.one_right U).sub_right hUR
  have hVQ : Commute V Q := (Commute.one_right V).sub_right hVR
  have hDU : Commute D U := (hUR.mul_right (hUQ.pow_right 2)).symm
  have hUT : Commute U T := modularStrongGroup_commute_middle J Ω hsep hcyc t
  have hVT : Commute V T := modularStrongGroup_commute_middle J Ω hsep hcyc (-t)
  have hTR : Commute T R := by
    change Commute (tomitaMiddleOperator (M := M) J Ω) (graphResolvent M J Ω 1)
    rw [← tomitaGraphRoot_square J Ω]
    have h : Commute (tomitaMiddleOperator (M := M) J Ω) (tomitaGraphRoot (M := M) J Ω) :=
      (Commute.refl _).mul_left (tomitaGraphRoots_commute J Ω).symm
    exact h.mul_right h
  have hTQ : Commute T Q := (Commute.one_right T).sub_right hTR
  have hDT : Commute D T := (hTR.mul_right (hTQ.pow_right 2)).symm
  have hr (s : ℝ) : weightedStripOperator (M := M) J Ω ((1 / 2 : ℂ) + s * Complex.I) =
      D * Q * (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd s) : H →L[ℂ] H) := by
    rw [weightedStripOperator_right J Ω hsep hcyc]
    dsimp only [D, Q, R]
    noncomm_ring
  have hl (s : ℝ) : weightedStripOperator (M := M) J Ω ((-1 / 2 : ℂ) + s * Complex.I) =
      D * R * (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd s) : H →L[ℂ] H) := by
    rw [weightedStripOperator_left J Ω hsep hcyc]
    dsimp only [D, Q, R]
    noncomm_ring
  rw [show -((1 / 2 : ℂ) + t * Complex.I) = (-1 / 2 : ℂ) + (-t) * Complex.I by ring,
    show -((-1 / 2 : ℂ) + t * Complex.I) = (1 / 2 : ℂ) + (-t) * Complex.I by ring,
    ← Complex.ofReal_neg, hl (-t), hr t, hr (-t), hl t,
    weightedStripOperator_center J Ω hsep hcyc]
  change α • ((D * R * V) * X * (D * Q * U)) +
    β • ((D * Q * V) * X * (D * R * U)) = (D * T) * (V * Y * U) * (D * T)
  rw [sandwich_reorder D R Q U V X hVR.symm hDQ hDU,
    sandwich_reorder D Q R U V X hVQ.symm hDR hDU]
  calc
    _ = D * V * (α • (R * X * Q) + β • (Q * X * R)) * U * D := by
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    _ = D * V * (T * Y * T) * U * D := by rw [← heq]
    _ = (D * T * V) * Y * (D * T * U) :=
      (sandwich_reorder D T T U V Y hVT.symm hDT hDU).symm
    _ = (D * T) * (V * Y * U) * (D * T) := by
      rw [((hDU.mul_left hUT.symm).eq : D * T * U = U * (D * T))]
      simp only [mul_assoc]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularOrbitAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded modular equation determines the orbit average

The scalar contour theorem is applied after multiplying by an injective
dense-range spectral weight. Its cancellation then identifies the actual
operator average, not only its weighted matrix coefficients.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularOrbitAverage_eq_of_equation (X Y : H →L[ℂ] H) (φ : ℝ)
    (hφ : |φ| < Real.pi)
    (heq : tomitaMiddleOperator (M := M) J Ω * Y * tomitaMiddleOperator (M := M) J Ω =
      Complex.exp (Complex.I * φ / 2) •
          (graphResolvent M J Ω 1 * X * (1 - graphResolvent M J Ω 1)) +
        Complex.exp (-(Complex.I * φ / 2)) •
          ((1 - graphResolvent M J Ω 1) * X * graphResolvent M J Ω 1)) :
    modularOrbitAverage J Ω hsep hcyc Y φ hφ = X := by
  apply weightedStripOperator_cancel_sandwich J Ω hsep hcyc
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  let W := weightedStripOperator (M := M) J Ω 0
  let F := modularOrbit J Ω hsep hcyc Y
  let w := stripAverageKernel Real.pi (φ : ℂ)
  have hw : Integrable w := stripAverageKernel_integrable (by simpa using hφ)
  have hi : Integrable (fun t => w t • F t (W η)) :=
    integrable_weighted_operator_vector volume w hw F
      (fun x => (modularOrbit_continuous J Ω hsep hcyc Y x).aestronglyMeasurable)
      ‖Y‖ (Filter.Eventually.of_forall (modularOrbit_norm_le J Ω hsep hcyc Y)) (W η)
  have hav : inner ℂ ξ ((W * modularOrbitAverage J Ω hsep hcyc Y φ hφ * W) η) =
      ∫ t : ℝ, w t * inner ℂ ξ ((W * F t * W) η) := by
    change ((innerSL ℂ ξ).comp W) (∫ t : ℝ, w t • F t (W η)) = _
    rw [← ((innerSL ℂ ξ).comp W).integral_comp_comm hi]
    simp only [ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul,
      mul_apply_eq_comp, innerSL_apply_apply]
  have hb (t : ℝ) :
      inner ℂ ξ ((W * F t * W) η) =
        Complex.exp (Complex.I * φ / 2) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((1 / 2 : ℂ) + t * Complex.I) +
          Complex.exp (-(Complex.I * φ / 2)) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((-1 / 2 : ℂ) + t * Complex.I) := by
    have h := congrArg (fun A : H →L[ℂ] H => inner ℂ ξ (A η))
      (weightedStrip_boundary_factorization J Ω hsep hcyc X Y _ _ heq t)
    simpa only [add_apply, smul_apply,
      inner_add_right, inner_smul_right, smul_eq_mul, weightedStripCoefficient, W, F, modularOrbit] using h.symm
  calc
    _ = ∫ t : ℝ, w t * inner ℂ ξ ((W * F t * W) η) := hav
    _ = ∫ t : ℝ, stripAverageKernel Real.pi (φ : ℂ) t *
        (Complex.exp (Complex.I * φ / 2) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((1 / 2 : ℂ) + t * Complex.I) +
          Complex.exp (-(Complex.I * φ / 2)) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((-1 / 2 : ℂ) + t * Complex.I)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => congrArg (w t * ·) (hb t)
    _ = _ := by
      simpa only [weightedStripCoefficient, neg_zero] using
        weightedStripCoefficient_average J Ω X ξ η φ hφ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaPolarCorePairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The vector-state identity for polar conjugation on the algebraic core -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaCoreCoordinate_complement (a : Algebra M) :
    tomitaGraphComplementRoot (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) =
      tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω) := by
  have h := tomitaCoreCoordinate_adjoint J Ω hsep hcyc a
  rw [tomitaGraphRoot_polar_symm J Ω hsep hcyc] at h
  have he := congrArg (tomitaPolarConjugation J Ω hsep hcyc) h
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at he
  exact he

theorem tomitaPolarConjugation_core_pairing (a b : Algebra M) :
    inner ℂ (a.val Ω) (tomitaPolarConjugation J Ω hsep hcyc (star b.val Ω)) =
      inner ℂ (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω)) (b.val Ω) := by
  let u := tomitaCoreCoordinate J Ω hsep hcyc a
  let v := tomitaCoreCoordinate J Ω hsep hcyc b
  rw [← tomitaCoreCoordinate_first J Ω hsep hcyc a,
    ← tomitaCoreCoordinate_first J Ω hsep hcyc b,
    ← tomitaCoreCoordinate_complement J Ω hsep hcyc a,
    ← tomitaCoreCoordinate_complement J Ω hsep hcyc b]
  have hr : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot (M := M) J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  have hq : (tomitaGraphComplementRoot (M := M) J Ω).adjoint =
      tomitaGraphComplementRoot (M := M) J Ω :=
    (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint.star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hr,
    ← ContinuousLinearMap.adjoint_inner_right, hq]
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ u (T v))
    (tomitaGraphRoots_commute J Ω).eq

theorem tomitaPolarConjugation_vectorState (a b : Algebra M) :
    inner ℂ Ω (b.val (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω))) =
      inner ℂ (a.val (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω))) Ω := by
  have h := tomitaPolarConjugation_core_pairing J Ω hsep hcyc (star b) (star a)
  change inner ℂ (star b.val Ω)
      (tomitaPolarConjugation J Ω hsep hcyc (star (star a.val) Ω)) =
    inner ℂ (tomitaPolarConjugation J Ω hsep hcyc (star (star b.val) Ω))
      (star a.val Ω) at h
  rw [star_star, star_star] at h
  calc
    inner ℂ Ω (b.val (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω))) =
        inner ℂ (star b.val Ω) (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω)) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω)) (star a.val Ω) := h
    _ = inner ℂ (a.val (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω))) Ω := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PolarCommutantEquality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The polar commutant equality from the averaged inclusion -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaPolarConjugation_commutant_eq_of_inclusion
    (hincl : ∀ b : Algebra M.commutant,
      conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val ∈ M) :
    conjugateRightAlgebra (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaPolarConjugation_involutive J Ω hsep hcyc) M = M.commutant := by
  have hreverse := polar_commutant_reverse (tomitaPolarConjugation J Ω hsep hcyc)
    (tomitaPolarConjugation_involutive J Ω hsep hcyc) Ω
    (tomitaPolarConjugation_fixes_vector J Ω hsep hcyc) hcyc hsep
    (tomitaPolarConjugation_vectorState J Ω hsep hcyc) hincl
  apply le_antisymm
  · rintro T ⟨a, ha, rfl⟩
    exact hreverse ⟨a, ha⟩
  · intro T hT
    exact ⟨conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) T,
      hincl ⟨T, hT⟩,
      conjugationOperator_twice _ (tomitaPolarConjugation_involutive J Ω hsep hcyc) T⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularOrbitCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Modular orbits of polar-conjugated commutant elements

The bounded equation and strip-average separation give the inclusion on
every orbit. The reverse inclusion is the previously proved polar duality.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularOrbit_polar_commutant_selfAdjoint_mem (b : Algebra M.commutant)
    (hb : IsSelfAdjoint b) (t : ℝ) :
    modularOrbit J Ω hsep hcyc
      (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val) t ∈ M := by
  let Y := conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val
  apply mem_of_strip_averages M Real.pi_pos (modularOrbit J Ω hsep hcyc Y)
    (modularOrbit_continuous J Ω hsep hcyc Y) ‖Y‖ (modularOrbit_norm_le J Ω hsep hcyc Y) _ t
  intro φ hφ
  let z := Complex.exp (Complex.I * φ / 2)
  have hz : 0 < z.re := by
    have hcos : 0 < Real.cos (φ / 2) := Real.cos_pos_of_mem_Ioo
      ⟨by have := (abs_lt.mp hφ).1; linarith,
        by have := (abs_lt.mp hφ).2; linarith⟩
    simpa [z, Complex.exp_re] using hcos
  have hzs : star z = Complex.exp (-(Complex.I * φ / 2)) := by
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    have harg : (starRingEnd ℂ) (Complex.I * φ / 2) = -(Complex.I * φ / 2) := by
      calc
        _ = (-Complex.I) * (φ : ℂ) / 2 := by
          rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, htwo]
        _ = _ := by ring
    exact (Complex.exp_conj (Complex.I * φ / 2)).symm.trans (congrArg Complex.exp harg)
  obtain ⟨x, _, _, hx⟩ := modular_bounded_equation J Ω hsep hcyc b hb z hz
  have hav := modularOrbitAverage_eq_of_equation J Ω hsep hcyc x.val Y φ hφ (by
    change _ = _ at hx ⊢
    rw [hzs] at hx
    exact hx.trans (add_comm _ _))
  change modularOrbitAverage J Ω hsep hcyc Y φ hφ ∈ M
  rw [hav]
  exact x.property

theorem modularOrbit_polar_commutant_mem (b : Algebra M.commutant) (t : ℝ) :
    modularOrbit J Ω hsep hcyc
      (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val) t ∈ M := by
  have hr := modularOrbit_polar_commutant_selfAdjoint_mem J Ω hsep hcyc
    (realPart b).val (realPart b).property t
  have hi := modularOrbit_polar_commutant_selfAdjoint_mem J Ω hsep hcyc
    (imaginaryPart b).val (imaginaryPart b).property t
  have hb : b.val = (realPart b).val.val + Complex.I • (imaginaryPart b).val.val :=
    (congrArg Subtype.val (realPart_add_I_smul_imaginaryPart b)).symm
  rw [hb, conjugationOperator_add, conjugationOperator_smul]
  change _ ∈ M
  have hs : modularOrbit J Ω hsep hcyc
      (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) (realPart b).val.val) t +
      star Complex.I • modularOrbit J Ω hsep hcyc
        (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) (imaginaryPart b).val.val) t ∈ M :=
    M.add_mem hr (M.smul_mem hi (star Complex.I))
  simpa only [modularOrbit, mul_add, add_mul, mul_smul_comm, smul_mul_assoc] using hs

theorem tomitaPolarConjugation_commutant_eq :
    conjugateRightAlgebra (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaPolarConjugation_involutive J Ω hsep hcyc) M = M.commutant := by
  apply tomitaPolarConjugation_commutant_eq_of_inclusion J Ω hsep hcyc
  intro b
  have h := modularOrbit_polar_commutant_mem J Ω hsep hcyc b 0
  simpa only [modularOrbit, neg_zero, show Multiplicative.ofAdd (0 : ℝ) = 1 from rfl,
    map_one, OneMemClass.coe_one, one_mul, mul_one] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularNormalization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalization by the constructed modular group -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularOrbit_mem {a : H →L[ℂ] H} (ha : a ∈ M) (t : ℝ) :
    modularOrbit J Ω hsep hcyc a t ∈ M := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hC := tomitaPolarConjugation_involutive J Ω hsep hcyc
  have hb : conjugationOperator C a ∈ M.commutant := by
    rw [← tomitaPolarConjugation_commutant_eq J Ω hsep hcyc]
    exact ⟨a, ha, rfl⟩
  have h := modularOrbit_polar_commutant_mem J Ω hsep hcyc
    ⟨conjugationOperator C a, hb⟩ t
  change modularOrbit J Ω hsep hcyc (conjugationOperator C (conjugationOperator C a)) t ∈ M at h
  rw [conjugationOperator_twice C hC] at h
  exact h

theorem modularStrongGroup_conj_mem (s : ℝ) {a : H →L[ℂ] H} (ha : a ∈ M) :
    unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd s)) a ∈ M := by
  have h := modularOrbit_mem J Ω hsep hcyc ha (-s)
  simpa only [modularOrbit, neg_neg, unitaryConj, ← Unitary.coe_star,
    regularGroup_star_eq] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreWindowDualComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Dual translation changes the trace of every nonzero sub-half-window -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def constructedCoreDualEquiv (a : ℝ) :
    Algebra (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) ≃⋆ₐ[ℂ]
    Algebra (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) :=
  regularCoreDualEquiv _ _ M
    (fun s _ ha => modularStrongGroup_conj_mem J Ω hsep hcyc s.toAdd ha) a

end

end KadisonKastler

end OAI
end


