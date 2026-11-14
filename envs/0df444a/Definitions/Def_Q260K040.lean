-- Prove2me | Definitions.Def_Q260K040
-- name    : Q260K040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T14:26:38.415665+00:00
-- url     : https://prove2.me/theorems/91aecd3f-5c39-4106-8e68-ffb3003e7555
-- title:
--   Definitions bundle Q260K040 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 1 definition and 21 theorems. The definitions and types are `OAI.KadisonKastler.modularCyclicGauge`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_CyclicCutSwap`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CyclicCutSwap.lean), [`KadisonKastler_CyclicGaugeKernel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CyclicGaugeKernel.lean), [`KadisonKastler_CyclicGaugeSwap`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CyclicGaugeSwap.lean), [`KadisonKastler_ModularCentralizerFixed`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularCentralizerFixed.lean), [`KadisonKastler_ModularCyclicGroup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularCyclicGroup.lean), [`KadisonKastler_ModularFixedVectors`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularFixedVectors.lean), [`KadisonKastler_ModularGaugeTransport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularGaugeTransport.lean), [`KadisonKastler_ModularKMSVectors`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularKMSVectors.lean), [`KadisonKastler_ModularPolarSymmetry`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularPolarSymmetry.lean), [`KadisonKastler_ModularSpectralStrip`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularSpectralStrip.lean), [`KadisonKastler_ModularStripSpectralBoundary`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularStripSpectralBoundary.lean), [`KadisonKastler_TomitaCoreCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomitaCoreCoordinates.lean).
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundle `Q260K042` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K045`; the statements `OAI_KadisonKastler_PointedMatrixSites_spatial_remote_adjoint_commutator_tendsto`, `OAI_KadisonKastler_PointedMatrixSites_spatial_remote_commutator_tendsto`, `OAI_KadisonKastler_concrete_unitary_of_finite_coefficient_tests`, `OAI_KadisonKastler_regularCore_spatial_of_injective_matrix_subalgebra` and `OAI_KadisonKastler_uniform_regularCore_strong_stability`; the proofs of `OAI_KadisonKastler_PointedMatrixSites_spatial_remote_adjoint_commutator_tendsto`, `OAI_KadisonKastler_PointedMatrixSites_spatial_remote_commutator_tendsto`, `OAI_KadisonKastler_TwoRatioProductModel_tensor_typeIII1`, `OAI_KadisonKastler_concrete_unitary_of_finite_coefficient_tests`, `OAI.KadisonKastler.constructedCore_subhalf_not_equivalent_dual`, `OAI.KadisonKastler.constructedCore_traceSymmetry`, `OAI.KadisonKastler.constructedFactorialCore_projectionSemifinite`, `OAI_KadisonKastler_finite_factor_of_near_II1`, `OAI_KadisonKastler_regularCore_spatial_of_injective_matrix_subalgebra` and `OAI_KadisonKastler_uniform_regularCore_strong_stability`.
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
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
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
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K042

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

theorem modularCyclicGroup_continuous (v : ModularCyclicSpace M J Ω x) :
    Continuous (fun t : ℝ => (modularCyclicGroup J Ω hsep hcyc x
      (Multiplicative.ofAdd t) : ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) v) := by
  apply (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).isometry.comp_continuous_iff.mp
  change Continuous (fun t => resolventCyclicIsometry _
    (graphResolvent_positive J Ω 1).isSelfAdjoint x (modularCyclicPhaseOperator M J Ω x t v))
  simp_rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x]
  exact modularStrongLimit_continuous J Ω hsep hcyc _

theorem modularCyclicGroup_apply_ae (t : ℝ) (v : ModularCyclicSpace M J Ω x) :
    (modularCyclicGroup J Ω hsep hcyc x (Multiplicative.ofAdd t) :
      ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) v =ᵐ[
        resolventVectorMeasure (graphResolvent M J Ω 1)
          (graphResolvent_positive J Ω 1).isSelfAdjoint x]
      fun s => modularSpectralPhase t s.val * v s := by
  exact resolventScalarMultiplier_apply_ae (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint x (fun s => modularSpectralPhase t s.val)
    ((modularSpectralPhase_measurable t).comp measurable_subtype_coe) 1
    (fun s => (modularSpectralPhase_norm t s.val).le) v

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicCutSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem cyclicCutField_swap (a : ℝ) (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    l2ScalarSwap volume
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (modularCyclicCutField M J Ω x a F) =
    fourierShiftedField
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a
      (l2ScalarSwap volume
        (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x) F) := by
  exact l2ScalarSwap_intertwines_of_tensor (volume : Measure ℝ)
    (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
    (modularCyclicCutField M J Ω x a)
    (fourierShiftedField
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a)
    (cyclicCutField_swap_tensor J Ω hsep hcyc x a) F

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGaugeKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

theorem cyclicGauge_tensor_rows (f : Lp ℂ 2 (volume : Measure ℝ))
    (v : ModularCyclicSpace M J Ω x) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ s ∂resolventVectorMeasure (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x,
      ((regularGauge (modularCyclicGroup J Ω hsep hcyc x)
        (modularCyclicGroup_continuous J Ω hsep hcyc x) :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)) (scalarLpTensor volume f v)) t s =
        modularSpectralPhase t s.val * f t * v s := by
  let U := modularCyclicGroup J Ω hsep hcyc x
  filter_upwards [regularGauge_apply_ae U (modularCyclicGroup_continuous J Ω hsep hcyc x)
    (scalarLpTensor volume f v), scalarLpTensor_apply_ae volume f v] with t ht hf
  have he := ht.trans (congrArg
    (U (Multiplicative.ofAdd t) : ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) hf)
  filter_upwards [modularCyclicGroup_apply_ae J Ω hsep hcyc x t (f t • v),
    Lp.coeFn_smul (f t) v] with s hs hv
  calc
    _ = ((U (Multiplicative.ofAdd t) : ModularCyclicSpace M J Ω x →L[ℂ]
        ModularCyclicSpace M J Ω x) (f t • v)) s :=
      congrArg (fun w : ModularCyclicSpace M J Ω x => w s) he
    _ = modularSpectralPhase t s.val * (f t • v) s := hs
    _ = _ := by rw [hv]; change _ * (f t * v s) = _; ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGaugeSwap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The full cyclic gauge under the L2 variable swap -/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

def modularCyclicGauge : unitary
    (RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
      RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :=
  regularGauge (modularCyclicGroup J Ω hsep hcyc x) (modularCyclicGroup_continuous J Ω hsep hcyc x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularFixedVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable [SeparableSpace H]

theorem modularStrongGroup_fixes_state (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω = Ω :=
  modularStrongGroup_fixes_half_eigen J Ω hsep hcyc t Ω (graphResolvent_state J Ω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCentralizerFixed
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # From fixed centralizer vectors to fixed operators

Normalization and separation of the state vector upgrade the fixed-vector
identity to a fixed-operator identity.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem modularStrongGroup_centralizer_fixed (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hnormal : ∀ t, Conjugates (modularStrongGroup J Ω hsep hcyc t) M M)
    (x : H →L[ℂ] H) (hx : x ∈ M) (hcentral : ProductStateCentralizes M Ω x)
    (t : Multiplicative ℝ) :
    unitaryConj (modularStrongGroup J Ω hsep hcyc t) x = x := by
  let u := modularStrongGroup J Ω hsep hcyc t
  have hfix : (u : H →L[ℂ] H) Ω = Ω :=
    modularStrongGroup_fixes_state J Ω hsep hcyc t.toAdd
  have hstar : star (u : H →L[ℂ] H) Ω = Ω := by
    calc
      _ = star (u : H →L[ℂ] H) ((u : H →L[ℂ] H) Ω) := by rw [hfix]
      _ = Ω := congrArg (fun T : H →L[ℂ] H => T Ω) (Unitary.star_mul_self_of_mem u.property)
  have hmem : unitaryConj u x ∈ M := by
    change unitaryConj u x ∈ (M : Set (H →L[ℂ] H))
    rw [← hnormal t]
    exact Set.mem_image_of_mem _ hx
  have hvec : unitaryConj u x Ω = x Ω := by
    change (u : H →L[ℂ] H) (x (star (u : H →L[ℂ] H) Ω)) = _
    rw [hstar]
    exact modularStrongGroup_fixes_centralizer_vector J Ω hsep hcyc t.toAdd ⟨x, hx⟩
      (fun a => hcentral a.val a.property)
  have he : (⟨unitaryConj u x, hmem⟩ : Algebra M) = ⟨x, hx⟩ := hsep hvec
  exact congrArg (fun a : Algebra M => a.val) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularGaugeTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

theorem modularCyclicEmbedding_group (t : Multiplicative ℝ) (v : ModularCyclicSpace M J Ω x) :
    modularCyclicEmbedding (M := M) J Ω x ((modularCyclicGroup J Ω hsep hcyc x t :
      ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) v) =
    (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) (modularCyclicEmbedding (M := M) J Ω x v) :=
  modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x t.toAdd v

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPolarSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Polar conjugation commutes with the constructed modular group

Conjugation exchanges `R` and `1-R`. It therefore negates the real
regularized logarithm, while also conjugating the imaginary scalar in
its exponential. These two sign changes cancel.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem regularizedModularLog_polar_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) {ε : ℝ} (hε : 0 < ε) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (regularizedModularLog M J Ω ε).val = -(regularizedModularLog M J Ω ε).val := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hcont := regularizedLogScalar_continuousOn (M := M) J Ω hε
  rw [regularizedModularLog_eq_cfc J Ω hε,
    conjugationOperator_cfc_real _ (tomitaPolarConjugation_involutive J Ω hsep hcyc)
      _ hR _ hcont, tomitaPolarConjugation_resolvent]
  have hc : ContinuousOn (regularizedLogScalar ε)
      ((fun s : ℝ => 1 - s) '' spectrum ℝ R) := by
    rintro _ ⟨s, hs, rfl⟩
    have hb := graphResolvent_spectrum_bounds J Ω hs
    have hm : ContinuousAt (fun r : ℝ => 1 - r + ε) (1 - s) := by fun_prop
    have hp : ContinuousAt (fun r : ℝ => r + ε) (1 - s) := by fun_prop
    exact ((Real.continuousAt_log (by linarith)).comp hm).continuousWithinAt.sub
      (((Real.continuousAt_log (by linarith)).comp hp).continuousWithinAt)
  have ha : cfc (fun s : ℝ => 1 - s) R = 1 - R := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) R (by fun_prop) (by fun_prop),
      cfc_const_one ℝ R hR, cfc_id' ℝ R hR]
  have he := cfc_comp (regularizedLogScalar ε) (fun s : ℝ => 1 - s) R hR hc (by fun_prop)
  rw [ha] at he
  rw [← he]
  have hf : (regularizedLogScalar ε ∘ fun s : ℝ => 1 - s) =
      fun s => -regularizedLogScalar ε s := by
    funext s
    unfold regularizedLogScalar
    dsimp
    rw [show 1 - (1 - s) + ε = s + ε by ring]
    ring
  rw [hf, cfc_neg (regularizedLogScalar ε) R]

theorem regularizedModularGroup_polar_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hC := tomitaPolarConjugation_involutive J Ω hsep hcyc
  let e := conjugationRealStarAlgEquiv C hC
  have he : Continuous e := (conjugationRealStarAlgEquiv_isometry C hC).continuous
  change e (NormedSpace.exp (Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val))) = _
  rw [NormedSpace.map_exp e he]
  change NormedSpace.exp (conjugationOperator C
    (Complex.I • ((t : ℂ) • (regularizedModularLog M J Ω ε).val))) = _
  rw [conjugationOperator_smul, conjugationOperator_smul,
    regularizedModularLog_polar_conjugation J Ω hsep hcyc hε]
  simp only [Complex.star_def, Complex.conj_I, Complex.conj_ofReal, smul_neg, neg_smul,
    neg_neg]
  rfl

variable [SeparableSpace H]

theorem modularStrongGroup_polar_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  ext x
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hl := C.continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hsep hcyc t (C x))
  have he (n : ℕ) : C (modularApproximation M J Ω n t (C x)) =
      modularApproximation M J Ω n t x :=
    congrArg (fun A : H →L[ℂ] H => A x)
      (regularizedModularGroup_polar_conjugation J Ω hsep hcyc
        (modularRegularizationScale_pos n) t)
  change Tendsto (fun n => C (modularApproximation M J Ω n t (C x))) atTop
    (𝓝 (C (modularStrongLimit J Ω hsep hcyc t (C x)))) at hl
  simp only [he] at hl
  exact tendsto_nhds_unique hl (modularApproximation_tendsto J Ω hsep hcyc t x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomitaCoreCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded graph coordinates for algebraic Tomita vectors

Every algebra vector is the image of a concrete vector under the square
root of the graph resolvent. Its adjoint vector uses the polar conjugate
of the same coordinate. These are the two boundary data for the KMS strip.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaCoreCoordinate_star (a : Algebra M) :
    tomitaCoreCoordinate J Ω hsep hcyc (star a) =
      tomitaPolarConjugation J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a) := by
  apply (tomitaPolarCoordinates J Ω hsep hcyc).injective
  apply Subtype.ext
  rw [tomitaPolarCoordinates_conjugation]
  change (tomitaPolarCoordinates J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc (star a))).val =
    tomitaGraphFlip J (tomitaPolarCoordinates J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a)).val
  rw [tomitaCoreCoordinate_graph, tomitaCoreCoordinate_graph, tomitaGraphFlip_vector J Ω a]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularKMSVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Resolvent coordinates of the lower KMS boundary -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularRoot_inner_group (t : ℝ) (a b : H) :
    inner ℂ (tomitaGraphRoot (M := M) J Ω a)
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (tomitaGraphRoot (M := M) J Ω b)) =
    inner ℂ a (graphResolvent M J Ω 1
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) b)) := by
  have hc := congrArg (fun T : H →L[ℂ] H => T b)
    (modularStrongGroup_commute_root J Ω hsep hcyc t).eq
  change (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
    (tomitaGraphRoot (M := M) J Ω b) =
    tomitaGraphRoot (M := M) J Ω
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) b) at hc
  rw [hc, ← ContinuousLinearMap.adjoint_inner_right]
  have hs : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot (M := M) J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  rw [hs]
  exact congrArg (inner ℂ a) (congrArg (fun T : H →L[ℂ] H =>
    T ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) b))
      (tomitaGraphRoot_square J Ω))

theorem modularState_lower_resolvent (t : ℝ) (x y : Algebra M) :
    productVectorState Ω
      (unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t)) x.val * y.val) =
    inner ℂ (tomitaCoreCoordinate J Ω hsep hcyc (star x))
      (graphResolvent M J Ω 1
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
          (tomitaCoreCoordinate J Ω hsep hcyc y))) := by
  rw [productVectorState_conjugate_left Ω _
    (modularStrongGroup_fixes_state J Ω hsep hcyc t)]
  have hs : star (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) :=
    congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H))
      (regularGroup_star_eq (modularStrongGroup J Ω hsep hcyc) t)
  rw [hs]
  have hx : star x.val Ω = tomitaGraphRoot (M := M) J Ω
      (tomitaCoreCoordinate J Ω hsep hcyc (star x)) :=
    (tomitaCoreCoordinate_first J Ω hsep hcyc (star x)).symm
  rw [hx, ← tomitaCoreCoordinate_first J Ω hsep hcyc y]
  exact modularRoot_inner_group J Ω hsep hcyc (-t) _ _

theorem polar_resolvent_group (t : ℝ) (a : H) :
    tomitaPolarConjugation J Ω hsep hcyc
      (graphResolvent M J Ω 1
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) a)) =
    (1 - graphResolvent M J Ω 1)
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (tomitaPolarConjugation J Ω hsep hcyc a)) := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hC := tomitaPolarConjugation_involutive J Ω hsep hcyc
  have h := conjugationOperator_mul C hC (graphResolvent M J Ω 1)
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
  rw [tomitaPolarConjugation_resolvent, modularStrongGroup_polar_conjugation] at h
  have hv := congrArg (fun T : H →L[ℂ] H => T (C a)) h
  change C (graphResolvent M J Ω 1
    ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) (C (C a)))) = _ at hv
  have hCa : C (C a) = a := hC a
  rw [hCa] at hv
  exact hv

theorem modularState_upper_resolvent (t : ℝ) (x y : Algebra M) :
    productVectorState Ω
      (y.val * unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t)) x.val) =
    inner ℂ (tomitaCoreCoordinate J Ω hsep hcyc (star x))
      ((1 - graphResolvent M J Ω 1)
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
          (tomitaCoreCoordinate J Ω hsep hcyc y))) := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  let X := tomitaCoreCoordinate J Ω hsep hcyc x
  let Y := tomitaCoreCoordinate J Ω hsep hcyc y
  let T : H →L[ℂ] H := 1 - graphResolvent M J Ω 1
  let u := modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t)
  let v := modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t))
  have hstar : star (u : H →L[ℂ] H) = (v : H →L[ℂ] H) :=
    congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H))
      (regularGroup_star_eq (modularStrongGroup J Ω hsep hcyc) t)
  have hT : T.adjoint = T :=
    ((IsSelfAdjoint.one (R := H →L[ℂ] H)).sub (graphResolvent_positive J Ω 1).isSelfAdjoint).star_eq
  have hvT : Commute (v : H →L[ℂ] H) T :=
    (Commute.one_right _).sub_right (modularStrongGroup_commute_resolvent J Ω hsep hcyc (-t))
  rw [productVectorState_conjugate_right Ω _
    (modularStrongGroup_fixes_state J Ω hsep hcyc t)]
  have hy : star y.val Ω = tomitaGraphRoot (M := M) J Ω (C Y) :=
    (tomitaCoreCoordinate_adjoint J Ω hsep hcyc y).symm
  have hx : x.val Ω = tomitaGraphRoot (M := M) J Ω X :=
    (tomitaCoreCoordinate_first J Ω hsep hcyc x).symm
  rw [hy, hx, modularRoot_inner_group J Ω hsep hcyc t, polar_inner_swap J Ω hsep hcyc,
    polar_resolvent_group J Ω hsep hcyc t]
  change inner ℂ (T ((u : H →L[ℂ] H) (C X))) Y = _
  rw [← ContinuousLinearMap.adjoint_inner_right, hT,
    ← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (C X) (star (u : H →L[ℂ] H) (T Y)) = _
  rw [hstar]
  have he := congrArg (fun A : H →L[ℂ] H => A Y) hvT.eq
  change (v : H →L[ℂ] H) (T Y) = T ((v : H →L[ℂ] H) Y) at he
  rw [he, tomitaCoreCoordinate_star J Ω hsep hcyc x]


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularSpectralStrip
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Analytic strips for matrix coefficients of the graph resolvent -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modularSpectralStrip_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (X Y : H) :
    ContinuousOn (modularSpectralStrip (M := M) J Ω X Y) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ 1} :=
  modularStripIntegral_continuousOn _ _ measurable_subtype_coe _
    (modularSpectralCoefficient_integrable J Ω X Y)
    (graphResolventVectorMeasure_interior J Ω hsep hcyc Y)

theorem modularSpectralStrip_differentiableOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (X Y : H) :
    DifferentiableOn ℂ (modularSpectralStrip (M := M) J Ω X Y) {z : ℂ | 0 < z.im ∧ z.im < 1} :=
  modularStripIntegral_differentiableOn _ _ measurable_subtype_coe _
    (modularSpectralCoefficient_integrable J Ω X Y)
    (graphResolventVectorMeasure_interior J Ω hsep hcyc Y)

theorem modularSpectralStrip_bounded (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (X Y : H) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 →
      ‖modularSpectralStrip (M := M) J Ω X Y z‖ ≤ C := by
  refine ⟨∫ s, ‖modularSpectralCoefficient (M := M) J Ω X Y s‖
    ∂resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint Y,
    fun z hz0 hz1 => ?_⟩
  exact modularStripIntegral_bound _ _ _
    (modularSpectralCoefficient_integrable J Ω X Y)
    (graphResolventVectorMeasure_interior J Ω hsep hcyc Y) ⟨hz0, hz1⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularStripSpectralBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operator boundary values of the spectral strip integral -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)

variable [TopologicalSpace.SeparableSpace H]
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem cyclic_phase_one (Y : H) (t : ℝ) :
    resolventCyclicIsometry (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint Y
      (modularCyclicPhaseOperator M J Ω Y t
        (ContinuousMap.toLp 2 (resolventVectorMeasure (graphResolvent M J Ω 1)
          (graphResolvent_positive J Ω 1).isSelfAdjoint Y) ℂ 1)) =
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) Y := by
  rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc Y,
    resolventCyclicIsometry_one]
  rfl

theorem modularSpectralStrip_bottom (X Y : H) (t : ℝ) :
    modularSpectralStrip (M := M) J Ω X Y (t : ℂ) =
      inner ℂ X (graphResolvent M J Ω 1
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) Y)) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR Y
  let e : ResolventCyclicL2 R hR Y := ContinuousMap.toLp 2 μ ℂ 1
  let w := modularCyclicPhaseOperator M J Ω Y (-t) e
  let v := resolventCoordinateOperator R hR Y w
  apply modularSpectralStrip_eq_inner J Ω X Y _ (t : ℂ) v
  · have hw : w =ᵐ[μ] fun s => modularSpectralPhase (-t) s.val * e s :=
      resolventScalarMultiplier_apply_ae R hR Y _ _ _ _ e
    filter_upwards [resolventCoordinateOperator_apply_ae R hR Y w, hw,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (1 : C(spectrum ℝ R, ℂ))]
      with s hv hw he
    rw [hv, hw, he, ContinuousMap.one_apply, mul_one, modularStripKernel_bottom]
  · exact (resolventCoordinateOperator_intertwines R hR Y w).trans
      (congrArg R (cyclic_phase_one J Ω hsep hcyc Y (-t)))

theorem modularSpectralStrip_top (X Y : H) (t : ℝ) :
    modularSpectralStrip (M := M) J Ω X Y ((t : ℂ) + Complex.I) =
      inner ℂ X ((1 - graphResolvent M J Ω 1)
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) Y)) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR Y
  let e : ResolventCyclicL2 R hR Y := ContinuousMap.toLp 2 μ ℂ 1
  let w := modularCyclicPhaseOperator M J Ω Y (-t) e
  let v := (1 - resolventCoordinateOperator R hR Y) w
  apply modularSpectralStrip_eq_inner J Ω X Y _ ((t : ℂ) + Complex.I) v
  · have hw : w =ᵐ[μ] fun s => modularSpectralPhase (-t) s.val * e s :=
      resolventScalarMultiplier_apply_ae R hR Y _ _ _ _ e
    have hv : v =ᵐ[μ] fun s => w s - (resolventCoordinateOperator R hR Y w) s :=
      (Lp.coeFn_sub w (resolventCoordinateOperator R hR Y w))
    filter_upwards [hv, resolventCoordinateOperator_apply_ae R hR Y w, hw,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (1 : C(spectrum ℝ R, ℂ)),
      graphResolventVectorMeasure_interior J Ω hsep hcyc Y] with s hv hc hw he hs
    rw [hv, hc, hw, he, ContinuousMap.one_apply, mul_one,
      modularStripKernel_top hs.1 hs.2]
    push_cast
    ring
  · exact (one_sub_resolventCoordinateOperator_intertwines R hR Y w).trans
      (congrArg (fun v : H => (1 - R) v) (cyclic_phase_one J Ω hsep hcyc Y (-t)))

end

end KadisonKastler

end OAI
end


