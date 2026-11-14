-- Prove2me | Definitions.Def_Q260K050
-- name    : Q260K050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T21:53:39.160975+00:00
-- url     : https://prove2.me/theorems/741a819e-da31-4276-b33f-dfb5937e18f4
-- title:
--   Definitions bundle Q260K050 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 5 definitions and 5 theorems. The definitions and types are `OAI.KadisonKastler.constructedModularSpectralResolution`, `OAI.KadisonKastler.constructedStateCocycle`, `OAI.KadisonKastler.tracialModularSpectralResolution`, `OAI.KadisonKastler.twoStateConstructedResolution`, `OAI.KadisonKastler.twoStateCornerResolution`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonKastler_ConstructedModularData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ConstructedModularData.lean), [`KadisonKastler_ConstructedStateCocycle`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ConstructedStateCocycle.lean), [`KadisonKastler_ModularGaugeIdentity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularGaugeIdentity.lean), [`KadisonKastler_ModularGaugeTransport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ModularGaugeTransport.lean), [`KadisonKastler_TracialModularResolution`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TracialModularResolution.lean), [`KadisonKastler_TwoStateModularIdentification`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TwoStateModularIdentification.lean).
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundle `Q260K049` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K051`; the statement `OAI_KadisonKastler_PointedMatrixSites_exists_spatial_modular_coisometries`; the proofs of `OAI_KadisonKastler_TypeIIIFactor_exists_bounded_selfAdjoint_split`, `OAI.KadisonKastler.constructedCore_equiv_of_two_states`, `OAI.KadisonKastler.cyclicOrbitProjection_not_finite`, `OAI.KadisonKastler.exists_spatial_of_normal_cyclic_separating`, `OAI_KadisonKastler_expectedMatrixSubfactorModel_of_local_refinement`, `OAI.KadisonKastler.haagerup_witnesses_of_polar_coisometries`, `OAI.KadisonKastler.kmsGroup_eq_constructed`, `OAI.KadisonKastler.modularCore_equiv_of_normal`, `OAI.KadisonKastler.regularCore_not_factor_of_II1`, `OAI.KadisonKastler.regularCore_not_factor_of_normal_centralizing_corner`, `OAI_KadisonKastler_regularCore_spatial_of_matrix_corner`, `OAI_KadisonKastler_spatialMatrix_union_weakUnitBallDense` and `OAI.KadisonKastler.uniform_factor_strong_stability`.
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
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.LinearAlgebra.Complex.Module
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
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
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
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
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
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
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
import Definitions.Def_Q260K049

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularGaugeTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem modularCyclicEmbedding_gauge_fourier (a : ℝ)
    (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    (𝓕 ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          ((modularCyclicEmbedding (M := M) J Ω x).compLp F)))) : RegularCoreHilbert H) =
      modularUpperCutField M J Ω a (𝓕 ((modularCyclicEmbedding (M := M) J Ω x).compLp F)) := by
  let L := modularCyclicEmbedding (M := M) J Ω x
  exact fourier_intertwines_of_transport L
    ((star (modularCyclicGauge J Ω hsep hcyc x) :
      RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
        RegularCoreHilbert (ModularCyclicSpace M J Ω x)) * regularFrequencyProjection a *
      (modularCyclicGauge J Ω hsep hcyc x :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)))
    (modularCyclicCutField M J Ω x a)
    ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * regularFrequencyProjection a *
      (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (modularUpperCutField M J Ω a)
    (compLp_regularGaugeFrequency L (modularCyclicGroup J Ω hsep hcyc x)
      (modularStrongGroup J Ω hsep hcyc) (modularCyclicGroup_continuous J Ω hsep hcyc x)
      (modularStrongGroup_continuous J Ω hsep hcyc)
      (modularCyclicEmbedding_group J Ω hsep hcyc x) a)
    (modularCyclicEmbedding_cutField J Ω x a)
    (cyclicGauge_fourier J Ω hsep hcyc x a) F

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularGaugeIdentity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The Fourier gauge identity for the constructed modular group -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularGauge_fourier_tensor (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    (𝓕 ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          (scalarLpTensor volume f x)))) : RegularCoreHilbert H) =
      modularUpperCutField M J Ω a (𝓕 (scalarLpTensor volume f x)) := by
  let μ := modularCyclicMeasure (M := M) J Ω x
  let v : ModularCyclicSpace M J Ω x := ContinuousMap.toLp 2 μ ℂ 1
  have hv : modularCyclicEmbedding (M := M) J Ω x v = x :=
    resolventCyclicIsometry_one (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x
  have ht : (modularCyclicEmbedding (M := M) J Ω x).compLp (scalarLpTensor volume f v) =
      scalarLpTensor volume f x := by
    rw [compLp_scalarLpTensor, hv]
  have h := modularCyclicEmbedding_gauge_fourier J Ω hsep hcyc x a (scalarLpTensor volume f v)
  rw [ht] at h
  exact h

theorem modularGauge_fourier (a : ℝ) (F : RegularCoreHilbert H) :
    (𝓕 ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) F))) : RegularCoreHilbert H) =
      modularUpperCutField M J Ω a (𝓕 F) := by
  let G := regularGauge (modularStrongGroup J Ω hsep hcyc)
    (modularStrongGroup_continuous J Ω hsep hcyc)
  let A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (Lp.fourierTransformₗᵢ ℝ H).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection a * (G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
  let B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (modularUpperCutField M J Ω a).comp
      (Lp.fourierTransformₗᵢ ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  change A F = B F
  refine (l2TensorEmbedding_dense volume).induction_on (p := fun F => A F = B F) F ?_ ?_
  · exact isClosed_eq A.continuous B.continuous
  · intro z
    induction z using OAI.tensorInductionOn with
    | tmul f x => exact modularGauge_fourier_tensor J Ω hsep hcyc a f x
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

theorem modularGauge_identity (a : ℝ) :
    (star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      regularFrequencyProjection a *
      (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (modularUpperCutField M J Ω a) := by
  exact linearIsometryEquiv_conjugate_of_intertwines (Lp.fourierTransformₗᵢ ℝ H) _ _
    (modularGauge_fourier J Ω hsep hcyc a)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedModularData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Spectral modular data for a modular group normalizing the algebra. -/
def constructedModularSpectralResolution
    (hnormal : ∀ t, Conjugates (modularStrongGroup J Ω hsep hcyc t) M M) :
    ModularSpectralResolution M Ω where
  group := modularStrongGroup J Ω hsep hcyc
  continuous := modularStrongGroup_continuous J Ω hsep hcyc
  normalizes := hnormal
  isModular := modularStrongGroup_isModular J Ω hsep hcyc
  centralizer_fixed := modularStrongGroup_centralizer_fixed J Ω hsep hcyc hnormal
  upperCut := modularUpperCut M J Ω
  projection := modularUpperCut_projection J Ω
  upper_contracts := modularUpperCut_contracts J Ω
  lower_contracts := modularUpperCut_complement_contracts J Ω
  measurable := modularUpperCut_measurable J Ω
  gauge_identity := modularGauge_identity J Ω hsep hcyc
  high_inverse K := modularUpperCut_high_inverse J K Ω
  low_bound K := modularUpperCut_low_bound J K Ω
  low_support K := modularUpperCut_low_support J K Ω

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateModularIdentification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Identifying both diagonal modular actions with their original states -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
  (hΩs : Function.Injective (algebraVectorMap M Ω))
  (hξs : Function.Injective (algebraVectorMap M ξ))

def twoStateConstructedResolution
    (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H) :
    ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ) :=
  constructedModularSpectralResolution L (twoStateMatrixVector Ω ξ)
    (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
    (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc)
    (modularStrongGroup_normalizes L (twoStateMatrixVector Ω ξ)
      (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
      (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc))

def twoStateCornerResolution (J : H ≃ₗᵢ⋆[ℂ] H) (i : Fin 2) :
    ModularSpectralResolution M (twoStateVectorAt Ω ξ i) :=
  constructedModularSpectralResolution J (twoStateVectorAt Ω ξ i)
    (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
    (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)
    (modularStrongGroup_normalizes J (twoStateVectorAt Ω ξ i)
      (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
      (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i))

theorem twoStateCornerAction_identification (J : H ≃ₗᵢ⋆[ℂ] H)
    (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H)
    (i : Fin 2) (t : Multiplicative ℝ) (a : Algebra M) :
    twoStateCornerAction M Ω ξ (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) i t a =
      modularAlgebraAut (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs J i) t a := by
  apply twoStateVectorAt_separating M Ω ξ hΩs hξs i
  change (twoStateCornerAction M Ω ξ _ i t a).val (twoStateVectorAt Ω ξ i) =
    (modularAlgebraAut _ t a).val (twoStateVectorAt Ω ξ i)
  rw [modularAlgebraAut_vector]
  apply (twoStateCornerEmbedding i).injective
  rw [twoStateCornerAction_vector]
  exact modularStrongGroup_isometry J L (twoStateVectorAt Ω ξ i) (twoStateMatrixVector Ω ξ)
    (twoStateCornerEmbedding i) (twoStateCorner_resolvent M Ω ξ i J L 1)
    (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
    (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)
    (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
    (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) t (a.val (twoStateVectorAt Ω ξ i))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedStateCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A constructed cocycle comparing two faithful cyclic vector states

The two-by-two matrix modular action yields a strongly-star continuous
unitary cocycle. Its diagonal restrictions are identified through the actual
closed Tomita graphs. Thus the cores of the two constructed modular groups
are isomorphic without a change-of-state premise.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
  (hΩs : Function.Injective (algebraVectorMap M Ω))
  (hξs : Function.Injective (algebraVectorMap M ξ))
  (J K : H ≃ₗᵢ⋆[ℂ] H)
  (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H)

def constructedStateCocycle : ModularActionCocycle M
    (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs J 0).group
    (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs K 1).group where
  value t := Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)
    (twoStateCornerCocycle M Ω ξ (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) t)
  mem t := (twoStateCornerCocycle M Ω ξ
    (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) t : Algebra M).property
  continuous x := twoStateCornerCocycle_continuous M Ω ξ _ x
  continuous_star x := twoStateCornerCocycle_star_continuous M Ω ξ _ x
  value_mul s t := by
    have h := congrArg Subtype.val (twoStateCornerCocycle_mul M Ω ξ
      (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) s t)
    rw [twoStateCornerAction_identification M Ω ξ hΩc hξc hΩs hξs J L] at h
    exact h
  action t a ha := by
    have h := congrArg Subtype.val (twoStateCornerAction_conjugate M Ω ξ
      (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) t ⟨a, ha⟩)
    rw [twoStateCornerAction_identification M Ω ξ hΩc hξc hΩs hξs K L,
      twoStateCornerAction_identification M Ω ξ hΩc hξc hΩs hξs J L] at h
    exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TracialModularResolution
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tracial specialization of the constructed modular operators

For a tracial vector state the group is the identity on a dense algebra
orbit. Its normalization clause is therefore unconditional. The polar
conjugation acts by adjoint and gives the right multiplication operators.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))
  (htrace : ∀ a b : Algebra M,
    inner ℂ Ω ((a.val * b.val) Ω) = inner ℂ Ω ((b.val * a.val) Ω))

include htrace

variable [TopologicalSpace.SeparableSpace H]

def tracialModularSpectralResolution : ModularSpectralResolution M Ω :=
  constructedModularSpectralResolution J Ω hsep hcyc (fun t => by
    rw [modularStrongGroup_tracial J Ω hsep hcyc htrace t]
    exact conjugates_one M)

end

end KadisonKastler

end OAI
end


