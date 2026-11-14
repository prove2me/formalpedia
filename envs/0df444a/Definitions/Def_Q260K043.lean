-- Prove2me | Definitions.Def_Q260K043
-- name    : Q260K043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T16:16:40.578551+00:00
-- url     : https://prove2.me/theorems/9ae05ac8-b9a0-4209-bff3-de926b19e8d4
-- title:
--   Definitions bundle Q260K043 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 2 definitions and 29 theorems. The definitions and types are `OAI.KadisonKastler.coreTraceLeftCoordinate`, `OAI.KadisonKastler.coreTraceRightCoordinate`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_CoreTraceTomitaCoordinates`, `KadisonKastler_CyclicGaugeKernel`, `KadisonKastler_GraphHighCutInverse`, `KadisonKastler_GraphLowCutBound`, `KadisonKastler_GraphScaleFunctionalCalculus`, `KadisonKastler_ModularActionVector`, `KadisonKastler_ModularAlgebraAutomorphism`, `KadisonKastler_ModularCutBounds`, `KadisonKastler_ModularIsometryTransport`, `KadisonKastler_ModularKMS`, `KadisonKastler_ModularNormalization`, `KadisonKastler_TwoStateCocycleContinuity`, `KadisonKastler_TwoStateCornerCocycle`, `KadisonKastler_TwoStateCornerCovariance`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K039` and `Q260K040` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K046`; the statements `OAI_KadisonKastler_PointedMatrixSites_block_coisometry`, `OAI_KadisonKastler_StateScales_coisometry_adjoint_commutator_bound`, `OAI_KadisonKastler_exists_neighbor_standardTracialPosition` and `OAI_KadisonKastler_positiveCone_polar_conjugation`; the proofs of `OAI_KadisonKastler_StateScales_coisometry_adjoint_commutator_bound`, `OAI.KadisonKastler.constructedCore_traceSymmetry`, `OAI.KadisonKastler.constructedFactorialCore_projectionSemifinite`, `OAI_KadisonKastler_exists_neighbor_standardTracialPosition`, `OAI_KadisonKastler_initial_cyclic_neighbor_of_alignment` and `OAI_KadisonKastler_maximal_admissibleFamily_gap`.
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
import Definitions.Def_Q260K039
import Definitions.Def_Q260K040

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

theorem graphScaleInverse_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousOn (fun s => (graphScaleScalar c s)⁻¹) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  apply ContinuousOn.inv₀ (by unfold graphScaleScalar; fun_prop)
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  exact (graphScaleScalar_pos hc hb.1 hb.2).ne'

theorem graphScaleDenominator_mul_inverse (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    graphScaleDenominator M J Ω c * graphScaleInverse M J Ω c = 1 := by
  rw [graphScaleDenominator_eq_cfc, graphScaleInverse,
    ← cfc_mul (graphScaleScalar c) (fun s => (graphScaleScalar c s)⁻¹) _
      (by unfold graphScaleScalar; fun_prop) (graphScaleInverse_continuousOn J Ω hc)]
  calc
    _ = cfc (fun _ : ℝ => 1) (graphResolvent M J Ω 1) := by
      apply cfc_congr
      intro s hs
      have hb := graphResolvent_spectrum_bounds J Ω hs
      exact mul_inv_cancel₀ (graphScaleScalar_pos hc hb.1 hb.2).ne'
    _ = 1 := cfc_const_one ℝ _ (graphResolvent_positive J Ω 1).isSelfAdjoint

theorem graphResolvent_eq_mul_scaleInverse (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    graphResolvent M J Ω c = graphResolvent M J Ω 1 * graphScaleInverse M J Ω c := by
  calc
    _ = graphResolvent M J Ω c *
        (graphScaleDenominator M J Ω c * graphScaleInverse M J Ω c) := by
      rw [graphScaleDenominator_mul_inverse J Ω hc, mul_one]
    _ = _ := by rw [← mul_assoc, graphResolvent_mul_scaleDenominator]

/-- An arbitrary nonzero graph scale is a bounded rational function of the scale-one resolvent. -/
theorem graphResolvent_eq_cfc_scale (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    graphResolvent M J Ω c =
      cfc (fun s => s / graphScaleScalar c s) (graphResolvent M J Ω 1) := by
  rw [graphResolvent_eq_mul_scaleInverse J Ω hc, graphScaleInverse]
  have hR := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  conv_lhs => lhs; rw [← cfc_id' ℝ (graphResolvent M J Ω 1) hR]
  rw [← cfc_mul (fun s : ℝ => s) (fun s => (graphScaleScalar c s)⁻¹) _
    (by fun_prop) (graphScaleInverse_continuousOn J Ω hc)]
  simp only [div_eq_mul_inv]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphHighCutInverse
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem complementScale_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousOn (fun s => 1 - s / graphScaleScalar c s) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  apply continuousOn_const.sub
  apply continuousOn_id.div (by unfold graphScaleScalar; fun_prop)
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  exact (graphScaleScalar_pos hc hb.1 hb.2).ne'

theorem one_sub_graphResolvent_eq_cfc_scale (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    1 - graphResolvent M J Ω c =
      cfc (fun s => 1 - s / graphScaleScalar c s) (graphResolvent M J Ω 1) := by
  have hquot : ContinuousOn (fun s : ℝ => s / graphScaleScalar c s)
      (spectrum ℝ (graphResolvent M J Ω 1)) := by
    apply continuousOn_id.div (by unfold graphScaleScalar; fun_prop)
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact (graphScaleScalar_pos hc hb.1 hb.2).ne'
  rw [cfc_sub (fun _ : ℝ => 1) (fun s => s / graphScaleScalar c s) _
    continuousOn_const hquot,
    cfc_const_one ℝ _ (graphResolvent_positive J Ω 1).isSelfAdjoint,
    ← graphResolvent_eq_cfc_scale J Ω hc]

theorem graphHighCutInverse_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖graphHighCutInverse M J Ω c r‖ ≤ graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
  have hk : 0 ≤ graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
    exact div_nonneg (graphScaleScalar_pos hc hr hr1.le).le
      (mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hr1.le))
  have hf : ‖cfc (graphHighInverseScalar c r) (graphResolvent M J Ω 1)‖ ≤
      graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
    apply norm_cfc_le hk
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    rw [Real.norm_eq_abs, abs_of_nonneg (graphHighInverseScalar_nonneg hc hr hr1 hb.1)]
    exact graphHighInverseScalar_bound hc hr hr1 hb.1
  calc
    _ ≤ ‖cfc (graphHighInverseScalar c r) (graphResolvent M J Ω 1)‖ *
        ‖resolventLowerCut (graphResolvent M J Ω 1) r‖ := norm_mul_le _ _
    _ ≤ (graphScaleScalar c r / (c ^ 2 * (1 - r))) * 1 :=
      mul_le_mul hf ((resolventLowerCut_projection _ _).norm_le _) (norm_nonneg _) hk
    _ = _ := mul_one _

theorem graphHighCutInverse_identity (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr1 : r < 1) :
    (1 - graphResolvent M J Ω c) * graphHighCutInverse M J Ω c r =
      resolventLowerCut (graphResolvent M J Ω 1) r := by
  let R := graphResolvent M J Ω 1
  let f := graphHighInverseScalar c r
  let g := fun s => 1 - s / graphScaleScalar c s
  have hf : ContinuousOn f (spectrum ℝ R) :=
    (graphHighInverseScalar_continuousOn hc hr1).mono
      (fun s hs => graphResolvent_spectrum_bounds J Ω hs)
  have hg : ContinuousOn g (spectrum ℝ R) := complementScale_continuousOn J Ω hc
  have hz : ((1 - graphResolvent M J Ω c) * cfc f R - 1) * resolventCutGenerator R r = 0 := by
    rw [one_sub_graphResolvent_eq_cfc_scale J Ω hc]
    change (cfc g R * cfc f R - 1) * cfc (fun s : ℝ => max (r - s) 0) R = 0
    rw [← cfc_mul g f R hg hf, ← cfc_const_one ℝ R (graphResolvent_positive J Ω 1).isSelfAdjoint,
      ← cfc_sub (fun s => g s * f s) (fun _ : ℝ => 1) R (hg.mul hf) continuousOn_const,
      ← cfc_mul (fun s => g s * f s - 1) (fun s : ℝ => max (r - s) 0) R
        ((hg.mul hf).sub continuousOn_const) (by fun_prop)]
    calc
      _ = cfc (fun _ : ℝ => 0) R := by
        apply cfc_congr
        intro s hs
        have hb := graphResolvent_spectrum_bounds J Ω hs
        exact graphHighInverseScalar_cut_identity hc hr1 hb.1 hb.2
      _ = 0 := cfc_const_zero ℝ R
  have hp := mul_resolventLowerCut_eq_zero R _ r hz
  rw [sub_mul, one_mul, mul_assoc] at hp
  exact sub_eq_zero.mp hp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphLowCutBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem graphComplementScalar_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousOn (graphComplementScalar c) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  apply continuousOn_const.sub
  apply continuousOn_id.div (by unfold graphScaleScalar; fun_prop)
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  exact (graphScaleScalar_pos hc hb.1 hb.2).ne'

theorem graphLowCut_clipped (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - graphResolvent M J Ω c) * (1 - resolventLowerCut (graphResolvent M J Ω 1) r) =
      cfc (fun s => min (graphComplementScalar c s) (graphComplementScalar c r))
        (graphResolvent M J Ω 1) * (1 - resolventLowerCut (graphResolvent M J Ω 1) r) := by
  let R := graphResolvent M J Ω 1
  let g := graphComplementScalar c
  let f := fun s => min (g s) (g r)
  let k := graphLowFactorScalar c r
  have hg : ContinuousOn g (spectrum ℝ R) := graphComplementScalar_continuousOn J Ω hc
  have hf : ContinuousOn f (spectrum ℝ R) := by
    have hp : ContinuousOn (fun s => (g s, g r)) (spectrum ℝ R) :=
      hg.prodMk continuousOn_const
    exact continuous_min.comp_continuousOn hp
  have hk : ContinuousOn k (spectrum ℝ R) := by
    apply continuousOn_const.div
      ((show ContinuousOn (graphScaleScalar c) (spectrum ℝ R) by
        unfold graphScaleScalar; fun_prop).mul continuousOn_const)
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact mul_ne_zero (graphScaleScalar_pos hc hb.1 hb.2).ne'
      (graphScaleScalar_pos hc hr hr1).ne'
  have hid : cfc g R - cfc f R = cfc k R * resolventCutGenerator R r := by
    rw [← cfc_sub g f R hg hf, resolventCutGenerator,
      ← cfc_mul k (fun s : ℝ => max (r - s) 0) R hk (by fun_prop)]
    apply cfc_congr
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact graphComplementScalar_clipping hc hr hr1 hb.1 hb.2
  have hz : (cfc g R - cfc f R) * (1 - resolventLowerCut R r) = 0 := by
    rw [hid, mul_assoc, resolventCutGenerator_mul_complement R
      (graphResolvent_positive J Ω 1).isSelfAdjoint, mul_zero]
  rw [sub_mul, sub_eq_zero] at hz
  rw [one_sub_graphResolvent_eq_cfc_scale J Ω hc]
  exact hz

theorem graphLowCut_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖(1 - resolventLowerCut (graphResolvent M J Ω 1) r) *
      (1 - graphResolvent M J Ω c)‖ ≤ graphComplementScalar c r := by
  let R := graphResolvent M J Ω 1
  let P := resolventLowerCut R r
  let f := fun s => min (graphComplementScalar c s) (graphComplementScalar c r)
  have hp : IsStarProjection P := resolventLowerCut_projection R r
  have hcomm : Commute P (graphResolvent M J Ω c) := by
    rw [graphResolvent_eq_cfc_scale J Ω hc]
    exact resolventLowerCut_commutes_cfc R (graphResolvent_positive J Ω 1).isSelfAdjoint r _
  have hcomm' : Commute (1 - P) (1 - graphResolvent M J Ω c) :=
    (Commute.one_right _).sub_right ((Commute.one_left _).sub_left hcomm)
  have hg0 := graphComplementScalar_nonneg hc hr hr1
  have hf : ‖cfc f R‖ ≤ graphComplementScalar c r := by
    apply norm_cfc_le hg0
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min
      (graphComplementScalar_nonneg hc hb.1 hb.2) hg0)]
    exact min_le_right _ _
  rw [hcomm'.eq, graphLowCut_clipped J Ω hc hr hr1]
  calc
    _ ≤ ‖cfc f R‖ * ‖1 - P‖ := norm_mul_le _ _
    _ ≤ graphComplementScalar c r * 1 :=
      mul_le_mul hf (hp.one_sub.norm_le _) (norm_nonneg _) hg0
    _ = _ := mul_one _

theorem graphLowCut_support (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    (1 - resolventLowerCut (graphResolvent M J Ω 1) r) * (1 - graphResolvent M J Ω c) *
      (1 - resolventLowerCut (graphResolvent M J Ω 1) r) =
    (1 - resolventLowerCut (graphResolvent M J Ω 1) r) * (1 - graphResolvent M J Ω c) := by
  have hp := (resolventLowerCut_projection (graphResolvent M J Ω 1) r).one_sub
  have hcomm : Commute (resolventLowerCut (graphResolvent M J Ω 1) r)
      (graphResolvent M J Ω c) := by
    rw [graphResolvent_eq_cfc_scale J Ω hc]
    exact resolventLowerCut_commutes_cfc _ (graphResolvent_positive J Ω 1).isSelfAdjoint r _
  have hcomm' := (Commute.one_right _).sub_right ((Commute.one_left _).sub_left hcomm)
  rw [mul_assoc, ← hcomm'.eq, ← mul_assoc, hp.isIdempotentElem.eq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicGaugeKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem cyclicGauge_swap_tensor (f : Lp ℂ 2 (volume : Measure ℝ))
    (v : ModularCyclicSpace M J Ω x) :
    l2ScalarSwap volume (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      ((regularGauge (modularCyclicGroup J Ω hsep hcyc x)
        (modularCyclicGroup_continuous J Ω hsep hcyc x) :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)) (scalarLpTensor volume f v)) =
    (characterField (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) :
      Lp (RegularCoreHilbert ℂ) 2 (resolventVectorMeasure (graphResolvent M J Ω 1)
        (graphResolvent_positive J Ω 1).isSelfAdjoint x) →L[ℂ] _)
      (scalarLpTensor _ v f) := by
  let R := graphResolvent M J Ω 1
  let hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR x
  let U := modularCyclicGroup J Ω hsep hcyc x
  let hU := modularCyclicGroup_continuous J Ω hsep hcyc x
  let l : spectrum ℝ R → ℝ := fun s => resolventLogFrequency s.val
  have hl : Measurable l := resolventLogFrequency_measurable.comp measurable_subtype_coe
  let k : ℝ × spectrum ℝ R → ℂ := fun p => modularSpectralPhase p.1 p.2.val
  let F := (regularGauge U hU : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
    RegularCoreHilbert (ModularCyclicSpace M J Ω x)) (scalarLpTensor volume f v)
  let G := (characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
    Lp (RegularCoreHilbert ℂ) 2 μ) (scalarLpTensor μ v f)
  change l2ScalarSwap volume μ F = G
  apply l2ScalarSwap_of_kernel volume μ (fun t s => k (t, s) * f t * v s) F G
  · exact cyclicGauge_tensor_rows J Ω hsep hcyc x f v
  · have h := characterField_tensor_rows μ l hl f v
    filter_upwards [h] with s hs
    filter_upwards [hs] with t ht
    exact ht.trans (congrArg (fun z : ℂ => z * f t * v s)
      (modularSpectralPhase_eq_character s.val t).symm)
  · intro f' v'
    apply integrable_bounded_L2_kernel volume μ k _ (fun p => (modularSpectralPhase_norm _ _).le) f f' v v'
    change Measurable (fun p : ℝ × spectrum ℝ R =>
      Complex.exp (Complex.I * ((p.1 : ℂ) * (resolventLogFrequency p.2.val : ℂ))))
    exact Complex.continuous_exp.measurable.comp
      (measurable_const.mul ((Complex.continuous_ofReal.measurable.comp measurable_fst).mul
        (Complex.continuous_ofReal.measurable.comp
          (resolventLogFrequency_measurable.comp (measurable_subtype_coe.comp measurable_snd)))))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceTomitaCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common spectral coordinates for the two trace-boundary vectors

The algebra vector and its conjugate adjoint use square-root weights
in one cyclic resolvent model. These coordinates let the clipped
exponential translation law be applied to both sides of a monomial.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def coreTraceLeftCoordinate (a : Algebra M) :
    ModularCyclicSpace M J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) :=
  ContinuousMap.toLp 2
    (modularCyclicMeasure (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)) ℂ
    (resolventSqrtFunction (graphResolvent M J Ω 1))

def coreTraceRightCoordinate (a : Algebra M) :
    ModularCyclicSpace M J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) :=
  ContinuousMap.toLp 2
    (modularCyclicMeasure (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)) ℂ
    (resolventComplementSqrtFunction (graphResolvent M J Ω 1))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularAlgebraAutomorphism
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular automorphism group on the represented algebra -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem modularAlgebraAut_coe (m : ModularSpectralResolution M Ω) (t : Multiplicative ℝ)
    (a : Algebra M) : (modularAlgebraAut m t a).val = unitaryConj (m.group t) a.val := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularActionVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The vector implementation and strong continuity of the modular algebra action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H} (m : ModularSpectralResolution M Ω)

theorem modularAlgebraAut_vector (t : Multiplicative ℝ) (a : Algebra M) :
    (modularAlgebraAut m t a).val Ω = (m.group t : H →L[ℂ] H) (a.val Ω) := by
  rw [modularAlgebraAut_coe]
  change (m.group t : H →L[ℂ] H) (a.val ((star (m.group t) : H →L[ℂ] H) Ω)) = _
  have hs : (star (m.group t) : H →L[ℂ] H) Ω = Ω := by
    have he : star (m.group t) = m.group t⁻¹ := by
      change (m.group t)⁻¹ = m.group t⁻¹
      exact (map_inv m.group t).symm
    rw [← Unitary.coe_star, he]
    exact m.isModular.fixes_vector _
  rw [hs]

theorem modularAlgebraAut_strongContinuous (a : Algebra M) (x : H) :
    Continuous (fun t : ℝ => (modularAlgebraAut m (Multiplicative.ofAdd t) a).val x) := by
  have hs (y : H) : Continuous (fun t : ℝ =>
      (star (m.group (Multiplicative.ofAdd t)) : H →L[ℂ] H) y) := by
    simp_rw [← Unitary.coe_star, regularGroup_star_eq]
    exact (m.continuous y).comp continuous_neg
  change Continuous (fun t : ℝ => (m.group (Multiplicative.ofAdd t) : H →L[ℂ] H)
    (a.val ((star (m.group (Multiplicative.ofAdd t)) : H →L[ℂ] H) x)))
  exact continuous_unitary_field_apply _ m.continuous _ (a.val.continuous.comp (hs x))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCutBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative modular cuts in every graph identification

The graph comparison controls three bounded spectral cuts. These estimates
are independent of the KMS condition and the Fourier gauge identity.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem modularUpperCut_high_inverse (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ∃ R : H →L[ℂ] H,
      ‖R‖ ≤ 1 + Real.exp (-(1 / 2 : ℝ)) ∧
      (1 - graphResolvent M K Ω (Real.exp (-a / 2))) * R =
        modularUpperCut M J Ω (a + 1 / 2) ∧
      modularUpperCut M J Ω (a + 1 / 2) * R = R := by
  rw [modularUpperCut_identification_independent J K]
  refine ⟨graphHighCutInverse M K Ω (Real.exp (-a / 2))
    (modularCutThreshold (a + 1 / 2)), ?_, ?_, ?_⟩
  · have hb := graphHighCutInverse_bound (M := M) K Ω (Real.exp_ne_zero (-a / 2))
      (modularCutThreshold_pos (a + 1 / 2)).le (modularCutThreshold_lt_one (a + 1 / 2))
    exact hb.trans_eq (graphHighInverse_bound_exp a)
  · exact graphHighCutInverse_identity K Ω (Real.exp_ne_zero _) (modularCutThreshold_lt_one _)
  · exact graphHighCutInverse_supported K Ω _ _

theorem modularUpperCut_low_bound (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ‖(1 - modularUpperCut M J Ω (a - 1 / 2)) *
      (1 - graphResolvent M K Ω (Real.exp (-a / 2)))‖ ≤
      Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ))) := by
  rw [modularUpperCut_identification_independent J K]
  exact (graphLowCut_bound K Ω (Real.exp_ne_zero _)
    (modularCutThreshold_pos _).le (modularCutThreshold_lt_one _).le).trans_eq
      (graphComplementScalar_exp a)

theorem modularUpperCut_low_support (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    (1 - modularUpperCut M J Ω (a - 1 / 2)) *
      (1 - graphResolvent M K Ω (Real.exp (-a / 2))) *
      (1 - modularUpperCut M J Ω (a - 1 / 2)) =
    (1 - modularUpperCut M J Ω (a - 1 / 2)) *
      (1 - graphResolvent M K Ω (Real.exp (-a / 2))) := by
  rw [modularUpperCut_identification_independent J K]
  exact graphLowCut_support K Ω (Real.exp_ne_zero _) _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularIsometryTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transport of the modular group along a reducing Hilbert isometry -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K) (Ω : H) (ξ : K)
  (V : H →ₗᵢ[ℂ] K)
  (hR : ∀ x, graphResolvent N L ξ 1 (V x) = V (graphResolvent M J Ω 1 x))

include hR in
theorem modularApproximation_isometry (n : ℕ) (t : ℝ) (x : H) :
    modularApproximation N L ξ n t (V x) = V (modularApproximation M J Ω n t x) := by
  have he : (graphResolvent N L ξ 1).comp V.toContinuousLinearMap =
      V.toContinuousLinearMap.comp (graphResolvent M J Ω 1) := by
    ext y
    exact hR y
  have h := cfc_rectangular_intertwines _ _ V.toContinuousLinearMap
    (graphResolvent_positive L ξ 1).isSelfAdjoint
    (graphResolvent_positive J Ω 1).isSelfAdjoint he
    (modularPhaseScalar t (modularRegularizationScale n))
    (modularPhaseScalar_continuousOn L ξ t (modularRegularizationScale_pos n))
    (modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n))
  have hx := congrArg (fun T : H →L[ℂ] K => T x) h
  change (regularizedModularGroup N L ξ (modularRegularizationScale n)
    (Multiplicative.ofAdd t) : K →L[ℂ] K) (V x) =
    V ((regularizedModularGroup M J Ω (modularRegularizationScale n)
      (Multiplicative.ofAdd t) : H →L[ℂ] H) x)
  rw [regularizedModularGroup_eq_cfc L ξ t (modularRegularizationScale_pos n),
    regularizedModularGroup_eq_cfc J Ω t (modularRegularizationScale_pos n)]
  exact hx

variable [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hMcyc : DenseRange (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))
  (hNcyc : DenseRange (algebraVectorMap N ξ))

include hR in
theorem modularStrongGroup_isometry (t : Multiplicative ℝ) (x : H) :
    (modularStrongGroup L ξ hNsep hNcyc t : K →L[ℂ] K) (V x) =
      V ((modularStrongGroup J Ω hMsep hMcyc t : H →L[ℂ] H) x) := by
  have hK := modularApproximation_tendsto L ξ hNsep hNcyc t.toAdd (V x)
  have hH := V.continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hMsep hMcyc t.toAdd x)
  have he (n : ℕ) := modularApproximation_isometry J L Ω ξ V hR n t.toAdd x
  change Tendsto (fun n => V (modularApproximation M J Ω n t.toAdd x)) atTop
    (𝓝 (V (modularStrongLimit J Ω hMsep hMcyc t.toAdd x))) at hH
  simp_rw [← he] at hH
  exact tendsto_nhds_unique hK hH

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularKMS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The KMS condition for the constructed modular group

The graph coordinates give both boundary values of a bounded holomorphic
strip. No normalization or commutant theorem is assumed here.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularStrongGroup_kms :
    VectorStateKMS M Ω (modularStrongGroup J Ω hsep hcyc) := by
  intro x hx y hy
  let a : Algebra M := ⟨x, hx⟩
  let b : Algebra M := ⟨y, hy⟩
  let X := tomitaCoreCoordinate J Ω hsep hcyc (star a)
  let Y := tomitaCoreCoordinate J Ω hsep hcyc b
  refine ⟨modularSpectralStrip (M := M) J Ω X Y,
    modularSpectralStrip_continuousOn J Ω hsep hcyc X Y,
    modularSpectralStrip_differentiableOn J Ω hsep hcyc X Y,
    modularSpectralStrip_bounded J Ω hsep hcyc X Y, ?_, ?_⟩
  · intro t
    exact (modularSpectralStrip_bottom J Ω hsep hcyc X Y t).trans
      (modularState_lower_resolvent J Ω hsep hcyc t a b).symm
  · intro t
    exact (modularSpectralStrip_top J Ω hsep hcyc X Y t).trans
      (modularState_upper_resolvent J Ω hsep hcyc t a b).symm

theorem modularStrongGroup_isModular :
    IsModularStateGroup M Ω (modularStrongGroup J Ω hsep hcyc) where
  fixes_vector t := modularStrongGroup_fixes_state J Ω hsep hcyc t.toAdd
  kms := modularStrongGroup_kms J Ω hsep hcyc

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularNormalization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem modularStrongGroup_normalizes (t : Multiplicative ℝ) :
    Conjugates (modularStrongGroup J Ω hsep hcyc t) M M := by
  change unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t.toAdd)) ''
    (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact modularStrongGroup_conj_mem J Ω hsep hcyc t.toAdd hb
  · intro ha
    have h := modularStrongGroup_conj_mem J Ω hsep hcyc (-t.toAdd) ha
    rw [← regularGroup_star_eq] at h
    refine ⟨_, h, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj
      (star (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t.toAdd))) a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateCornerCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The algebraic cocycle between the two modular corners -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (m : ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

theorem twoStateCornerCocycle_mul (s t : Multiplicative ℝ) :
    (twoStateCornerCocycle M Ω ξ m (s * t) : Algebra M) =
      (twoStateCornerCocycle M Ω ξ m s : Algebra M) *
        twoStateCornerAction M Ω ξ m 0 s (twoStateCornerCocycle M Ω ξ m t : Algebra M) :=
  matrixActionCocycleValue_mul _ _ s t

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateCocycleContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (m : ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

theorem twoStateMatrixAut_entry_continuous (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M))
    (i j : Fin 2) (x : H) :
    Continuous (fun t : ℝ => (twoStateMatrixAut M Ω ξ m (Multiplicative.ofAdd t) a i j).val x) := by
  have he (t : Multiplicative ℝ) : twoStateMatrixEquiv M (twoStateMatrixAut M Ω ξ m t a) =
      modularAlgebraAut m t (twoStateMatrixEquiv M a) := by
    change (twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm _) = _
    exact (twoStateMatrixEquiv M).apply_symm_apply _
  have hp : Continuous (fun v : TwoStateMatrixHilbert H H => v.fst i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => H) i).comp (by fun_prop)
  have h := hp.comp (modularAlgebraAut_strongContinuous m (twoStateMatrixEquiv M a)
    (twoStateFirstColumnVector j x))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  change (twoStateMatrixAut M Ω ξ m (Multiplicative.ofAdd t) a i j).val x =
    ((modularAlgebraAut m (Multiplicative.ofAdd t) (twoStateMatrixEquiv M a)).val
      (twoStateFirstColumnVector j x)).fst i
  rw [← he, twoStateMatrixEquiv_firstEntry]

theorem twoStateCornerCocycle_continuous (x : H) :
    Continuous (fun t : ℝ => (twoStateCornerCocycle M Ω ξ m (Multiplicative.ofAdd t) :
      Algebra M).val x) :=
  twoStateMatrixAut_entry_continuous M Ω ξ m (matrixSlot 1 0 1) 1 0 x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoStateCornerCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular implementation of each corner action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (m : ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

theorem twoStateCornerAction_reconstruct (t : Multiplicative ℝ) (i : Fin 2)
    (a : Algebra M) :
    twoStateMatrixAut M Ω ξ m t (matrixSlot i i a) =
      matrixSlot i i (twoStateCornerAction M Ω ξ m i t a) :=
  matrixSlot_image_reconstruct _ _ _ (twoStateMatrixAut_fixes_diagonal M Ω ξ m t i)
    (twoStateMatrixAut_fixes_diagonal M Ω ξ m t i) a

theorem twoStateCornerAction_vector (t : Multiplicative ℝ) (i : Fin 2) (a : Algebra M) :
    twoStateCornerEmbedding i ((twoStateCornerAction M Ω ξ m i t a).val
      (twoStateVectorAt Ω ξ i)) =
        (m.group t : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H)
          (twoStateCornerEmbedding i (a.val (twoStateVectorAt Ω ξ i))) := by
  rw [twoStateCornerEmbedding_vector,
    ← twoStateCornerAction_reconstruct M Ω ξ m t i a,
    twoStateCornerEmbedding_vector]
  have he : twoStateMatrixEquiv M (twoStateMatrixAut M Ω ξ m t (matrixSlot i i a)) =
      modularAlgebraAut m t (twoStateMatrixEquiv M (matrixSlot i i a)) := by
    change (twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm _) = _
    exact (twoStateMatrixEquiv M).apply_symm_apply _
  rw [he, modularAlgebraAut_coe]
  have hf : (star (m.group t) : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H)
      (twoStateMatrixVector Ω ξ) = twoStateMatrixVector Ω ξ := by
    have he : star (m.group t) = m.group t⁻¹ := by
      change (m.group t)⁻¹ = m.group t⁻¹
      exact (map_inv m.group t).symm
    rw [← Unitary.coe_star, he]
    exact m.isModular.fixes_vector _
  change (m.group t : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H) ((twoStateMatrixEquiv M (matrixSlot i i a)).val
    ((star (m.group t) : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H) (twoStateMatrixVector Ω ξ))) = _
  rw [hf]

end

end KadisonKastler

end OAI
end


